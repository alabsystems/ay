// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Lane driver: posture, deepening loop, SAT solve and publication.

use std::collections::BTreeMap;
use std::time::Duration;

use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::{TermId, TseitinResult};
use ay_frontend::OptionValue;
use ay_sat::{Literal, SatResult, Solver as SatSolver, Variable};

use super::decode::Decoder;
use super::encode::{initial_depth, Encoder};
use super::export::Accepted;
use super::guards::{alias_map, guarded_selectors};
use super::memory;
use super::scan::{FieldSort, Node, Scan, SortShape};
use super::MAX_ROUNDS;
use crate::executor::theories::ChainSpend;
use crate::executor::Executor;
use crate::executor_types::{Result, SolveResult};

/// Clause budget of one encoding (the largest blocksworld file needs ~3.3M).
const MAX_CLAUSES: usize = 24_000_000;
/// Largest cell count the lane will encode.
const MAX_D: usize = 256;
/// Work budget of the `D_0` heuristic.
const MAX_DEPTH_WORK: usize = 20_000_000;
/// Wall cap of the SAT-only posture (default, proofs, self-check). A wall
/// backstop on purpose: each SAT search is also armed with the counted
/// allowances (`arm_sat_count_budget`), which stop it first under `:rlimit`.
const SAT_ONLY_CAP: Duration = Duration::from_secs(4);
#[cfg(test)]
thread_local! {
    /// Test-only cell-count override (the soundness tests force tiny `D`).
    pub(super) static D_OVERRIDE: std::cell::Cell<Option<usize>> =
        const { std::cell::Cell::new(None) };
    /// Test-only record of `solve_deadline` when publication began.
    pub(super) static PUBLICATION_DEADLINE: std::cell::Cell<Option<Option<ay_core::time::Instant>>> =
        const { std::cell::Cell::new(None) };
}

/// What the lane may publish.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(super) enum Posture {
    /// `--z3-mode`: validated SAT and Theorem-1 UNSAT.
    Full,
    /// Every other posture: validated SAT only.
    SatOnly,
}

/// Outcome of one encode-and-solve round.
enum Round {
    /// A model the lane's evaluator accepted: its CNF model and its values.
    Sat(Vec<bool>, Accepted),
    Unsat(SatResult),
    /// Rejected model with a deep value: retry with more cells.
    Spurious,
    /// Decline (budget, size, interrupt, shallow rejection).
    GiveUp(&'static str),
}

impl Round {
    fn label(&self) -> &'static str {
        match self {
            Round::Sat(..) => "sat",
            Round::Unsat(_) => "unsat",
            Round::Spurious => "spurious",
            Round::GiveUp(why) => why,
        }
    }
}

impl Executor {
    /// Try the finite-domain datatype lane. `Ok(None)` means "not applicable
    /// or not decided — use the general lanes" (always sound to return).
    ///
    /// The whole attempt runs inside the DT lanes' speculative bracket
    /// (`dt_abandon.rs`, #dt-lazy-abandon-restore). The occurs-check and the
    /// SAT export create terms and the validation pipeline records model
    /// artifacts; an attempt that does not decide is erased (term store,
    /// proof ledger, term-indexed caches, assertion window), so the fallback
    /// lanes start from exactly the state they would have had without this
    /// lane. A decided attempt commits. (Without the bracket, terms left over
    /// from a rejected publication changed the lazy lane's atom set and lost
    /// verdicts the fallback lanes decide on main.)
    pub(in crate::executor) fn try_solve_dt_finite_domain(
        &mut self,
    ) -> Result<Option<SolveResult>> {
        // The lane reads only `ctx.assertions`. Live assumptions are carried
        // separately on the assumption routes, which run the lane on the
        // merged window instead (`try_dt_finite_domain_assuming`). A push/pop
        // session is no reason to decline: `ctx.assertions` is the whole
        // scoped stack at every check, and the lane keeps no state across
        // commands (its CNF and solver are per check). Declining there handed
        // the next check of a session whose earlier check the lane decided to
        // the eager incremental route cold, which main's warm session never
        // asks it to be, and that route spent the whole budget on queries main
        // answers at once (#dt-fd-session, E13 round 6 `e13only_hang_*`).
        if self.last_assumptions.is_some() {
            self.last_statistics
                .set_string("dt_fd.decline", "assumptions");
            return Ok(None);
        }
        // A certification re-solve of an obligation the outer solve already
        // refuted (`new_derived_query_executor`) wants UNSAT, which the
        // SAT-only posture can never publish: running the lane there
        // re-encodes and re-refutes the same CNF for nothing, and the time it
        // takes comes out of the lanes that can answer (#dt-fd-reentry: three
        // full passes in one default-posture check-sat). A derived query that
        // asks whether the problem is SAT (the forged-UNSAT guard) keeps it.
        if self.certification_resolve && self.dt_fd_posture() == Posture::SatOnly {
            self.last_statistics
                .set_string("dt_fd.decline", "derived-query");
            return Ok(None);
        }
        // The gate is read-only (`&self`), so a declined query never opens the
        // bracket and leaves every other lane's state untouched.
        let scan = match self.dt_fd_scan() {
            Ok(scan) => scan,
            Err(why) => {
                tracing::debug!(target: "ay_dpll::dt_fd", decline = %why, "dt-fd lane declined");
                self.last_statistics.set_string("dt_fd.decline", &why);
                return Ok(None);
            }
        };
        // The same window, already left undecided by this command, would
        // be re-encoded and re-searched for the same outcome with less time
        // (#dt-fd-session).
        let mut window = self.ctx.assertions.clone();
        window.sort_unstable();
        window.dedup();
        if self.dt_fd_undecided_windows.contains(&window) {
            self.last_statistics
                .set_string("dt_fd.decline", "undecided-this-command");
            return Ok(None);
        }
        let Some(entry) = self.dt_lazy_capture_entry_state() else {
            self.last_statistics
                .set_string("dt_fd.decline", "no-checkpoint");
            return Ok(None);
        };
        let first_term = self.ctx.terms.len();
        match self.dt_fd_attempt(&scan) {
            Ok(None) => {
                self.dt_fd_undecided_windows.push(window);
                self.dt_lazy_discard_attempt(entry, "dt-fd");
                // What an undecided attempt left behind (when the store
                // could not be rolled back) is history for every later
                // axiom scan (#dt-live-scan).
                self.record_dt_history_term_range(first_term, self.ctx.terms.len());
                Ok(None)
            }
            decided => {
                self.dt_lazy_commit_attempt(entry);
                // From this command on, every decision command's terms
                // become history when it ends (#dt-live-scan).
                self.dt_fd_decided_command = true;
                decided
            }
        }
    }

    /// The lane proper (inside the bracket of [`Self::try_solve_dt_finite_domain`]).
    fn dt_fd_attempt(&mut self, scan: &Scan) -> Result<Option<SolveResult>> {
        // A cyclic constraint is never refuted by the lane (Theorem 1 has no
        // acyclicity); leave it to the lanes that run the occurs-check.
        let roots = scan.roots.clone();
        if self.dt_occurs_check_unsat_from_equalities(&roots, &[]) {
            self.last_statistics
                .set_string("dt_fd.decline", "occurs-check");
            return Ok(None);
        }
        let posture = self.dt_fd_posture();
        // The SAT-only cap bounds the lane's SEARCH (encode + solve), never
        // its publication: validation polls `solve_deadline`, and a stop it
        // observes is recorded STICKY in the decision's evaluation attempt, so
        // a publication run under the cap turned a model found in time into
        // `unknown (timeout)` for the whole check-sat and skipped every
        // fallback lane (#dt-fd-cap-publication).
        let cap = match (posture, self.solve_deadline.get()) {
            (Posture::Full, _) => None,
            (Posture::SatOnly, outer) => {
                let now = ay_core::time::Instant::now();
                match outer {
                    Some(d) if d <= now => return Ok(None),
                    Some(d) => Some(now + ((d - now) / 8).min(SAT_ONLY_CAP)),
                    None => Some(now + SAT_ONLY_CAP),
                }
            }
        };
        self.dt_fd_rounds(scan, posture, cap)
    }

    fn dt_fd_posture(&self) -> Posture {
        let cores = matches!(
            self.ctx.get_option("produce-unsat-cores"),
            Some(OptionValue::Bool(true))
        );
        if self.competition_shedding_active() && !cores {
            Posture::Full
        } else {
            Posture::SatOnly
        }
    }

    fn dt_fd_rounds(
        &mut self,
        scan: &Scan,
        posture: Posture,
        cap: Option<ay_core::time::Instant>,
    ) -> Result<Option<SolveResult>> {
        let alias = alias_map(scan);
        let (guarded, unguarded) = guarded_selectors(scan);
        if tracing::enabled!(target: "ay_dpll::dt_fd", tracing::Level::TRACE) {
            for &t in unguarded.iter().take(8) {
                let shown = self.format_term(t);
                tracing::trace!(target: "ay_dpll::dt_fd", selector = %shown, "unguarded selector");
            }
            for &r in &scan.roots {
                let mut shown = self.format_term(r);
                shown.truncate(4000);
                tracing::trace!(target: "ay_dpll::dt_fd", root = %shown, "root");
            }
        }
        let mut d = initial_depth(scan, MAX_DEPTH_WORK).clamp(1, MAX_D);
        #[cfg(test)]
        if let Some(forced) = D_OVERRIDE.with(std::cell::Cell::get) {
            d = forced;
        }
        let stats = &mut self.last_statistics;
        stats.set_int("dt_fd.guarded_selectors", guarded.len() as u64);
        stats.set_int("dt_fd.aliases", alias.len() as u64);
        let mut reason = "rounds-exhausted";
        for round in 0..=MAX_ROUNDS {
            self.last_statistics
                .set_int("dt_fd.rounds", round as u64 + 1);
            self.last_statistics.set_int("dt_fd.d", d as u64);
            let outer = self.solve_deadline.get();
            if let Some(cap) = cap {
                self.solve_deadline
                    .set(Some(outer.map_or(cap, |o| o.min(cap))));
            }
            let outcome = self.dt_fd_round(scan, &alias, &guarded, d);
            self.solve_deadline.set(outer);
            tracing::debug!(
                target: "ay_dpll::dt_fd",
                round,
                d,
                outcome = outcome.label(),
                guarded = guarded.len(),
                aliases = alias.len(),
                "dt-fd round"
            );
            match outcome {
                Round::Sat(model, accepted) => {
                    return self.dt_fd_publish_sat(scan, model, &accepted);
                }
                Round::Unsat(result) => {
                    if posture == Posture::SatOnly {
                        reason = "unsat-not-published";
                        break;
                    }
                    self.last_statistics
                        .set_string("solver.dt_fd_lane", "unsat");
                    let empty =
                        TseitinResult::new(Vec::new(), BTreeMap::new(), BTreeMap::new(), 0, 0);
                    let out = self.solve_and_store_model_full(
                        result, &empty, None, None, None, None, None, None, None, None,
                    )?;
                    return Ok(Some(out));
                }
                Round::Spurious if d < MAX_D => d = (d * 2).min(MAX_D),
                Round::Spurious => break,
                Round::GiveUp(why) => {
                    reason = why;
                    break;
                }
            }
        }
        self.last_statistics.set_string("solver.dt_fd_lane", reason);
        self.pending_sat_unknown_reason = None;
        Ok(None)
    }

    /// One encoding at cell count `d`, solved and (on SAT) checked.
    fn dt_fd_round(
        &mut self,
        scan: &Scan,
        alias: &HashMap<TermId, TermId>,
        guarded: &HashSet<TermId>,
        d: usize,
    ) -> Round {
        let budget = memory::clause_budget(MAX_CLAUSES);
        let mut enc = Encoder::new(scan, d, budget, alias, guarded);
        if enc.encode().is_none() {
            let short_of_memory =
                enc.cnf.memory_out() || (enc.cnf.overflowed() && budget < MAX_CLAUSES);
            return Round::GiveUp(if short_of_memory {
                "memory"
            } else {
                "encode-declined"
            });
        }
        self.last_statistics
            .set_int("dt_fd.vars", u64::from(enc.cnf.num_vars()));
        self.last_statistics
            .set_int("dt_fd.clauses", enc.cnf.num_clauses() as u64);
        if !memory::solver_fits(enc.cnf.num_clauses(), enc.cnf.flat_literals().len()) {
            return Round::GiveUp("memory");
        }
        let started = ay_core::time::Instant::now();
        let result = self.dt_fd_solve(&mut enc);
        tracing::debug!(
            target: "ay_dpll::dt_fd",
            d,
            vars = enc.cnf.num_vars(),
            clauses = enc.cnf.num_clauses(),
            solve_ms = started.elapsed().as_millis() as u64,
            "dt-fd solve"
        );
        match result {
            SatResult::Sat(model) => dt_fd_check_model(&enc, model),
            r @ SatResult::Unsat(_) => Round::Unsat(r),
            _ => Round::GiveUp("sat-unknown"),
        }
    }

    /// Run `ay-sat` on the encoding.
    fn dt_fd_solve(&mut self, enc: &mut Encoder<'_>) -> SatResult {
        let cnf = &enc.cnf;
        let mut solver = SatSolver::new(cnf.num_vars() as usize);
        self.apply_random_seed_to_sat(&mut solver);
        self.apply_progress_to_sat(&mut solver);
        if let Some(seed) = self.random_seed {
            solver.set_random_seed(seed);
        }
        let flat = cnf.flat_literals();
        solver.reserve_clause_capacity(cnf.num_clauses(), flat.len());
        let mut buf: Vec<Literal> = Vec::with_capacity(16);
        for &l in flat {
            if l == 0 {
                solver.add_clause_reusing_buffer(&mut buf);
                buf.clear();
            } else {
                buf.push(to_sat(l));
            }
        }
        enc.cnf.release_clauses();
        self.arm_sat_count_budget(&mut solver, ChainSpend::NONE);
        let should_stop = self.make_should_stop();
        // Learned clauses grow the solver; stopping short of the process
        // ceiling lets the fallback lanes run instead of a `memout`.
        let stop = move || should_stop() || memory::solve_memory_exceeded();
        let result = solver.solve_interruptible(stop).into_inner();
        collect_sat_stats!(self, &solver);
        result
    }

    /// Publish an evaluator-accepted model: export, the always-on validation
    /// pipeline and the independent gate. `Ok(None)` when the model is not
    /// confirmed (the caller's bracket then erases the attempt).
    fn dt_fd_publish_sat(
        &mut self,
        scan: &Scan,
        model: Vec<bool>,
        accepted: &Accepted,
    ) -> Result<Option<SolveResult>> {
        #[cfg(test)]
        PUBLICATION_DEADLINE.with(|c| c.set(Some(self.solve_deadline.get())));
        let confirmed = self.dt_fd_publish_steps(scan, model, accepted)?;
        if confirmed.is_none() {
            // The pins describe the rejected model only; no later model of
            // this command may be constructed from them.
            self.lane_model_pin_roots.clear();
            self.pending_lane_model_pin_roots.clear();
            self.last_statistics
                .set_string("solver.dt_fd_lane", "fallback-gate");
            self.last_model_validated = false;
            self.last_unknown_reason = None;
            self.last_result = None;
            self.last_model = None;
            self.pending_sat_unknown_reason = None;
        }
        Ok(confirmed)
    }

    /// The publication steps; `Ok(None)` when the model is not confirmed.
    fn dt_fd_publish_steps(
        &mut self,
        scan: &Scan,
        model: Vec<bool>,
        accepted: &Accepted,
    ) -> Result<Option<SolveResult>> {
        let Some((euf, pins)) = self.dt_fd_export(scan, accepted) else {
            return Ok(None);
        };
        self.pending_lane_model_pin_roots = pins;
        let term_to_var = accepted.bool_vars.clone();
        let var_to_term: BTreeMap<u32, TermId> =
            term_to_var.iter().map(|(&t, &v)| (v, t)).collect();
        let num_vars = model.len() as u32;
        let tseitin = TseitinResult::new(Vec::new(), term_to_var, var_to_term, 0, num_vars);
        let out = self.solve_and_store_model_full(
            SatResult::Sat(model),
            &tseitin,
            Some(euf),
            None,
            None,
            None,
            None,
            None,
            None,
            None,
        )?;
        let gate =
            matches!(out, SolveResult::Sat).then(|| self.confirm_sat_with_independent_gate());
        tracing::debug!(target: "ay_dpll::dt_fd", pipeline = ?out, gate = ?gate, "dt-fd sat publication");
        let confirmed = matches!(gate, Some(ay_model_check::GateVerdict::ConfirmedSat));
        if confirmed {
            self.last_statistics.set_string("solver.dt_fd_lane", "sat");
            // The confirmed model, whole, for the value printers
            // (#dt-fd-ground-model).
            self.lane_ground_model = self.dt_fd_ground_model(scan, accepted).map(Box::new);
            return Ok(Some(SolveResult::Sat));
        }
        Ok(None)
    }
}

/// DIMACS literal to an `ay-sat` literal (variable `v` is index `v - 1`).
fn to_sat(l: i32) -> Literal {
    let var = Variable::new(l.unsigned_abs() - 1);
    if l > 0 {
        Literal::positive(var)
    } else {
        Literal::negative(var)
    }
}

/// Lemma 3: decode, evaluate the original roots, classify the outcome.
fn dt_fd_check_model(enc: &Encoder<'_>, model: Vec<bool>) -> Round {
    let mut dec = Decoder::new(enc, &model);
    let Some(env) = dec.evaluate() else {
        return if dec.any_deep() {
            Round::Spurious
        } else {
            Round::GiveUp("rejected-shallow")
        };
    };
    // Declared Bool constants own one positive CNF variable each.
    let mut bool_vars = BTreeMap::new();
    for (&t, (node, sort)) in &enc.scan.nodes {
        if matches!(node, Node::Const) && *sort == FieldSort::Bool {
            if let Some(l) = enc.vals.get(&t).and_then(|v| v.lit()) {
                if l > 1 {
                    bool_vars.insert(t, l as u32);
                }
            }
        }
    }
    // The wrong-constructor values every list selector takes on nil (the
    // evaluator above read exactly these), so the published model is total.
    let mut rest_nil = HashMap::default();
    let mut field_nil = HashMap::default();
    for (s, sort) in enc.scan.sorts.iter().enumerate() {
        let SortShape::List { cell_fields, .. } = &sort.shape else {
            continue;
        };
        let s = s as u32;
        if let Some(v) = dec.rest_nil(s) {
            rest_nil.insert(s, v);
        }
        for j in 0..cell_fields.len() {
            if let Some(v) = dec.field_nil(s, j) {
                field_nil.insert((s, j), v);
            }
        }
    }
    let values = std::mem::take(&mut dec.values);
    Round::Sat(
        model,
        Accepted {
            values,
            env,
            bool_vars,
            rest_nil,
            field_nil,
        },
    )
}
