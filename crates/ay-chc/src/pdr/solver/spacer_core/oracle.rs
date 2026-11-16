// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The ONE oracle of the Spacer lane: query builder and the legacy backend
//! (`DESIGN` §3.4, §4.2.2, Appendix C). Owner: **WP-B1-L**.
//!
//! Q1 (`Hyp::Reach`) keeps HEAD's verdict path byte-for-byte (S4): the same
//! `bound_int_vars` + `expand_select_store_symbolic` query text, the same
//! `propagate_equalities() == false` shortcut and the same
//! `with_phase_seed_model(check_sat_with_ite_case_split)` dispatch. The
//! proxied assumption solve (D1) only refines an established UNSAT into a
//! core. Q2 (`Hyp::Inductive`) / Q3 (`Hyp::Push`) are a new query family
//! under the same fail-closed posture: the assumption solve runs first (one
//! solve, verdict + core), an assumption-mode SAT is trusted only when it
//! evaluates on the query (#6480), and `Unknown` falls through to the split
//! verdict; an `Unknown` verdict means "keep the literal".
//!
//! `OracleBackend` lives in `pdr/config.rs` (it is a field of the `pub`
//! `SpacerLane`) and is re-exported here. `Session` is currently a route and
//! accounting label; every query below retains the legacy implementation.

#![allow(dead_code, unused)]

use crate::pdr::cube::literals::LitCube;
use crate::pdr::solver::spacer_core::stats::Q1CoreSource;
use crate::pdr::solver::PdrSolver;
use crate::smt::deadline::ScopedSmtDeadline;
use crate::smt::{SmtResult, SmtValue};
use crate::{ChcExpr, ChcOp, ChcSort, ChcVar, PredicateId};
use ay_core::kani_compat::DetHashMap as FxHashMap;
use std::time::Duration;

mod proxy;

#[cfg(test)]
pub(in crate::pdr::solver) use proxy::map_proxies;

pub(in crate::pdr::solver) use crate::pdr::config::OracleBackend;

/// Query shape (the frame hypothesis is `frame_hyp`, the delta frame, D2).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(in crate::pdr::solver) enum Hyp {
    /// Q1: `F_f(body) ∧ T_c ∧ cube(head)` (f = frame index = level-1; monotone in the cube).
    Reach,
    /// Q2: `F_f(body) ∧ ¬cube(body) ∧ T_c ∧ cube(head)` (`¬cube` only when body_pred == pred; f = level-1).
    Inductive,
    /// Q3: `F_f(body) ∧ T_c ∧ cube(head)` with f = k (push of `¬cube` from k to k+1).
    Push,
}

/// One clause of the POB's predicate, as the oracle sees it.
pub(in crate::pdr::solver) struct ClauseQuery<'a> {
    pub clause_index: usize,
    pub head_args: &'a [ChcExpr],
    /// The clause's body atoms: empty = fact clause, one = linear clause,
    /// several = hyperedge (the nonlinear lane, `lane_nonlinear`).
    pub body: &'a [(PredicateId, Vec<ChcExpr>)],
    /// `clause.body.constraint` or `Bool(true)`.
    pub transition: &'a ChcExpr,
}

/// Oracle verdict. `core` indexes the cube's literals; `exact` = came from a
/// solver core (proxied / session); `uses_level` session only.
pub(in crate::pdr::solver) enum Verdict {
    Unsat {
        core: Vec<bool>,
        exact: bool,
        uses_level: Option<usize>,
    },
    /// Full model in ORIGINAL clause names.
    Sat(FxHashMap<String, SmtValue>),
    Unknown,
}

/// Per-derivation oracle budget (`DESIGN` §5: `ind_gen_budget()`).
///
/// `calls` counts oracle calls issued against this budget (`count()`); the
/// budget is `exhausted()` when `calls >= max_calls` or the deadline passed.
/// Exhaustion is not an error (the current mask is the lemma).
#[derive(Clone, Copy, Debug)]
pub(in crate::pdr::solver) struct Budget {
    pub deadline: Option<ay_core::time::Instant>,
    pub per_call: Duration,
    pub max_calls: usize,
    /// Oracle calls issued so far (skeleton addition to §3.4; P's
    /// `q1_core_for_clause` callers construct one with `Budget::new`).
    pub calls: usize,
}

impl Budget {
    pub(in crate::pdr::solver) fn new(
        deadline: Option<ay_core::time::Instant>,
        per_call: Duration,
        max_calls: usize,
    ) -> Self {
        Self {
            deadline,
            per_call,
            max_calls,
            calls: 0,
        }
    }

    /// A budget bounded only by `per_call` (for C3 callers outside a derivation).
    pub(in crate::pdr::solver) fn per_call_only(per_call: Duration) -> Self {
        Self::new(None, per_call, usize::MAX)
    }

    pub(in crate::pdr::solver) fn exhausted(&self) -> bool {
        self.calls >= self.max_calls
            || self
                .deadline
                .is_some_and(|d| ay_core::time::Instant::now() >= d)
    }

    pub(in crate::pdr::solver) fn count(&mut self) {
        self.calls = self.calls.saturating_add(1);
    }

    /// Install the per-solve thread deadline: `per_call` from now, tightened
    /// by the derivation deadline (nested installs never extend, so the
    /// enclosing solve/main-loop deadline is kept too).
    fn scoped_deadline(&self) -> ScopedSmtDeadline {
        let now = ay_core::time::Instant::now();
        let until = match self.deadline {
            Some(d) => d.min(now + self.per_call),
            None => now + self.per_call,
        };
        ScopedSmtDeadline::install_until(until)
    }

    /// The absolute deadline handed to the assumption entry.
    fn assumption_deadline(&self) -> Option<ay_core::time::Instant> {
        let now = ay_core::time::Instant::now();
        Some(match self.deadline {
            Some(d) => d.min(now + self.per_call),
            None => now + self.per_call,
        })
    }
}

/// A built query: `background ∧ [neg_cube_on_body] ∧ lits_on_head` (§4.2.2).
pub(in crate::pdr::solver) struct BuiltQuery {
    pub background: Vec<ChcExpr>,
    /// `lits_on_head[i] = apply_to_args(pred, cube.lits()[i], head_args)`.
    pub lits_on_head: Vec<ChcExpr>,
    /// `Some(¬and_all(cube on body args))` iff `hyp == Inductive && body_pred == pred`.
    pub neg_cube_on_body: Option<ChcExpr>,
    /// The fact this query instantiates the body with (level-1 per-fact
    /// expansion), for telemetry.
    pub fact_index: Option<usize>,
}

/// Name prefix of the proxy Booleans of the proxied assumption solve (D1).
pub(in crate::pdr::solver) const PROXY_PREFIX: &str = "__sc_lit_";

/// `true` iff the expression mentions a Real-sorted variable or constant
/// (the assumption entry answers `Unknown` on UNSAT for those, #5925).
pub(in crate::pdr::solver) fn expr_has_real(e: &ChcExpr) -> bool {
    crate::expr::maybe_grow_expr_stack(|| match e {
        ChcExpr::Real(_, _) => true,
        ChcExpr::Var(v) => matches!(v.sort, ChcSort::Real),
        ChcExpr::Op(_, args) | ChcExpr::PredicateApp(_, _, args) => {
            args.iter().any(|a| expr_has_real(a))
        }
        ChcExpr::FuncApp(_, sort, args) => {
            matches!(sort, ChcSort::Real) || args.iter().any(|a| expr_has_real(a))
        }
        _ => false,
    })
}

/// Outcome of one proxied assumption solve, already mapped to literal indices.
pub(in crate::pdr::solver) enum ProxiedOutcome {
    /// `core` by index; `exact == false` on the contradiction path (every
    /// proxy returned — a valid but over-inclusive core).
    Unsat {
        core: Vec<bool>,
        exact: bool,
    },
    /// Plain `Unsat`: the background alone (or with Farkas activations only)
    /// is UNSAT — the empty core.
    UnsatEmpty,
    Sat(FxHashMap<String, SmtValue>),
    Unknown,
}

impl PdrSolver {
    /// Whether the proxied assumption solve can decide/refine queries of
    /// this problem: integer arithmetic / Bool only (the assumption entry
    /// returns `Unknown` on UNSAT as soon as a Real theory atom is present,
    /// #5925), and the query itself has no Real atoms.
    pub(in crate::pdr::solver) fn lane_lia_ok(&self, exprs: &[&ChcExpr]) -> bool {
        self.problem_is_integer_arithmetic
            && !self.problem.has_real_sorts()
            && !exprs.iter().any(|e| expr_has_real(e))
    }

    /// D1 / Appendix C: `bg ∪ {(¬p_i ∨ lit_i)}` in the background, `{p_i}`
    /// as the assumptions; `smt.reset()` first; deadline-clamped.
    pub(in crate::pdr::solver) fn proxied_assumption_solve(
        &mut self,
        bg: &[ChcExpr],
        lits: &[ChcExpr],
        deadline: Option<ay_core::time::Instant>,
    ) -> ProxiedOutcome {
        // Preparation and attribution share one admission budget and the SAME
        // absolute deadline; no source census is depth-truncated or positional.
        let _deadline = deadline.map(ScopedSmtDeadline::install_until);
        let observed_memory = ay_sys::current_memory_group_observation();
        let mut credit = proxy::Admission::new();
        let open = |solver: &Self| {
            !solver.is_cancelled()
                && !ay_sys::current_memory_group_soft_tripped()
                && !observed_memory
                    .as_ref()
                    .is_some_and(|group| group.is_tripped())
        };
        let Some((bg2, proxies)) = proxy::prepare(bg, lits, &mut credit, &mut || open(self)) else {
            return ProxiedOutcome::Unknown;
        };
        self.smt.reset();
        self.spacer_stats.smt_solves_total += 1;
        // The assumption loop's budget reads the thread deadline, so the
        // derivation clamp rides a scope (nested scopes never extend).
        let res = self.smt.check_sat_with_assumption_conjuncts(&bg2, &proxies);
        if !open(self) {
            return ProxiedOutcome::Unknown;
        }
        match res {
            SmtResult::UnsatWithCore(c) => {
                let Some(core) =
                    proxy::map(&c.conjuncts, &proxies, &mut credit, &mut || open(self))
                else {
                    return ProxiedOutcome::Unknown;
                };
                if core.iter().all(|b| !*b) {
                    // Only Farkas activation literals were in the core
                    // (`assumptions.rs` empty-conjuncts path): the background
                    // alone is UNSAT.
                    return ProxiedOutcome::UnsatEmpty;
                }
                // The equality-closure contradiction path (`assumptions.rs`,
                // before any DPLL(T) iteration) returns every proxy. The
                // closure mines `var = const` / `var = var` from top-level
                // `And`/`Eq` conjuncts only (`smt/bounds.rs`); the proxies
                // are bare Bool vars and the literals sit under `Or`, so the
                // conflicting constants came from the BACKGROUND alone: the
                // background is UNSAT by itself and the empty core is its
                // exact core (Phase 0 confirms an empty seed before it can
                // become lemma `false`). Measured on two_counters: reporting
                // it inexact (the design's conservative reading) sent every
                // such block through Phase A for nothing.
                let all = core.iter().all(|b| *b);
                let contradiction_path =
                    all && c.farkas_conflicts.is_empty() && c.diagnostics.dt_iterations == 0;
                if contradiction_path {
                    return ProxiedOutcome::UnsatEmpty;
                }
                ProxiedOutcome::Unsat { core, exact: true }
            }
            SmtResult::Unsat | SmtResult::UnsatWithFarkas(_) => ProxiedOutcome::UnsatEmpty,
            SmtResult::Sat(m) => ProxiedOutcome::Sat(m),
            SmtResult::Unknown => ProxiedOutcome::Unknown,
        }
    }

    /// C3 (called by P from `single_body.rs` / `reachability/mod.rs` after an
    /// UNSAT Q1 verdict): the core of `background ∧ lits_on_head` over
    /// `lits_on_head` by index. Legacy: proxied assumption solve (LIA/Bool,
    /// deadline-clamped); LRA or Unknown ⇒ all-true inexact. Never changes
    /// the verdict. The background carries NO exclusion. Records the Q1
    /// telemetry (`record_q1`: core source / size / exactness / solve time).
    pub(in crate::pdr::solver) fn q1_core_for_clause(
        &mut self,
        background: &[ChcExpr],
        lits_on_head: &[ChcExpr],
        budget: &mut Budget,
    ) -> (Vec<bool>, bool /* exact */) {
        let n = lits_on_head.len();
        budget.count();
        let (core, exact, source, elapsed) = self.proxied_core(background, lits_on_head, budget);
        let k = core.iter().filter(|b| **b).count();
        self.spacer_stats
            .record_q1(source, Some(k), exact, elapsed, 0);
        (core, exact)
    }

    /// The proxied core solve behind C3 and the oracle's Reach path (no Q1
    /// telemetry; the caller decides). Returns `(core, exact, source, solve time)`.
    fn proxied_core(
        &mut self,
        background: &[ChcExpr],
        lits_on_head: &[ChcExpr],
        budget: &mut Budget,
    ) -> (Vec<bool>, bool, Q1CoreSource, Option<Duration>) {
        let n = lits_on_head.len();
        if n == 0 {
            // Nothing to attribute: the UNSAT rests on the background alone.
            return (Vec::new(), true, Q1CoreSource::None, None);
        }
        if !self.config.spacer.core_lemma || budget.exhausted() {
            return (vec![true; n], false, Q1CoreSource::None, None);
        }
        let mut refs: Vec<&ChcExpr> = background.iter().collect();
        refs.extend(lits_on_head.iter());
        if !self.lane_lia_ok(&refs) {
            return (vec![true; n], false, Q1CoreSource::None, None);
        }
        let started = ay_core::time::Instant::now();
        let deadline = budget.assumption_deadline();
        let out = {
            let _scope = budget.scoped_deadline();
            self.proxied_assumption_solve(background, lits_on_head, deadline)
        };
        let elapsed = Some(started.elapsed());
        match out {
            ProxiedOutcome::Unsat { core, exact } => (core, exact, Q1CoreSource::Proxied, elapsed),
            // Background alone UNSAT (plain Unsat, activation-only core or the
            // equality-closure contradiction): the empty exact core (confirmed
            // by Phase 0 before it can become lemma `false`).
            ProxiedOutcome::UnsatEmpty => {
                (vec![false; n], true, Q1CoreSource::Contradiction, elapsed)
            }
            // SAT: the exclusion-free query is satisfiable — the Q1 UNSAT was
            // exclusion-dependent (or came from a split/ITE leaf the assumption
            // lane cannot reproduce). Coverage record only. Unknown: no core.
            ProxiedOutcome::Sat(_) | ProxiedOutcome::Unknown => {
                (vec![true; n], false, Q1CoreSource::None, elapsed)
            }
        }
    }

    /// `build_clause_query(pred, level, cq, cube, hyp, with_exclusions)` (§4.2.2):
    /// the single built query of a clause whose body frame is NOT the per-fact
    /// expansion (fact clause, or body frame index ≥ 1). For the general case
    /// (one query per fact at frame index 0) use [`Self::build_clause_queries`].
    /// `None` ⇒ `Verdict::Unknown` (an `apply_to_args` failure).
    pub(in crate::pdr::solver) fn build_clause_query(
        &self,
        pred: PredicateId,
        level: usize,
        cq: &ClauseQuery<'_>,
        cube: &LitCube,
        hyp: Hyp,
        with_exclusions: Option<&[(usize, PredicateId, ChcExpr)]>,
    ) -> Option<BuiltQuery> {
        let mut qs = self.build_clause_queries(pred, level, cq, cube, hyp, with_exclusions)?;
        if qs.len() == 1 {
            qs.pop()
        } else {
            None
        }
    }

    /// All built queries of one clause (§4.2.2). Empty ⇒ the clause is
    /// vacuously UNSAT (a body predicate with no fact at frame index 0).
    ///
    /// - `lits_on_head[i] = apply_to_args(pred, cube.lits()[i], head_args)`;
    /// - background = `cq.transition`, `clause_guarded_constraint(pred, clause, head_args, g)` with
    ///   `g = level` (`Reach | Inductive`) or `push_guard_check_level(level)` (`Push`),
    ///   the body frame by `hyp` (`Reach | Inductive`: `frame_hyp(level-1, body)` on the body
    ///   args when `level-1 ≥ 1`; `level-1 == 0`: one query per fact `fact ∧ init_match` with
    ///   the `__fact_` renaming of `inductive_blocking.rs`; `Push`: `frame_hyp(level, body)`;
    ///   fact clause: nothing), exclusions (`Reach` with `with_exclusions` only);
    /// - `neg_cube_on_body = Some(¬cube(body))` iff `hyp == Inductive && body_pred == pred`.
    ///
    /// Level 0 never builds a single-body query (D5): callers iterate fact
    /// clauses only at level 0; a single-body clause at level 0 returns `None`.
    pub(in crate::pdr::solver) fn build_clause_queries(
        &self,
        pred: PredicateId,
        level: usize,
        cq: &ClauseQuery<'_>,
        cube: &LitCube,
        hyp: Hyp,
        with_exclusions: Option<&[(usize, PredicateId, ChcExpr)]>,
    ) -> Option<Vec<BuiltQuery>> {
        let mut lits_on_head = Vec::with_capacity(cube.len());
        for lit in cube.lits() {
            lits_on_head.push(self.apply_to_args(pred, lit, cq.head_args)?);
        }
        // Guard check level: the HEAD level of the query. `Reach`/`Inductive`
        // put the head at `level` (body frame `level - 1`); a `Push` from
        // `level` assumes the body frame `F_level`, so its head is at
        // `level + 1` — the one reading every push shares
        // (`push_guard_check_level`, Spacer `is_invariant(next_level(lvl))`).
        let guard_level = match hyp {
            Hyp::Reach | Hyp::Inductive => level,
            Hyp::Push => Self::push_guard_check_level(level),
        };
        let guarded =
            self.clause_guarded_constraint(pred, cq.clause_index, cq.head_args, guard_level);
        let mut background: Vec<ChcExpr> = Vec::with_capacity(4);
        if !matches!(cq.transition, ChcExpr::Bool(true)) {
            background.push(cq.transition.clone());
        }
        if !matches!(guarded, ChcExpr::Bool(true)) {
            background.push(guarded);
        }
        let (body_pred, body_args) = match cq.body {
            [] => {
                return Some(vec![BuiltQuery {
                    background,
                    lits_on_head,
                    neg_cube_on_body: None,
                    fact_index: None,
                }]);
            }
            [(body_pred, body_args)] => (*body_pred, body_args.as_slice()),
            atoms => {
                return self.build_hyperedge_query(
                    pred,
                    level,
                    atoms,
                    cube,
                    hyp,
                    with_exclusions,
                    background,
                    lits_on_head,
                );
            }
        };
        let f = match hyp {
            Hyp::Reach | Hyp::Inductive => level.checked_sub(1)?,
            Hyp::Push => level,
        };
        let neg_cube_on_body = if hyp == Hyp::Inductive && body_pred == pred {
            Some(ChcExpr::not(self.apply_to_args(
                pred,
                cube.expr(),
                body_args,
            )?))
        } else {
            None
        };
        if hyp == Hyp::Reach {
            if let Some(unknowns) = with_exclusions {
                for (unknown_parent_level, unknown_pred, state) in unknowns {
                    if *unknown_parent_level == level && *unknown_pred == body_pred {
                        if let Some(on_body) = self.apply_to_args(body_pred, state, body_args) {
                            background.push(ChcExpr::not(on_body));
                        }
                    }
                }
            }
        }
        if f >= 1 {
            if let Some(frame) = self.frame_hyp(f, body_pred) {
                let on_body = self.apply_to_args(body_pred, &frame, body_args)?;
                background.push(on_body);
            }
            return Some(vec![BuiltQuery {
                background,
                lits_on_head,
                neg_cube_on_body,
                fact_index: None,
            }]);
        }
        // Frame index 0: the body predicate's facts, one query each, the fact
        // renamed apart from every source name (`fact_names::SourceNames`, as
        // `single_body.rs` and `inductive_blocking.rs` do: a prefix is not
        // freshness — legal source binders can spell it). A stopped or
        // partial rename yields no query (`None`), never a captured one.
        // The solver's cached census (`source_names()`, once per solver; a
        // census cut short by cancellation is `None` and never cached).
        let names = self.source_names()?;
        let mut open = || !self.is_cancelled();
        let mut out = Vec::new();
        for (fact_index, fact) in self
            .problem
            .clauses_defining_with_index(body_pred)
            .filter(|(_, c)| c.is_fact())
        {
            let fact_head_args = match &fact.head {
                crate::ClauseHead::Predicate(_, a) => a.as_slice(),
                crate::ClauseHead::False => continue,
            };
            if fact_head_args.len() != body_args.len() {
                continue;
            }
            let fact_constraint = fact.body.constraint.clone().unwrap_or(ChcExpr::Bool(true));
            let (renamed_fact, renamed_args) = names.rename(
                &fact_constraint,
                fact_head_args,
                &format!("__fact{fact_index}_"),
                background
                    .iter()
                    .chain(lits_on_head.iter())
                    .chain(neg_cube_on_body.iter())
                    .chain(body_args.iter()),
                &mut open,
            )?;
            let init_match = ChcExpr::and_all(
                body_args
                    .iter()
                    .cloned()
                    .zip(renamed_args.iter().cloned())
                    .map(|(a, b)| ChcExpr::eq(a, b)),
            );
            let mut bg = background.clone();
            if !matches!(renamed_fact, ChcExpr::Bool(true)) {
                bg.push(renamed_fact);
            }
            bg.push(init_match);
            out.push(BuiltQuery {
                background: bg,
                lits_on_head: lits_on_head.clone(),
                neg_cube_on_body: neg_cube_on_body.clone(),
                fact_index: Some(fact_index),
            });
        }
        Some(out)
    }

    /// [`Self::build_clause_queries`] for a hyperedge clause (the nonlinear
    /// lane): the ONE query `T ∧ guarded ∧ ∧_i F_f(Q_i)(y_i) ∧ lits(head)`,
    /// with `F_f` the delta frame (`f ≥ 1`) or the disjunction of `Q_i`'s
    /// renamed facts (`f == 0`, [`Self::lane_body_hyps`]); `Inductive` adds
    /// `¬cube(y_i)` for EVERY body occurrence of `pred` (Spacer's
    /// `check_inductive` assumes the candidate on every self-occurrence);
    /// `Reach` with exclusions excludes the recorded unknown states of each
    /// atom. An atom without a fact at `f == 0` makes the clause vacuous
    /// (`Some(vec![])`, UNSAT with the empty core).
    fn build_hyperedge_query(
        &self,
        pred: PredicateId,
        level: usize,
        atoms: &[(PredicateId, Vec<ChcExpr>)],
        cube: &LitCube,
        hyp: Hyp,
        with_exclusions: Option<&[(usize, PredicateId, ChcExpr)]>,
        mut background: Vec<ChcExpr>,
        lits_on_head: Vec<ChcExpr>,
    ) -> Option<Vec<BuiltQuery>> {
        let f = match hyp {
            Hyp::Reach | Hyp::Inductive => level.checked_sub(1)?,
            Hyp::Push => level,
        };
        let mut negs = Vec::new();
        if hyp == Hyp::Inductive {
            for (body_pred, body_args) in atoms {
                if *body_pred == pred {
                    negs.push(ChcExpr::not(self.apply_to_args(
                        pred,
                        cube.expr(),
                        body_args,
                    )?));
                }
            }
        }
        let neg_cube_on_body = (!negs.is_empty()).then(|| ChcExpr::and_all(negs));
        if hyp == Hyp::Reach {
            if let Some(unknowns) = with_exclusions {
                for (body_pred, body_args) in atoms {
                    for (unknown_parent_level, unknown_pred, state) in unknowns {
                        if *unknown_parent_level == level && unknown_pred == body_pred {
                            if let Some(on_body) = self.apply_to_args(*body_pred, state, body_args)
                            {
                                background.push(ChcExpr::not(on_body));
                            }
                        }
                    }
                }
            }
        }
        let roots: Vec<ChcExpr> = background
            .iter()
            .chain(lits_on_head.iter())
            .chain(neg_cube_on_body.iter())
            .cloned()
            .collect();
        let Some(hyps) = self.lane_body_hyps(atoms, f, &roots)? else {
            return Some(Vec::new());
        };
        background.extend(hyps.into_iter().map(|h| h.expr));
        Some(vec![BuiltQuery {
            background,
            lits_on_head,
            neg_cube_on_body,
            fact_index: None,
        }])
    }

    /// The query text of a built query, exactly as `single_body.rs` forms it
    /// (`bound_int_vars(and_all(..)).expand_select_store_symbolic()`).
    fn built_query_text(&self, bq: &BuiltQuery) -> ChcExpr {
        let parts = bq
            .background
            .iter()
            .cloned()
            .chain(bq.neg_cube_on_body.clone())
            .chain(bq.lits_on_head.iter().cloned());
        self.bound_int_vars(ChcExpr::and_all(parts))
            .expand_select_store_symbolic()
    }

    /// Appendix C `legacy_check_clause`: one built query, one shape.
    /// `want_core == false` skips the proxied core re-solve after a Reach
    /// UNSAT (QuickXplain only needs the verdict).
    #[allow(clippy::too_many_arguments)]
    fn legacy_check_query(
        &mut self,
        bq: &BuiltQuery,
        hyp: Hyp,
        want_model: bool,
        want_core: bool,
        phase_seed: Option<&FxHashMap<String, SmtValue>>,
        budget: &mut Budget,
        lia_ok: bool,
    ) -> Verdict {
        let n = bq.lits_on_head.len();
        let q = self.built_query_text(bq);
        if matches!(q.propagate_equalities(), ChcExpr::Bool(false)) {
            // HEAD's syntactic shortcut (S4). A Reach caller that wants the
            // core still gets the proxied one: the shortcut proves UNSAT, the
            // assumption solve attributes it (its own equality closure fires
            // on the same contradiction when it lies in the background).
            if hyp == Hyp::Reach && want_core && lia_ok && n >= 1 && self.config.spacer.core_lemma {
                let (core, exact, _, _) =
                    self.proxied_core(&bq.background, &bq.lits_on_head, budget);
                return Verdict::Unsat {
                    core,
                    exact,
                    uses_level: None,
                };
            }
            return Verdict::Unsat {
                core: vec![true; n],
                exact: false,
                uses_level: None,
            };
        }
        let verbose = self.config.verbose;
        // Inductive / Push: assumption solve first (verdict + core in one solve).
        if hyp != Hyp::Reach && lia_ok && n >= 1 {
            let started = ay_core::time::Instant::now();
            let deadline = budget.assumption_deadline();
            let outcome = {
                let _scope = budget.scoped_deadline();
                let mut bg = bq.background.clone();
                bg.extend(bq.neg_cube_on_body.clone());
                self.proxied_assumption_solve(&bg, &bq.lits_on_head, deadline)
            };
            self.spacer_stats
                .q2_ms_hist
                .add(usize::try_from(started.elapsed().as_millis()).unwrap_or(usize::MAX));
            match outcome {
                ProxiedOutcome::Unsat { core, exact } => {
                    return Verdict::Unsat {
                        core,
                        exact,
                        uses_level: None,
                    };
                }
                ProxiedOutcome::UnsatEmpty => {
                    return Verdict::Unsat {
                        core: vec![false; n],
                        exact: true,
                        uses_level: None,
                    };
                }
                ProxiedOutcome::Sat(m) => {
                    // #6480: an assumption-mode SAT is trusted only when the
                    // model evaluates the query to true.
                    if self.mbp.eval_bool(&q, &m) == Some(true) {
                        return Verdict::Sat(m);
                    }
                    self.spacer_stats.q2_fallback_verdict += 1;
                }
                ProxiedOutcome::Unknown => {
                    self.spacer_stats.q2_assume_unknown += 1;
                    self.spacer_stats.q2_fallback_verdict += 1;
                }
            }
        }
        // The split verdict (HEAD's Q1 dispatch, S4).
        let started = ay_core::time::Instant::now();
        self.spacer_stats.smt_solves_total += 1;
        let (res, _sat_query) = {
            let _scope = budget.scoped_deadline();
            if want_model {
                self.smt.with_phase_seed_model(phase_seed, |s| {
                    Self::check_sat_with_ite_case_split(s, verbose, &q)
                })
            } else {
                Self::check_sat_with_ite_case_split(&mut self.smt, verbose, &q)
            }
        };
        let elapsed = started.elapsed();
        if hyp != Hyp::Reach {
            self.spacer_stats
                .q2_ms_hist
                .add(usize::try_from(elapsed.as_millis()).unwrap_or(usize::MAX));
        }
        match res {
            SmtResult::Sat(m) => Verdict::Sat(m),
            SmtResult::Unknown => Verdict::Unknown,
            SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_) => {
                if hyp == Hyp::Reach
                    && want_core
                    && lia_ok
                    && n >= 1
                    && self.config.spacer.core_lemma
                {
                    // Exclusion-free proxied re-solve for the core (D1).
                    let (core, exact, _, _) =
                        self.proxied_core(&bq.background, &bq.lits_on_head, budget);
                    return Verdict::Unsat {
                        core,
                        exact,
                        uses_level: None,
                    };
                }
                Verdict::Unsat {
                    core: vec![true; n],
                    exact: false,
                    uses_level: None,
                }
            }
        }
    }

    /// THE oracle. One clause, one shape, either backend. `apply_to_args`
    /// failure ⇒ `Verdict::Unknown`. `with_exclusions` adds the parent-level
    /// exclusion constraint (Reach only; Q1 verdict parity).
    ///
    /// A clause whose body frame is the per-fact expansion is checked once
    /// per fact; the clause is UNSAT iff every fact query is, with the union
    /// of the per-fact cores. No fact at all ⇒ vacuously UNSAT (empty core).
    #[allow(clippy::too_many_arguments)]
    pub(in crate::pdr::solver) fn oracle_check_clause(
        &mut self,
        pred: PredicateId,
        level: usize,
        cq: &ClauseQuery<'_>,
        cube: &LitCube,
        hyp: Hyp,
        with_exclusions: Option<&[(usize, PredicateId, ChcExpr)]>,
        want_model: bool,
        phase_seed: Option<&FxHashMap<String, SmtValue>>,
        budget: &mut Budget,
    ) -> Verdict {
        self.oracle_check_clause_opts(
            pred,
            level,
            cq,
            cube,
            hyp,
            with_exclusions,
            want_model,
            true,
            phase_seed,
            budget,
        )
    }

    /// [`Self::oracle_check_clause`] with `want_core` (false: verdict only).
    #[allow(clippy::too_many_arguments)]
    fn oracle_check_clause_opts(
        &mut self,
        pred: PredicateId,
        level: usize,
        cq: &ClauseQuery<'_>,
        cube: &LitCube,
        hyp: Hyp,
        with_exclusions: Option<&[(usize, PredicateId, ChcExpr)]>,
        want_model: bool,
        want_core: bool,
        phase_seed: Option<&FxHashMap<String, SmtValue>>,
        budget: &mut Budget,
    ) -> Verdict {
        let Some(queries) = self.build_clause_queries(pred, level, cq, cube, hyp, with_exclusions)
        else {
            return Verdict::Unknown;
        };
        let n = cube.len();
        if queries.is_empty() {
            return Verdict::Unsat {
                core: vec![false; n],
                exact: true,
                uses_level: None,
            };
        }
        let lia_ok = {
            let mut refs: Vec<&ChcExpr> = Vec::new();
            for bq in &queries {
                refs.extend(bq.background.iter());
                refs.extend(bq.neg_cube_on_body.iter());
                refs.extend(bq.lits_on_head.iter());
            }
            self.lane_lia_ok(&refs)
        };
        let mut union = vec![false; n];
        let mut exact = true;
        for bq in &queries {
            if self.is_cancelled() {
                return Verdict::Unknown;
            }
            match self
                .legacy_check_query(bq, hyp, want_model, want_core, phase_seed, budget, lia_ok)
            {
                Verdict::Unsat { core, exact: e, .. } => {
                    for (u, c) in union.iter_mut().zip(core.iter()) {
                        *u |= *c;
                    }
                    exact &= e;
                }
                other => return other,
            }
        }
        Verdict::Unsat {
            core: union,
            exact,
            uses_level: None,
        }
    }

    /// All defining clauses of `pred` (facts included; at level 1 single-body
    /// clauses expand per fact with the renaming of
    /// `inductive_blocking.rs:297-305`). Stops at the first Sat/Unknown.
    /// UNSAT core = union of per-clause cores; `exact` = all exact;
    /// `uses_level` = min. **Level 0 never builds a single-body query** (D5).
    pub(in crate::pdr::solver) fn oracle_check_all_clauses(
        &mut self,
        pred: PredicateId,
        level: usize,
        cube: &LitCube,
        hyp: Hyp,
        budget: &mut Budget,
    ) -> Verdict {
        self.oracle_check_all_clauses_ex(pred, level, cube, hyp, budget)
            .0
    }

    /// [`Self::oracle_check_all_clauses`] plus the index of the clause that
    /// answered `Sat` / `Unknown` (for the within-run CTP list, which needs
    /// the clause's head/body argument vectors to evaluate a stored model).
    pub(in crate::pdr::solver) fn oracle_check_all_clauses_ex(
        &mut self,
        pred: PredicateId,
        level: usize,
        cube: &LitCube,
        hyp: Hyp,
        budget: &mut Budget,
    ) -> (Verdict, Option<usize>) {
        self.oracle_check_all_clauses_opts(pred, level, cube, hyp, true, budget)
    }

    /// [`Self::oracle_check_all_clauses_ex`] with `want_core` (false: the
    /// Reach verdict only — QuickXplain's predicate).
    pub(in crate::pdr::solver) fn oracle_check_all_clauses_opts(
        &mut self,
        pred: PredicateId,
        level: usize,
        cube: &LitCube,
        hyp: Hyp,
        want_core: bool,
        budget: &mut Budget,
    ) -> (Verdict, Option<usize>) {
        budget.count();
        let n = cube.len();
        let mut union = vec![false; n];
        let mut exact = true;
        let clause_ids: Vec<usize> = self
            .problem
            .clauses_defining_with_index(pred)
            .map(|(i, _)| i)
            .collect();
        for ci in clause_ids {
            if self.is_cancelled() {
                return (Verdict::Unknown, Some(ci));
            }
            let clause = self.problem.clauses()[ci].clone();
            let head_args = match &clause.head {
                crate::ClauseHead::Predicate(_, a) => a.clone(),
                crate::ClauseHead::False => continue,
            };
            if level == 0 && !clause.is_fact() {
                // D5: level 0 is fact-only.
                continue;
            }
            if clause.body.predicates.len() > 1 && !self.lane_nonlinear {
                // A hyperedge clause is the nonlinear lane's; on a linear
                // problem it cannot occur.
                return (Verdict::Unknown, Some(ci));
            }
            let transition = clause
                .body
                .constraint
                .clone()
                .unwrap_or(ChcExpr::Bool(true));
            let cq = ClauseQuery {
                clause_index: ci,
                head_args: &head_args,
                body: &clause.body.predicates,
                transition: &transition,
            };
            match self.oracle_check_clause_opts(
                pred, level, &cq, cube, hyp, None, true, want_core, None, budget,
            ) {
                Verdict::Unsat { core, exact: e, .. } => {
                    for (u, c) in union.iter_mut().zip(core.iter()) {
                        *u |= *c;
                    }
                    exact &= e;
                }
                Verdict::Sat(m) => return (Verdict::Sat(m), Some(ci)),
                Verdict::Unknown => return (Verdict::Unknown, Some(ci)),
            }
        }
        (
            Verdict::Unsat {
                core: union,
                exact,
                uses_level: None,
            },
            None,
        )
    }
}
