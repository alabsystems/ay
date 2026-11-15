// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! SAT-only equality-QE quantifier lane (#eq-qe-lane).
//!
//! # The gap
//!
//! Kopczynski-LOIS `incremental4.smt2` (2025 Incremental Arith selection)
//! asserts, from check-sat #746 on, a live Boolean combination of closed
//! sentences over `Real` that only ever compare binders for equality, e.g.
//!
//! ```smt2
//! (or (exists ((f Real) (g Real)) (or (= g f) (exists ((k Real)) (or (= g k) (= f k)))))
//!     (and (forall ((f Real) (g Real)) (and (not (= g f)) (forall ((k Real)) ...))) ...))
//! ```
//!
//! plus, in later scopes, ∀∃/∃∀ alternations over free constants. The legacy
//! quantifier path abstracts every quantifier under the Boolean structure
//! into a free proxy (`#quantifier-proxy-abstraction`), whose ground `Sat` is
//! by construction not evidence, so every remaining check-sat of the file
//! (2600+ `sat` per cvc5) answered `unknown (quantifier-unhandled)`.
//!
//! # The lane
//!
//! When EVERY quantifier of the authored query is in the equality-only
//! fragment of [`crate::qe::eq_qe`], each quantified root is replaced by its
//! EXACT quantifier-free equivalent (in the proof-carrying posture a root over
//! `Int` binders may instead take the affine route, [`affine_route`]). The
//! eliminated ground problem is first decided on a DISPOSABLE executor over a
//! cloned context (the discipline of every nested probe,
//! `qpf_probe_executor`). Only a probe `Sat` goes on: the
//! lane solves the ground problem again IN PLACE to install its model and
//! asks the unchanged quantified model gate, which re-decides every AUTHORED
//! quantified conjunct against the model: an equality-fragment root with the
//! independent evaluator (`ay-model-check`'s equality-only planner, sharing no
//! code with the elimination); an affine-route root NOT so independently —
//! see [`affine_route`], "What confirms a sat". Only a gate confirmation
//! answers `sat`; the ordinary SAT emission then runs every gate again. The
//! lane NEVER answers `unsat`: an exact ground refutation of the eliminated
//! problem is sound mathematically, but it is not an authored-scope proof,
//! and publication of a quantified refutation needs one.
//!
//! # What a decline leaves behind
//!
//! Every decline returns `None` with the assertion window untouched, the
//! model cleared and the unknown reason restored, and records the authored
//! roots so an internal retry of the same public check-sat skips the lane.
//!
//! * Declines BEFORE the in-place solve — a quantifier outside the fragment,
//!   a spent elimination budget, a probe `Unsat`/`Unknown` — are ERASED:
//!   the elimination and the vanished-constant pins only mint terms, the
//!   probe touches nothing of this executor, and the pass is rolled back
//!   with the qlra lane's bracket (`qlra_lane_roll_back`: term store and
//!   fresh-name counter, array-default sidecars, the thread-local LIA probe
//!   hint, the eval memo and store-indexed caches). The legacy path then runs
//!   as it does with the lane switched off; the unit test
//!   `a_ground_unsat_decline_is_erased_before_the_legacy_path_runs` pins the
//!   verdict, store size, fresh-name counter and SAT search counters equal.
//!   The in-place ground solve this probe replaced, together with a second
//!   lane pass inside the trace-armed retry, sent a single query (review
//!   fuzz `min_flat.smt2`) down a different legacy route that ended
//!   `unknown` where base published `unsat`.
//! * Declines AFTER the in-place solve (probe `Sat`, then the in-place solve
//!   or the gate does not confirm; counted in `in_place_declines`) restore
//!   the incremental SAT/BV state and the absence of a quantifier manager,
//!   but cannot roll the store back: the solve's terms may be held by solver
//!   state, exactly as after the qlra lane's SAT route. The query is then
//!   known SATISFIABLE (the elimination is exact), so the legacy path could
//!   only have answered `sat` or `unknown`; what such a decline can cost is
//!   a legacy `sat`, never a correct `unsat`.
//! * Time: the probe and the in-place solve each get `eq_qe_ground_budget`
//!   (an eighth of the remaining search wall, at most 5 s).
//!
//! A probe `Unsat` DOES settle that the query has no model, so in an
//! incremental session the lane bounds the legacy path's remaining time on
//! THIS check-sat (it can only certify the `unsat` or fail to); see
//! `eq_qe_bound_legacy_refutation`. Measured on `incremental4.smt2`: without
//! the bound, check-sat #2104 (a refutation the legacy path cannot certify)
//! ran to the session's wall clock and took all 1293 later answers with it.
//!
//! Unlike the qlra lane this probe also runs in incremental mode: every
//! quantified incremental window already starts from a clean solver state
//! (`saved_quantified_incremental_state`), which the caller restores on the
//! lane's publication exactly as on the qlra lane's.

use std::time::Duration;

use ay_core::time::Instant;
use ay_core::{Sort, TermData, TermId};

use super::Executor;
use crate::ematching::contains_quantifier;
use crate::executor_types::{Result, SolveResult};
use crate::qe::eq_qe::{eliminate_equality_quantifiers, in_equality_fragment, EqQeBudget};

/// Work allowance for eliminating one query's quantified roots.
const EQ_QE_WORK: usize = 1 << 21;

/// Hard cap on the lane's ground-solve wall allowance.
const GROUND_BUDGET_CAP: Duration = Duration::from_secs(5);

/// The disposable ground probe's verdict on the eliminated problem.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum GroundProbe {
    Sat,
    Unsat,
    Unknown,
}

impl GroundProbe {
    fn label(self) -> &'static str {
        match self {
            Self::Sat => "sat",
            Self::Unsat => "unsat",
            Self::Unknown => "unknown",
        }
    }
}

/// Session-lifetime lane outcomes (see the field on `Executor`).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(in crate::executor) struct EqQeLaneCounters {
    /// Passes whose every quantified root was eliminated.
    pub(in crate::executor) recognized: u64,
    /// Ground solves of the eliminated problem that were `unsat`.
    pub(in crate::executor) ground_unsat: u64,
    /// Lane models the quantified model gate confirmed (published `sat`).
    pub(in crate::executor) gate_confirmed: u64,
    /// Lane models the gate REFUSED. The elimination is exact, so this stays
    /// zero unless a leaf was left unpinned or a budget ran out.
    pub(in crate::executor) gate_refused: u64,
    /// Ground refutations after which the legacy path's remaining time on
    /// the check-sat was bounded (incremental sessions only).
    pub(in crate::executor) refutation_bounds: u64,
    /// Declines AFTER the in-place solve (the probe said `sat`, then the
    /// in-place solve or the gate did not confirm): the only declines that
    /// leave solver state behind.
    pub(in crate::executor) in_place_declines: u64,
}

impl Executor {
    fn eq_qe_lane_admissible(&self) -> bool {
        crate::quant_unit_authority::eq_qe_lane_enabled()
            && !self.in_alternation_validation
            && !self.in_quantified_model_gate
            && !self.in_closed_universal_precheck
            && self.last_assumptions.as_ref().is_none_or(Vec::is_empty)
    }

    /// Run the lane. `Some(Ok(Sat))` is a gate-confirmed verdict; `None`
    /// hands the query back to the legacy path.
    pub(in crate::executor) fn try_eq_qe_lane(&mut self) -> Option<Result<SolveResult>> {
        if !self.eq_qe_lane_admissible() {
            return None;
        }
        let roots = self.exact_concrete_authored_scope();
        if roots.is_empty() {
            return None;
        }
        if let Some(reason) = self.qlra_query_is_not_authored_scope(&roots) {
            self.last_statistics.set_string("eq_qe.inert", reason);
            return None;
        }
        // Side-effect-free recognition first: an out-of-fragment query (the
        // common case) mints nothing and costs one walk. Outside the equality
        // fragment only the affine route may take a root (`affine_route`).
        let affine_admitted = self.produce_proofs_enabled();
        let mut quantified = false;
        let mut affine_roots = 0u64;
        for &root in &roots {
            if contains_quantifier(&self.ctx.terms, root) {
                quantified = true;
                if in_equality_fragment(&self.ctx.terms, root) {
                    continue;
                }
                if !affine_admitted || !affine_route::admits_root(&self.ctx.terms, root) {
                    return None;
                }
                affine_roots += 1;
            }
        }
        if !quantified {
            return None;
        }
        // An internal retry of the same public check-sat re-enters here. A
        // decline is final for the check-sat: re-running would repeat the
        // elimination and the ground probe for the same verdict.
        if self.eq_qe_lane_declined.as_deref() == Some(roots.as_slice()) {
            self.last_statistics.set_int("eq_qe.retry_skipped", 1);
            return None;
        }
        // Everything up to the in-place solve is erasable: the elimination and
        // the pins only mint terms, and the ground probe runs on a disposable
        // executor over a cloned context. `qlra_lane_roll_back` restores the
        // store and the thread-local holders a probe can touch.
        let entry = self.qlra_lane_entry();
        let Some(mut working) = self.eq_qe_eliminate_roots(&roots) else {
            self.eq_qe_lane_erase(entry, &roots);
            return None;
        };
        self.last_statistics.set_int("eq_qe.recognized", 1);
        if affine_roots > 0 {
            self.last_statistics
                .set_int("eq_qe.affine_roots", affine_roots);
        }
        self.eq_qe_lane_counters.recognized += 1;
        self.eq_qe_pin_vanished_constants(&roots, &mut working);
        let budget = self.eq_qe_ground_budget();
        let probed = self.eq_qe_ground_probe(&working, budget);
        if probed != GroundProbe::Sat {
            self.last_statistics
                .set_string("eq_qe.ground", probed.label());
            self.eq_qe_lane_erase(entry, &roots);
            if probed == GroundProbe::Unsat {
                self.eq_qe_lane_counters.ground_unsat += 1;
                // Scheduling on the elimination's exactness: kept to the
                // equality fragment, whose eliminator is the one measured.
                if affine_roots == 0 {
                    self.eq_qe_bound_legacy_refutation();
                }
            }
            return None;
        }
        // The probe found a model, so the query is SATISFIABLE (the
        // elimination is exact): the legacy path can no longer answer `unsat`.
        // Solve again IN PLACE to install that model for the gate. This is the
        // only step a decline cannot erase; see the module docs.
        self.eq_qe_publish_sat(working, budget, &roots)
    }

    /// Solve the eliminated problem in place, then ask the quantified model
    /// gate. `Some(Ok(Sat))` only on a gate confirmation.
    fn eq_qe_publish_sat(
        &mut self,
        working: Vec<TermId>,
        budget: Duration,
        roots: &[TermId],
    ) -> Option<Result<SolveResult>> {
        let saved_reason = self.last_unknown_reason;
        let prior_theory = self.incr_theory_state.take();
        let prior_bv = self.incr_bv_state.take();
        let had_quantifier_manager = self.quantifier_manager.is_some();
        let outer_deadline = self.solve_deadline.get();
        let bounded = Instant::now() + budget;
        if outer_deadline.is_none_or(|outer| bounded < outer) {
            self.set_search_deadline(Some(bounded));
        }
        let (category, _) = self.detect_logic_category(&working);
        let window = std::mem::replace(&mut self.ctx.assertions, working);
        let solved = self.solve_for_category(category);
        self.ctx.assertions = window;
        self.set_search_deadline(outer_deadline);
        let confirmed = if matches!(solved, Ok(SolveResult::Sat)) && self.last_model.is_some() {
            self.last_model_validated = false;
            let gated = self.apply_quantified_model_failclosed_gate(SolveResult::Sat);
            let confirmed = gated == SolveResult::Sat && !self.should_abort_theory_loop();
            self.last_statistics.set_string(
                "eq_qe.gate",
                if confirmed { "confirmed" } else { "refused" },
            );
            if !confirmed {
                self.eq_qe_lane_counters.gate_refused += 1;
            }
            confirmed
        } else {
            let ground = match solved {
                Ok(SolveResult::Sat) => "in-place-no-model",
                Ok(SolveResult::Unsat(_)) => "in-place-unsat",
                Ok(SolveResult::Unknown) => "in-place-unknown",
                Err(_) => "in-place-error",
            };
            self.last_statistics.set_string("eq_qe.ground", ground);
            false
        };
        if confirmed {
            self.eq_qe_lane_counters.gate_confirmed += 1;
            self.last_unknown_reason = None;
            return Some(Ok(SolveResult::Sat));
        }
        // Decline after the in-place solve: hand the legacy path the
        // incremental SAT state and quantifier manager it had before, so it
        // does not reuse a solver holding the lane's eliminated formulas.
        self.eq_qe_lane_counters.in_place_declines += 1;
        self.incr_theory_state = prior_theory;
        self.incr_bv_state = prior_bv;
        if !had_quantifier_manager {
            self.quantifier_manager = None;
        }
        self.last_model = None;
        self.last_model_validated = false;
        self.last_unknown_reason = saved_reason;
        self.eq_qe_lane_declined = Some(roots.to_vec());
        None
    }

    /// Erase a declining pass that never solved in place, and remember the
    /// decline for internal retries of this check-sat.
    fn eq_qe_lane_erase(&mut self, entry: super::qlra_lane::QlraLaneEntry, roots: &[TermId]) {
        self.qlra_lane_roll_back(entry, "eq_qe.rollback");
        self.eq_qe_lane_declined = Some(roots.to_vec());
    }

    /// The lane's own wall allowance for the ground solve (probe, then the
    /// in-place re-solve): an eighth of what remains, at most
    /// [`GROUND_BUDGET_CAP`]. Base declined these queries in milliseconds,
    /// so the lane must not spend the budget the legacy path needs.
    fn eq_qe_ground_budget(&self) -> Duration {
        match self.solve_deadline.get() {
            Some(deadline) => {
                (deadline.saturating_duration_since(Instant::now()) / 8).min(GROUND_BUDGET_CAP)
            }
            None => GROUND_BUDGET_CAP,
        }
    }

    /// Decide the eliminated (quantifier-free) problem on a DISPOSABLE
    /// executor over a cloned context, the discipline of every nested probe
    /// (`qpf_probe_executor`): nothing it does reaches this executor except
    /// the verdict. The verdict is advisory only — `Sat` sends the lane to
    /// its in-place solve and the gate, `Unsat` only shortens a deadline.
    fn eq_qe_ground_probe(&mut self, working: &[TermId], budget: Duration) -> GroundProbe {
        let budget_ms = u64::try_from(budget.as_millis()).unwrap_or(u64::MAX);
        if budget_ms == 0 || self.should_abort_theory_loop() || !self.qpf_probe_preflight() {
            return GroundProbe::Unknown;
        }
        let Some(probe_ctx) = self.isolated_probe_context(working) else {
            return GroundProbe::Unknown;
        };
        let mut probe = self.qpf_probe_executor(probe_ctx, budget_ms);
        probe.original_problem_had_quantifiers = false;
        probe.incremental_mode = false;
        probe.begin_public_solve(false);
        probe.bind_unsat_query_assumptions(&[]);
        let verdict = match probe.check_sat() {
            Ok(SolveResult::Sat) => GroundProbe::Sat,
            Ok(SolveResult::Unsat(_)) => GroundProbe::Unsat,
            _ => GroundProbe::Unknown,
        };
        drop(probe);
        verdict
    }

    /// The exact quantifier-free equivalent of every root, or `None` unless
    /// at least one root is quantified and every quantified root eliminates.
    fn eq_qe_eliminate_roots(&mut self, roots: &[TermId]) -> Option<Vec<TermId>> {
        let mut budget = EqQeBudget::new(EQ_QE_WORK);
        let mut working = Vec::with_capacity(roots.len());
        let mut quantified = false;
        for &root in roots {
            if contains_quantifier(&self.ctx.terms, root) {
                quantified = true;
                let eliminated = if in_equality_fragment(&self.ctx.terms, root) {
                    eliminate_equality_quantifiers(&mut self.ctx.terms, root, &mut budget)?
                } else {
                    self.affine_route_eliminate(root)?
                };
                working.push(eliminated);
            } else {
                working.push(root);
            }
        }
        quantified.then_some(working)
    }

    /// The eliminated problem is EXACTLY equivalent to the authored query, so
    /// its ground refutation settles that the query has no model: the legacy
    /// path below can no longer find a `sat`, only certify the `unsat` (or
    /// fail to). Measured on Kopczynski-LOIS `incremental4.smt2`, it either
    /// certifies within ~4 s or runs to the session's wall clock without an
    /// answer, and in an incremental session that one check-sat then takes
    /// every later answer with it. In an INCREMENTAL session, bound the rest
    /// of THIS check-sat (the per-call deadline is restored at the check-sat
    /// boundary) to `clamp(remaining / 10, 2 s, 10 s)`. A single query keeps
    /// its whole budget: nothing later depends on it, and a certification
    /// slower than the cap would otherwise be lost. Scheduling only: a
    /// refutation the legacy path certifies in time publishes exactly as
    /// before, and running out of time answers `unknown`, never a wrong
    /// verdict.
    fn eq_qe_bound_legacy_refutation(&mut self) {
        const FLOOR: Duration = Duration::from_secs(2);
        const CAP: Duration = Duration::from_secs(10);
        if !self.incremental_mode {
            return;
        }
        let Some(deadline) = self.solve_deadline.get() else {
            return;
        };
        let now = Instant::now();
        let remaining = deadline.saturating_duration_since(now);
        let budget = (remaining / 10).clamp(FLOOR, CAP);
        let bounded = now + budget;
        if bounded < deadline {
            self.solve_deadline.set(Some(bounded));
            self.eq_qe_lane_counters.refutation_bounds += 1;
            self.last_statistics.set_int(
                "eq_qe.legacy_refutation_budget_ms",
                u64::try_from(budget.as_millis()).unwrap_or(u64::MAX),
            );
        }
    }

    /// Pin every free `Int`/`Real`/`Bool` constant of the authored
    /// quantified roots that the elimination made VANISH from the working
    /// set (`∃x. x = c ∨ p` eliminates to `true`): the ground solver would
    /// leave it unassigned, and the quantified model gate cannot evaluate an
    /// authored comparison against an unpinned leaf. Sound for this lane's
    /// use: the working set is equivalent to the authored scope and mentions
    /// no such constant, so the authored scope's truth does not depend on
    /// it, and conjoining `c = 0` (resp. `p`) preserves satisfiability of
    /// the working set in both directions.
    fn eq_qe_pin_vanished_constants(&mut self, roots: &[TermId], working: &mut Vec<TermId>) {
        let mut authored: Vec<TermId> = Vec::new();
        for &root in roots {
            if contains_quantifier(&self.ctx.terms, root) {
                collect_free_scalar_constants(&self.ctx.terms, root, &mut authored);
            }
        }
        if authored.is_empty() {
            return;
        }
        let mut present = ay_core::kani_compat::DetHashSet::default();
        let mut stack: Vec<TermId> = working.clone();
        while let Some(t) = stack.pop() {
            if present.insert(t) {
                stack.extend(self.ctx.terms.children(t));
            }
        }
        for constant in authored {
            if present.contains(&constant) {
                continue;
            }
            let pin = match self.ctx.terms.sort(constant).clone() {
                Sort::Bool => constant,
                Sort::Int => {
                    let zero = self.ctx.terms.mk_int(num_bigint::BigInt::from(0));
                    self.ctx.terms.mk_eq(constant, zero)
                }
                Sort::Real => {
                    let zero = self
                        .ctx
                        .terms
                        .mk_rational(num_rational::BigRational::from_integer(0.into()));
                    self.ctx.terms.mk_eq(constant, zero)
                }
                _ => continue,
            };
            working.push(pin);
        }
    }
}

/// Visit cap for [`collect_free_scalar_constants`]; past it the collection
/// is partial, which can only leave a leaf unpinned (the gate then refuses
/// and the lane declines).
const MAX_FREE_CONSTANT_VISITS: usize = 1 << 20;

/// Free (unbound) `Int`/`Real`/`Bool` variables of `root`, respecting
/// binder scope by name, in first-seen order.
fn collect_free_scalar_constants(terms: &ay_core::TermStore, root: TermId, out: &mut Vec<TermId>) {
    fn walk<'t>(
        terms: &'t ay_core::TermStore,
        term: TermId,
        scope: &mut Vec<&'t str>,
        visits: &mut usize,
        out: &mut Vec<TermId>,
    ) {
        let Some(left) = visits.checked_sub(1) else {
            return;
        };
        *visits = left;
        match terms.get(term) {
            TermData::Var(name, _) => {
                if !scope.contains(&name.as_str())
                    && matches!(terms.sort(term), Sort::Int | Sort::Real | Sort::Bool)
                    && !out.contains(&term)
                {
                    out.push(term);
                }
            }
            TermData::Forall(vars, body, _) | TermData::Exists(vars, body, _) => {
                let depth = scope.len();
                scope.extend(vars.iter().map(|(name, _)| name.as_str()));
                walk(terms, *body, scope, visits, out);
                scope.truncate(depth);
            }
            _ => {
                for child in terms.children(term) {
                    walk(terms, child, scope, visits, out);
                }
            }
        }
    }
    let mut visits = MAX_FREE_CONSTANT_VISITS;
    walk(terms, root, &mut Vec::new(), &mut visits, out);
}

mod affine_route;
#[cfg(test)]
mod tests;
