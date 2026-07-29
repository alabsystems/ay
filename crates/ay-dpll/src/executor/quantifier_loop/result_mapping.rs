// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Quantifier result mapping: interprets SAT/UNSAT through CEGQI and E-matching semantics.
//!
//! `map_quantifier_result` translates the raw theory-solve result into the correct
//! quantified-formula answer by accounting for CEGQI forall/exists inversion,
//! E-matching incompleteness, interleaved refinement, and assertion restoration.

use ay_core::{TermData, TermId};

use super::super::Executor;
use super::collect_and_conjuncts;
use super::QuantifierProcessingResult;
use crate::cegqi::CegqiInstantiator;
use crate::ematching::contains_quantifier;
use crate::executor::mbqi::{is_pure_arith_bool_symbol, SkippedQuantifierMbqiGate};
use crate::executor::model::{EvalValue, Model};
use crate::executor_types::{Result, SolveResult, UnknownReason};

/// #unit-conjunctive: a top-level assertion counts as a unit FACT only when it
/// is a plain ATOM — no Boolean structure, no quantifier. Restricting it this
/// way is what keeps the unit simplification from smuggling in an obligation:
/// only something unconditionally true may be used to simplify.
fn is_unit_atom(terms: &ay_core::TermStore, t: TermId) -> bool {
    match terms.get(t) {
        TermData::Forall(..) | TermData::Exists(..) | TermData::Not(..) => false,
        TermData::App(ay_core::Symbol::Named(name), _) => {
            !matches!(name.as_str(), "and" | "or" | "=>" | "not" | "ite" | "xor")
        }
        _ => true,
    }
}

/// Truth of `t` under the top-level unit facts, if determined: `Some(true)` /
/// `Some(false)`, or `None` when the units say nothing about it. Handles a
/// negated atom by flipping its atom's unit value.
fn unit_value(
    terms: &ay_core::TermStore,
    units: &ay_core::kani_compat::DetHashMap<TermId, bool>,
    t: TermId,
) -> Option<bool> {
    if let Some(&v) = units.get(&t) {
        return Some(v);
    }
    if let TermData::Not(inner) = terms.get(t) {
        if let Some(&v) = units.get(inner) {
            return Some(!v);
        }
    }
    None
}

/// Rebuild an evaluated scalar as a constant of exactly `sort`.
///
/// `EvalValue::Rational` represents both SMT `Int` and `Real` values, so the
/// expected term sort is load-bearing: integral Reals must remain Real, Ints
/// must be integral, and bit-vector widths must agree. Any incompatible pair
/// fails closed instead of relying on `mk_eq` to discover a sort mismatch.
fn pin_eval_const_for_sort(
    terms: &mut ay_core::TermStore,
    sort: &ay_core::Sort,
    value: &EvalValue,
) -> Option<TermId> {
    match (sort, value) {
        (ay_core::Sort::Bool, EvalValue::Bool(value)) => Some(terms.mk_bool(*value)),
        (ay_core::Sort::Int, EvalValue::Rational(value)) if value.is_integer() => {
            Some(terms.mk_int(value.numer().clone()))
        }
        (ay_core::Sort::Real, EvalValue::Rational(value)) => Some(terms.mk_rational(value.clone())),
        (ay_core::Sort::BitVec(sort), EvalValue::BitVec { value, width })
            if sort.width == *width =>
        {
            Some(terms.mk_bitvec(value.clone(), *width))
        }
        _ => None,
    }
}
use crate::logic_detection::LogicCategory;
use ay_core::kani_compat::DetHashMap as HashMap;

use super::super::MAX_INTERLEAVED_EMATCHING_ROUNDS;

/// Exact constructor-site provenance for recursive NNF normalization inside a
/// positive universal.
///
/// This record is observational: it does not grant authority by itself.
/// `fold_quantified_linear_eqs` installs it only when `source_forall` is an
/// immutable authored assertion root, and the proof tracker still validates
/// exact binders/triggers/substitution plus every changed arithmetic literal.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct QuantifiedLinearNnfProvenance {
    source_forall: TermId,
    normalized_forall: TermId,
}

/// Mutable state threaded through interleaved E-matching refinement.
struct InterleavedEmatchingState {
    result: Result<SolveResult>,
    reached_instantiation_limit: bool,
    ematching_added_instantiations: bool,
    unsat_from_interleaved: bool,
    has_uninstantiated_quantifiers: bool,
    ematching_rounds_completed: u64,
    ematching_instances_created: u64,
}

impl Executor {
    /// Map theory-solve result through quantifier/CEGQI semantics.
    ///
    /// Handles CEGQI forall/exists result inversion, E-matching incompleteness,
    /// and assertion restoration after quantifier preprocessing.
    pub(in crate::executor) fn map_quantifier_result(
        &mut self,
        result: Result<SolveResult>,
        qr: QuantifierProcessingResult,
        category: LogicCategory,
    ) -> Result<SolveResult> {
        let QuantifierProcessingResult {
            has_uninstantiated_quantifiers,
            reached_instantiation_limit,
            has_deferred,
            cegqi_has_forall,
            cegqi_has_exists,
            ematching_added_instantiations,
            refinement_assertions,
            cegqi_ce_lemma_ids,
            cegqi_ce_lemma_groups,
            has_completely_unhandled_quantifiers,
            unhandled_quantifiers,
            ematching_has_exists,
            ematching_rounds_completed,
            ematching_instances_created,
            original_assertions,
            cegqi_state,
            has_unsafe_partial_quantifiers,
            quantifier_consumer_opaque_seq_sat_certificate,
            unsafe_quantifiers_supported_by_uf_completion,
            quantifiers_supported_by_uf_completion,
            quantifiers_supported_by_uf_completion_given_sat,
        } = qr;

        // Phase 0 (M5 demand lane, PRODUCTION for classified families): on-demand
        // frontier flush + fence drain. When the demand lane parked over-frontier
        // instances (LAW #7) and the frontier-gated first solve did NOT already
        // refute, bump `F` and flush the newly-under-frontier parked instances (LAW
        // #1), re-solving each bump; then, before concluding, fence-drain any
        // residual parked queue (LAW #2). Inert (returns `result` verbatim) unless
        // the lane armed — i.e. a classified self-chaining/bridge-cycle family was
        // present (`demand_lane_armed` false otherwise ⇒ byte-identical).
        let result = self.demand_refine(result, category);

        // Phase 1: Interleaved E-matching refinement (#5927).
        let ems = self.run_interleaved_ematching(
            result,
            &refinement_assertions,
            has_uninstantiated_quantifiers,
            ematching_added_instantiations,
            reached_instantiation_limit,
            ematching_rounds_completed,
            ematching_instances_created,
            category,
        );
        self.last_statistics.ematching_rounds_completed = ems.ematching_rounds_completed;
        self.last_statistics.ematching_instances_created = ems.ematching_instances_created;

        // FULL E-MATCHING COVERAGE premise for the left-inverse SAT
        // certificate (#2774) — the certificate-side analogue of the
        // `quantifiers_supported_by_uf_completion_given_sat` coverage
        // conjunction built in quantifier_loop/mod.rs: every quantifier fully
        // instantiated by E-matching within budget (pre- AND post-interleaved
        // flags, conservatively OR-ed), no instantiation-limit hit, no
        // deferred (cost-capped, never-asserted) instantiation, and no
        // existential in the mix. The certificate's construction argument
        // re-verifies every original assertion itself; this gate is the
        // defense-in-depth demanded by #8969's post-mortem — a coverage gap
        // means the ground solve never saw some obligation, and no SAT
        // authority may fire from inside such a gap.
        let full_ematching_coverage = !has_uninstantiated_quantifiers
            && !ems.has_uninstantiated_quantifiers
            && !reached_instantiation_limit
            && !ems.reached_instantiation_limit
            && !has_deferred
            && !ematching_has_exists;

        // Phase 2: Classify result through CEGQI/E-matching semantics.
        let mut final_result = self.classify_quantifier_result(
            ems.result,
            ems.ematching_added_instantiations,
            ems.reached_instantiation_limit,
            ems.unsat_from_interleaved,
            ems.has_uninstantiated_quantifiers,
            has_deferred,
            cegqi_has_forall,
            cegqi_has_exists,
            &cegqi_ce_lemma_ids,
            &cegqi_ce_lemma_groups,
            has_completely_unhandled_quantifiers,
            &unhandled_quantifiers,
            ematching_has_exists,
            refinement_assertions.as_deref(),
            &cegqi_state,
            category,
            has_unsafe_partial_quantifiers,
            quantifier_consumer_opaque_seq_sat_certificate,
            unsafe_quantifiers_supported_by_uf_completion,
            quantifiers_supported_by_uf_completion,
            quantifiers_supported_by_uf_completion_given_sat,
        );

        // Phase 2.5 (CAP-1 certified MBQI SAT): a quantifier-incompleteness
        // Unknown may still be a certifiable SAT when every snapshot `forall`
        // lies in the conservative finite-table + default class. The
        // certificate re-verifies EVERY snapshot assertion under an explicitly
        // constructed interpretation (see `try_finite_table_sat_certificate`
        // for the machine-checked totality argument), so it is self-contained:
        // it never trusts the classification that produced the Unknown, and it
        // can only upgrade a fail-closed Unknown to Sat — an Unsat (or any
        // non-quantifier Unknown reason, e.g. Timeout/Incomplete) is never
        // touched.
        let mut finite_table_sat_certificate = false;
        if matches!(final_result, Ok(SolveResult::Unknown))
            && matches!(
                self.last_unknown_reason,
                Some(
                    UnknownReason::QuantifierCegqiIncomplete
                        | UnknownReason::QuantifierUnhandled
                        | UnknownReason::QuantifierRoundLimit
                        // CCMC M1: a patterned/curried forall whose trigger never
                        // e-matched a ground app lands here (ematching-exists
                        // incompleteness). It is SAFE to consult the finite-table
                        // certificate: the cert partition
                        // (`try_finite_table_sat_certificate`) rejects any
                        // snapshot whose top level contains an exists / nested
                        // quantifier (grant-only, fail-closed), so a genuine
                        // existential is never wrongly discharged here.
                        | UnknownReason::QuantifierEmatchingExistsIncomplete
                )
            )
            // M4 (item 4, CERTIFICATE DISCIPLINE): consult the finite-table SAT
            // certificate ONLY after a full grant-only flush — a parked-nonempty
            // state (the fence hit the deadline/ceiling and left instances withheld)
            // must NEVER grant Sat, because a withheld parked instance could be the
            // refutation. `demand_parked_blocks_sat` is false on production (lane not
            // armed) so this is byte-identical there.
            && !self.demand_parked_blocks_sat()
        {
            if let Some(snapshot) = refinement_assertions.as_deref() {
                let snapshot = snapshot.to_vec();
                if self
                    .try_finite_table_sat_certificate(&snapshot, category)
                    .is_some()
                    // (#p2-default-row) c2: the n-ary bare-tuple + default-row
                    // certificate (multi-binder CAP-1 generalization, e.g.
                    // `∀x,y:Int. p(x,y)`). Grant-only, self-contained,
                    // fail-closed — same discipline as CAP-1.
                    || self
                        .try_default_row_sat_certificate(&snapshot, category)
                        .is_some()
                {
                    finite_table_sat_certificate = true;
                    self.defer_model_validation = false;
                    self.last_model_validated = true;
                    self.last_unknown_reason = None;
                    final_result = Ok(SolveResult::Sat);
                }
            }
        }

        // Phase 2.5b (DT-MBQI-Sat certificate): a datatype-binder `forall`
        // whose body is F4 cell-invariant (`forall x:DT. atom-over-{uf(x)}`)
        // lands here as a quantifier-incompleteness `Unknown` (the datatype
        // binder stays MBQI-unsafe). `try_dt_model_sat_certificate` re-verifies
        // EVERY snapshot assertion under an explicitly completed interpretation
        // (grant-only, self-contained, `AY_DT_CERT`-gated: `None` — hence
        // byte-identical — unless `AY_DT_CERT=on`), so a genuine existential /
        // bridge / mixed snapshot is never wrongly discharged (all-or-nothing
        // over F4). It only ever upgrades a fail-closed quantifier-class
        // `Unknown` to `Sat`; it never touches `Unsat`.
        if matches!(final_result, Ok(SolveResult::Unknown))
            && matches!(
                self.last_unknown_reason,
                Some(
                    UnknownReason::QuantifierCegqiIncomplete
                        | UnknownReason::QuantifierUnhandled
                        | UnknownReason::QuantifierRoundLimit
                        | UnknownReason::QuantifierEmatchingExistsIncomplete
                )
            )
            && !self.demand_parked_blocks_sat()
        {
            if let Some(snapshot) = refinement_assertions.as_deref() {
                let snapshot = snapshot.to_vec();
                if self
                    .try_dt_model_sat_certificate(&snapshot, category)
                    .is_some()
                {
                    self.defer_model_validation = false;
                    self.last_model_validated = true;
                    // The post-solve certificate is the same all-or-nothing
                    // authority as the re-sequencing certificate: it validates
                    // every snapshot assertion against its completed model M',
                    // while `last_model` remains the pre-completion candidate M.
                    // Record the grant on this path too so the public emission
                    // funnel does not recheck M against already-certified
                    // universals.  Omitting this made the verdict depend on
                    // whether the earlier bounded re-sequencing probe happened
                    // to finish before its wall-clock budget.
                    self.dt_cert_grant_active = true;
                    self.last_unknown_reason = None;
                    final_result = Ok(SolveResult::Sat);
                }
            }
        }

        // Phase 3: Restore original assertions after solve (#2844).
        let vacuous_trigger_sat_certificate =
            self.sat_is_genuine_under_vacuous_triggers(refinement_assertions.as_deref());
        self.restore_assertions(
            original_assertions,
            &mut final_result,
            category,
            quantifier_consumer_opaque_seq_sat_certificate,
            quantifiers_supported_by_uf_completion,
            quantifiers_supported_by_uf_completion_given_sat,
            has_uninstantiated_quantifiers,
            full_ematching_coverage,
            finite_table_sat_certificate,
            vacuous_trigger_sat_certificate,
        );

        // Phase 3.5 (CCMC M1): a candidate Sat can be demoted here to a
        // quantifier-class Unknown (typically
        // `QuantifierEmatchingExistsIncomplete`) by `restore_assertions` when a
        // PATTERNED/CURRIED forall was E-match-handled but skipped by model
        // validation and left no independent ground evidence — this is exactly
        // the fail-closed path the P0 fix introduced. The finite-table
        // certificate re-verifies the ENTIRE snapshot under an explicitly
        // constructed interpretation (grant-only, self-contained: it never
        // trusts the classification, only upgrades a fail-closed
        // quantifier-class Unknown into Sat, never touches Unsat, and rejects
        // any snapshot with exists/nested quantifiers), so it can still
        // discharge the curried grant shape that only surfaces AFTER restore.
        // Byte-identical to the pre-restore arm on every snapshot the cert
        // rejects; the parked-fence guard still applies.
        if matches!(final_result, Ok(SolveResult::Unknown))
            && matches!(
                self.last_unknown_reason,
                Some(
                    UnknownReason::QuantifierCegqiIncomplete
                        | UnknownReason::QuantifierUnhandled
                        | UnknownReason::QuantifierRoundLimit
                        | UnknownReason::QuantifierEmatchingExistsIncomplete
                )
            )
            && !self.demand_parked_blocks_sat()
        {
            if let Some(snapshot) = refinement_assertions.as_deref() {
                let snapshot = snapshot.to_vec();
                if self
                    .try_finite_table_sat_certificate(&snapshot, category)
                    .is_some()
                    // (#p2-default-row) c2, post-restore mirror of the
                    // phase-2.5 arm.
                    || self
                        .try_default_row_sat_certificate(&snapshot, category)
                        .is_some()
                {
                    self.defer_model_validation = false;
                    self.last_model_validated = true;
                    self.last_unknown_reason = None;
                    final_result = Ok(SolveResult::Sat);
                }
            }
        }

        // Phase 3.5b (DT-MBQI-Sat certificate, post-restore): the datatype-
        // binder F4 grant shape that only surfaces after `restore_assertions`
        // demotes a candidate Sat to a quantifier-class `Unknown`. Same
        // grant-only, `AY_DT_CERT`-gated, all-or-nothing certificate as the
        // pre-restore arm; byte-identical on every snapshot it declines.
        if matches!(final_result, Ok(SolveResult::Unknown))
            && matches!(
                self.last_unknown_reason,
                Some(
                    UnknownReason::QuantifierCegqiIncomplete
                        | UnknownReason::QuantifierUnhandled
                        | UnknownReason::QuantifierRoundLimit
                        | UnknownReason::QuantifierEmatchingExistsIncomplete
                )
            )
            && !self.demand_parked_blocks_sat()
        {
            if let Some(snapshot) = refinement_assertions.as_deref() {
                let snapshot = snapshot.to_vec();
                if self
                    .try_dt_model_sat_certificate(&snapshot, category)
                    .is_some()
                {
                    self.defer_model_validation = false;
                    self.last_model_validated = true;
                    // Mirror the pre-restore DT grant arm above.  Both paths
                    // certify the completed model M', so both must carry the
                    // same emission-gate authority bit.
                    self.dt_cert_grant_active = true;
                    self.last_unknown_reason = None;
                    final_result = Ok(SolveResult::Sat);
                }
            }
        }

        final_result
    }

    /// M5 demand lane (PRODUCTION for classified families) — Phase 0 refinement:
    /// the outer demand loop that turns the frontier gate into a decision procedure.
    ///
    /// LAW #6 (interleave engages on Sat-OR-Unknown-with-model): a definitive
    /// UNSAT is the frontier-gated refutation — return it untouched (this is the
    /// takesome flip). Otherwise, while over-frontier instances are parked and the
    /// frontier ceiling is not hit:
    ///   LAW #1 (unconditional under-frontier flush): bump `F`, assert EVERY parked
    ///   instance now at generation `<= F` (model filtering may ORDER, never
    ///   suppress — the parking-fixpoint trap), and re-solve.
    /// Then LAW #2 (fence): if any instances remain parked (still over the final
    /// frontier), drain the WHOLE queue directly — bypassing the E-matching seen
    /// memo, fresh budget — and re-solve once before any conclusion. The fence
    /// guarantees no Sat/Unknown is reported while a parked instance that could
    /// refute is withheld.
    ///
    /// SOUNDNESS: every asserted instance is a universal-instantiation consequence
    /// (adding it only strengthens the problem), so an UNSAT reached here is
    /// genuine and any surviving non-UNSAT is at least as strong as the eager
    /// path's. The lane is armed only when a classified self-chaining/bridge-cycle
    /// family is present, so this whole method is inert (`result` returned verbatim)
    /// on every unclassified-quantifier / force-eager solve (byte-identical).
    fn demand_refine(
        &mut self,
        mut result: Result<SolveResult>,
        category: LogicCategory,
    ) -> Result<SolveResult> {
        if !self.demand_lane_armed() {
            return result;
        }
        // A definitive UNSAT is the frontier-gated refutation: done (the flip).
        if matches!(result, Ok(SolveResult::Unsat(_))) {
            return result;
        }
        // LAW #6: engage only on Sat / Unknown (a model or a fail-closed Unknown);
        // a hard error is left alone.
        if !matches!(result, Ok(SolveResult::Sat) | Ok(SolveResult::Unknown)) {
            return result;
        }
        // Frontier ceiling: bound the on-demand deepening. The gated families are
        // recursive-datatype defining axioms whose refutations (per the campaign's
        // measured depth analysis) sit at F<=2; a handful of extra bumps is ample
        // insurance without unbounding the loop.
        const DEMAND_FRONTIER_CEILING: u32 = 8;

        // M4 (item 2, DEADLINE SHARE): the demand lane's fence/deepening work is
        // capped at 50% of the REMAINING deadline, reserving the other half for the
        // decisive fence-drain + ground solve. Principled split (the only magic
        // constant is the 50%): the iterative-deepening flush loop below runs under
        // the tightened sub-deadline; the full deadline is restored before the fence
        // drain so the final ground solve gets the reserved budget. On a null
        // deadline nothing is installed (and the restore is a no-op). SHADOW-ONLY —
        // `demand_refine` already early-returned on production.
        let original_deadline = self.solve_deadline.get();
        if let Some(dl) = original_deadline {
            let now = ay_core::time::Instant::now();
            if let Some(remaining) = dl.checked_duration_since(now) {
                if let Some(fence_dl) = now.checked_add(remaining / 2) {
                    self.solve_deadline.set(Some(fence_dl));
                }
            }
        }

        // LAW #1: flush under-frontier on demand, re-solving each bump. A definitive
        // UNSAT reached mid-loop is the refutation — record it and break so the
        // deadline restore (below) always runs before we return it.
        let mut refuted = false;
        loop {
            let has_parked = self
                .quantifier_manager
                .as_ref()
                .is_some_and(crate::quantifier_manager::QuantifierManager::demand_has_parked);
            let frontier = self.quantifier_manager.as_ref().map_or(
                0,
                crate::quantifier_manager::QuantifierManager::demand_frontier,
            );
            if !has_parked || frontier >= DEMAND_FRONTIER_CEILING || self.should_abort_theory_loop()
            {
                break;
            }
            let flushed = match self.quantifier_manager.as_mut() {
                Some(qm) => qm.demand_flush_under_frontier(&mut self.ctx.terms),
                None => break,
            };
            if !self.demand_assert_flushed(flushed) {
                // Nothing new asserted this bump — a further bump only raises F,
                // so keep going until the ceiling or the queue empties, but avoid
                // a no-progress re-solve.
                continue;
            }
            result = self.solve_for_category(category);
            if matches!(result, Ok(SolveResult::Unsat(_))) {
                refuted = true;
                break;
            }
        }

        // M4 (item 2): restore the full deadline for the decisive fence + ground
        // solve BEFORE any return path — the flush loop above consumed at most 50%
        // of the remaining budget; the fence gets the reserved remainder.
        self.solve_deadline.set(original_deadline);
        if refuted {
            return result;
        }

        // LAW #2: fence drain. Any residual parked instance (over the final
        // frontier) is asserted directly before we conclude. The fence drains the
        // WHOLE queue (grant-only — no model filter), bypassing the seen memo and
        // resetting the seen frame (M4), then re-solves under the reserved deadline.
        let residual = self
            .quantifier_manager
            .as_ref()
            .is_some_and(crate::quantifier_manager::QuantifierManager::demand_has_parked);
        if residual && !self.should_abort_theory_loop() {
            let drained = match self.quantifier_manager.as_mut() {
                Some(qm) => qm.demand_fence_drain(&mut self.ctx.terms),
                None => Vec::new(),
            };
            if self.demand_assert_flushed(drained) {
                result = self.solve_for_category(category);
            }
        }
        result
    }

    /// M4 (item 4, CERTIFICATE DISCIPLINE): whether a demand-lane PARKED-nonempty
    /// state must block a SAT certificate. True iff the demand lane is armed (a
    /// classified family was present) AND instances are still parked (the fence did
    /// not achieve a full grant-only flush — a deadline/ceiling cut it short), so a
    /// certificate would be granting Sat while a possibly-refuting instance is
    /// withheld. On any unclassified-quantifier / force-eager solve the lane is not
    /// armed and this is always `false` — byte-identical.
    ///
    /// This complements `QuantifierManager::has_deferred` (LAW #3), which already
    /// counts the parked queue so the ordinary classification routes a
    /// parked-nonempty state to Unknown; this guard closes the ONE re-upgrade path
    /// (the Phase 2.5 finite-table certificate) that does not consult `has_deferred`.
    fn demand_parked_blocks_sat(&self) -> bool {
        self.demand_lane_armed()
            && self
                .quantifier_manager
                .as_ref()
                .is_some_and(crate::quantifier_manager::QuantifierManager::demand_has_parked)
    }

    /// Assert flushed/fenced demand-lane instances into `ctx.assertions`,
    /// deduplicating against what is already present. Returns whether anything new
    /// was added. (The instances are E-matching instances of universally-asserted
    /// foralls — sound to assert; see `demand_refine`.)
    fn demand_assert_flushed(&mut self, instances: Vec<TermId>) -> bool {
        if instances.is_empty() {
            return false;
        }
        let existing: std::collections::HashSet<TermId> =
            self.ctx.assertions.iter().copied().collect();
        let mut added = false;
        for inst in instances {
            if existing.contains(&inst) {
                continue;
            }
            self.ctx.assertions.push(inst);
            added = true;
        }
        added
    }

    /// DPLL(T)-interleaved E-matching (#5927): after the initial SAT solve,
    /// re-run E-matching with the fresh EUF model until fixpoint.
    fn run_interleaved_ematching(
        &mut self,
        result: Result<SolveResult>,
        refinement_assertions: &Option<Vec<TermId>>,
        has_uninstantiated_quantifiers: bool,
        ematching_added_instantiations: bool,
        reached_instantiation_limit: bool,
        ematching_rounds_completed: u64,
        ematching_instances_created: u64,
        category: LogicCategory,
    ) -> InterleavedEmatchingState {
        let mut state = InterleavedEmatchingState {
            result,
            reached_instantiation_limit,
            ematching_added_instantiations,
            unsat_from_interleaved: false,
            has_uninstantiated_quantifiers,
            ematching_rounds_completed,
            ematching_instances_created,
        };
        let had_preprocessing_instances = ematching_added_instantiations;

        let orig = match (refinement_assertions, &state.result) {
            (Some(orig), Ok(SolveResult::Sat)) => orig,
            _ => return state,
        };
        if !state.ematching_added_instantiations && !has_uninstantiated_quantifiers {
            return state;
        }

        self.set_active_solve_phase("quantifier-interleaved-ematching", "ematching");
        // Capture the deadline/interrupt closure before the loop (owns its
        // snapshots, no borrow of `self`).
        let should_stop = self.make_should_stop();
        for round_idx in 0..MAX_INTERLEAVED_EMATCHING_ROUNDS {
            // Deadline/interrupt guard (#quantifier-deadline): stop refining once
            // the budget is spent. Setting `reached_instantiation_limit` forces
            // the current Sat to be classified as Unknown(QuantifierRoundLimit),
            // never finalized as Sat. (try_ematching_refinement_round carries the
            // same guard for the gap between this check and its inner work.)
            if should_stop() {
                state.reached_instantiation_limit = true;
                break;
            }
            let Some(round) = self.try_ematching_refinement_round(orig) else {
                break;
            };
            state.ematching_rounds_completed += 1;
            state.ematching_instances_created += round.instances_created;
            state.reached_instantiation_limit |= round.reached_limit;
            state.has_uninstantiated_quantifiers = round.has_uninstantiated;

            if round.added == 0 {
                break;
            }
            state.ematching_added_instantiations = true;
            if round_idx + 1 == MAX_INTERLEAVED_EMATCHING_ROUNDS {
                state.reached_instantiation_limit = true;
            }

            self.set_active_solve_phase(
                "quantifier-interleaved-resolve",
                format!("theory:{category:?}"),
            );
            let re_result = self.solve_for_category(category);
            match re_result {
                Ok(SolveResult::Sat) => {
                    state.result = re_result;
                }
                Ok(SolveResult::Unsat(_)) => {
                    state.result = re_result;
                    state.reached_instantiation_limit = false;
                    if had_preprocessing_instances {
                        state.unsat_from_interleaved = true;
                    }
                    break;
                }
                other => {
                    state.result = other;
                    break;
                }
            }
        }
        state
    }

    /// Classify the solve result through CEGQI/E-matching semantics.
    #[allow(clippy::too_many_arguments)]
    fn classify_quantifier_result(
        &mut self,
        result: Result<SolveResult>,
        ematching_added_instantiations: bool,
        reached_instantiation_limit: bool,
        unsat_from_interleaved: bool,
        has_uninstantiated_quantifiers: bool,
        has_deferred: bool,
        cegqi_has_forall: bool,
        cegqi_has_exists: bool,
        cegqi_ce_lemma_ids: &[TermId],
        cegqi_ce_lemma_groups: &[(TermId, Vec<TermId>)],
        has_completely_unhandled_quantifiers: bool,
        unhandled_quantifiers: &[TermId],
        ematching_has_exists: bool,
        refinement_assertions: Option<&[TermId]>,
        cegqi_state: &[(TermId, CegqiInstantiator)],
        category: LogicCategory,
        has_unsafe_partial_quantifiers: bool,
        quantifier_consumer_opaque_seq_sat_certificate: bool,
        unsafe_quantifiers_supported_by_uf_completion: bool,
        quantifiers_supported_by_uf_completion: bool,
        quantifiers_supported_by_uf_completion_given_sat: bool,
    ) -> Result<SolveResult> {
        let cegqi_mixed = cegqi_has_forall && cegqi_has_exists;
        if std::env::var_os("AY_DEBUG_CERT").is_some() {
            let kind = match &result {
                Ok(SolveResult::Sat) => "Sat",
                Ok(SolveResult::Unsat(_)) => "Unsat",
                Ok(SolveResult::Unknown) => "Unknown",
                Err(_) => "Err",
            };
            eprintln!(
                "CERT/classify: result={kind} em_added={ematching_added_instantiations} cegqi_f={cegqi_has_forall} cegqi_e={cegqi_has_exists} uninst={has_uninstantiated_quantifiers} unhandled={has_completely_unhandled_quantifiers}"
            );
        }

        // SOUNDNESS (#quant-alternation wrong-unsat, disjunctive instances): a
        // ground UNSAT cannot be trusted when it may rest on instances of a
        // `forall` that sits in a NON-conjunctive position. E-matching and
        // enumerative instantiation add every collected `forall`'s instances to
        // the assertion set CONJUNCTIVELY; for a `forall` in a disjunction (or
        // negated antecedent — `(=> (forall ...) c)` is NNF `(or (exists. forall
        // ...) c)`) this is unsound: the conjoined instances can manufacture a
        // contradiction the original disjunctive formula does not have. When the
        // UNSAT did NOT come from interleaved refinement or CEGQI, and there is at
        // least one collected `forall` that is not in conjunctive position,
        // re-validate by re-solving ONLY the quantifier-free conjuncts of the
        // pre-instantiation snapshot. If that ground core is not itself UNSAT, the
        // contradiction was instance-manufactured — fail closed to Unknown rather
        // than report a wrong UNSAT. (A genuine top-level-conjunct forall driven
        // to UNSAT by MBQI is handled by the conjunctive-position arm below and is
        // unaffected: all its foralls ARE conjunctive, so this guard is skipped.)
        // `ematching_added_instantiations` is included because the unsound
        // conjoined-instance UNSAT can also arise when a non-conjunctive `forall`
        // WAS instantiated by E-matching (so there are no LEFTOVER uninstantiated
        // quantifiers): the e-matched instances are conjoined just the same. The
        // body still fails closed only when the snapshot has a non-conjunctive
        // forall AND its quantifier-free ground core is satisfiable, so genuine
        // conjunctive-forall and genuine ground-core UNSATs are untouched.
        // This ALSO covers `unsat_from_interleaved`: the unsound conjoined-instance
        // UNSAT arises identically whether the non-conjunctive `forall`'s instances
        // were added up front or by interleaved E-matching (the dt/array case
        // `(not (= (ite (forall v. (= (select a v) (select b v))) ...) ...))`
        // reaches UNSAT via interleaved e-matching at array-extensionality Skolem
        // witnesses). The soundness gate is the BODY: degrade only when the
        // snapshot actually has a non-conjunctive `forall` AND its quantifier-free
        // ground core is satisfiable — i.e. the contradiction was manufactured by
        // conjoining instances of a disjunctively/conditionally-positioned forall.
        // Genuine conjunctive-forall UNSATs (every forall conjunctive ⇒
        // `snapshot_has_nonconjunctive_forall` false) and genuine ground-core
        // UNSATs are untouched; `cegqi_*` UNSATs are handled by the arms below.
        if matches!(result, Ok(SolveResult::Unsat(_))) && !cegqi_has_forall && !cegqi_has_exists {
            if let Some(snapshot) = refinement_assertions {
                if self.snapshot_has_nonconjunctive_forall(snapshot)
                    && !self.ground_core_is_unsat(snapshot, category)
                {
                    if std::env::var_os("AY_DEBUG_CERT").is_some() {
                        eprintln!("CERT/degrade@277");
                    }
                    self.last_unknown_reason = Some(UnknownReason::QuantifierUnhandled);
                    return Ok(SolveResult::Unknown);
                }
            }
        }

        // Soundness guard: a `forall` whose binder sort MBQI cannot synthesize
        // (Array, FP, Seq, RegLan) has no sound SAT path through E-matching
        // alone — E-matching produces only ground instances that already exist
        // in the problem, while the forall ranges over an infinite domain.
        // If the ground solver returned SAT and we did not establish UNSAT
        // through interleaved refinement, return Unknown. UNSAT propagates
        // unchanged because adding partial quantifier instances can only
        // strengthen the problem (ay #8729 / Z3 #6303).
        if has_unsafe_partial_quantifiers
            && !quantifier_consumer_opaque_seq_sat_certificate
            && !unsafe_quantifiers_supported_by_uf_completion
        {
            if let Ok(SolveResult::Sat) | Ok(SolveResult::Unknown) = &result {
                if !unsat_from_interleaved {
                    // SOUND UNSAT RESCUE before the MBQI-unsafe fail-close
                    // (#instance-closure@298 / F6 part v generalization). The
                    // interleaved lane can surface `Sat`/`Unknown` on a window
                    // whose universal-INSTANTIATION consequence set — the ground
                    // snapshot conjuncts plus the E-matched instances of
                    // UNCONDITIONALLY-asserted foralls — is independently UNSAT.
                    // That refutation rests ONLY on instantiation consequences
                    // (`forall i.P(i)` entails `P(t)`), NEVER on the MBQI-unsafe
                    // infinite-domain / extensionality witness this guard
                    // protects, so it is exactly the sound half already trusted
                    // at the `instance_closure` Unknown-arm below — which the
                    // early `return` here otherwise skips. It is the fix for the
                    // mixed-fragment stall where an IDLE LIA atom (e.g. a seq
                    // `len` equation) coexisting with an array-`forall` refutation
                    // flips the ground verdict from `Unsat` to `Unknown` and
                    // spuriously degrades a genuinely-UNSAT query (probe M1/M1d;
                    // minimal repro: an UNSAT array-forall core + `(= len 1)`).
                    //
                    // SOUNDNESS: `instance_closure_ground_unsat` only EVER
                    // promotes UNSAT, and only when a set of universal-
                    // instantiation consequences is itself UNSAT — so it cannot
                    // be the ay#8729/Z3#6303 wrong-SAT (a SAT flip): the
                    // `(forall i. a[i]=b[i]) ∧ a≠b` extensionality case has NO
                    // clashing ground-instance pair (a and b differ only at a
                    // non-instantiated index), so its consequence set stays SAT
                    // and this rescue declines, degrading to Unknown as before.
                    // Gated on `ematching_added_instantiations` so the closure
                    // set genuinely carries instances; declines to the existing
                    // degrade otherwise.
                    if ematching_added_instantiations {
                        if let Some(snapshot) = refinement_assertions {
                            let snapshot = snapshot.to_vec();
                            if self.instance_closure_ground_unsat(&snapshot, category) {
                                if std::env::var_os("AY_DEBUG_CERT").is_some() {
                                    eprintln!("CERT/rescue@298: instance-closure UNSAT");
                                }
                                return Ok(SolveResult::unsat());
                            }
                        }
                    }
                    if std::env::var_os("AY_DEBUG_CERT").is_some() {
                        eprintln!("CERT/degrade@298");
                    }
                    self.last_unknown_reason = Some(UnknownReason::QuantifierUnhandled);
                    return Ok(SolveResult::Unknown);
                }
            }
            // CEGQI's Unsat->Sat disambiguation (the `cegqi_has_forall` /
            // `cegqi_mixed` arms below) is itself unsound for an MBQI-unsafe
            // forall: a ground UNSAT obtained under counterexample-instantiation
            // lemmas can be flipped to a spurious SAT because the missing
            // infinite-domain / extensionality witness was never instantiated
            // (AUFLIA `(forall i. a[i]=b[i]) ∧ a≠b`: the ground solver returns
            // UNSAT, but disambiguation reads that as "forall valid" and reports
            // SAT — ay #8729 / Z3 #6303). A genuinely sound UNSAT here arrives via
            // interleaved E-matching (`unsat_from_interleaved`, handled below and
            // left untouched); any other CEGQI-disambiguated UNSAT degrades to
            // Unknown rather than risk a wrong sat/unsat.
            if let Ok(SolveResult::Unsat(_)) = &result {
                if !unsat_from_interleaved && (cegqi_has_forall || cegqi_mixed) {
                    // SOUNDNESS-PRESERVING COMPLETENESS (#mbqi-completeness Q1):
                    // The blanket degrade above is conservative. Adding a `forall`'s
                    // E-matching INSTANCES is always sound (each instance is a logical
                    // consequence: forall i.P(i) entails P(0)), so a ground UNSAT that
                    // rests on those instances - NOT on CEGQI's (possibly unsound) CE
                    // lemmas - is a genuine UNSAT even for an MBQI-unsafe (array-
                    // indexing) binder. Reconstruct a THEORY-INDEPENDENT refutation
                    // directly from the pre-instantiation snapshot: if instantiating
                    // the conjunctive-position foralls at ground terms yields a literal
                    // and its complement (a pure propositional / equality clash, valid
                    // under every interpretation incl. arrays), the contradiction came
                    // purely from sound instantiation + ground core. Accept it. The
                    // array-extensionality wrong-SAT concern (AUFLIA
                    // (forall i. a[i]=b[i]) and a!=b) is unaffected: that arrives here
                    // as a *Sat* and is degraded by the `Sat` arm above; only an
                    // independently-reconstructed UNSAT survives this exception, and a
                    // satisfiable (forall i. a[i]=b[i]) and a[0]=b[0] has no clashing
                    // literal pair.
                    let clash = refinement_assertions
                        .map(|snap| {
                            !self.snapshot_has_nonconjunctive_forall(snap)
                                && self.unsat_from_direct_instance_clash(snap, category)
                        })
                        .unwrap_or(false);
                    if clash {
                        return Ok(SolveResult::unsat());
                    }
                    if std::env::var_os("AY_DEBUG_CERT").is_some() {
                        eprintln!("CERT/degrade@343");
                    }
                    self.last_unknown_reason = Some(UnknownReason::QuantifierUnhandled);
                    return Ok(SolveResult::Unknown);
                }
            }
        }

        // QuantifierConsumer's library-style universal facts are sometimes intentionally
        // completion axioms over otherwise supported UF/LIA ground state. When
        // process_quantifiers proved that every forall and ground assertion is
        // completion-safe, a ground SAT/UNKNOWN lower result is a satisfiable
        // completion, not an opaque quantifier failure. Existentials still use
        // the normal CEGQI/E-matching mapping because completion does not
        // supply witnesses for them.
        //
        // LEG DISTINCTION (#quantifier_consumer-arith): a genuine ground `Sat` may use the
        // MODEL-BACKED certificate (`..._given_sat`) — the solver's model
        // already establishes every pure-arithmetic ground atom, so only the
        // remaining foralls need completion freedom. A lower `Unknown` (e.g.
        // mod/div incompleteness, empty model) must keep the STRICT
        // certificate: nothing has verified the ground arithmetic atoms, and
        // promoting on evaluability alone is the #quantifier_consumer-arith wrong-SAT.
        //
        // The STRICT certificate stays valid on the `Sat` arm too: it is
        // trusted even to promote a lower `Unknown`, so a fortiori it covers a
        // confirmed ground `Sat` (verification-consumer guarded UF-definition foralls over
        // Seq binders with an empty/supported ground core). Consulting ONLY
        // `given_sat` there silently dropped those to quantifier-unhandled
        // Unknown (caught by seq_get_in_bounds_axiom_reducer_is_sat).
        let uf_completion_certificate = match &result {
            // MERGE: both streams landed this independently (the Seq-sorted
            // verification-consumer reducers regressed to Unknown when this leg consulted
            // `given_sat` alone — their forall bodies fail its BV/Bool/EUF/LIA
            // fragment check by SORT). Identical semantics either way; the
            // #quantifier_consumer-arith wrong-SAT is untouched because the Unknown leg
            // below stays strict-only.
            Ok(SolveResult::Sat) => {
                quantifiers_supported_by_uf_completion
                    || quantifiers_supported_by_uf_completion_given_sat
            }
            Ok(SolveResult::Unknown) => quantifiers_supported_by_uf_completion,
            _ => false,
        };
        if uf_completion_certificate && !cegqi_has_exists {
            if let Ok(SolveResult::Sat) | Ok(SolveResult::Unknown) = &result {
                // DECISION (#forall-alternation): the UF-completion certificate
                // also bypasses model validation. Before trusting it, validate
                // the candidate model with MBQI: if a model-driven instantiation
                // of a snapshot `forall` re-solves to UNSAT, the universal is
                // genuinely violated — decide UNSAT (matching z3). Catches the
                // alternation cases routed here whose body applies a Skolem/UF to
                // the bound variable so the body is not pure-arith. Aggressive mode:
                // a bare `(forall q0 (exists q1 q2 ...))` over Int with no real UF
                // completion is ALSO classified uf-completion-supported and reaches
                // here, so enable the multi-Skolem FM / UF over-approximation
                // refutations. They never flip a genuine completion to UNSAT (they
                // only return UNSAT on a real instantiation contradiction), and the
                // wrapper fully restores model state on any non-UNSAT outcome.
                if let Some(snapshot) = refinement_assertions {
                    if let Some(Ok(SolveResult::Unsat(_))) =
                        self.disambiguate_cegqi_valid_via_mbqi_ext(snapshot, category, true)
                    {
                        return Ok(SolveResult::unsat());
                    }
                }
                self.last_unknown_reason = None;
                return Ok(SolveResult::Sat);
            }
        }

        match result {
            Ok(SolveResult::Sat) | Ok(SolveResult::Unknown) if cegqi_mixed => {
                self.last_unknown_reason = Some(UnknownReason::QuantifierCegqiIncomplete);
                Ok(SolveResult::Unknown)
            }
            Ok(SolveResult::Unsat(_))
                if unsat_from_interleaved && cegqi_ce_lemma_ids.is_empty() =>
            {
                Ok(SolveResult::unsat())
            }
            Ok(SolveResult::Unsat(_))
                if (cegqi_mixed || cegqi_has_forall) && !cegqi_ce_lemma_ids.is_empty() =>
            {
                let disamb = self.disambiguate_cegqi_unsat_ext(
                    category,
                    cegqi_ce_lemma_ids,
                    cegqi_ce_lemma_groups,
                    cegqi_mixed,
                    // Rank-9 step 3: pointwise UF definitions routed through
                    // CEGQI (an Int-sorted defined head is a CEGQI candidate)
                    // land here when the CE lemma drives the first solve
                    // UNSAT; the model-backed certificate decides the
                    // ground-only Sat without a CE-lemma refutation.
                    quantifiers_supported_by_uf_completion_given_sat,
                    // #7956 regression 2: the STRICT completion certificate —
                    // the same one the uf_completion_certificate leg above
                    // already trusts to decide Sat from a lower Unknown — is
                    // consulted for the CE-lemma-driven UNSAT route too (see
                    // the `_ext` doc for the soundness argument).
                    quantifiers_supported_by_uf_completion,
                    cegqi_state,
                    refinement_assertions,
                );
                // SOUNDNESS (#classA half-bounded wrong-UNSAT): even after
                // disambiguation re-affirms UNSAT, that UNSAT cannot be trusted when
                // the pre-instantiation snapshot has a `forall` in a NON-conjunctive
                // position — e.g. the forall disjunct of `(or (not p) (forall X. ¬(X≤4)))`
                // (the NNF of `(not (exists X. (and (≤ X 4) p)))`). Stripping that
                // quantifier-bearing assertion drops its non-quantifier disjuncts (the
                // `(not p)` escape), so the conjoined CE-lemma instance manufactures a
                // bare `Bool(false)` the original disjunctive formula never entailed →
                // wrong-UNSAT (and `disambiguate_cegqi_unsat`'s `ground_only` still
                // carries that derived `Bool(false)`). Re-validate against the
                // quantifier-free ground core of the snapshot; if that core is NOT
                // itself UNSAT the contradiction was instance-manufactured, so fail
                // closed to Unknown. This mirrors the identical guard for the non-CEGQI
                // E-matching path above, which this arm bypasses via the
                // `cegqi_has_forall` gate. SOUND: it only ever weakens UNSAT→Unknown
                // (never produces Sat/Unsat), so it cannot make an invalid goal verify.
                // Applied ONLY to a re-affirmed UNSAT so cases where disambiguation
                // correctly recovers SAT (e.g. QF_AX extensionality) are untouched. A
                // genuine conjunctive-position `forall` driven to UNSAT has
                // `snapshot_has_nonconjunctive_forall == false` and is untouched (its
                // contradiction survives on the quantifier-free ground core).
                if matches!(disamb, Ok(SolveResult::Unsat(_))) {
                    if let Some(snapshot) = refinement_assertions {
                        if self.snapshot_has_nonconjunctive_forall(snapshot)
                            && !self.ground_core_is_unsat(snapshot, category)
                        {
                            self.last_unknown_reason =
                                Some(UnknownReason::QuantifierCegqiIncomplete);
                            return Ok(SolveResult::Unknown);
                        }
                    }
                }
                // SOUNDNESS (#forall-alternation wrong-sat): a CEGQI "forall valid
                // ⟹ SAT" verdict is unreliable when the snapshot has a
                // skolemized-alternation forall with a witness-independent
                // arithmetic conjunct (a bound-var constraint no existential
                // witness can repair). Fail closed there. The genuine
                // witness-driven cases (e.g. `(forall x (exists y (> y x)))`,
                // skolemized to `(forall x (> sk(x) x))`) have no such conjunct
                // and keep their SAT.
                if matches!(disamb, Ok(SolveResult::Sat)) {
                    if let Some(snapshot) = refinement_assertions {
                        // DECISION (#forall-alternation): the CEGQI "forall valid"
                        // verdict bypasses model validation. Validate it directly
                        // with model-based quantifier instantiation against the
                        // candidate (ground-only) model: instantiate each snapshot
                        // `forall` at ground/synthesized candidates, evaluate under
                        // the model, and re-solve the falsifying instances. If that
                        // drives the problem UNSAT the universal is genuinely
                        // violated — decide UNSAT (matching z3) rather than trust
                        // the unvalidated certificate. This resolves the
                        // alternation wrong-sats where infeasibility comes from the
                        // COMBINATION of (skolem-)constrained conjuncts, which no
                        // syntactic guard can see.
                        if let Some(Ok(SolveResult::Unsat(_))) =
                            self.disambiguate_cegqi_valid_via_mbqi_ext(snapshot, category, true)
                        {
                            return Ok(SolveResult::unsat());
                        }
                        // Safety net: fail closed on the unreliable
                        // skolem-alternation shape MBQI could not refute.
                        if self.snapshot_has_witness_independent_skolem_alternation(snapshot) {
                            self.last_unknown_reason =
                                Some(UnknownReason::QuantifierCegqiIncomplete);
                            return Ok(SolveResult::Unknown);
                        }
                    }
                    // When CEGQI disambiguation proves the forall valid (SAT), the
                    // result is semantically validated by the CEGQI proof: CE lemma
                    // UNSAT + ground assertions SAT. The ground-only model cannot be
                    // re-validated against the original quantified assertions because
                    // no ground model satisfies a forall. Skip deferred validation to
                    // prevent false Unknown degradation.
                    self.defer_model_validation = false;
                    self.last_model_validated = true;
                }
                // DECISION (#quantified-ce-lemma, second S3 route): when
                // disambiguation stays honestly Unknown (ground remainder Sat
                // but the CE obligation neither refuted nor decided), try the
                // model-based instantiation refutation before surfacing the
                // Unknown — mirror of the refinement-Unknown branch below. It
                // only ever returns UNSAT on a real instantiation contradiction
                // (a sound universal instance driven UNSAT, now including the
                // per-candidate ISOLATED single-instance solves that decide the
                // NIA-conjunction chokepoint), so this can only upgrade a
                // fail-closed Unknown to the decisive answer, never flip a
                // genuine verdict.
                if matches!(disamb, Ok(SolveResult::Unknown)) {
                    if let Some(snapshot) = refinement_assertions {
                        if let Some(Ok(SolveResult::Unsat(_))) =
                            self.disambiguate_cegqi_valid_via_mbqi_ext(snapshot, category, true)
                        {
                            return Ok(SolveResult::unsat());
                        }
                    }
                }
                disamb
            }
            Ok(SolveResult::Sat) if cegqi_has_forall => {
                let refinement_result = self.try_cegqi_arith_refinement(
                    cegqi_state,
                    category,
                    cegqi_ce_lemma_ids,
                    cegqi_ce_lemma_groups,
                    refinement_assertions,
                );
                if let Some(result) = refinement_result {
                    // DECISION (#forall-alternation): the skolemized inner
                    // existentials of a `forall (exists ...)` leave a pure `forall`
                    // that reaches HERE (cegqi_has_forall, no surviving exists). When
                    // CEGQI refinement is honestly Unknown it has not validated the
                    // certificate; validate with the MBQI / FM projection /
                    // over-approximation pipeline and, if a snapshot `forall`
                    // instantiation / witness projection drives the problem UNSAT,
                    // decide UNSAT (matching z3). The validation only ever returns
                    // UNSAT on a real contradiction, so this only ever upgrades a
                    // fail-closed Unknown to the decisive answer. A genuine SAT
                    // ("forall valid") verdict is LEFT UNTOUCHED — re-validating it
                    // would re-enter the solver and corrupt the SAT model state — so
                    // its model-population path is byte-identical to before.
                    if matches!(result, Ok(SolveResult::Unknown)) {
                        if let Some(snapshot) = refinement_assertions {
                            if let Some(Ok(SolveResult::Unsat(_))) =
                                self.disambiguate_cegqi_valid_via_mbqi_ext(snapshot, category, true)
                            {
                                return Ok(SolveResult::unsat());
                            }
                            // SAT leg (#quantified-ce-lemma): the refinement is
                            // honestly Unknown and MBQI could not refute. This is
                            // the ONLY reachable hook for the valid skolemized
                            // alternation (`forall x (exists y (> y x))`), whose
                            // refinement rounds stay Sat and never reach
                            // disambiguation: rebuild each universal's
                            // DE-SKOLEMIZED counterexample obligation
                            // `L_q = forall ys. ¬psi0(ys, e)` and refute it by a
                            // bounded, isolated ground instantiation. Every L_q
                            // refuted ⟹ every universal is VALID ⟹ with the
                            // full-set Sat already established on entry to this
                            // arm, the problem is SAT (see
                            // `try_quantified_ce_valid_flip` for the certificate
                            // and its gates).
                            if let Some(flip) =
                                self.try_quantified_ce_valid_flip(cegqi_state, snapshot, category)
                            {
                                return flip;
                            }
                        }
                    }
                    if matches!(result, Ok(SolveResult::Sat)) {
                        self.defer_model_validation = false;
                        self.last_model_validated = true;
                    }
                    result
                } else {
                    // No refinement verdict: still try to refute the (unvalidated)
                    // SAT certificate before failing closed — a real instantiation
                    // contradiction makes this the decisive UNSAT.
                    if let Some(snapshot) = refinement_assertions {
                        if let Some(Ok(SolveResult::Unsat(_))) =
                            self.disambiguate_cegqi_valid_via_mbqi_ext(snapshot, category, true)
                        {
                            return Ok(SolveResult::unsat());
                        }
                        // SAT leg (#quantified-ce-lemma): same hook as the
                        // refinement-Unknown branch above, for problems where
                        // refinement was not applicable at all (no model / no
                        // arithmetic CE variables).
                        if let Some(flip) =
                            self.try_quantified_ce_valid_flip(cegqi_state, snapshot, category)
                        {
                            return flip;
                        }
                    }
                    self.last_unknown_reason = Some(UnknownReason::QuantifierCegqiIncomplete);
                    Ok(SolveResult::Unknown)
                }
            }
            Ok(SolveResult::Sat) if cegqi_has_exists => {
                // SOUNDNESS (RED S3, 2026-07-08): for a PURE existential the ground
                // Sat IS the witness (the skolem constants), so the passthrough is
                // sound. But when the snapshot ALSO carries a `forall` — the ∀∃
                // alternation, e.g. `(forall x (exists y (= (* y y) x)))`, which is
                // FALSE (x = 2 has no square root) — the ground Sat only reflects
                // the finitely-INSTANTIATED fragment of the universal (0 and 1 ARE
                // perfect squares), and "incomplete instantiation defaulted to sat".
                // Try to refute via model-based instantiation first (a real
                // instantiation contradiction is the decisive UNSAT, matching z3);
                // otherwise fail closed to Unknown. Pure-∃ snapshots keep the
                // passthrough byte-identically.
                let snapshot_has_forall = refinement_assertions.as_ref().is_some_and(|snap| {
                    snap.iter().any(|&a| {
                        let mut stack = vec![a];
                        while let Some(t) = stack.pop() {
                            match self.ctx.terms.get(t) {
                                TermData::Forall(..) => return true,
                                TermData::App(_, args) => stack.extend(args.iter().copied()),
                                TermData::Not(i) => stack.push(*i),
                                TermData::Ite(c, th, el) => {
                                    stack.push(*c);
                                    stack.push(*th);
                                    stack.push(*el);
                                }
                                TermData::Exists(_, b, _) => stack.push(*b),
                                _ => {}
                            }
                        }
                        false
                    })
                });
                if snapshot_has_forall {
                    if let Some(snapshot) = refinement_assertions {
                        if let Some(Ok(SolveResult::Unsat(_))) =
                            self.disambiguate_cegqi_valid_via_mbqi_ext(snapshot, category, true)
                        {
                            return Ok(SolveResult::unsat());
                        }
                    }
                    self.last_unknown_reason = Some(UnknownReason::QuantifierCegqiIncomplete);
                    Ok(SolveResult::Unknown)
                } else {
                    Ok(SolveResult::Sat)
                }
            }
            Ok(SolveResult::Unsat(_)) if cegqi_has_exists => {
                self.last_unknown_reason = Some(UnknownReason::QuantifierCegqiIncomplete);
                Ok(SolveResult::Unknown)
            }
            Ok(SolveResult::Sat)
                if (has_uninstantiated_quantifiers && !ematching_added_instantiations)
                    || reached_instantiation_limit
                    || has_deferred
                    || has_completely_unhandled_quantifiers =>
            {
                // Vacuous-trigger completeness (#verification-consumer lang/while_let): a
                // triggered `forall` whose every trigger group references a
                // function symbol that has NO ground occurrence in the problem
                // can never be instantiated by E-matching — it contributes zero
                // ground instances. Such a quantifier is therefore *fully*
                // E-match-covered (by the empty set of instances), and a ground
                // SAT model extends to it by interpreting the never-grounded,
                // uninterpreted symbol freely. When the ONLY thing keeping this
                // SAT from being final is one or more such vacuous quantifiers —
                // and there is no OTHER source of incompleteness (no
                // round-limit, no deferred instances, no existentials, no CEGQI
                // forall, no unsafe-binder forall) — the ground SAT is genuine.
                //
                // SOUNDNESS: this branch only ever converts a ground `Sat` into
                // a final `Sat`. It NEVER produces an Unsat, so it cannot make
                // an invalid (should_fail) goal verify: verification requires
                // Unsat, and a `Sat` here means the verification condition's
                // negation is satisfiable (the obligation is NOT discharged).
                // It strictly removes a spurious `Unknown(quantifier-unhandled)`
                // escalation, replacing it with the answer the ground solver
                // already computed and which no possible instantiation could
                // change.
                // The quantifier_consumer-opaque-Seq certificate reaches this arm too: the
                // line-292 skip keeps a certified ground Sat from the blanket
                // unsafe-binder degrade, but the flow then lands here (the
                // verification-consumer axioms are `:pattern`-marked no-MBQI, so the
                // refinement classifier below would fail closed at "no
                // eligible conjunctive foralls"). The certificate's premise —
                // every quantified original is a whitelisted axiom shape with
                // a known model, every ground assertion is in the opaque
                // fragment — is exactly a semantic SAT argument for the
                // skipped quantifiers, the same one the restore_assertions
                // mbqi_gate bypass already trusts. Guards for OTHER
                // incompleteness sources (round limit, deferred instances,
                // existentials) stay.
                if (!reached_instantiation_limit
                    && !has_deferred
                    && !cegqi_has_forall
                    && !cegqi_has_exists
                    && !ematching_has_exists
                    && !has_unsafe_partial_quantifiers
                    && self.sat_is_genuine_under_vacuous_triggers(refinement_assertions))
                    // (#quantifier_consumer-opaque-seq-limit) The certificate does NOT rest on
                    // exhaustive instantiation, so the round limit is not evidence
                    // against it — and REQUIRING !reached_instantiation_limit made
                    // the certificate unusable on the very library it recognizes:
                    // seq_concat associativity plus push_back/push_front-as-concat
                    // saturate E-matching without bound, so the limit is always hit.
                    //
                    // MODEL-EXISTENCE ARGUMENT (why the limit is irrelevant here):
                    // the certificate requires EVERY quantified assertion to be a
                    // recognized quantifier_consumer opaque-Seq axiom, and every ground assertion
                    // to lie in the ground fragment — which BLOCKS every interesting
                    // Seq symbol (seq_concat/seq_get/seq_index_logic/seq_push_*/
                    // seq_contains/...). So ground facts can only mention seq_len,
                    // seq_array and seq_offset. The axioms DEFINE the blocked symbols
                    // from those (e.g. the select bridge defines seq_index_logic from
                    // seq_array/seq_offset; get in/out-of-bounds define seq_get from
                    // seq_index_logic and seq_len), so any ground model extends to the
                    // whole library by interpreting the blocked symbols accordingly.
                    // The ONE library constraint on a ground-visible symbol is
                    // seq_len >= 0, and that is checked explicitly and separately by
                    // `quantifier_consumer_seq_len_ground_terms_have_nonneg_instances`. Guards for
                    // the OTHER incompleteness sources (deferred instances,
                    // existentials, CEGQI foralls) stay.
                    || (quantifier_consumer_opaque_seq_sat_certificate
                        && !has_deferred
                        && !cegqi_has_forall
                        && !cegqi_has_exists
                        && !ematching_has_exists)
                {
                    // The ground SAT is genuine: every uninstantiated forall is
                    // vacuously E-match-complete (its triggers reference a symbol
                    // with no ground occurrence), so the ground model extends to
                    // all of them by interpreting the never-grounded uninterpreted
                    // symbols freely. Mark the result validated and clear the
                    // deferred-validation flag so `restore_assertions` does NOT
                    // re-run the skipped-quantifier MBQI soundness gate (which
                    // would degrade this correct SAT back to Unknown). This
                    // mirrors the `quantifiers_supported_by_uf_completion` SAT
                    // acceptance path. A fresh empty model is installed when none
                    // is present (the SAT carries no theory content for the
                    // free symbols).
                    if self.last_model.is_none() {
                        self.last_model = Some(Model {
                            sat_model: Vec::new(),
                            term_to_var: HashMap::default(),
                            bool_overrides: HashMap::default(),
                            euf_model: None,
                            array_model: None,
                            lra_model: None,
                            lia_model: None,
                            bv_model: None,
                            fp_model: None,
                            string_model: None,
                            seq_model: None,
                            completed_values: HashMap::default(),
                            dt_ground: HashMap::default(),
                            dt_pins: HashMap::default(),
                        });
                    }
                    self.defer_model_validation = false;
                    self.last_model_validated = true;
                    self.last_unknown_reason = None;
                    return Ok(SolveResult::Sat);
                }
                if !unhandled_quantifiers.is_empty() {
                    // SOUNDNESS (#quant-alternation wrong-unsat): `try_mbqi_refinement`
                    // discharges an unhandled `forall` by adding a falsifying ground
                    // instance and re-solving — if that drives the problem to UNSAT it
                    // concludes the universal is violated. That is only sound when the
                    // `forall` is a top-level CONJUNCT of the (post-Skolemization)
                    // problem: a conjunct that is false makes the whole problem false.
                    // A `forall` sitting in a DISJUNCTIVE position (e.g. produced by
                    // finite-domain expansion of an outer `exists` — `(exists x. forall
                    // y. (= x 0))` expands to `(or (forall y. (= 0 0)) (forall y. (= 1
                    // 0)) ...)`) is NOT a conjunct: a false disjunct does not refute the
                    // formula (a sibling `(forall y. (= 0 0))` disjunct is true, so the
                    // whole `exists` is SAT). Feeding such a disjunct to MBQI and reading
                    // its instance-driven UNSAT as a verdict is the alternation
                    // wrong-UNSAT bug. Restrict MBQI to conjunctive-position foralls; if
                    // any unhandled forall is only in a non-conjunctive position, the
                    // ground SAT cannot be soundly refuted here — fail closed to Unknown.
                    // A `forall` marked "E-matching only" (`mark_no_mbqi`, e.g. the
                    // Hilbert-`choose` witness axiom) is treated like a
                    // non-conjunctive-position forall: EXCLUDED from MBQI, and its
                    // presence forces a fail-closed `Unknown` when MBQI does not
                    // otherwise refute — so it is discharged ONLY by E-matching on a
                    // ground trigger (an established witness), matching Verus. Sound
                    // (conservative): can only lose proofs, never a wrong-UNSAT.
                    let conjunctive = refinement_assertions
                        .map(|snap| self.forall_ids_in_conjunctive_position(snap));
                    let (mbqi_quants, has_nonconjunctive): (Vec<TermId>, bool) =
                        if let Some(conj_set) = &conjunctive {
                            let mbqi: Vec<TermId> = unhandled_quantifiers
                                .iter()
                                .copied()
                                .filter(|q| conj_set.contains(q) && !self.ctx.terms.is_no_mbqi(*q))
                                .collect();
                            let has_nonconj = unhandled_quantifiers
                                .iter()
                                .any(|q| !conj_set.contains(q) || self.ctx.terms.is_no_mbqi(*q));
                            (mbqi, has_nonconj)
                        } else {
                            // No snapshot to classify positions: keep the prior
                            // behaviour (all unhandled foralls eligible) EXCEPT still
                            // honor the no-MBQI marker. This path is only reached when
                            // refinement_assertions is None, which does not occur for
                            // quantified problems.
                            let mbqi: Vec<TermId> = unhandled_quantifiers
                                .iter()
                                .copied()
                                .filter(|q| !self.ctx.terms.is_no_mbqi(*q))
                                .collect();
                            let has_nonconj = unhandled_quantifiers
                                .iter()
                                .any(|q| self.ctx.terms.is_no_mbqi(*q));
                            (mbqi, has_nonconj)
                        };

                    let mbqi_result = if mbqi_quants.is_empty() {
                        None
                    } else {
                        self.try_mbqi_refinement(&mbqi_quants, category)
                    };

                    match mbqi_result {
                        // UNSAT from a conjunctive-position forall is sound.
                        Some(Ok(SolveResult::Unsat(_))) => Ok(SolveResult::unsat()),
                        // A SAT/Unknown from MBQI, or no eligible conjunctive foralls,
                        // combined with a still-undischarged non-conjunctive forall,
                        // means the ground SAT is not verified: fail closed.
                        other => {
                            if let Some(result) = other {
                                if !has_nonconjunctive {
                                    // FAIL-CLOSED (P0 patterned-forall wrong-sat): MBQI's
                                    // "no counterexample found" is NOT a totality proof —
                                    // it rests only on the finitely-many ground candidates
                                    // it probed. For a `forall` that E-matching left
                                    // uninstantiated (this arm), emitting that as a final
                                    // SAT is exactly the shifted-trigger (`f(x+1)`)
                                    // wrong-sat this P0 closes: the ground candidate set
                                    // need not contain the falsifying witness (`f(3) = -5`
                                    // is falsified at x=2, not a ground term). Only an
                                    // MBQI *refutation* (Unsat, handled above) is decisive
                                    // here; a non-refuting outcome degrades to a sound
                                    // Unknown. (Genuine SATs certified by the finite-table
                                    // / UF-completion / quantifier_consumer certificate paths are
                                    // decided upstream and never reach here.)
                                    match result {
                                        Ok(SolveResult::Sat) => {
                                            // SOUND EPR / finite-uninterpreted-domain
                                            // SAT certification
                                            // (#special-relations-mbqi-sat). MBQI's
                                            // "no counterexample found" is not by
                                            // itself a totality proof (the P0
                                            // shifted-trigger concern above). But when
                                            // every binder ranges over an uninterpreted
                                            // sort whose universe is generated SOLELY by
                                            // ground constants, the MBQI fixpoint model
                                            // (`try_mbqi_refinement` pinned the predicate
                                            // at every ground point) is a COMPLETE, exact
                                            // witness: the validator re-checks every
                                            // cross-product instance to a definite
                                            // `Bool(true)` over the fully-enumerated
                                            // finite universe. It NEVER grants a wrong
                                            // sat — the shifted-trigger / arithmetic
                                            // shapes are excluded by the
                                            // uninterpreted-sort + no-generating-function
                                            // gates, so this only recovers the
                                            // special-relations (order-axiom) SAT family
                                            // that would otherwise fail closed.
                                            let epr_quants: Vec<TermId> = refinement_assertions
                                                .map(|snap| {
                                                    snap.iter()
                                                        .copied()
                                                        .filter(|&a| {
                                                            matches!(
                                                                self.ctx.terms.get(a),
                                                                TermData::Forall(..)
                                                            )
                                                        })
                                                        .collect()
                                                })
                                                .unwrap_or_else(|| mbqi_quants.clone());
                                            if self
                                                .mbqi_sat_validated_finite_uninterpreted_domain(
                                                    &epr_quants,
                                                )
                                                .is_some()
                                            {
                                                self.defer_model_validation = false;
                                                self.last_model_validated = true;
                                                self.last_unknown_reason = None;
                                                Ok(SolveResult::Sat)
                                            } else if let Some(decided) = refinement_assertions
                                                .and_then(|snap| {
                                                    let snap = snap.to_vec();
                                                    // (#p2-mbqi-empty-universe) EPR
                                                    // over an EMPTY universe:
                                                    // singleton-witness decide (both
                                                    // directions; heavily guarded,
                                                    // fail-closed — see the mbqi.rs
                                                    // doc for the review guards).
                                                    self.mbqi_empty_universe_singleton_decide(
                                                        &snap,
                                                        &epr_quants,
                                                        category,
                                                    )
                                                })
                                            {
                                                Ok(decided)
                                            } else {
                                                self.last_unknown_reason =
                                                    Some(UnknownReason::QuantifierUnhandled);
                                                Ok(SolveResult::Unknown)
                                            }
                                        }
                                        _ => result,
                                    }
                                } else {
                                    if std::env::var_os("AY_DEBUG_CERT").is_some() {
                                        eprintln!("CERT/degrade@802");
                                    }
                                    self.last_unknown_reason =
                                        Some(UnknownReason::QuantifierUnhandled);
                                    Ok(SolveResult::Unknown)
                                }
                            } else {
                                // (#p2-mbqi-empty-universe) No MBQI verdict at
                                // all (no eligible candidates — e.g. an empty
                                // ground universe): try the singleton-witness
                                // decide before failing closed.
                                if !has_nonconjunctive {
                                    if let Some(snap) = refinement_assertions {
                                        let snap = snap.to_vec();
                                        let epr_quants: Vec<TermId> = snap
                                            .iter()
                                            .copied()
                                            .filter(|&a| {
                                                matches!(
                                                    self.ctx.terms.get(a),
                                                    TermData::Forall(..)
                                                )
                                            })
                                            .collect();
                                        if let Some(decided) = self
                                            .mbqi_empty_universe_singleton_decide(
                                                &snap,
                                                &epr_quants,
                                                category,
                                            )
                                        {
                                            return Ok(decided);
                                        }
                                    }
                                }
                                let reason = if reached_instantiation_limit {
                                    UnknownReason::QuantifierRoundLimit
                                } else {
                                    UnknownReason::QuantifierUnhandled
                                };
                                self.last_unknown_reason = Some(reason);
                                Ok(SolveResult::Unknown)
                            }
                        }
                    }
                } else {
                    let reason = if reached_instantiation_limit {
                        UnknownReason::QuantifierRoundLimit
                    } else if has_deferred {
                        UnknownReason::QuantifierDeferred
                    } else {
                        UnknownReason::QuantifierUnhandled
                    };
                    self.last_unknown_reason = Some(reason);
                    Ok(SolveResult::Unknown)
                }
            }
            Ok(SolveResult::Unsat(_)) if ematching_has_exists && !cegqi_has_exists => {
                if let Some(Ok(SolveResult::Unsat(_))) =
                    self.disambiguate_ematching_exists_unsat(refinement_assertions, category)
                {
                    Ok(SolveResult::unsat())
                } else {
                    self.last_unknown_reason =
                        Some(UnknownReason::QuantifierEmatchingExistsIncomplete);
                    Ok(SolveResult::Unknown)
                }
            }
            // (#p2-ufnia-refutation) A ground `Unknown` about to be surfaced,
            // with E-matched instances present: the in-place lane may have
            // failed on a window a FRESH solve of the same consequence set
            // decides (UFNIA `f(0)=0 ∧ ∀x. f(x)²≥1`). Re-solve the
            // quantifier-free snapshot conjuncts plus the provenance-filtered
            // support-axiom instances in isolation; a definitive UNSAT of that
            // consequence set is a sound UNSAT of the problem. Anything else
            // keeps the existing Unknown (reason preserved). CEGQI engagement
            // does not gate this: the closure set is built ONLY from snapshot
            // QF conjuncts + `active_support_axioms` (instances of
            // unconditionally-asserted foralls), so CE lemmas are structurally
            // excluded whatever CEGQI did. (Mixed forall/exists Unknowns are
            // already returned by the `cegqi_mixed` arm above.)
            Ok(SolveResult::Unknown) if ematching_added_instantiations => {
                if std::env::var_os("AY_DEBUG_CERT").is_some() {
                    eprintln!("CERT/instance-closure: unknown-arm reached");
                }
                if let Some(snapshot) = refinement_assertions {
                    let snapshot = snapshot.to_vec();
                    if self.instance_closure_ground_unsat(&snapshot, category) {
                        return Ok(SolveResult::unsat());
                    }
                }
                Ok(SolveResult::Unknown)
            }
            other => other,
        }
    }

    /// Collect the quantifier TermIds (as `collect_quantifiers` would surface
    /// them, including NNF `Not(Exists)`/`Not(Forall)` conversion) that occur in
    /// a top-level CONJUNCTIVE position of `snapshot`.
    ///
    /// A quantifier in conjunctive position is a top-level conjunct of the
    /// problem: if it is universally false, the whole problem is false, so MBQI
    /// may soundly drive it to UNSAT. Quantifiers reachable only through
    /// disjunctions, `ite` branches, or function arguments are NOT conjuncts and
    /// must not be refuted to UNSAT (the alternation wrong-UNSAT family, e.g. the
    /// disjunction of inner foralls produced by finite-domain expanding an outer
    /// `exists`).
    ///
    /// The descent follows only conjunctive contexts: each assertion is a
    /// conjunct; `(and ...)` propagates conjunctive position to its arguments;
    /// `Not(Not(x))` propagates (double negation); `Not(or ...)` De-Morgans to a
    /// conjunction of negations and propagates; and `Not(=> p q)` ≡ `p ∧ ¬q`
    /// propagates. This mirrors the conjunctive cases of
    /// `ArithInstantiator::process_assertion` and `collect_quantifiers`.
    /// A top-level assertion counts as a unit FACT only when it is a plain
    /// atom — no Boolean structure and no quantifier — so unit-simplifying with
    /// it cannot smuggle in an obligation.
    #[allow(clippy::wrong_self_convention)]
    fn forall_ids_in_conjunctive_position(
        &mut self,
        snapshot: &[TermId],
    ) -> ay_core::kani_compat::DetHashSet<TermId> {
        use ay_core::kani_compat::DetHashSet as HashSet;
        use ay_core::Symbol;
        let mut out: HashSet<TermId> = HashSet::default();

        // #unit-conjunctive: a top-level UNIT literal is a FACT, so the
        // conjunctive-position test must be taken modulo those facts, not just
        // read off the syntax tree.
        //
        // `(=> ext_eq_0 (forall i . B i))` with `(assert ext_eq_0)` also present
        // puts that `forall` in a *disjunctive* syntactic position — the walk
        // below stops at `=>` — even though `ext_eq_0` is asserted true, which
        // makes the `forall` an outright top-level consequence and its instances
        // sound ground facts. The purely syntactic reading made
        // `snapshot_has_nonconjunctive_forall` fire, and the #classA guard then
        // discarded the genuine UNSAT the engine had already derived (#7956).
        //
        // Unit-simplifying first is sound (a unit assertion is unconditionally
        // true) and strictly more accurate — it only ever RECOGNISES foralls that
        // really are consequences; it never admits one that isn't.
        let mut units: ay_core::kani_compat::DetHashMap<TermId, bool> =
            ay_core::kani_compat::DetHashMap::default();
        for &a in snapshot {
            match self.ctx.terms.get(a) {
                TermData::Not(inner) => {
                    let inner = *inner;
                    if is_unit_atom(&self.ctx.terms, inner) {
                        units.insert(inner, false);
                    }
                }
                _ => {
                    if is_unit_atom(&self.ctx.terms, a) {
                        units.insert(a, true);
                    }
                }
            }
        }

        // `positive` tracks polarity: true = the term appears positively in a
        // conjunctive context, false = it appears negated (so an inner `and`
        // becomes a disjunction and stops conjunctive descent).
        let mut stack: Vec<(TermId, bool)> = snapshot.iter().map(|&a| (a, true)).collect();
        let mut visited: HashSet<(TermId, bool)> = HashSet::default();
        while let Some((term, positive)) = stack.pop() {
            if !visited.insert((term, positive)) {
                continue;
            }
            match self.ctx.terms.get(term).clone() {
                TermData::Forall(..) | TermData::Exists(..) if positive => {
                    // A bare quantifier in positive conjunctive position. Use
                    // collect_quantifiers to surface the exact TermId(s)
                    // (identity for forall/exists in this position).
                    let mut q = Vec::new();
                    crate::ematching::collect_quantifiers(&mut self.ctx.terms, term, &mut q);
                    out.extend(q);
                }
                TermData::Not(inner) => {
                    let inner_data = self.ctx.terms.get(inner).clone();
                    match inner_data {
                        // NNF: a negated quantifier in positive conjunctive
                        // position becomes the dual quantifier (a conjunct).
                        // Reproduce the exact TermId collect_quantifiers builds.
                        TermData::Exists(vars, body, triggers) if positive => {
                            let neg_body = self.ctx.terms.mk_not(body);
                            let converted = self
                                .ctx
                                .terms
                                .mk_forall_with_triggers(vars, neg_body, triggers);
                            out.insert(converted);
                        }
                        TermData::Forall(vars, body, triggers) if positive => {
                            let neg_body = self.ctx.terms.mk_not(body);
                            let converted = self
                                .ctx
                                .terms
                                .mk_exists_with_triggers(vars, neg_body, triggers);
                            out.insert(converted);
                        }
                        // Double negation: keep polarity, descend.
                        TermData::Not(inner2) => stack.push((inner2, positive)),
                        // Not(or A B) ≡ (and ¬A ¬B): conjunctive when positive.
                        // Not(and A B) ≡ (or ¬A ¬B): disjunctive — stop descent.
                        _ => stack.push((inner, !positive)),
                    }
                }
                TermData::App(Symbol::Named(name), args) => {
                    // `(and ...)` in positive position and `(or ...)` under a
                    // negation (De Morgan -> conjunction) both keep a conjunctive
                    // context for their arguments. Everything else (positive
                    // `or`, function applications, `=>`, `ite`) breaks conjunctive
                    // descent — quantifiers below are not top-level conjuncts...
                    if (name == "and" && positive) || (name == "or" && !positive) {
                        for &arg in &args {
                            stack.push((arg, positive));
                        }
                    } else if name == "=>" && positive && args.len() == 2 {
                        // ...EXCEPT modulo top-level unit facts (#unit-conjunctive).
                        // `(=> a b)`: if `a` is a unit fact, `b` is a top-level
                        // consequence, so descend conjunctively. If `b` is already
                        // true (or `a` already false), the implication is satisfied
                        // and constrains nothing — it cannot put any forall of its
                        // own into a disjunctive obligation, so descend into
                        // neither side.
                        let (a, b) = (args[0], args[1]);
                        let a_unit = unit_value(&self.ctx.terms, &units, a);
                        let b_unit = unit_value(&self.ctx.terms, &units, b);
                        if b_unit == Some(true) || a_unit == Some(false) {
                            // satisfied by a unit fact — contributes nothing
                        } else if a_unit == Some(true) {
                            stack.push((b, positive));
                        }
                    } else if name == "or" && positive {
                        // Unit propagation through a positive `or`: if every
                        // disjunct but one is falsified by a unit fact, the
                        // survivor is a top-level consequence.
                        if !args
                            .iter()
                            .any(|&x| unit_value(&self.ctx.terms, &units, x) == Some(true))
                        {
                            let live: Vec<TermId> = args
                                .iter()
                                .copied()
                                .filter(|&x| unit_value(&self.ctx.terms, &units, x) != Some(false))
                                .collect();
                            if live.len() == 1 {
                                stack.push((live[0], positive));
                            }
                        }
                    }
                }
                _ => {}
            }
        }
        out
    }

    /// Return `true` if `snapshot` contains a `forall` (as `collect_quantifiers`
    /// would surface it, including NNF `Not(Exists)`/`Not(Forall)` conversion)
    /// that is NOT in a top-level conjunctive position.
    ///
    /// Such a `forall` is a disjunctive obligation; instances of it added
    /// conjunctively to the assertion set can manufacture a spurious UNSAT.
    pub(super) fn snapshot_has_nonconjunctive_forall_probe(&mut self, snapshot: &[TermId]) -> bool {
        self.snapshot_has_nonconjunctive_forall(snapshot)
    }

    fn snapshot_has_nonconjunctive_forall(&mut self, snapshot: &[TermId]) -> bool {
        let conjunctive = self.forall_ids_in_conjunctive_position(snapshot);
        let mut all_quants: Vec<TermId> = Vec::new();
        for &a in snapshot {
            crate::ematching::collect_quantifiers(&mut self.ctx.terms, a, &mut all_quants);
        }
        all_quants
            .into_iter()
            .filter(|&q| matches!(self.ctx.terms.get(q), TermData::Forall(..)))
            .any(|q| !conjunctive.contains(&q))
    }

    /// Re-solve ONLY the quantifier-free conjuncts extracted from `snapshot`
    /// (the pre-instantiation view) and return `true` if they are UNSAT on their
    /// own. This is the genuine ground core: if it is UNSAT, a reported UNSAT did
    /// not depend on (possibly disjunctive) quantifier instances and is sound.
    fn ground_core_is_unsat(
        &mut self,
        snapshot: &[TermId],
        fallback_category: LogicCategory,
    ) -> bool {
        let mut ground: Vec<TermId> = Vec::new();
        for &assertion in snapshot {
            if contains_quantifier(&self.ctx.terms, assertion) {
                let mut conjuncts = Vec::new();
                collect_and_conjuncts(&self.ctx.terms, assertion, &mut conjuncts);
                for conjunct in conjuncts {
                    if !contains_quantifier(&self.ctx.terms, conjunct)
                        && !ground.contains(&conjunct)
                    {
                        ground.push(conjunct);
                    }
                }
            } else if !ground.contains(&assertion) {
                ground.push(assertion);
            }
        }
        if ground.is_empty() {
            // No quantifier-free core: the contradiction can only have come from
            // quantifier instances, so the ground core is NOT independently UNSAT.
            return false;
        }

        let saved_assertions = std::mem::replace(&mut self.ctx.assertions, ground.clone());
        let saved_theory_state = self.incr_theory_state.take();
        let saved_bv_state = self.incr_bv_state.take();
        let (category, _) = self.detect_logic_category(&ground);
        let category = if matches!(category, LogicCategory::Other) {
            fallback_category
        } else {
            category
        };
        let result = self.solve_for_category(category);
        self.ctx.assertions = saved_assertions;
        self.incr_theory_state = saved_theory_state;
        self.incr_bv_state = saved_bv_state;

        matches!(result, Ok(SolveResult::Unsat(_)))
    }

    /// (#p2-ufnia-refutation) Instance-closure FRESH re-solve: re-solve the
    /// quantifier-free conjuncts of `snapshot` TOGETHER WITH the terms of
    /// `self.active_support_axioms` (the E-matched instances of
    /// UNCONDITIONALLY-asserted top-level foralls) as a standalone ground
    /// problem, and return `true` iff that consequence set is definitively
    /// UNSAT on its own.
    ///
    /// WHY A FRESH RE-SOLVE: the in-place ground lane can return `Unknown` on
    /// an instance-augmented window that a fresh solve of the identical window
    /// decides (measured on the UFNIA shape `f(0)=0 ∧ ∀x. f(x)² ≥ 1`, whose
    /// e-matched instance at `x:=0` closes immediately standalone). The
    /// codebase already treats the in-place incremental state as unsafe for
    /// verdict-grade re-solves (`ground_core_is_unsat` deliberately `take()`s
    /// `incr_theory_state`); this mirrors that pattern with ONE extension —
    /// the support-axiom instances are included.
    ///
    /// SOUNDNESS: every re-solved formula is either (a) a quantifier-free
    /// top-level conjunct of the pre-instantiation snapshot, or (b) a member
    /// of `active_support_axioms`, whose provenance contract
    /// (`push_active_support_axiom`, preprocess.rs) guarantees it is a ground
    /// instance of an UNCONDITIONALLY-asserted `forall` — i.e. a universal-
    /// instantiation consequence. CE lemmas are excluded by construction
    /// (they are never pushed into the support set). UNSAT of a consequence
    /// set implies UNSAT of the original problem. The closure set is
    /// additionally FILTERED TO QUANTIFIER-FREE members: an instance of a
    /// forall with a nested-forall body is itself quantified, and feeding it
    /// to the fresh re-solve could re-enter the quantifier pipeline
    /// (reentrancy guard; dropping such a member only weakens the re-solved
    /// set, which is always sound).
    ///
    /// Only ever used to upgrade an `Unknown` to `Unsat`; it never produces a
    /// `Sat` and never overrides a decided verdict.
    fn instance_closure_ground_unsat(
        &mut self,
        snapshot: &[TermId],
        fallback_category: LogicCategory,
    ) -> bool {
        if self.external_stop_reason().is_some() {
            return false;
        }
        let mut ground: Vec<TermId> = Vec::new();
        for &assertion in snapshot {
            if contains_quantifier(&self.ctx.terms, assertion) {
                let mut conjuncts = Vec::new();
                collect_and_conjuncts(&self.ctx.terms, assertion, &mut conjuncts);
                for conjunct in conjuncts {
                    if !contains_quantifier(&self.ctx.terms, conjunct)
                        && !ground.contains(&conjunct)
                    {
                        ground.push(conjunct);
                    }
                }
            } else if !ground.contains(&assertion) {
                ground.push(assertion);
            }
        }
        // Extend with the quantifier-free support-axiom instances. Without at
        // least one, this would duplicate `ground_core_is_unsat` — bail out.
        let support_terms: Vec<TermId> = self
            .active_support_axioms
            .iter()
            .map(|l| l.term)
            .filter(|&inst| !contains_quantifier(&self.ctx.terms, inst))
            .collect();
        let mut added_support = false;
        for inst in support_terms {
            if !ground.contains(&inst) {
                ground.push(inst);
                added_support = true;
            }
        }
        if std::env::var_os("AY_DEBUG_CERT").is_some() {
            eprintln!(
                "CERT/instance-closure: ground={} support_added={added_support}",
                ground.len()
            );
        }
        if !added_support || ground.is_empty() {
            return false;
        }

        // One conjunction through `isolated_ground_solve_is_unsat`: it runs
        // the SAME Nelson-Oppen `purify_int_uf_arith` pass the top-level
        // check-sat pipeline runs (without it, `(* (f 0) (f 0))` stays an
        // opaque nonlinear product the NIA core cannot relate to `f(0)=0`,
        // and the fresh window misses the UNSAT a parsed standalone problem
        // decides in milliseconds), plus the full nested-solve state
        // discipline. Fail-closed: anything short of a definitive Unsat is
        // `false`.
        let formula = self.ctx.terms.mk_and(ground);
        let decided = self.isolated_ground_solve_is_unsat(formula, fallback_category);
        if decided && std::env::var_os("AY_DEBUG_CERT").is_some() {
            eprintln!("CERT/instance-closure: UNSAT via fresh consequence-set re-solve");
        }
        decided
    }

    /// SOUND closed-universal-validity precheck (#quant-ws closed-forall wrong-SAT).
    ///
    /// A top-level conjunct assertion that is a `Forall(vars, body)` with a
    /// CLOSED, quantifier-free `body` (every free symbol of `body` is one of
    /// `vars`; no free constant / UF / array / outer-bound var — see
    /// `closed_quantifier_free_forall_parts`) is model-INDEPENDENT: it is either
    /// VALID (its negation is unsat — nothing to do) or unconditionally FALSE
    /// (its negation is sat — `(check-sat)` is then UNSAT *regardless* of every
    /// other assertion, because a false top-level conjunct makes the whole
    /// conjunction false).
    ///
    /// For each such conjunct we skolemize the body (substitute each bound var
    /// with a fresh free constant of the same sort) and solve `(not body)` as a
    /// GROUND problem. If that ground negation is DEFINITIVELY SAT, the universal
    /// is provably false and we return `Some(unsat())`. Anything else (negation
    /// unsat ⇒ universal valid; negation unknown ⇒ undecided) leaves the
    /// universal untouched and we fall through.
    ///
    /// SOUNDNESS: this can ONLY return UNSAT, and ONLY when a conjunct is
    /// PROVABLY false (its skolemized negation is definitively SAT). It therefore
    /// cannot over-degrade a genuine SAT (it never returns SAT/Unknown), cannot
    /// flip a genuine UNSAT, and — because it excludes any forall with an inner
    /// existential (the body would contain a quantifier ⇒ rejected) or any free
    /// symbol (rejected) — never touches `∀x∃y. P` alternations or
    /// array-extensionality `∀i. A0[i]=A1[i]` universals. The full solver state
    /// it perturbs (assertions, incremental theory state, model/validation
    /// bookkeeping) is saved and restored on every path.
    ///
    /// Returns `None` when no closed false universal is found (the normal
    /// quantifier pipeline runs unchanged).
    pub(in crate::executor) fn closed_universal_validity_precheck(
        &mut self,
        fallback_category: LogicCategory,
    ) -> Option<Result<SolveResult>> {
        // Re-entrancy guard: the ground negation solve below runs the full
        // check-sat dispatch, which must not recurse back into this precheck.
        if self.in_closed_universal_precheck {
            return None;
        }

        // Identify top-level conjunct foralls with a closed, quantifier-free body.
        // Only top-level conjuncts qualify: a forall reachable only through a
        // disjunction / ite / function argument is NOT a conjunct, so its falsity
        // does not refute the problem. We descend solely through `(and ...)`.
        let mut candidates: Vec<TermId> = Vec::new();
        let assertions = self.ctx.assertions.clone();
        for &assertion in &assertions {
            let mut conjuncts = vec![assertion];
            collect_and_conjuncts(&self.ctx.terms, assertion, &mut conjuncts);
            for c in conjuncts {
                if super::closed_quantifier_free_forall_parts(&self.ctx.terms, c).is_some()
                    && !candidates.contains(&c)
                {
                    candidates.push(c);
                }
            }
        }
        if candidates.is_empty() {
            return None;
        }

        self.in_closed_universal_precheck = true;
        let result = self.closed_universal_validity_precheck_inner(&candidates, fallback_category);
        self.in_closed_universal_precheck = false;
        result
    }

    fn closed_universal_validity_precheck_inner(
        &mut self,
        candidates: &[TermId],
        fallback_category: LogicCategory,
    ) -> Option<Result<SolveResult>> {
        use crate::ematching::subst_vars;

        for &forall_id in candidates {
            let Some((vars, body)) =
                super::closed_quantifier_free_forall_parts(&self.ctx.terms, forall_id)
            else {
                continue;
            };

            // Skolemize: map each bound var to a fresh free constant of its sort.
            let mut subst: HashMap<String, TermId> = HashMap::default();
            for (name, sort) in &vars {
                let fresh = self
                    .ctx
                    .terms
                    .mk_fresh_var(&format!("cu!{name}"), sort.clone());
                subst.insert(name.clone(), fresh);
            }
            let skolem_body = subst_vars(&mut self.ctx.terms, body, &subst);
            let neg = self.ctx.terms.mk_not(skolem_body);

            // Solve `(not body)` as a ground problem in isolation. Save and
            // restore every piece of state the ground solve perturbs so the
            // outer solve is unaffected on any non-refuting path.
            let saved_assertions = std::mem::replace(&mut self.ctx.assertions, vec![neg]);
            let saved_theory_state = self.incr_theory_state.take();
            let saved_bv_state = self.incr_bv_state.take();
            let saved_model = self.last_model.take();
            let saved_model_validated = self.last_model_validated;
            let saved_validation_stats = self.last_validation_stats.take();
            let saved_unknown_reason = self.last_unknown_reason;
            let saved_defer = self.defer_model_validation;
            self.defer_model_validation = false;

            let neg_assertions = vec![neg];
            let (category, _) = self.detect_logic_category(&neg_assertions);
            let category = if matches!(category, LogicCategory::Other) {
                fallback_category
            } else {
                category
            };
            let neg_result = self.solve_for_category(category);
            // S2 FAIL-CLOSED (2026-07-08, ay wishlist rank 2 / RED suite S2): the
            // Sat below flips the WHOLE problem to UNSAT — the ex-falso direction —
            // so it must never rest on an UNVALIDATED model. `solve_for_category`
            // can return Sat without validation on incomplete fragments (the
            // solve_nia leg is the recorded wrong-UNSAT witness). Run the canonical
            // validation gate NOW, while the negation is still asserted: it is
            // fill-only + full-validation, so it can only DOWNGRADE an unverified
            // Sat to Unknown, never mint one.
            let neg_result = match neg_result {
                Ok(SolveResult::Sat) if !self.last_model_validated => {
                    // Validation runs against the still-asserted negation; save and
                    // restore the two pieces of state it touches that the outer
                    // save/restore set does not cover, so the ground validation
                    // cannot leak into the enclosing solve.
                    let saved_last_result = self.last_result.take();
                    let saved_skip_model_eval = self.skip_model_eval;
                    self.last_result = Some(SolveResult::Sat);
                    let validated = self.finalize_sat_model_validation();
                    self.last_result = saved_last_result;
                    self.skip_model_eval = saved_skip_model_eval;
                    validated
                }
                other => other,
            };

            self.ctx.assertions = saved_assertions;
            self.incr_theory_state = saved_theory_state;
            self.incr_bv_state = saved_bv_state;
            self.last_model = saved_model;
            self.last_model_validated = saved_model_validated;
            self.last_validation_stats = saved_validation_stats;
            self.last_unknown_reason = saved_unknown_reason;
            self.defer_model_validation = saved_defer;

            // The skolemized negation is definitively SAT — and its model passed
            // the canonical validation gate — ⇒ the universal is provably false
            // ⇒ the whole (conjunctive) problem is UNSAT.
            if matches!(neg_result, Ok(SolveResult::Sat)) {
                return Some(Ok(SolveResult::unsat()));
            }
        }
        None
    }

    /// Recover UNSAT when the quantifier-free slice is already contradictory.
    ///
    /// E-matching an existential is incomplete for proving UNSAT because it
    /// adds witness instances conjunctively. However, if the ground assertions
    /// from the pre-E-matching snapshot are UNSAT on their own, the existential
    /// instances did not cause the contradiction and the original formula is
    /// definitively UNSAT.
    fn disambiguate_ematching_exists_unsat(
        &mut self,
        refinement_assertions: Option<&[TermId]>,
        fallback_category: LogicCategory,
    ) -> Option<Result<SolveResult>> {
        let refinement_assertions = refinement_assertions?;
        let mut ground = Vec::new();
        for &assertion in refinement_assertions {
            let mut conjuncts = Vec::new();
            collect_and_conjuncts(&self.ctx.terms, assertion, &mut conjuncts);
            if conjuncts.is_empty() {
                conjuncts.push(assertion);
            }
            for conjunct in conjuncts {
                if !contains_quantifier(&self.ctx.terms, conjunct) && !ground.contains(&conjunct) {
                    ground.push(conjunct);
                }
            }
        }
        if ground.is_empty() {
            return None;
        }

        let saved_assertions = std::mem::replace(&mut self.ctx.assertions, ground.clone());
        let saved_theory_state = self.incr_theory_state.take();
        let saved_bv_state = self.incr_bv_state.take();
        let (category, _) = self.detect_logic_category(&ground);
        let category = if matches!(category, LogicCategory::Other) {
            fallback_category
        } else {
            category
        };
        let result = self.solve_for_category(category);
        self.ctx.assertions = saved_assertions;
        self.incr_theory_state = saved_theory_state;
        self.incr_bv_state = saved_bv_state;

        Some(result)
    }

    /// Decide whether a ground `Sat` is genuine even though some triggered
    /// `forall`s were left uninstantiated — specifically, whether EVERY `forall`
    /// in the pre-strip refinement snapshot is *vacuously E-match-complete*
    /// (its triggers reference a function symbol with no ground occurrence, so
    /// no instantiation is possible) AND at least one such vacuous `forall` is
    /// present.
    ///
    /// Returns `false` (the conservative answer that preserves the existing
    /// `Unknown` escalation) when the snapshot is missing, when there are no
    /// foralls, or when ANY forall could still be instantiated. The ground terms
    /// for the trigger-presence test are read from the same snapshot, so the
    /// check sees exactly the ground state the solver reasoned over.
    ///
    /// SOUNDNESS: see the call site. This is a SAT-preservation predicate only;
    /// returning `true` keeps a ground `Sat` as `Sat` and is never used to
    /// produce an `Unsat`.
    fn sat_is_genuine_under_vacuous_triggers(
        &self,
        refinement_assertions: Option<&[TermId]>,
    ) -> bool {
        let Some(snapshot) = refinement_assertions else {
            return false;
        };
        let mut saw_forall = false;
        for &assertion in snapshot {
            let mut conjuncts = Vec::new();
            collect_and_conjuncts(&self.ctx.terms, assertion, &mut conjuncts);
            if conjuncts.is_empty() {
                conjuncts.push(assertion);
            }
            for conjunct in conjuncts {
                if matches!(self.ctx.terms.get(conjunct), TermData::Forall(..)) {
                    saw_forall = true;
                    // Any forall that could still be instantiated (its triggers
                    // have ground candidates, or it has no user triggers) blocks
                    // the genuine-SAT conclusion.
                    if !crate::ematching::quantifier_has_no_possible_trigger_match(
                        &self.ctx.terms,
                        conjunct,
                        snapshot,
                    ) {
                        return false;
                    }
                }
            }
        }
        saw_forall
    }

    /// Restore original assertions after quantifier solving (#2844).
    ///
    /// When `defer_model_validation` is set, validates the model against the
    /// restored original assertions. Model validation violations (Violated)
    /// are caught and degraded to Unknown rather than propagated as hard
    /// errors, because the model was produced by solving preprocessed
    /// assertions (e.g., with mod_div_elim) and may not satisfy the original
    /// un-preprocessed assertions due to theory incompleteness. (#7979)
    fn restore_assertions(
        &mut self,
        original_assertions: Option<Vec<TermId>>,
        final_result: &mut Result<SolveResult>,
        category: LogicCategory,
        quantifier_consumer_opaque_seq_sat_certificate: bool,
        quantifiers_supported_by_uf_completion: bool,
        quantifiers_supported_by_uf_completion_given_sat: bool,
        has_uninstantiated_quantifiers: bool,
        full_ematching_coverage: bool,
        finite_table_sat_certificate: bool,
        vacuous_trigger_sat_certificate: bool,
    ) {
        if self.defer_model_validation {
            self.defer_model_validation = false;
            let pre_restore_assertions = self.ctx.assertions.clone();
            self.ctx.assertions = original_assertions
                .expect("BUG: defer_model_validation set but original_assertions is None");
            if matches!(final_result, Ok(SolveResult::Sat)) {
                if quantifiers_supported_by_uf_completion {
                    if self.last_model.is_none() {
                        self.last_model = Some(Model {
                            sat_model: Vec::new(),
                            term_to_var: HashMap::default(),
                            bool_overrides: HashMap::default(),
                            euf_model: None,
                            array_model: None,
                            lra_model: None,
                            lia_model: None,
                            bv_model: None,
                            fp_model: None,
                            string_model: None,
                            seq_model: None,
                            completed_values: HashMap::default(),
                            dt_ground: HashMap::default(),
                            dt_pins: HashMap::default(),
                        });
                    }
                    self.last_model_validated = true;
                    self.last_unknown_reason = None;
                    return;
                }
                match self.finalize_sat_model_validation() {
                    Ok(result) => {
                        // (#7979) Model validation now uses SAT-fallback for
                        // quantified assertions when the Tseitin variable is
                        // assigned true. If validation passed (returned Sat),
                        // trust it — the validation pipeline already handles the
                        // "no verification evidence" case internally. Only
                        // degrade to Unknown if quantifiers were skipped (no
                        // SAT-level evidence) AND no other assertions were
                        // independently verified.
                        //
                        // (#8729) When a quantifier assertion was skipped,
                        // theory-delegated evidence (`delegated_checks`) does
                        // NOT count as sufficient evidence. Delegation trusts a
                        // downstream theory solver (BV/array/EUF) to have
                        // validated the model, but those theory solvers never
                        // see quantifier constraints — the quantifier was only
                        // handled at the E-matching/SAT level, and its
                        // instances were removed when original_assertions were
                        // restored. Example: Z3 #6303 byte-concat reproducer
                        // (forall a[concat(...)]=b[concat(...)] + ground
                        // disequality select a #x0 != select b #x0). The
                        // quantifier is skipped; the ground disequality hits
                        // observation.rs Unknown+TERM_FLAG_ARRAY and returns
                        // delegated() because bv_model.is_some(). Prior guard
                        // saw checked > 0 (from delegation) and trusted SAT,
                        // yielding an unsound sat answer. We require
                        // *independent* evidence (checked - delegated_checks)
                        // or sat_fallback_count when a quantifier was skipped.
                        // If such evidence exists, we still run an MBQI
                        // quick-check on the restored quantifiers before
                        // trusting the SAT result.
                        if matches!(result, SolveResult::Sat) {
                            let stats = self.last_validation_stats.as_ref();
                            let has_skipped_quantifiers =
                                stats.is_some_and(|s| s.skipped_quantifier > 0);
                            let has_any_evidence = stats.is_some_and(|s| {
                                let independent = s.checked.saturating_sub(s.delegated_checks);
                                independent > 0 || s.sat_fallback_count > 0
                            });
                            if has_skipped_quantifiers {
                                let has_quantifier_consumer_seq_model_completion =
                                    super::model_completion::skipped_quantifiers_have_quantifier_consumer_seq_model_completion(
                                        &self.ctx.terms,
                                        &self.ctx.assertions,
                                    );
                                // `result == Sat` here means the model was
                                // VALIDATED against the restored assertions
                                // (modulo the skipped quantifiers), so the
                                // MODEL-BACKED certificate (`..._given_sat`)
                                // soundly covers the skipped UF-definition
                                // foralls: every ground atom's truth is
                                // established by the validated model, and the
                                // definition foralls complete pointwise
                                // (#quantifier_consumer-arith leg distinction).
                                // `no_mbqi` (trigger-gated Hilbert-`choose`)
                                // acceptance: with the synthesized-witness leak closed
                                // (the terms.is_synthesized guard in ematching/mod.rs),
                                // the finalize-VALIDATED `Sat` of a skipped no_mbqi
                                // forall is the genuine trigger-only (Verus-faithful)
                                // counterexample — accept it (=> Counterexample)
                                // instead of fail-closing to Unknown. Reached only for
                                // result==Sat, so it can never yield a wrong-Verified;
                                // no_mbqi is set solely by the deductive-checks choose encoder.
                                let restored_has_no_mbqi_forall = self
                                    .ctx
                                    .assertions
                                    .iter()
                                    .any(|&a| self.ctx.terms.is_no_mbqi(a));
                                // NOTE(#8969): no unguarded "restored total UF
                                // completion" authority belongs in these
                                // disjunctions — SAT acceptance for skipped
                                // UF-definition foralls must carry the
                                // LIA-fragment + ground-coverage premises that
                                // `quantifiers_supported_by_uf_completion_given_sat`
                                // enforces at its construction site. A
                                // shape-only pointwise arm (0bd4fda960)
                                // reproduced the popcount wrong-SAT.
                                let mbqi_gate = if has_quantifier_consumer_seq_model_completion
                                    || quantifier_consumer_opaque_seq_sat_certificate
                                    || quantifiers_supported_by_uf_completion
                                    || quantifiers_supported_by_uf_completion_given_sat
                                    || restored_has_no_mbqi_forall
                                {
                                    SkippedQuantifierMbqiGate::Inconclusive
                                } else {
                                    self.mbqi_soundness_gate_for_skipped_quantifiers()
                                };

                                let mbqi_gate_confirms = matches!(
                                    mbqi_gate,
                                    SkippedQuantifierMbqiGate::NoQuantifiers
                                        | SkippedQuantifierMbqiGate::ExhaustivelySatisfied
                                );

                                if has_quantifier_consumer_seq_model_completion
                                    || quantifier_consumer_opaque_seq_sat_certificate
                                    || quantifiers_supported_by_uf_completion
                                    || quantifiers_supported_by_uf_completion_given_sat
                                    || restored_has_no_mbqi_forall
                                    || mbqi_gate_confirms
                                {
                                    *final_result = Ok(result);
                                } else if !has_any_evidence {
                                    // SOUND COMPLETENESS (#mbqi-completeness Q2):
                                    // even with no independent ground evidence, an
                                    // EPR / finite-uninterpreted-domain problem whose
                                    // fixpoint model satisfies every cross-product
                                    // instance is a complete, sound SAT witness.
                                    if self
                                        .try_mbqi_sat_certification(
                                            &pre_restore_assertions,
                                            category,
                                            has_uninstantiated_quantifiers,
                                            full_ematching_coverage,
                                        )
                                        .is_some()
                                    {
                                        *final_result = Ok(SolveResult::Sat);
                                        return;
                                    }
                                    self.last_unknown_reason =
                                        Some(UnknownReason::QuantifierEmatchingExistsIncomplete);
                                    self.last_result = Some(SolveResult::Unknown);
                                    *final_result = Ok(SolveResult::Unknown);
                                } else {
                                    if let Some(refinement_result) = self
                                        .try_skipped_quantifier_mbqi_refinement(
                                            &pre_restore_assertions,
                                            category,
                                        )
                                    {
                                        match refinement_result {
                                            Ok(SolveResult::Unsat(_)) => {
                                                *final_result = Ok(SolveResult::unsat());
                                                return;
                                            }
                                            Err(err) => {
                                                *final_result = Err(err);
                                                return;
                                            }
                                            Ok(SolveResult::Sat | SolveResult::Unknown) => {}
                                        }
                                    }
                                    // SOUND COMPLETENESS (#mbqi-completeness Q2):
                                    // the refinement found no counterexample. If the
                                    // problem is in the EPR / finite-uninterpreted-
                                    // domain fragment, the fixpoint model is a
                                    // complete, sound witness - certify SAT instead
                                    // of failing closed. NEVER returns a wrong SAT
                                    // (the validator requires every cross-product
                                    // instance to evaluate to a definite Bool true
                                    // over a fully-enumerated finite universe).
                                    if self
                                        .try_mbqi_sat_certification(
                                            &pre_restore_assertions,
                                            category,
                                            has_uninstantiated_quantifiers,
                                            full_ematching_coverage,
                                        )
                                        .is_some()
                                    {
                                        *final_result = Ok(SolveResult::Sat);
                                        return;
                                    }
                                    self.last_unknown_reason =
                                        Some(UnknownReason::QuantifierEmatchingExistsIncomplete);
                                    self.last_result = Some(SolveResult::Unknown);
                                    *final_result = Ok(SolveResult::Unknown);
                                }
                            } else {
                                *final_result = Ok(result);
                            }
                        } else {
                            *final_result = Ok(result);
                        }
                    }
                    Err(_) => {
                        // (#p2-ufnia-refutation) Before degrading, try the
                        // instance-closure fresh re-solve: the QF conjuncts of
                        // the restored original assertions plus the
                        // provenance-filtered support-axiom instances form a
                        // consequence set; a definitive standalone UNSAT of it
                        // is a sound UNSAT of the problem (the failed model
                        // validation is evidence the in-place lane's window
                        // handling broke, not that the problem is undecided).
                        let restored_snapshot = self.ctx.assertions.clone();
                        if self.instance_closure_ground_unsat(&restored_snapshot, category) {
                            self.last_unknown_reason = None;
                            self.last_result = Some(SolveResult::unsat());
                            *final_result = Ok(SolveResult::unsat());
                            return;
                        }
                        // Model validation violation against restored assertions
                        // means the solver produced a model (via preprocessed
                        // constraints like mod_div_elim) that doesn't satisfy the
                        // original assertions. This is a theory solver
                        // incompleteness (e.g., mod/div reasoning), not a soundness
                        // bug. Degrade to Unknown. (#7979)
                        self.last_unknown_reason = Some(UnknownReason::Incomplete);
                        self.last_result = Some(SolveResult::Unknown);
                        *final_result = Ok(SolveResult::Unknown);
                    }
                }
            }
        } else if let Some(original_assertions) = original_assertions {
            let pre_restore_assertions = self.ctx.assertions.clone();
            self.ctx.assertions = original_assertions;

            // A few quantified SAT certificates intentionally clear deferred
            // validation before reaching this restoration branch.  That does
            // not make a sampled interpretation of a bound-dependent declared
            // UF total: require the same explicit completion/exhaustiveness
            // authorities as the deferred branch.  Pure arithmetic CEGQI and
            // Skolem-witness certificates do not need this extra UF-totality
            // premise and remain untouched.
            if matches!(final_result, Ok(SolveResult::Sat))
                && self.restored_has_bound_dependent_non_skolem_application()
            {
                let has_quantifier_consumer_seq_model_completion =
                    super::model_completion::skipped_quantifiers_have_quantifier_consumer_seq_model_completion(
                        &self.ctx.terms,
                        &self.ctx.assertions,
                    );
                let restored_has_no_mbqi_forall = self
                    .ctx
                    .assertions
                    .iter()
                    .any(|&a| self.ctx.terms.is_no_mbqi(a));
                // CEGQI can classify the ground remainder Sat before phase
                // 2.5 gets a chance to run the finite-table certificate.  In
                // that case re-check the restored snapshot here.  The
                // certificate's own bare-argument scan still rejects shifted
                // applications such as `f(x + 1)`.
                let finite_table_sat_certificate = finite_table_sat_certificate || {
                    let restored_snapshot = self.ctx.assertions.clone();
                    self.try_finite_table_sat_certificate(&restored_snapshot, category)
                        .is_some()
                };
                let explicit_certificate = has_quantifier_consumer_seq_model_completion
                    || quantifier_consumer_opaque_seq_sat_certificate
                    || quantifiers_supported_by_uf_completion
                    || quantifiers_supported_by_uf_completion_given_sat
                    || finite_table_sat_certificate
                    || vacuous_trigger_sat_certificate
                    || restored_has_no_mbqi_forall;
                let mbqi_gate_confirms = explicit_certificate
                    || matches!(
                        self.mbqi_soundness_gate_for_skipped_quantifiers(),
                        SkippedQuantifierMbqiGate::NoQuantifiers
                            | SkippedQuantifierMbqiGate::ExhaustivelySatisfied
                    );

                if !mbqi_gate_confirms {
                    // Preserve the independently exhaustive EPR/finite-domain
                    // authority used by the deferred branch.
                    if self
                        .try_mbqi_sat_certification(
                            &pre_restore_assertions,
                            category,
                            has_uninstantiated_quantifiers,
                            full_ematching_coverage,
                        )
                        .is_some()
                    {
                        return;
                    }
                    self.last_unknown_reason =
                        Some(UnknownReason::QuantifierEmatchingExistsIncomplete);
                    self.last_result = Some(SolveResult::Unknown);
                    *final_result = Ok(SolveResult::Unknown);
                }
            }
        }
    }

    /// Try to turn a restored skipped-quantifier model counterexample into a
    /// ground refinement before failing closed to Unknown.
    ///
    /// `restore_assertions` validates SAT against the original quantified
    /// assertions. If validation skips a `forall`, MBQI may find a concrete
    /// falsifying instance in the candidate model. In that case, re-solving the
    /// pre-restore ground assertion set plus the MBQI instance can prove UNSAT
    /// instead of returning Unknown. The original assertion set is restored on
    /// every path so incremental callers keep seeing the same formulas. Only
    /// definitive UNSAT and error results are promoted; otherwise the
    /// caller falls back to the existing fail-closed gate with the original
    /// validated model.
    fn try_skipped_quantifier_mbqi_refinement(
        &mut self,
        pre_restore_assertions: &[TermId],
        category: LogicCategory,
    ) -> Option<Result<SolveResult>> {
        let original_assertions = self.ctx.assertions.clone();
        let saved_model = self.last_model.clone();
        let saved_model_validated = self.last_model_validated;
        let saved_validation_stats = self.last_validation_stats.clone();
        let saved_unknown_reason = self.last_unknown_reason;
        let forall_quants: Vec<TermId> = original_assertions
            .iter()
            .copied()
            .filter(|&a| matches!(self.ctx.terms.get(a), TermData::Forall(..)))
            .collect();

        if forall_quants.is_empty() {
            return None;
        }

        let saved_theory_state = self.incr_theory_state.take();
        let saved_bv_state = self.incr_bv_state.take();
        self.ctx.assertions = pre_restore_assertions.to_vec();
        let refinement_result = self.try_mbqi_refinement(&forall_quants, category);
        self.ctx.assertions = original_assertions;
        self.incr_theory_state = saved_theory_state;
        self.incr_bv_state = saved_bv_state;

        match refinement_result {
            Some(Ok(SolveResult::Unsat(_))) => Some(Ok(SolveResult::unsat())),
            Some(Err(err)) => Some(Err(err)),
            _ => {
                self.last_model = saved_model;
                self.last_model_validated = saved_model_validated;
                self.last_validation_stats = saved_validation_stats;
                self.last_unknown_reason = saved_unknown_reason;
                None
            }
        }
    }

    /// SOUND MBQI SAT certification for EPR / finite-uninterpreted-domain
    /// problems (#mbqi-completeness Q2).
    ///
    /// `restore_assertions` fails closed to `Unknown` when a skipped `forall`
    /// could not be re-validated, even though the MBQI refinement found NO
    /// counterexample (the model satisfies every instance). For the EPR /
    /// finite-model-finding fragment - every binder over an uninterpreted sort
    /// whose universe is generated only by ground constants - that fixpoint model
    /// is a COMPLETE, sound witness: there are finitely many domain elements and
    /// every cross-product instance evaluates true. This certifies SAT.
    ///
    /// Drives the MBQI refinement over `pre_restore_assertions` to a fixpoint
    /// (forcing model-dependent facts like the symmetric pair (r b a) implied by
    /// a (r a b) => (r b a) instance), then runs the exact finite-domain
    /// validator on the resulting model. Returns `Some(())` only on a complete,
    /// definite-Bool certification; everything else restores state and returns
    /// `None` (caller keeps its fail-closed `Unknown`). NEVER returns a wrong SAT.
    fn try_mbqi_sat_certification(
        &mut self,
        pre_restore_assertions: &[TermId],
        category: LogicCategory,
        has_uninstantiated_quantifiers: bool,
        full_ematching_coverage: bool,
    ) -> Option<()> {
        let original_assertions = self.ctx.assertions.clone();
        let saved_model = self.last_model.clone();
        let saved_model_validated = self.last_model_validated;
        let saved_validation_stats = self.last_validation_stats.clone();
        let saved_unknown_reason = self.last_unknown_reason;

        let forall_quants: Vec<TermId> = original_assertions
            .iter()
            .copied()
            .filter(|&a| matches!(self.ctx.terms.get(a), TermData::Forall(..)))
            .collect();
        if forall_quants.is_empty() {
            return None;
        }

        let saved_theory_state = self.incr_theory_state.take();
        let saved_bv_state = self.incr_bv_state.take();
        self.ctx.assertions = pre_restore_assertions.to_vec();
        let refinement_result = self.try_mbqi_refinement(&forall_quants, category);

        // Only proceed to certification when refinement did NOT refute
        // (None => SAT fixpoint, or Sat).
        let proceed = !matches!(
            refinement_result,
            Some(Ok(SolveResult::Unsat(_))) | Some(Err(_))
        );

        let certified = if proceed {
            self.mbqi_sat_validated_finite_uninterpreted_domain(&forall_quants)
                .is_some()
                // A MIX of pointwise-materializable UF definitions and guarded
                // foralls `forall x. (or … G …)` whose ground consequent `G` is
                // TRUE in the returned model, over a fully-evaluable (linear-Int /
                // Bool / BV / EUF) ground core: the model then genuinely satisfies
                // every skipped quantifier, so this `Sat` is a real Verus
                // counterexample. Covers the transparent-spec-fn choose fail case
                // (f-definition + guarded choose axiom with a witness-forced
                // consequent) that the finite-domain leg cannot (its Int binder).
                //
                // SOUNDNESS GATE `!has_uninstantiated_quantifiers`: the
                // materialization is only sound when the ground model already
                // agrees with each definition at EVERY ground application (the
                // given_sat leg's "full e-matching instantiation coverage"
                // precondition). Without it, two CONFLICTING definitions of the
                // same symbol with no ground terms (`forall i.f(i)=i` ∧
                // `forall i.f(i)=i+1`) are each pointwise-materializable over an
                // empty (vacuously-evaluable) ground core and would be certified
                // SAT though jointly UNSAT — a wrong-SAT / false counterexample.
                // Leftover uninstantiated quantifiers mean coverage is incomplete,
                // so fail closed.
                || (!has_uninstantiated_quantifiers
                    && saved_model.as_ref().is_some_and(|m| {
                        self.mbqi_sat_validated_definitions_plus_model_true_guards(
                            &forall_quants,
                            m,
                        )
                    }))
                // LEFT-INVERSE (boxing) axioms `forall x. Unbox(Box x) = x`
                // (deductive-checks polymorphism, #2774), mixed only with
                // universe-independent shapes (unary identity definitions,
                // guarded foralls with a materialized-true closed disjunct).
                // The certificate EXHIBITS a total model by functionalized
                // re-evaluation — Box := injective embedding, Unbox :=
                // table-inverse + fallback, identity heads := id — and
                // re-verifies EVERY original assertion under it, trusting
                // neither the prior validation nor the (lossy) extracted
                // function tables; see
                // `mbqi_sat_validated_left_inverse_axioms`. COVERAGE GATE:
                // same premise family as the definitions leg above, widened
                // to the full `full_ematching_coverage` conjunction (no
                // uninstantiated quantifier pre- or post-interleaving, no
                // instantiation-limit hit, no deferred instantiation, no
                // existential) — #8969 defense-in-depth on top of the
                // certificate's own construction argument.
                || (!has_uninstantiated_quantifiers
                    && full_ematching_coverage
                    && match saved_model.as_ref() {
                        Some(m) => self.mbqi_sat_validated_left_inverse_axioms(
                            &original_assertions,
                            &forall_quants,
                            m,
                        ),
                        None => false,
                    })
                // (#p2-mbqi-empty-universe) EPR foralls over an EMPTY
                // universe: the singleton-witness decide (guarded, fail-
                // closed; see mbqi.rs). Only its SAT verdict certifies here —
                // an UNSAT outcome restores state and simply does not certify
                // (this path can only keep/deny a Sat, never emit Unsat).
                || {
                    let snapshot = original_assertions.clone();
                    matches!(
                        self.mbqi_empty_universe_singleton_decide(
                            &snapshot,
                            &forall_quants,
                            category,
                        ),
                        Some(SolveResult::Sat)
                    )
                }
        } else {
            false
        };

        self.ctx.assertions = original_assertions;
        self.incr_theory_state = saved_theory_state;
        self.incr_bv_state = saved_bv_state;

        if certified {
            self.last_model_validated = true;
            self.last_unknown_reason = None;
            Some(())
        } else {
            self.last_model = saved_model;
            self.last_model_validated = saved_model_validated;
            self.last_validation_stats = saved_validation_stats;
            self.last_unknown_reason = saved_unknown_reason;
            None
        }
    }

    /// True iff `root` mentions any CE variable in `ce_vars` (#cegqi-ce-strip,
    /// 2026-07-18).
    ///
    /// CE variables are `Var` leaves, so hash-consing keeps their `TermId`
    /// stable across every in-place rewrite — membership by id on the leaf is
    /// exact even after a parent conjunct has been re-minted under a fresh id
    /// (the failure mode of the identity-only CE-lemma strip: solve_array_euf's
    /// multi-pass rewrite — ite-lift, FlattenAnd, store-flat inlining — re-mints
    /// the CE conjunct and appends ROW clauses folded under CE units, all of
    /// which escape `!ce_lemma_ids.contains(a)`). Walks the full term DAG;
    /// unknown future variants conservatively count as a mention (the caller
    /// strips more, which only weakens the probe — sound).
    fn mentions_any_ce_var(
        terms: &ay_core::TermStore,
        root: TermId,
        ce_vars: &ay_core::kani_compat::DetHashSet<TermId>,
    ) -> bool {
        use ay_core::kani_compat::DetHashSet;
        if ce_vars.is_empty() {
            return false;
        }
        let mut visited: DetHashSet<TermId> = DetHashSet::default();
        let mut stack = vec![root];
        while let Some(t) = stack.pop() {
            if !visited.insert(t) {
                continue;
            }
            if ce_vars.contains(&t) {
                return true;
            }
            match terms.get(t) {
                TermData::Const(_) | TermData::Var(_, _) => {}
                TermData::App(_, args) => stack.extend(args.iter().copied()),
                TermData::Not(inner) => stack.push(*inner),
                TermData::Ite(c, a, b) => {
                    stack.push(*c);
                    stack.push(*a);
                    stack.push(*b);
                }
                TermData::Let(bindings, body) => {
                    stack.extend(bindings.iter().map(|(_, v)| *v));
                    stack.push(*body);
                }
                TermData::Forall(_, body, triggers) | TermData::Exists(_, body, triggers) => {
                    stack.push(*body);
                    stack.extend(triggers.iter().flatten().copied());
                }
                // Future TermData variants: fail closed — treat as a mention
                // so the caller strips the assertion (weakens the probe only).
                _ => return true,
            }
        }
        false
    }

    /// Disambiguate UNSAT from CEGQI refinement (#5975).
    ///
    /// Re-solves without CE lemmas to determine if UNSAT is genuine
    /// (from ground assertions alone) or CE-induced (forall is valid → SAT).
    ///
    /// `cegqi_state` carries the (quantifier, instantiator) pairs so the
    /// quantified-CE-lemma decider legs can rebuild per-universal obligations;
    /// `snapshot` is the pre-instantiation assertion snapshot
    /// (`refinement_assertions`), threaded through every caller (including the
    /// CEGQI refinement loop). A `None` snapshot DISABLES both decider legs
    /// (they need the snapshot for the quantifier-coverage / conjunctive-
    /// position gates) — fail-soft to the pre-existing behavior.
    pub(super) fn disambiguate_cegqi_unsat(
        &mut self,
        category: LogicCategory,
        ce_lemma_ids: &[TermId],
        ce_lemma_groups: &[(TermId, Vec<TermId>)],
        is_mixed: bool,
        cegqi_state: &[(TermId, CegqiInstantiator)],
        snapshot: Option<&[TermId]>,
    ) -> Result<SolveResult> {
        self.disambiguate_cegqi_unsat_ext(
            category,
            ce_lemma_ids,
            ce_lemma_groups,
            is_mixed,
            false,
            false,
            cegqi_state,
            snapshot,
        )
    }

    /// [`Self::disambiguate_cegqi_unsat`] with the MODEL-BACKED UF-definition
    /// certificate threaded through (rank-9 step 3).
    ///
    /// `uf_definitions_given_sat_certificate` is
    /// `quantifiers_supported_by_uf_completion_given_sat` from the quantifier
    /// pass: every snapshot `forall` is a distinct-head pointwise-
    /// materializable UF definition over the evaluable linear fragment, the
    /// ground core is fragment-evaluable/consistent, E-matching coverage is
    /// COMPLETE (no uninstantiated quantifier, no round/instance limit, no
    /// deferred instance) and no existential survives. Under that flag a
    /// ground-minus-CE-lemma `Sat` is decided `Sat` WITHOUT requiring the CE
    /// lemma itself to be refuted: the certificate's materialization argument
    /// (`f := λv⃗. eval(rhs)` guarded pointwise extension, see
    /// `pointwise_materializable_uf_definition_head`) establishes the
    /// universals directly from the ground model, independent of any CEGQI
    /// premise — the S3 concern (a satisfiable CE lemma hiding a genuine
    /// counterexample, e.g. the ∀∃ perfect-square alternation) cannot arise
    /// because a skolemized alternation body applies a Skolem function to the
    /// binder and is therefore NOT a pointwise UF definition (its head is not
    /// a completable UF over exactly the binders), so the flag is false there.
    /// The caller's `Ok(Sat)` arm still runs the MBQI cross-validation /
    /// skolem-alternation safety nets on this verdict before finalizing.
    /// Callers that cannot establish the premise pass `false` and keep the
    /// fail-closed behavior byte-identically.
    ///
    /// `uf_completion_strict_certificate` is the STRICT completion
    /// certificate (`quantifiers_supported_by_uf_completion` from the
    /// quantifier pass): every snapshot `forall` is completion-safe
    /// (`quantifier_supported_by_uf_completion`) and every ground assertion
    /// passes the completion-freedom + consistency gates. `classify_
    /// quantifier_result` already trusts EXACTLY this certificate to decide
    /// `Sat` from a lower `Unknown` — with no confirmed ground model at all
    /// (the verification-consumer Seq library-axiom families, #7956). Consulting it here
    /// is the SAME decision under a strictly STRONGER premise: the lower
    /// UNSAT is CE-lemma-driven (the lemma is CEGQI's counterexample-search
    /// assertion, not part of the problem), and the ground-minus-CE-lemma
    /// re-solve just CONFIRMED the live ground set (originals + all sound
    /// instantiation consequences) satisfiable, which subsumes the weak
    /// `ground_assertions_consistent` probes the Unknown-flip settles for.
    /// The `!is_mixed` gate below implies no CEGQI existential (this arm is
    /// only reached with `cegqi_has_forall`), mirroring the primary leg's
    /// `!cegqi_has_exists` gate — completion supplies no witnesses. The
    /// caller's `Ok(Sat)` arm still runs the MBQI cross-validation and
    /// skolem-alternation safety nets before finalizing, exactly as for the
    /// model-backed certificate.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn disambiguate_cegqi_unsat_ext(
        &mut self,
        category: LogicCategory,
        ce_lemma_ids: &[TermId],
        ce_lemma_groups: &[(TermId, Vec<TermId>)],
        is_mixed: bool,
        uf_definitions_given_sat_certificate: bool,
        uf_completion_strict_certificate: bool,
        cegqi_state: &[(TermId, CegqiInstantiator)],
        snapshot: Option<&[TermId]>,
    ) -> Result<SolveResult> {
        if ce_lemma_ids.is_empty() {
            return Ok(SolveResult::unsat());
        }

        // #cegqi-ce-strip (2026-07-18): strip CE lemmas by IDENTITY *and* by
        // CE-VARIABLE MENTION. The id filter alone is broken by any solver leg
        // that rewrites `ctx.assertions` in place (solve_array_euf: ite-lift,
        // FlattenAnd, store-flat inlining re-mint the CE conjunct under a
        // fresh hash-consed id, and the array-axiom fixpoint appends ROW
        // clauses simplified UNDER the CE units — e.g. a read-over-write
        // instance valid only given the CE hypothesis `e != 3`). The surviving
        // CE-derived residue then re-derives the same CE-driven contradiction
        // in the "ground-minus-CE" probe and the `Ok(Unsat)` arm below minted
        // a WRONG UNSAT for entailed foralls (`b = store a 3 9` plus
        // `forall i. i!=3 => b[i]=a[i]`, z3: sat). SOUNDNESS: the mention
        // strip only WEAKENS the probe set, and every survivor is
        // CE-variable-free — original assertions (equisatisfiably rewritten),
        // ground instances of asserted foralls, and valid theory axioms — so
        // "probe still unsat => trust unsat" stays sound; the Sat arm mints no
        // new authority (the flip to SAT is still decided solely by the
        // per-lemma refutation certificates against the pre-instantiation
        // snapshot ground core, whose fresh-constant argument is independent
        // of this strip).
        let ce_vars: ay_core::kani_compat::DetHashSet<TermId> = cegqi_state
            .iter()
            .flat_map(|(_, inst)| inst.ce_variables().values().copied())
            .collect();
        let ground_only: Vec<TermId> = self
            .ctx
            .assertions
            .iter()
            .copied()
            .filter(|a| {
                !ce_lemma_ids.contains(a)
                    && !Self::mentions_any_ce_var(&self.ctx.terms, *a, &ce_vars)
            })
            .collect();

        let saved = std::mem::replace(&mut self.ctx.assertions, ground_only);

        let saved_theory_state = self.incr_theory_state.take();
        let saved_bv_state = self.incr_bv_state.take();
        let ground_result = self.solve_for_category(category);
        self.ctx.assertions = saved;
        self.incr_theory_state = saved_theory_state;
        self.incr_bv_state = saved_bv_state;

        match ground_result {
            Ok(SolveResult::Unsat(_)) => Ok(SolveResult::unsat()),
            Ok(SolveResult::Sat)
                if !is_mixed
                    && (uf_definitions_given_sat_certificate
                        || uf_completion_strict_certificate) =>
            {
                // Rank-9 step 3: the ground-minus-CE-lemma solve just produced
                // a genuine ground model, and the certificate premise (see the
                // `_ext` doc above) extends it pointwise over every remaining
                // `forall` (all of them distinct-head UF definitions with full
                // E-matching coverage). This SAT does not rest on any CEGQI
                // premise, so the CE-lemma refutation below is not required.
                // The caller still MBQI-cross-validates the Sat.
                //
                // #7956 regression 2 (STRICT leg): the strict completion
                // certificate decides the same way — see the `_ext` doc.
                // Before d21172e1's model-value-consistency fix this family
                // reached the classify UF-completion flip through a lower
                // `Unknown`; the changed model/instantiation interplay now
                // routes it here through a CE-lemma-driven UNSAT, where the
                // certificate was never consulted and the (structurally
                // impossible for Seq-sorted problems) per-universal
                // refutation certificates failed closed to Unknown.
                Ok(SolveResult::Sat)
            }
            Ok(SolveResult::Sat) if !is_mixed => {
                // SOUNDNESS (RED S3, 2026-07-08): "ground-minus-CE-lemma is Sat"
                // does NOT establish the universal's validity — the CEGQI-sound
                // premise for the valid→SAT flip is "the CE lemma (the
                // counterexample search space) is UNSAT". The old unconditional
                // flip minted a wrong SAT for the ∀∃ alternation
                // `(forall x (exists y (= (* y y) x)))` (FALSE at x = 2): its CE
                // lemma `¬∃y. y² = sk` is SATISFIABLE (sk := 2), yet the empty
                // ground remainder answered Sat and the flip shipped it. Verify
                // the premise independently on the CE lemmas ALONE; anything
                // short of a definitive UNSAT fails closed to Unknown (exactly
                // the honest verdict the RED fixture prescribes). Legitimate
                // recoveries (QF_AX extensionality) carry a provably-UNSAT CE
                // lemma and keep their SAT.
                // SOUNDNESS (multi-lemma disjunction hole, 2026-07-10): the
                // refutation must be PER LEMMA, not joint. A joint UNSAT of
                // `¬B1(sk1) ∧ ¬B2(sk2)` only proves the DISJUNCTION
                // `(∀x.B1) ∨ (∀y.B2)` — not that both universals are valid.
                // With two universals coupled through a shared free symbol
                // (`∀x. x≥0 ∨ q` and `∀y. y<0 ∨ ¬q`, jointly ≡ q ∧ ¬q, UNSAT)
                // the joint CE conjunction contains `¬q ∧ q` and is trivially
                // UNSAT, and the joint flip minted a wrong SAT. Per-lemma
                // isolated UNSAT (`¬Bi(ski)` unsatisfiable on its own) proves
                // EVERY universal valid — the sound premise. Strictly stronger
                // than the joint solve, so no wrong verdict the joint check
                // rejected can pass here.
                // Full nested-solve state discipline (mirrors
                // `closed_universal_validity_precheck_inner`): save and restore
                // every piece of solver state the ground solves perturb, so the
                // verification cannot leak into (or trip the postconditions of)
                // the enclosing solve.
                // CONTEXT (#cegqi-ground-core, 2026-07-10): refute each lemma
                // against the quantifier-free ground core G0 of the
                // PRE-INSTANTIATION snapshot, not in an empty context. Sound
                // by the fresh-constant rule: the CE constants c⃗ were minted
                // AFTER the snapshot, so no G0 conjunct mentions them, and
                // UNSAT of `G0 ∧ ¬B(c⃗)` proves `G0 ⊨ ∀x⃗.B`; entailment is
                // monotone in premises, so the full ground set (just proved
                // Sat above) also entails the universal — the flip is a real
                // SAT. The snapshot (NOT the live assertion set) is essential:
                // live CEGQI instantiation lemmas can mention c⃗ (the round
                // instantiates at the CE witness), which would break freshness
                // and make the "refutation" vacuous. Empty-context isolation
                // (1ccc600d) demanded each universal be VALID outright and
                // degraded every relative-to-ground universal — asserted-Bool,
                // ground-UF, bound-coupled-free-var shapes — to Unknown (10
                // regressed group_quantifiers tests, 2026-07-10 bisect).
                let mut ground_core: Vec<TermId> = Vec::new();
                if let Some(snap) = snapshot {
                    for &assertion in snap {
                        if contains_quantifier(&self.ctx.terms, assertion) {
                            let mut conjuncts = Vec::new();
                            collect_and_conjuncts(&self.ctx.terms, assertion, &mut conjuncts);
                            for conjunct in conjuncts {
                                if !contains_quantifier(&self.ctx.terms, conjunct)
                                    && !ground_core.contains(&conjunct)
                                {
                                    ground_core.push(conjunct);
                                }
                            }
                        } else if !ground_core.contains(&assertion) {
                            ground_core.push(assertion);
                        }
                    }
                }
                let saved = std::mem::take(&mut self.ctx.assertions);
                let saved_theory_state = self.incr_theory_state.take();
                let saved_bv_state = self.incr_bv_state.take();
                let saved_model = self.last_model.take();
                let saved_model_validated = self.last_model_validated;
                let saved_validation_stats = self.last_validation_stats.take();
                let saved_unknown_reason = self.last_unknown_reason;
                let saved_defer = self.defer_model_validation;
                self.defer_model_validation = false;
                // Model-relative pins (#cegqi-mdef, 2026-07-11): the
                // fresh-constant certificate below (G0 ⊨ ∀x⃗.B) cannot
                // certify a universal that is merely SATISFIED BY THE
                // CANDIDATE MODEL rather than entailed by ground facts
                // (`forall x. x>4 ∨ p` with nothing asserted: p:=true is
                // forced by no ground fact). Pin the ground-only candidate
                // model's values for the free NON-CE constants occurring in
                // the CE conjuncts: UNSAT of `M_def ∧ G0 ∧ ¬B(c⃗)` with c⃗
                // fresh w.r.t. M_def ∧ G0 proves the pinned model satisfies
                // ∀x⃗.B — an MBQI-style certificate for the model the solve
                // above just produced. Skolem-minted constants are never
                // pinned (an alternation's witness stays free, so its lemma
                // stays unrefutable on this leg — RED S3 keeps its UNSAT
                // route), and the VACUITY GUARD below requires M_def ∧ G0 to
                // be satisfiable before any refutation may use the pins, so
                // an inconsistent pin set can never mint a flip.
                let mut m_def: Vec<TermId> = Vec::new();
                let mut uf_pins: Vec<TermId> = Vec::new();
                if let Some(model) = saved_model.as_ref() {
                    use ay_core::kani_compat::DetHashSet;
                    let mut pin_vars: Vec<TermId> = Vec::new();
                    let mut uf_app_candidates: Vec<TermId> = Vec::new();
                    let mut seen: DetHashSet<TermId> = DetHashSet::default();
                    for (_, group) in ce_lemma_groups {
                        for &conjunct in group {
                            let mut stack = vec![conjunct];
                            while let Some(t) = stack.pop() {
                                if !seen.insert(t) {
                                    continue;
                                }
                                match self.ctx.terms.get(t) {
                                    TermData::Var(name, _) => {
                                        if !ce_vars.contains(&t)
                                            && !self.ctx.terms.is_skolem_symbol(name)
                                        {
                                            pin_vars.push(t);
                                        }
                                    }
                                    TermData::App(_, args) => {
                                        // UF-graph pin candidates (#cegqi-mdef
                                        // v2): every application in a CE
                                        // conjunct; head filtering below.
                                        if !args.is_empty() {
                                            uf_app_candidates.push(t);
                                        }
                                        stack.extend(args.iter().copied());
                                    }
                                    TermData::Not(inner) => stack.push(*inner),
                                    TermData::Ite(c, a, b) => {
                                        stack.push(*c);
                                        stack.push(*a);
                                        stack.push(*b);
                                    }
                                    _ => {}
                                }
                            }
                        }
                    }
                    for v in pin_vars {
                        match self.evaluate_term(model, v) {
                            EvalValue::Bool(true) => m_def.push(v),
                            EvalValue::Bool(false) => {
                                let nv = self.ctx.terms.mk_not(v);
                                m_def.push(nv);
                            }
                            EvalValue::Rational(r)
                                if r.is_integer()
                                    && matches!(self.ctx.terms.sort(v), ay_core::Sort::Int) =>
                            {
                                let c = self.ctx.terms.mk_int(r.numer().clone());
                                let eq = self.ctx.terms.mk_eq(v, c);
                                m_def.push(eq);
                            }
                            EvalValue::BitVec { value, width } => {
                                let c = self.ctx.terms.mk_bitvec(value, width);
                                let eq = self.ctx.terms.mk_eq(v, c);
                                m_def.push(eq);
                            }
                            // Unpinnable value (FP/uninterpreted/...): leave
                            // the constant free — a group needing it stays
                            // unrefuted, which fails closed.
                            _ => {}
                        }
                    }
                    // UF-GRAPH pins (#cegqi-mdef v2, 2026-07-11): constant
                    // pins cannot constrain a UF application `f(t⃗)` in a CE
                    // conjunct, so universals whose validity rests on the
                    // model's INTERPRETATION of f stayed Unknown. Pin each
                    // such head to a re-completion M′ of the candidate model:
                    // collect the concrete graph {a⃗ᵢ ↦ bᵢ} of ALL f
                    // occurrences across (live ground-only set ∪ ground
                    // core), evaluated under M, and emit per CE application
                    //   ⋁ᵢ (t⃗ = a⃗ᵢ ∧ f(t⃗) = bᵢ) ∨ f(t⃗) = d_f
                    // with d_f the sort completion default. SOUNDNESS: M′ :=
                    // M with pinned heads re-completed to "graph else d_f"
                    // satisfies (1) every ground premise — every ground f
                    // occurrence IS a collected point carrying M's own value,
                    // enforced FAIL-CLOSED: an unevaluable / conflicting /
                    // overflowing occurrence, a >point-cap graph, an
                    // over-budget walk, or a quantified root drops the WHOLE
                    // head (never a single point — dropping a point would let
                    // M′ disagree with a ground premise); (2) the constant
                    // pins (untouched); (3) every pin under EVERY CE-variable
                    // assignment (the disjuncts mirror the two completion
                    // cases exactly — the pin is weaker than the completion,
                    // which only makes refutation harder, never unsound). So
                    // per-group UNSAT of G0 ∧ M_def ∧ pins ∧ ¬B(c⃗) proves
                    // M′ ⊨ ∀x⃗.B — the flip's SAT is witnessed by M′. Skolem
                    // heads are NEVER pinned, so an alternation lemma
                    // ¬psi0(sk(c),c) stays unrefutable here and RED S3 keeps
                    // its UNSAT route.
                    const MAX_UF_GRAPH_HEADS: usize = 4;
                    const MAX_UF_GRAPH_POINTS: usize = 8;
                    const UF_GRAPH_WALK_BUDGET: usize = 20_000;
                    let mut heads: Vec<String> = Vec::new();
                    for &app in &uf_app_candidates {
                        if let TermData::App(sym, _) = self.ctx.terms.get(app) {
                            let n = sym.name();
                            if !Self::is_known_theory_symbol(n)
                                && self.ctx.is_constructor(n).is_none()
                                && !self.is_dt_internal_symbol(n)
                                && !self.ctx.terms.is_skolem_symbol(n)
                                && !heads.iter().any(|h| h == n)
                            {
                                if heads.len() >= MAX_UF_GRAPH_HEADS {
                                    heads.clear(); // over cap: drop ALL (fail closed)
                                    break;
                                }
                                heads.push(n.to_string());
                            }
                        }
                    }
                    if !heads.is_empty() {
                        // The set M′ must keep satisfying: live ground-only
                        // assertions (instantiation lemmas included — they
                        // are consequences the model already satisfies) plus
                        // the snapshot ground core.
                        // #cegqi-ce-strip: same identity-independent filter as
                        // the ground_only probe above — a re-minted CE conjunct
                        // or CE-tainted ROW clause must not seed the UF-graph
                        // pins either.
                        let mut roots: Vec<TermId> = saved
                            .iter()
                            .copied()
                            .filter(|a| {
                                !ce_lemma_ids.contains(a)
                                    && !Self::mentions_any_ce_var(&self.ctx.terms, *a, &ce_vars)
                            })
                            .collect();
                        for &g in &ground_core {
                            if !roots.contains(&g) {
                                roots.push(g);
                            }
                        }
                        type Graph = Vec<(Vec<EvalValue>, EvalValue)>;
                        let mut head_points: Vec<(String, Option<Graph>)> = heads
                            .iter()
                            .map(|h| (h.clone(), Some(Vec::new())))
                            .collect();
                        // A value is pinnable iff we can rebuild it as a term
                        // (mirrors the constant-pin acceptance above).
                        let pinnable = |this: &Self, term: TermId, v: &EvalValue| -> bool {
                            match (this.ctx.terms.sort(term), v) {
                                (ay_core::Sort::Bool, EvalValue::Bool(_)) => true,
                                (ay_core::Sort::Int, EvalValue::Rational(r)) => r.is_integer(),
                                (ay_core::Sort::Real, EvalValue::Rational(_)) => true,
                                (ay_core::Sort::BitVec(sort), EvalValue::BitVec { width, .. }) => {
                                    sort.width == *width
                                }
                                _ => false,
                            }
                        };
                        let mut walk_seen: DetHashSet<TermId> = DetHashSet::default();
                        let mut stack = roots;
                        let mut budget = UF_GRAPH_WALK_BUDGET;
                        while let Some(t) = stack.pop() {
                            if !walk_seen.insert(t) {
                                continue;
                            }
                            if budget == 0 {
                                for hp in &mut head_points {
                                    hp.1 = None;
                                }
                                break;
                            }
                            budget -= 1;
                            match self.ctx.terms.get(t).clone() {
                                TermData::App(sym, args) => {
                                    if let Some(hp) =
                                        head_points.iter_mut().find(|(h, _)| h == sym.name())
                                    {
                                        if let Some(points) = hp.1.as_mut() {
                                            let mut avals: Vec<EvalValue> =
                                                Vec::with_capacity(args.len());
                                            let mut ok = true;
                                            for &a in &args {
                                                let av = self.evaluate_term(model, a);
                                                if !pinnable(self, a, &av) {
                                                    ok = false;
                                                    break;
                                                }
                                                avals.push(av);
                                            }
                                            let rv = self.evaluate_term(model, t);
                                            if !ok || !pinnable(self, t, &rv) {
                                                hp.1 = None;
                                            } else if let Some((_, prev)) =
                                                points.iter().find(|(pa, _)| *pa == avals)
                                            {
                                                if *prev != rv {
                                                    // Same point, two values:
                                                    // extraction inconsistency —
                                                    // drop the head.
                                                    hp.1 = None;
                                                }
                                            } else if points.len() >= MAX_UF_GRAPH_POINTS {
                                                hp.1 = None;
                                            } else {
                                                points.push((avals, rv));
                                            }
                                        }
                                    }
                                    stack.extend(args.iter().copied());
                                }
                                TermData::Not(i) => stack.push(i),
                                TermData::Ite(c, a, b) => {
                                    stack.push(c);
                                    stack.push(a);
                                    stack.push(b);
                                }
                                TermData::Let(binds, body) => {
                                    for (_, v) in binds {
                                        stack.push(v);
                                    }
                                    stack.push(body);
                                }
                                // A quantified root hides f occurrences M′
                                // must honor but we cannot enumerate: drop
                                // every head.
                                TermData::Forall(..) | TermData::Exists(..) => {
                                    for hp in &mut head_points {
                                        hp.1 = None;
                                    }
                                    break;
                                }
                                _ => {}
                            }
                        }
                        for &app in &uf_app_candidates {
                            let TermData::App(sym, args) = self.ctx.terms.get(app).clone() else {
                                continue;
                            };
                            let Some((_, Some(points))) =
                                head_points.iter().find(|(h, _)| h == sym.name())
                            else {
                                continue;
                            };
                            let points = points.clone();
                            let app_sort = self.ctx.terms.sort(app).clone();
                            let Some(dflt) = self.unconstrained_default_value(&app_sort) else {
                                continue;
                            };
                            let Some(d_term) =
                                pin_eval_const_for_sort(&mut self.ctx.terms, &app_sort, &dflt)
                            else {
                                continue;
                            };
                            let mut disjuncts: Vec<TermId> = Vec::new();
                            let mut ok = true;
                            for (avals, rv) in &points {
                                let mut conj: Vec<TermId> = Vec::new();
                                for (&arg, av) in args.iter().zip(avals) {
                                    let arg_sort = self.ctx.terms.sort(arg).clone();
                                    let Some(a_term) =
                                        pin_eval_const_for_sort(&mut self.ctx.terms, &arg_sort, av)
                                    else {
                                        ok = false;
                                        break;
                                    };
                                    let eq = self.ctx.terms.mk_eq(arg, a_term);
                                    conj.push(eq);
                                }
                                if !ok {
                                    break;
                                }
                                let Some(r_term) =
                                    pin_eval_const_for_sort(&mut self.ctx.terms, &app_sort, rv)
                                else {
                                    ok = false;
                                    break;
                                };
                                let eq = self.ctx.terms.mk_eq(app, r_term);
                                conj.push(eq);
                                disjuncts.push(self.ctx.terms.mk_and(conj));
                            }
                            if !ok {
                                // Never emit a pin missing a graph disjunct —
                                // the premise could be false in M′.
                                continue;
                            }
                            let d_eq = self.ctx.terms.mk_eq(app, d_term);
                            disjuncts.push(d_eq);
                            uf_pins.push(self.ctx.terms.mk_or(disjuncts));
                        }
                    }
                }
                // Shared tight deadline (same discipline as
                // `refuted_all_quantified_ce_lemmas`): the refutations are a
                // pure certificate — running out of budget leaves lemmas
                // unrefuted and falls through to the recovery legs / honest
                // Unknown, never a wrong verdict.
                let saved_deadline = self.solve_deadline.get();
                let tight = ay_core::time::Instant::now() + std::time::Duration::from_millis(300);
                self.set_deadline(match saved_deadline {
                    Some(d) if d < tight => Some(d),
                    _ => Some(tight),
                });
                // Refute PER UNIVERSAL (#cegqi-per-universal, 2026-07-11):
                // `ce_lemma_ids` holds the AND-FLATTENED conjuncts of every
                // CE lemma (see `flatten_and_strip_quantifiers`), so solving
                // them one-by-one demanded each CONJUNCT be unsatisfiable —
                // `¬(c>4)` from `¬((c>4) ∨ p)` never is, and the flip died on
                // shapes whose refutation lives in the OTHER conjunct(s)
                // (assert-p family). The sound unit is each universal's WHOLE
                // conjunction `¬B_q(c⃗)`: UNSAT of `G0 ∧ ¬B_q(c⃗)` with c⃗
                // fresh w.r.t. G0 proves `G0 ⊨ ∀x⃗.B_q` (fresh-constant
                // rule), and every group is solved SEPARATELY, so conjuncts
                // of two coupled universals can never refute each other (the
                // multi-lemma disjunction hole stays closed). A group that
                // lost all its conjuncts to the CE-exclusive filter has its
                // constraints in the ground core already — nothing left to
                // refute, no certificate. Fail closed when the groups are
                // missing entirely.
                // STAGED vacuity guard for the pins: usable only when
                // consistent with the ground core (all are true of the
                // candidate model, so a genuine model always passes). If the
                // joint set fails, retry WITHOUT the UF-graph pins so a flaky
                // graph can never disable the already-validated constant
                // pins; with uf_pins empty the path is identical to v1.
                let mut pins_usable = !m_def.is_empty();
                let mut uf_pins_usable = !uf_pins.is_empty();
                if pins_usable || uf_pins_usable {
                    let mut ctx0 = ground_core.clone();
                    ctx0.extend(m_def.iter().copied());
                    ctx0.extend(uf_pins.iter().copied());
                    self.ctx.assertions = ctx0;
                    self.incr_theory_state = None;
                    self.incr_bv_state = None;
                    let joint_ok =
                        matches!(self.solve_for_category(category), Ok(SolveResult::Sat));
                    if !joint_ok {
                        uf_pins_usable = false;
                        if pins_usable {
                            let mut ctx0 = ground_core.clone();
                            ctx0.extend(m_def.iter().copied());
                            self.ctx.assertions = ctx0;
                            self.incr_theory_state = None;
                            self.incr_bv_state = None;
                            pins_usable =
                                matches!(self.solve_for_category(category), Ok(SolveResult::Sat));
                        }
                    }
                }
                let mut all_ce_lemmas_refuted = !ce_lemma_groups.is_empty();
                for (quant, group) in ce_lemma_groups {
                    if !matches!(self.ctx.terms.get(*quant), TermData::Forall(..)) {
                        // Defensive: an exists group cannot be certified by
                        // refutation — no flip.
                        all_ce_lemmas_refuted = false;
                        break;
                    }
                    if group.is_empty() || ay_core::time::Instant::now() >= tight {
                        all_ce_lemmas_refuted = false;
                        break;
                    }
                    let mut lemma_ctx = ground_core.clone();
                    if pins_usable {
                        lemma_ctx.extend(m_def.iter().copied());
                    }
                    if uf_pins_usable {
                        lemma_ctx.extend(uf_pins.iter().copied());
                    }
                    lemma_ctx.extend(group.iter().copied());
                    self.ctx.assertions = lemma_ctx;
                    self.incr_theory_state = None;
                    self.incr_bv_state = None;
                    let ce_result = self.solve_for_category(category);
                    if !matches!(ce_result, Ok(SolveResult::Unsat(_))) {
                        all_ce_lemmas_refuted = false;
                        break;
                    }
                }
                self.set_deadline(saved_deadline);
                self.ctx.assertions = saved;
                self.incr_theory_state = saved_theory_state;
                self.incr_bv_state = saved_bv_state;
                self.last_model = saved_model;
                self.last_model_validated = saved_model_validated;
                self.last_validation_stats = saved_validation_stats;
                self.last_unknown_reason = saved_unknown_reason;
                self.defer_model_validation = saved_defer;
                if all_ce_lemmas_refuted {
                    Ok(SolveResult::Sat)
                } else {
                    // The joint ground CE solve could not refute — for a
                    // SKOLEMIZED alternation it never can (the stored lemma
                    // `¬psi0(sk(e), e)` keeps the Skolem application free and is
                    // always satisfiable). Run the quantified-CE-lemma decider
                    // legs, both gated on the pre-instantiation snapshot being
                    // available (fail-soft None ⟹ keep the honest Unknown).
                    if let Some(snapshot) = snapshot {
                        // SAT leg: rebuild each universal's DE-SKOLEMIZED
                        // counterexample obligation `L_q = ∀ys.¬psi0(ys, e)` and
                        // refute it with bounded isolated instantiations. Every
                        // L_q refuted ⟹ every universal VALID; the ground
                        // remainder was just proved Sat by the solve above, so
                        // the problem is SAT. The certificate is strictly
                        // stronger than the legacy joint-conjunction refutation
                        // (per-lemma), and the caller-side MBQI cross-validation
                        // / witness-independent-skolem-alternation nets at the
                        // `Ok(Sat)` consumer still apply to this verdict.
                        if self.refuted_all_quantified_ce_lemmas(cegqi_state, snapshot, category) {
                            return Ok(SolveResult::Sat);
                        }
                        // UNSAT leg: a conjunctive-position universal that is
                        // FALSE at a concrete ground witness refutes the whole
                        // problem regardless of the CE lemma (universal
                        // instantiation + standalone-UNSAT instance; see
                        // `universal_false_at_ground_witness`).
                        let cegqi_foralls: Vec<TermId> = cegqi_state
                            .iter()
                            .filter(|(_, inst)| inst.is_forall())
                            .map(|(q, _)| *q)
                            .collect();
                        if let Some(unsat @ Ok(SolveResult::Unsat(_))) = self
                            .universal_false_at_ground_witness(&cegqi_foralls, snapshot, category)
                        {
                            return unsat;
                        }
                    }
                    self.last_unknown_reason = Some(UnknownReason::QuantifierCegqiIncomplete);
                    Ok(SolveResult::Unknown)
                }
            }
            _ => {
                self.last_unknown_reason = Some(UnknownReason::QuantifierCegqiIncomplete);
                Ok(SolveResult::Unknown)
            }
        }
    }

    /// SAT-leg flip of the quantified-CE-lemma decider (#quantified-ce-lemma),
    /// for the `classify_quantifier_result` refinement-Unknown/None hooks.
    ///
    /// # Certificate
    ///
    /// Fires only when [`Self::refuted_all_quantified_ce_lemmas`] establishes
    /// that EVERY CEGQI universal's de-Skolemized counterexample obligation is
    /// UNSAT — i.e. every original `forall x⃗ (exists y⃗ psi0)` assertion is
    /// VALID (true in every theory model, independent of any other assertion) —
    /// and its coverage gate establishes that those universals are the ONLY
    /// quantified assertions in the snapshot. The hooks that call this are
    /// entered only from the `Ok(Sat) if cegqi_has_forall` classify arm, so the
    /// FULL assertion set (ground remainder ∪ CE lemmas ∪ refinement
    /// instances) was already solved Sat at least once, which subsumes
    /// remainder-Sat; `last_model` holds that candidate model (guarded — no
    /// model, no flip). Valid universals + satisfiable ground remainder ⟹ the
    /// original problem is SAT.
    ///
    /// # Safety nets (mirror of the disambiguation `Ok(Sat)` consumer)
    ///
    /// The callers run the MBQI cross-validation
    /// (`disambiguate_cegqi_valid_via_mbqi_ext`) BEFORE this flip and return
    /// its UNSAT if it refutes; this method re-checks the
    /// witness-independent-skolem-alternation net and fails closed (`None`) on
    /// that shape. On success it performs the documented CEGQI-valid-verdict
    /// bookkeeping (`defer_model_validation = false`,
    /// `last_model_validated = true`): the verdict is semantically validated by
    /// the refutation certificates (the ground model witnesses the remainder;
    /// no ground model can witness a `forall`), exactly like the pre-existing
    /// CE-conjunction flip.
    fn try_quantified_ce_valid_flip(
        &mut self,
        cegqi_state: &[(TermId, CegqiInstantiator)],
        snapshot: &[TermId],
        category: LogicCategory,
    ) -> Option<Result<SolveResult>> {
        // Never mint Sat without a witness for the ground remainder: the
        // candidate model of the last full-set Sat solve must still be present.
        self.last_model.as_ref()?;
        if !self.refuted_all_quantified_ce_lemmas(cegqi_state, snapshot, category) {
            return None;
        }
        if self.snapshot_has_witness_independent_skolem_alternation(snapshot) {
            return None;
        }
        self.defer_model_validation = false;
        self.last_model_validated = true;
        self.last_unknown_reason = None;
        Some(Ok(SolveResult::Sat))
    }

    /// SAT leg of the quantified-CE-lemma decider (#quantified-ce-lemma):
    /// return `true` iff EVERY CEGQI universal's DE-SKOLEMIZED counterexample
    /// obligation `L_q = forall y⃗. ¬psi0(y⃗, e⃗)` is individually refuted by a
    /// bounded, ISOLATED ground instantiation, and the coverage gates hold.
    ///
    /// # Soundness (SAT direction)
    ///
    /// For each universal `quant = forall x⃗. B(x⃗)` (the post-Skolemization
    /// form of an original `forall x⃗ exists y⃗. psi0(y⃗, x⃗)`),
    /// [`rebuild_quantified_ce_lemma`] reconstructs `L_q` exactly (fail-closed
    /// `None` on anything outside the v1 fragment). By universal instantiation
    /// `L_q ⊨ rho(t⃗)` for ANY terms `t⃗`, so a standalone ground solve proving
    /// some `rho(t⃗)` UNSAT proves `L_q` UNSAT. `L_q` UNSAT means
    /// `exists y⃗. psi0(y⃗, e⃗)` is VALID with `e⃗` fresh free constants —
    /// i.e. the ORIGINAL assertion `forall x⃗ exists y⃗. psi0` is valid in
    /// every theory model, which is exactly the CEGQI premise ("the CE lemma
    /// alone is UNSAT") the joint ground refutation cannot discharge for
    /// skolemized lemmas (the stored `¬psi0(sk(e⃗), e⃗)` keeps `sk` free and is
    /// always satisfiable). Refutation is PER LEMMA — strictly stronger than
    /// the legacy joint-conjunction solve, which is retained byte-identically
    /// for all-ground lemma sets.
    ///
    /// Candidate synthesis is NOT a soundness surface: every candidate is
    /// verified by the isolated ground solve and silently skipped otherwise.
    /// Isolated solves are mandatory: conjoining instances demonstrably sends
    /// the NIA ground solver to unknown where each solo instance is decided.
    ///
    /// # Gates
    ///
    /// - `cegqi_state` must contain at least one universal and NO existential
    ///   (an existential CE obligation is a witness search, not a validity
    ///   check).
    /// - Coverage: every quantifier-bearing assertion in `snapshot` must BE a
    ///   bare top-level `forall` handled by CEGQI (present in `cegqi_state`).
    ///   This makes the validity certificates cover ALL quantified obligations
    ///   (a quantifier nested under `or`/`ite`/`not`, an E-matching-owned
    ///   trigger forall, or an unhandled quantifier fails the gate) so the
    ///   caller's remainder-Sat premise extends to the whole problem.
    /// - Work bounds: ≤ 12 isolated solves per lemma under one shared 300 ms
    ///   deadline for the whole leg (the standard tight-deadline pattern).
    fn refuted_all_quantified_ce_lemmas(
        &mut self,
        cegqi_state: &[(TermId, CegqiInstantiator)],
        snapshot: &[TermId],
        category: LogicCategory,
    ) -> bool {
        use ay_core::kani_compat::DetHashSet as HashSet;
        const MAX_LEMMA_REFUTATION_SOLVES: usize = 12;

        if cegqi_state.is_empty() {
            return false;
        }
        for (_, inst) in cegqi_state {
            if !inst.is_forall() {
                return false;
            }
        }

        // Coverage gate: the certificates below must account for EVERY
        // quantified obligation in the pre-instantiation snapshot.
        let covered: HashSet<TermId> = cegqi_state.iter().map(|(q, _)| *q).collect();
        for &assertion in snapshot {
            if contains_quantifier(&self.ctx.terms, assertion)
                && !(matches!(self.ctx.terms.get(assertion), TermData::Forall(..))
                    && covered.contains(&assertion))
            {
                return false;
            }
        }

        // Shared tight deadline across the whole leg.
        let saved_deadline = self.solve_deadline.get();
        let tight = ay_core::time::Instant::now() + std::time::Duration::from_millis(300);
        self.set_deadline(match saved_deadline {
            Some(d) if d < tight => Some(d),
            _ => Some(tight),
        });

        let mut all_refuted = true;
        'lemmas: for (quant, inst) in cegqi_state {
            let Some((binders, rho)) =
                rebuild_quantified_ce_lemma(&mut self.ctx.terms, *quant, inst)
            else {
                all_refuted = false;
                break;
            };
            if binders.is_empty() {
                // Ground lemma: the obligation IS the stored CE lemma; refute
                // it directly with one isolated solve.
                if self.isolated_ground_solve_is_unsat(rho, category) {
                    continue;
                }
                all_refuted = false;
                break;
            }
            let tuples = self.quantified_lemma_candidate_tuples(&binders, rho);
            if tuples.is_empty() {
                all_refuted = false;
                break;
            }
            for tuple in tuples.into_iter().take(MAX_LEMMA_REFUTATION_SOLVES) {
                if ay_core::time::Instant::now() >= tight {
                    all_refuted = false;
                    break 'lemmas;
                }
                let subst: HashMap<String, TermId> = binders
                    .iter()
                    .map(|(n, _)| n.clone())
                    .zip(tuple.iter().copied())
                    .collect();
                let instance = crate::ematching::subst_vars(&mut self.ctx.terms, rho, &subst);
                if self.isolated_ground_solve_is_unsat(instance, category) {
                    continue 'lemmas; // this lemma is refuted — next lemma
                }
            }
            all_refuted = false;
            break;
        }

        self.set_deadline(saved_deadline);
        all_refuted
    }

    /// Candidate instantiation tuples for the binders of a rebuilt
    /// counterexample obligation `L_q = forall y⃗. rho`. Reuses the existing
    /// binder-base synthesizers (free Int variables — which now surface the CE
    /// variables `e⃗` —, binder-independent UF values, atom boundaries, Skolem
    /// witness points, linear combinations) with small offsets, plus a constant
    /// window. Candidates mentioning another binder are dropped so every tuple
    /// substitutes to a formula over the lemma's free symbols only. Not a
    /// soundness surface (each tuple is verified by an isolated solve).
    fn quantified_lemma_candidate_tuples(
        &mut self,
        binders: &[(String, ay_core::Sort)],
        rho: TermId,
    ) -> Vec<Vec<TermId>> {
        const MAX_TUPLES: usize = 12;
        let all_names: ay_core::kani_compat::DetHashSet<String> =
            binders.iter().map(|(n, _)| n.clone()).collect();
        let cap_per_binder = if binders.len() == 1 { MAX_TUPLES } else { 3 };

        let mut per_binder: Vec<Vec<TermId>> = Vec::with_capacity(binders.len());
        for (name, _) in binders {
            let cands =
                self.quantified_lemma_binder_candidates(rho, name, &all_names, cap_per_binder);
            if cands.is_empty() {
                return Vec::new();
            }
            per_binder.push(cands);
        }

        let mut out: Vec<Vec<TermId>> = vec![Vec::new()];
        for cands in &per_binder {
            let mut next: Vec<Vec<TermId>> = Vec::new();
            'outer: for prefix in &out {
                for &c in cands {
                    let mut tuple = prefix.clone();
                    tuple.push(c);
                    next.push(tuple);
                    if next.len() >= MAX_TUPLES {
                        break 'outer;
                    }
                }
            }
            out = next;
        }
        out
    }

    /// Per-binder candidate terms for [`Self::quantified_lemma_candidate_tuples`]:
    /// the five binder-base synthesizers with offsets ±2, then a small constant
    /// window, capped and filtered of candidates that mention any lemma binder.
    fn quantified_lemma_binder_candidates(
        &mut self,
        rho: TermId,
        name: &str,
        all_binder_names: &ay_core::kani_compat::DetHashSet<String>,
        cap: usize,
    ) -> Vec<TermId> {
        const MAX_BASES: usize = 4;
        let mut bases: Vec<TermId> = self.free_int_binder_bases(rho, name);
        for b in self.uf_value_binder_bases(rho, name) {
            if !bases.contains(&b) {
                bases.push(b);
            }
        }
        for b in self.skolem_app_bases(rho, name) {
            if !bases.contains(&b) {
                bases.push(b);
            }
        }
        for b in self.atom_boundary_binder_bases(rho, name) {
            if !bases.contains(&b) {
                bases.push(b);
            }
        }
        for b in self.combination_binder_bases(rho, name) {
            if !bases.contains(&b) {
                bases.push(b);
            }
        }
        bases.retain(|&b| !self.term_mentions_bound_var(b, all_binder_names));
        bases.truncate(MAX_BASES);

        let mut out: Vec<TermId> = Vec::new();
        for &base in &bases {
            for k in [0i64, 1, -1, 2, -2] {
                let cand = if k == 0 {
                    base
                } else {
                    let kterm = self.ctx.terms.mk_int(num_bigint::BigInt::from(k));
                    self.ctx.terms.mk_add(vec![base, kterm])
                };
                if !out.contains(&cand) {
                    out.push(cand);
                    if out.len() >= cap {
                        return out;
                    }
                }
            }
        }
        for c in [0i64, 1, -1, 2, -2] {
            let cand = self.ctx.terms.mk_int(num_bigint::BigInt::from(c));
            if !out.contains(&cand) {
                out.push(cand);
                if out.len() >= cap {
                    break;
                }
            }
        }
        out
    }

    /// UNSAT leg of the quantified-CE-lemma decider (#quantified-ce-lemma):
    /// decide the WHOLE problem UNSAT when a conjunctive-position universal is
    /// FALSE at a concrete ground witness.
    ///
    /// # Soundness (UNSAT direction)
    ///
    /// The problem asserts each `q = forall x. B(x)` in
    /// [`Self::forall_ids_in_conjunctive_position`] as a top-level conjunct of
    /// the (post-Skolemization) snapshot, so `problem ⊨ B(c)` for every ground
    /// `c` (universal instantiation; a NON-conjunctive forall does not entail
    /// its instances and is skipped, mirroring the #classA guard). `B(c)` being
    /// UNSAT as a STANDALONE formula means NO interpretation of its free
    /// symbols — including the Skolem terms `sk(c)` left as free ground
    /// applications — satisfies it, hence no model of the problem exists;
    /// Skolemization preserves satisfiability, so the ORIGINAL problem is
    /// UNSAT regardless of any other assertion. A genuinely-SAT problem can
    /// never be flipped: its model satisfies `B(c)` for every `c`, so no
    /// standalone `B(c)` is UNSAT. Candidate synthesis
    /// ([`crate::executor::mbqi::synthesize_int_refutation_candidates`]) is not
    /// a soundness surface — every candidate is verified by the isolated
    /// ground solve, exactly like `unsat_from_direct_instance_clash` step 5.
    ///
    /// # Bounds
    ///
    /// Only single-`Int`-binder, quantifier-free-body universals that apply an
    /// uninterpreted function to the binder (the shapes the arithmetic CE
    /// search is incomplete over); ≤ 12 isolated solves under one shared
    /// 300 ms deadline.
    fn universal_false_at_ground_witness(
        &mut self,
        foralls: &[TermId],
        snapshot: &[TermId],
        fallback_category: LogicCategory,
    ) -> Option<Result<SolveResult>> {
        const MAX_WITNESS_SOLVES: usize = 12;
        if foralls.is_empty() {
            return None;
        }
        let conjunctive = self.forall_ids_in_conjunctive_position(snapshot);

        let saved_deadline = self.solve_deadline.get();
        let tight = ay_core::time::Instant::now() + std::time::Duration::from_millis(300);
        self.set_deadline(match saved_deadline {
            Some(d) if d < tight => Some(d),
            _ => Some(tight),
        });

        let mut budget = MAX_WITNESS_SOLVES;
        let mut outcome: Option<Result<SolveResult>> = None;
        'foralls: for &q in foralls {
            if !conjunctive.contains(&q) {
                continue;
            }
            let TermData::Forall(vars, body, _) = self.ctx.terms.get(q).clone() else {
                continue;
            };
            let [(name, ay_core::Sort::Int)] = vars.as_slice() else {
                continue;
            };
            if contains_quantifier(&self.ctx.terms, body) {
                continue;
            }
            // Focus on the alternation/UF shapes the arithmetic CE search is
            // incomplete over (mirrors the eager-instantiation gate of the
            // MBQI validation); pure-arith universals are already decided
            // soundly by CEGQI.
            let bound: ay_core::kani_compat::DetHashSet<String> =
                std::iter::once(name.clone()).collect();
            if !self.term_mentions_uninterpreted_of_bound_var(body, &bound) {
                continue;
            }
            let candidates = crate::executor::mbqi::synthesize_int_refutation_candidates(
                &self.ctx.terms,
                body,
                snapshot,
            );
            for c in candidates {
                if budget == 0 || ay_core::time::Instant::now() >= tight {
                    break 'foralls;
                }
                budget -= 1;
                let cterm = self.ctx.terms.mk_int(c);
                let mut subst: HashMap<String, TermId> = HashMap::default();
                subst.insert(name.clone(), cterm);
                let instance = crate::ematching::subst_vars(&mut self.ctx.terms, body, &subst);
                if self.isolated_ground_solve_is_unsat(instance, fallback_category) {
                    outcome = Some(Ok(SolveResult::unsat()));
                    break 'foralls;
                }
            }
        }

        self.set_deadline(saved_deadline);
        outcome
    }

    /// Solve a SINGLE quantifier-free formula as a standalone problem and
    /// return `true` iff it is definitively UNSAT. Full nested-solve state
    /// discipline: saves and restores all seven pieces of solver state the
    /// solve perturbs (`ctx.assertions`, `incr_theory_state`, `last_model`,
    /// `last_model_validated`, `last_validation_stats`, `last_unknown_reason`,
    /// `defer_model_validation`), so the probe can neither leak into nor trip
    /// the postconditions of the enclosing solve. Anything short of a
    /// definitive `Unsat` (Sat / Unknown / error / deadline abort) is `false`
    /// — fail-closed.
    pub(in crate::executor) fn isolated_ground_solve_is_unsat(
        &mut self,
        formula: TermId,
        fallback_category: LogicCategory,
    ) -> bool {
        if contains_quantifier(&self.ctx.terms, formula) {
            return false;
        }
        let mut assertions = vec![formula];
        // Nelson-Oppen purification of opaque Int-sorted UF applications inside
        // arithmetic, exactly as the top-level `check_sat` pipeline runs before
        // its solve. Without it a Skolem application inside a nonlinear product
        // (`(* (sk 2) (sk 2))` from the S3 ∀∃ perfect-square instance) is an
        // opaque slack the NIA core cannot relate to the arithmetic, and the
        // probe misses the definitive UNSAT. EQUISATISFIABLE (fresh `v` fully
        // defined by `v = u` — see `purify_int_uf_arith`), so the verdict maps
        // 1:1 onto the raw instance and the UNSAT-leg argument is unchanged.
        crate::executor::purify_int_uf_arith::purify_int_uf_arith(
            &mut self.ctx.terms,
            &mut assertions,
        );
        let (detected, _) = self.detect_logic_category(&assertions);
        let category = if matches!(detected, LogicCategory::Other) {
            fallback_category
        } else {
            detected
        };

        let saved_assertions = std::mem::replace(&mut self.ctx.assertions, assertions);
        let saved_theory_state = self.incr_theory_state.take();
        let saved_bv_state = self.incr_bv_state.take();
        let saved_model = self.last_model.take();
        let saved_model_validated = self.last_model_validated;
        let saved_validation_stats = self.last_validation_stats.take();
        let saved_unknown_reason = self.last_unknown_reason;
        let saved_defer = self.defer_model_validation;
        self.defer_model_validation = false;
        let result = self.solve_for_category(category);
        self.ctx.assertions = saved_assertions;
        self.incr_theory_state = saved_theory_state;
        self.incr_bv_state = saved_bv_state;
        self.last_model = saved_model;
        self.last_model_validated = saved_model_validated;
        self.last_validation_stats = saved_validation_stats;
        self.last_unknown_reason = saved_unknown_reason;
        self.defer_model_validation = saved_defer;
        matches!(result, Ok(SolveResult::Unsat(_)))
    }

    /// SOUND UNSAT independence check (#mbqi-completeness Q1).
    ///
    /// Reconstructs a theory-INDEPENDENT UNSAT derivation directly from the
    /// pre-instantiation `snapshot` and returns `true` iff one exists. It does
    /// NOT trust the theory solver's UNSAT (which can be a latent theory
    /// incompleteness / wrong-UNSAT - e.g. the array solver collapsing a
    /// satisfiable (forall i. a[i]=b[i]) and a[0]=b[0] to `false`). Instead it:
    ///
    ///   1. Collects the quantifier-free top-level CONJUNCTS of `snapshot` (the
    ///      ground core literals).
    ///   2. Collects the top-level conjunctive-position `forall`s.
    ///   3. Instantiates each `forall` body at every tuple of ground terms (by
    ///      bound-var sort) drawn from the snapshot - bounded by a small budget.
    ///      Each instance is a SOUND logical consequence of the universal
    ///      (instantiation is universally valid).
    ///   4. Checks the (ground literals union instance literals) set for a DIRECT
    ///      complementary pair: a literal `X` and its negation (`(not X)`, or the
    ///      `=` / `distinct` complement of an equality).
    ///   5. (#mbqi-completeness Q2) If no syntactic pair is found, re-solves the
    ///      GROUND conjunction of those same literals as a pure quantifier-free
    ///      problem and returns `true` iff it is definitively UNSAT.
    ///
    /// SOUNDNESS: a literal together with its complement (step 4) is a
    /// contradiction in PURE PROPOSITIONAL / EQUALITY logic, valid under EVERY
    /// interpretation - including the array/FP/Seq one the binder ranges over -
    /// and derived from sound instantiation only. Q1
    /// ((forall i. a[i]=b[i]) and not(a[0]=b[0])) instantiates at i:=0 to
    /// (= a[0] b[0]), which clashes with the ground (not (= a[0] b[0])) => `true`.
    /// Equalities are hash-consed, so an instance and the matching negated ground
    /// literal share the same inner `TermId`.
    ///
    /// Step 5 extends this to refutations the syntactic check cannot see: a ground
    /// DISJUNCTION (the finite-domain-expanded / skolemized negated goal
    /// `(or (< a[0] 0) (< a[1] 0) (< a[2] 0))`) that closes only after case-split
    /// against several instances, or a pair complementary only under LIA/EUF
    /// (`(< a[0] 0)` vs the instance `(<= 0 a[0])`) rather than as a syntactic
    /// `Not`-pair - both ubiquitous for array/seq FRAME quantifiers. It is SOUND:
    /// every element of `literals` is either a genuine quantifier-free CONJUNCT of
    /// the original problem or a sound universal INSTANCE (`forall v. body ⊨
    /// body[v:=t]`), so their ground conjunction is ENTAILED by the original
    /// assertions; if it is UNSAT the original is UNSAT. It can NEVER manufacture a
    /// wrong UNSAT - it adds only sound consequences to the real quantifier-free
    /// core and never rides CEGQI's possibly-unsound valid->SAT flip - and it
    /// leaves the conservative Unknown whenever the ground re-solve is not
    /// definitively UNSAT (e.g. array-extensionality (forall i. a[i]=b[i]) ∧ a≠b
    /// with no index terms yields no instances => ground re-solve SAT => not
    /// certified). The caller restricts this whole method to snapshots whose every
    /// `forall` is a CONJUNCTIVE-position universal, so conjoining their instances
    /// is sound (a non-conjunctive forall's instances must never be conjoined).
    fn unsat_from_direct_instance_clash(
        &mut self,
        snapshot: &[TermId],
        fallback_category: LogicCategory,
    ) -> bool {
        use ay_core::kani_compat::DetHashSet as HashSet;
        use ay_core::Sort;

        // 1. Ground (quantifier-free) literals + conjunctive-position foralls.
        let mut literals: Vec<TermId> = Vec::new();
        let conjunctive = self.forall_ids_in_conjunctive_position(snapshot);
        let mut foralls: Vec<TermId> = Vec::new();
        for &assertion in snapshot {
            let mut conjuncts = vec![assertion];
            collect_and_conjuncts(&self.ctx.terms, assertion, &mut conjuncts);
            for c in conjuncts {
                if contains_quantifier(&self.ctx.terms, c) {
                    if matches!(self.ctx.terms.get(c), TermData::Forall(..))
                        && conjunctive.contains(&c)
                        && !foralls.contains(&c)
                    {
                        foralls.push(c);
                    }
                } else if !literals.contains(&c) {
                    literals.push(c);
                }
            }
        }
        if foralls.is_empty() {
            return false;
        }

        // 2. Ground terms by sort, for instantiation candidates.
        let ground_by_sort =
            crate::ematching::collect_ground_terms_by_sort(&self.ctx.terms, snapshot);

        // 3. Instantiate each conjunctive forall at the bounded cross-product of
        //    ground candidates. Each instance is a sound consequence.
        const MAX_CLASH_INSTANCES: usize = 256;
        let mut produced = 0usize;
        'forall: for &q in &foralls {
            let (vars, body) = match self.ctx.terms.get(q) {
                TermData::Forall(v, b, _) => (v.clone(), *b),
                _ => continue,
            };
            if vars.is_empty() {
                continue;
            }
            let mut candidates_per_var: Vec<Vec<TermId>> = Vec::with_capacity(vars.len());
            for (_n, sort) in &vars {
                let cands = if matches!(sort, Sort::Bool) {
                    // A Bool binder ranges over EXACTLY {true, false}, so
                    // instantiating at both is sound (each is a consequence:
                    // `forall b. P(b)` ⊨ `P(true)` and ⊨ `P(false)`) AND complete
                    // for the binder (`forall b:Bool. P(b)` ≡ `P(true) ∧ P(false)`).
                    // Previously a Bool binder skipped the WHOLE forall
                    // (`continue 'forall`), so a mixed `forall (b Bool) (i S). …`
                    // contributed zero instances and any refutation needing a Bool
                    // case was missed. Reconstructing from these instances can only
                    // ADD genuine UNSATs — this function never returns SAT — so
                    // there is no wrong-verdict hazard. Two candidates keep the
                    // cross-product bounded.
                    vec![self.ctx.terms.true_term(), self.ctx.terms.false_term()]
                } else {
                    let cands = ground_by_sort.get(sort).cloned().unwrap_or_default();
                    if cands.is_empty() {
                        continue 'forall;
                    }
                    cands
                };
                candidates_per_var.push(cands);
            }
            let var_names: Vec<String> = vars.iter().map(|(n, _)| n.clone()).collect();
            let mut indices = vec![0usize; candidates_per_var.len()];
            loop {
                if produced >= MAX_CLASH_INSTANCES {
                    break 'forall;
                }
                let subst_map: HashMap<String, TermId> = var_names
                    .iter()
                    .enumerate()
                    .map(|(var_idx, name)| {
                        (name.clone(), candidates_per_var[var_idx][indices[var_idx]])
                    })
                    .collect();
                let inst = crate::ematching::subst_vars(&mut self.ctx.terms, body, &subst_map);
                if !literals.contains(&inst) {
                    literals.push(inst);
                }
                produced += 1;
                let mut carry = true;
                for i in (0..candidates_per_var.len()).rev() {
                    if carry {
                        indices[i] += 1;
                        if indices[i] < candidates_per_var[i].len() {
                            carry = false;
                        } else {
                            indices[i] = 0;
                        }
                    }
                }
                if carry {
                    break;
                }
            }
        }

        // 4. Direct complementary-pair check (pure propositional/equality).
        let false_term = self.ctx.terms.false_term();
        let true_term = self.ctx.terms.true_term();
        let mut positives: HashSet<TermId> = HashSet::default();
        let mut negatives: HashSet<TermId> = HashSet::default();
        for &lit in &literals {
            if lit == false_term {
                // A literal that IS the constant `false` (a ground conjunct or an
                // instance that simplified to false) is an unconditional, sound
                // contradiction.
                return true;
            }
            if lit == true_term {
                continue;
            }
            let (is_neg, inner) = match self.ctx.terms.get(lit) {
                TermData::Not(inner) => (true, *inner),
                TermData::App(sym, args) if sym.name() == "distinct" && args.len() == 2 => {
                    match self.ctx.terms.find_eq(args[0], args[1]) {
                        Some(eq) => (true, eq),
                        None => (false, lit),
                    }
                }
                _ => (false, lit),
            };
            if is_neg {
                if positives.contains(&inner) {
                    return true;
                }
                negatives.insert(inner);
            } else {
                if negatives.contains(&inner) {
                    return true;
                }
                positives.insert(inner);
            }
        }

        // 5. Sound ground re-solve certification (#mbqi-completeness Q2). The
        //    syntactic pair check misses refutations that need the theory/BCP
        //    solver to case-split a ground disjunction against several instances
        //    or to close a LIA/EUF-complementary pair. `literals` (ground
        //    conjuncts + sound conjunctive-forall instances) is entailed by the
        //    original assertions, so re-solving its ground conjunction certifies
        //    the reported UNSAT without trusting CEGQI's valid->SAT flip. All
        //    instances are quantifier-free by construction; bail if a nested
        //    quantifier in a forall body leaked one through, keeping this a pure
        //    ground solve.
        if literals.is_empty()
            || literals
                .iter()
                .any(|&l| contains_quantifier(&self.ctx.terms, l))
        {
            return false;
        }
        let saved_assertions = std::mem::replace(&mut self.ctx.assertions, literals.clone());
        let saved_theory_state = self.incr_theory_state.take();
        let saved_bv_state = self.incr_bv_state.take();
        let (detected, _) = self.detect_logic_category(&literals);
        let solve_category = if matches!(detected, LogicCategory::Other) {
            fallback_category
        } else {
            detected
        };
        let result = self.solve_for_category(solve_category);
        self.ctx.assertions = saved_assertions;
        self.incr_theory_state = saved_theory_state;
        self.incr_bv_state = saved_bv_state;
        matches!(result, Ok(SolveResult::Unsat(_)))
    }

    /// Validate a CEGQI "forall valid ⟹ SAT" verdict with model-based quantifier
    /// instantiation (MBQI) and DECIDE UNSAT when the universal is actually
    /// violated by the candidate model.
    ///
    /// `disambiguate_cegqi_unsat` leaves the ground-only candidate model in
    /// `last_model`. We rebuild the quantifier-free ground core from `snapshot`,
    /// then run `try_mbqi_refinement` over the snapshot's `forall`s: it
    /// instantiates each at ground/synthesized candidates, evaluates under the
    /// candidate model, and re-solves the falsifying instances. If that drives
    /// the problem UNSAT, the universal is genuinely false (e.g. the alternation
    /// cases whose infeasibility comes from the COMBINATION of skolem-constrained
    /// conjuncts, which no syntactic guard can detect), so we decide UNSAT —
    /// matching z3 — instead of trusting the unvalidated certificate. Returns
    /// `Some(Ok(unsat))` only on a definitive MBQI refutation; otherwise restores
    /// state and returns `None` (caller keeps the SAT / fail-closed path). MBQI
    /// is model-targeted (a few candidates per round), not a blind enumeration.
    // Non-aggressive entry point of the `_ext` API pair; live callers currently use
    // the `aggressive=true` form, but this default-mode wrapper is retained for the
    // non-alternation CEGQI/uf-completion validation paths it documents.
    #[allow(dead_code)]
    fn disambiguate_cegqi_valid_via_mbqi(
        &mut self,
        snapshot: &[TermId],
        category: LogicCategory,
    ) -> Option<Result<SolveResult>> {
        self.disambiguate_cegqi_valid_via_mbqi_ext(snapshot, category, false)
    }

    /// `aggressive` enables the relaxation-based extra refutation paths
    /// (multi-Skolem FM projection, binder-dependent UF over-approximation). They
    /// run additional `(forall ...)` sub-solves, so they are gated to the bare
    /// ALTERNATION arm: the uf-completion / CEGQI-disambiguation callers validate
    /// genuine-SAT library completions where those extra sub-solves would only burn
    /// time and perturb the SAT model-building state. The base validation (bounded
    /// instantiation + single-Skolem projection + Skolem over-approximation) runs
    /// in both modes and is unchanged from the pre-existing behaviour.
    fn disambiguate_cegqi_valid_via_mbqi_ext(
        &mut self,
        snapshot: &[TermId],
        category: LogicCategory,
        aggressive: bool,
    ) -> Option<Result<SolveResult>> {
        // Re-entrancy guard: the over-approximation step below issues its own
        // `(forall ...)` solve, which must not recurse back into this validation.
        if self.in_alternation_validation {
            return None;
        }
        // The validation's nested `(forall ...)` sub-solves re-enter the quantifier
        // pipeline and mutate the verdict-bookkeeping state (`defer_model_validation`
        // / model / validated / unknown-reason). Only an UNSAT outcome is consumed by
        // callers; for ANY other outcome this validation made no decision, so snapshot
        // that state and restore it fully. Otherwise a non-refuting validation run on
        // a genuine-SAT problem leaves `defer_model_validation` perturbed and the
        // caller's later SAT model build is skipped (panics the SAT/model postcondition
        // on library-completion problems that reach here).
        let saved_defer = self.defer_model_validation;
        let saved_model = self.last_model.clone();
        let saved_validated = self.last_model_validated;
        let saved_reason = self.last_unknown_reason;
        self.in_alternation_validation = true;
        let out = self.disambiguate_cegqi_valid_via_mbqi_inner(snapshot, category, aggressive);
        self.in_alternation_validation = false;
        if !matches!(out, Some(Ok(SolveResult::Unsat(_)))) {
            self.defer_model_validation = saved_defer;
            self.last_model = saved_model;
            self.last_model_validated = saved_validated;
            self.last_unknown_reason = saved_reason;
        }
        out
    }

    fn disambiguate_cegqi_valid_via_mbqi_inner(
        &mut self,
        snapshot: &[TermId],
        category: LogicCategory,
        aggressive: bool,
    ) -> Option<Result<SolveResult>> {
        let mut quants: Vec<TermId> = Vec::new();
        for &a in snapshot {
            crate::ematching::collect_quantifiers(&mut self.ctx.terms, a, &mut quants);
        }
        let foralls: Vec<TermId> = quants
            .into_iter()
            .filter(|&q| matches!(self.ctx.terms.get(q), TermData::Forall(..)))
            .collect();
        // PERF: this validation adds an instantiation solve. The alternation
        // wrong-sats it targets are small, bare-`forall` problems; a query with
        // many quantifiers or a large ground state (e.g. a verification-consumer/quantifier_consumer
        // completion) is genuinely SAT and must not pay for a validation solve.
        // Bound the work to keep it off the hot path.
        if foralls.is_empty() || foralls.len() > 3 {
            return None;
        }

        // Quantifier-free ground core (candidate terms + ground constraints).
        let mut ground: Vec<TermId> = Vec::new();
        for &assertion in snapshot {
            if contains_quantifier(&self.ctx.terms, assertion) {
                let mut conjuncts = Vec::new();
                collect_and_conjuncts(&self.ctx.terms, assertion, &mut conjuncts);
                for c in conjuncts {
                    if !contains_quantifier(&self.ctx.terms, c) && !ground.contains(&c) {
                        ground.push(c);
                    }
                }
            } else if !ground.contains(&assertion) {
                ground.push(assertion);
            }
        }
        if ground.len() > 12 {
            return None;
        }

        // Premise-forced refutation for the multi-binder / BitVec `fixpoint`
        // shape (`∀xs. premise(xs) ⟹ conclusion(xs)` with a UF-free
        // binder-pinning premise): the Int value-window loop below only covers
        // single-`Int`-binder foralls, so these fell through and the UF-
        // completion certificate granted a wrong `sat`. Sound; only ever UNSAT.
        if let Some(r @ Ok(SolveResult::Unsat(_))) =
            self.premise_forced_binder_refutation(&foralls, snapshot)
        {
            return Some(r);
        }

        // Eager bounded instantiation: for each single-`Int`-binder `forall`
        // with a quantifier-free body, add the ground instances `body[c]` for a
        // small window of concrete `c`. The Skolem function `sk` is SHARED across
        // instances, so a genuine universal (`(forall x (> sk(x) x))`) stays SAT
        // (`sk` maps each `c` to a witness), while a universal that is false at
        // some in-window `c` contributes a contradictory instance (e.g.
        // `(and (<= sk(2) 0) (>= sk(2) 2))`) that drives the whole conjunction
        // UNSAT. One solve decides it — no per-candidate sub-solving.
        let mut instances = ground;
        let mut added = false;
        let mut budget = 256usize;
        for &q in &foralls {
            let TermData::Forall(vars, body, _) = self.ctx.terms.get(q).clone() else {
                continue;
            };
            let [(name, ay_core::Sort::Int)] = vars.as_slice() else {
                continue;
            };
            if contains_quantifier(&self.ctx.terms, body) {
                continue;
            }
            // Only the ALTERNATION shapes can be wrongly SAT here: the body must
            // apply a Skolem/uninterpreted function to the bound variable (a
            // skolemized inner existential or a declared UF). A pure-arithmetic
            // universal is already decided soundly by CEGQI, so skip it to avoid
            // adding an instantiation solve on every benign forall.
            let bound: ay_core::kani_compat::DetHashSet<String> =
                std::iter::once(name.clone()).collect();
            if !self.term_mentions_uninterpreted_of_bound_var(body, &bound) {
                continue;
            }
            for c in -16i64..=16 {
                if budget == 0 {
                    break;
                }
                budget -= 1;
                let cval = self.ctx.terms.mk_int(num_bigint::BigInt::from(c));
                let mut subst: HashMap<String, TermId> = HashMap::default();
                subst.insert(name.clone(), cval);
                let body_c = crate::ematching::subst_vars(&mut self.ctx.terms, body, &subst);
                instances.push(body_c);
                added = true;
            }
            // E-matching instances: when the body applies a UF to a term LINEAR in
            // the bound variable (e.g. `(f (+ q0 q2))`) and the problem has a
            // ground application of the same UF (e.g. `(f 0)`), instantiate the
            // bound variable so the arguments ALIGN (`q2 = (- 0 q0)`). Congruence
            // then forces `(f (+ q0 q2)) = (f 0)`, exposing a contradiction a
            // value window cannot reach — the forall-over-UF-range case
            // `(forall q2 (and (= (f 0) 1) (<= (f (+ q0 q2)) 0)))`.
            for v in self.ematching_binder_values(body, name, &instances) {
                if budget == 0 {
                    break;
                }
                budget -= 1;
                let mut subst: HashMap<String, TermId> = HashMap::default();
                subst.insert(name.clone(), v);
                let body_v = crate::ematching::subst_vars(&mut self.ctx.terms, body, &subst);
                instances.push(body_v);
                added = true;
            }
            // Relative instances: the falsifying value can be OFFSET from another
            // (outer-quantified) Int variable rather than absolute, e.g.
            // `(forall q1 (or (and (> (f (- q0 q1)) 3) (<= q1 q0)) (= q1 -3)))`
            // is UNSAT via `q1 = q0 + 1` (just above `q0`). Instantiate the binder
            // at `other ± k` for each free Int variable `other` in the body.
            for base in self.free_int_binder_bases(body, name) {
                for k in -2i64..=2 {
                    if budget == 0 {
                        break;
                    }
                    budget -= 1;
                    let kterm = self.ctx.terms.mk_int(num_bigint::BigInt::from(k));
                    let v = self.ctx.terms.mk_add(vec![base, kterm]);
                    let mut subst: HashMap<String, TermId> = HashMap::default();
                    subst.insert(name.clone(), v);
                    let body_v = crate::ematching::subst_vars(&mut self.ctx.terms, body, &subst);
                    instances.push(body_v);
                    added = true;
                }
            }
            // Round-2 (skolem-aligned) instances: a universal conjunct that
            // constrains a UF over its WHOLE range (`f(q0-1) > 1` for all q0)
            // contradicts the existential witness point (`f(sk(q0)-2) < -2`) only
            // when the two arguments meet. The witness point lives at the Skolem
            // application `sk(q0)`, so ground it at a few concrete binder values
            // and instantiate the binder NEAR each — bringing the whole-range
            // conjunct to the witness point so congruence exposes the conflict.
            for sk_base in self.skolem_app_bases(body, name) {
                for k in -2i64..=2 {
                    if budget == 0 {
                        break;
                    }
                    budget -= 1;
                    let kterm = self.ctx.terms.mk_int(num_bigint::BigInt::from(k));
                    let v = self.ctx.terms.mk_add(vec![sk_base, kterm]);
                    let mut subst: HashMap<String, TermId> = HashMap::default();
                    subst.insert(name.clone(), v);
                    let body_v = crate::ematching::subst_vars(&mut self.ctx.terms, body, &subst);
                    instances.push(body_v);
                    added = true;
                }
            }
            // UF-value instances: instantiate the binder at `±U + k` for each
            // binder-independent UF value `U` (e.g. `f(3)`, `f(sk0)`). The
            // falsifying point of a universal over an unbounded binder with a
            // disjunctive/implication body frequently lands exactly at such a value
            // (`q1 = f(3)`) or just past its negation (`q1 = 1 - f(sk0)`), and the
            // two instances together expose a contradiction CEGQI's value window
            // and Presburger-incomplete path both miss. These are real instances of
            // the universal, so a resulting UNSAT is sound.
            for uf_base in self.uf_value_binder_bases(body, name) {
                let neg_base = self.ctx.terms.mk_neg(uf_base);
                for &base in &[uf_base, neg_base] {
                    for k in -2i64..=2 {
                        if budget == 0 {
                            break;
                        }
                        budget -= 1;
                        let kterm = self.ctx.terms.mk_int(num_bigint::BigInt::from(k));
                        let v = self.ctx.terms.mk_add(vec![base, kterm]);
                        let mut subst: HashMap<String, TermId> = HashMap::default();
                        subst.insert(name.clone(), v);
                        let body_v =
                            crate::ematching::subst_vars(&mut self.ctx.terms, body, &subst);
                        instances.push(body_v);
                        added = true;
                    }
                }
            }
            // Atom-boundary instances: instantiate the binder at `boundary + k`
            // for each comparison atom's flip point (handles scaled/combined free
            // expressions like `3*c0 + 2` or `sk0 - c0` that the per-variable and
            // UF-value bases cannot reach, plus DIVISIBILITY boundaries `div(-rest,
            // c)` for non-unit coefficients). Real instances ⇒ sound.
            for base in self.atom_boundary_binder_bases(body, name) {
                for k in -2i64..=2 {
                    if budget == 0 {
                        break;
                    }
                    budget -= 1;
                    let kterm = self.ctx.terms.mk_int(num_bigint::BigInt::from(k));
                    let v = self.ctx.terms.mk_add(vec![base, kterm]);
                    let mut subst: HashMap<String, TermId> = HashMap::default();
                    subst.insert(name.clone(), v);
                    let body_v = crate::ematching::subst_vars(&mut self.ctx.terms, body, &subst);
                    instances.push(body_v);
                    added = true;
                }
            }
            // Combination instances: instantiate the binder at pairwise / limited
            // triple sums and differences of the anchor expressions (free vars, UF
            // values, atom boundaries). The simultaneous-violation point of several
            // atoms can be a linear COMBINATION of their individual boundaries
            // (`sk0 + c0 - d0`) that no single boundary reaches. Real instances of
            // the universal ⇒ a resulting UNSAT is sound; offsets kept to ±1 to
            // bound the count.
            for base in self.combination_binder_bases(body, name) {
                for k in -1i64..=1 {
                    if budget == 0 {
                        break;
                    }
                    budget -= 1;
                    let kterm = self.ctx.terms.mk_int(num_bigint::BigInt::from(k));
                    let v = self.ctx.terms.mk_add(vec![base, kterm]);
                    let mut subst: HashMap<String, TermId> = HashMap::default();
                    subst.insert(name.clone(), v);
                    let body_v = crate::ematching::subst_vars(&mut self.ctx.terms, body, &subst);
                    instances.push(body_v);
                    added = true;
                }
            }
        }
        if !added {
            return None;
        }

        // Canonicalize the argument order of every `+` node in the instance set so
        // that sums equal up to commutativity share one interned node. The eager
        // instances are built by substitution (`mk_add` preserves source order),
        // so an aligned witness term like `f(q1-c0)[q1:=sk0+c0-2] = f(+ -2 sk0)`
        // would otherwise NOT hash-cons with the ground `f(+ sk0 -2)`, defeating
        // E-graph congruence and missing the very contradiction the alignment was
        // built to expose. This is LOCAL to the validation's throwaway assertion
        // set — the global `mk_add` order is left untouched (canonicalizing it
        // perturbs unrelated UFLIA solver heuristics into incompleteness).
        let instances: Vec<TermId> = instances
            .into_iter()
            .map(|t| self.canonicalize_sums(t))
            .collect();

        let saved_assertions = std::mem::replace(&mut self.ctx.assertions, instances);
        let saved_theory_state = self.incr_theory_state.take();
        let saved_bv_state = self.incr_bv_state.take();
        let saved_model = self.last_model.clone();
        let saved_validated = self.last_model_validated;
        let saved_reason = self.last_unknown_reason;
        let (cat, _) = self.detect_logic_category(&self.ctx.assertions);
        let cat = if matches!(cat, LogicCategory::Other) {
            category
        } else {
            cat
        };
        // PERF: bound this validation solve with a tight deadline (in addition to
        // any outer deadline). The targeted alternation refutations are small and
        // resolve in milliseconds; if the instantiated problem is instead an
        // expensive genuine query (e.g. a verification-consumer completion that reached here),
        // the solve aborts and we simply keep the original certificate rather than
        // let the validation dominate runtime. Only a definitive UNSAT is used.
        let saved_deadline = self.solve_deadline.get();
        let tight = ay_core::time::Instant::now() + std::time::Duration::from_millis(300);
        let bounded = match saved_deadline {
            Some(d) if d < tight => Some(d),
            _ => Some(tight),
        };
        self.set_deadline(bounded);
        let result = self.solve_for_category(cat);
        self.set_deadline(saved_deadline);
        self.ctx.assertions = saved_assertions;
        self.incr_theory_state = saved_theory_state;
        self.incr_bv_state = saved_bv_state;
        match result {
            Ok(SolveResult::Unsat(_)) => Some(Ok(SolveResult::unsat())),
            _ => {
                self.last_model = saved_model;
                self.last_model_validated = saved_validated;
                self.last_unknown_reason = saved_reason;
                // Per-candidate ISOLATED single-instance refutation
                // (#quantified-ce-lemma): the conjunction solve above conjoins
                // ~dozens of instances into ONE ground problem, and the NIA
                // ground solver demonstrably chokes on such conjunctions (three
                // UF-square atoms already answer unknown) while deciding each
                // instance SOLO (e.g. `(= (* (sk 2) (sk 2)) 2)` is UNSAT on its
                // own). Re-try a bounded set of concrete witnesses one instance
                // at a time. SOUND: gated to CONJUNCTIVE-position foralls (the
                // problem entails every instance of such a forall), and a
                // standalone instance being UNSAT means no interpretation of
                // its free symbols satisfies it — so the whole problem is
                // UNSAT. Candidate synthesis is not a soundness surface (every
                // candidate is verified by the ground solve).
                if let Some(r @ Ok(SolveResult::Unsat(_))) =
                    self.universal_false_at_ground_witness(&foralls, snapshot, category)
                {
                    return Some(r);
                }
                // Exact Fourier-Motzkin projection of the existential witness
                // (decides `(forall q1 (exists q2 <linear>))` shapes), then the
                // Skolem-atom over-approximation. These are the pre-existing base
                // refutations and run in both modes.
                if let Some(r @ Ok(SolveResult::Unsat(_))) =
                    self.alternation_project_witness_unsat(&foralls, category, aggressive)
                {
                    return Some(r);
                }
                if let Some(r @ Ok(SolveResult::Unsat(_))) =
                    self.alternation_overapprox_unsat(&foralls, category)
                {
                    return Some(r);
                }
                // Aggressive-only: the binder-dependent UF over-approximation (keeps
                // binder-INDEPENDENT UF terms as opaque constants — e.g. `f(1)` in
                // `(forall q0 (or (< q0 2) (<= (- q0 1) (f 1))))` — while weakening
                // binder-dependent UF atoms). Runs an extra `(forall ...)` sub-solve,
                // so it is reserved for the bare-alternation arm.
                if aggressive {
                    return self.alternation_uf_overapprox_unsat(&foralls, category);
                }
                None
            }
        }
    }

    /// Refute a conjunctive `∀xs. (premise(xs) ⟹ conclusion(xs))` in the
    /// multi-binder BitVector `fixpoint` family that the Int value-window path
    /// cannot reach.
    ///
    /// The recovered premise is ONLY a candidate generator. A disposable
    /// executor solves it at fresh BitVector constants and supplies concrete
    /// binder values `k`. We then substitute those literals into the WHOLE
    /// universal body and independently ground-solve `body(k)`. The premise is
    /// never asserted into the proof problem.
    ///
    /// SOUNDNESS. [`Self::forall_ids_in_conjunctive_position`] establishes that
    /// the original problem entails this universal, hence it entails every
    /// concrete instance `body(k)`. Therefore a definitive standalone UNSAT for
    /// `body(k)` proves the original problem UNSAT. Candidate quality is not a
    /// soundness surface: a mistaken De Morgan partition, a shadowed
    /// builtin-looking symbol, or an underspecified operation can at worst
    /// produce an unhelpful `k` whose whole-body verification is SAT/Unknown.
    /// Restricting binders to fixed-width BitVectors and Bool makes every
    /// candidate value exactly materializable as a model-independent literal.
    ///
    /// Both solves use fresh executors over cloned contexts. This is
    /// load-bearing: the old in-place probe changed quantified/QF routing state,
    /// invalidated proof/core provenance while registering constants, and leaked
    /// those registrations into later checks.
    fn premise_forced_binder_refutation(
        &mut self,
        foralls: &[TermId],
        snapshot: &[TermId],
    ) -> Option<Result<SolveResult>> {
        // Industrial UFBV routinely exceeds 100k terms: of the 12 wintersteiger
        // `fixpoint` wrong-SATs found by the 2026-07-25 corpus scoreboard, four
        // tripped this cap alone (ethernet-1 101,710; cache-coherence-3-1
        // 102,105; cache-coherence-3-2 252,741; pi-bus-2 310,022) — barely, in
        // two cases. The cap bounds sub-solve WORK, not soundness: the probe
        // returns UNSAT only after independently ground-solving the whole
        // substituted body at concrete literals, so a wider admission can add
        // decided UNSATs or waste time, never a wrong answer.
        const MAX_QPF_CONTEXT_TERMS: usize = 500_000;
        if self.ctx.terms.len() > MAX_QPF_CONTEXT_TERMS || !self.qpf_probe_preflight() {
            return None;
        }
        let _export_suppression = Self::suppress_bv_cnf_export_for_internal_checks();
        let conjunctive = self.forall_ids_in_conjunctive_position(snapshot);
        'quantifier: for &q in foralls {
            if !conjunctive.contains(&q) {
                continue;
            }
            let TermData::Forall(vars, body, _) = self.ctx.terms.get(q).clone() else {
                continue;
            };
            if vars.is_empty()
                || vars
                    .iter()
                    // Bool is admitted alongside fixed-width BitVec: the
                    // soundness argument in this function's doc comment is
                    // "every candidate value is exactly materializable as a
                    // model-independent literal", and `pin_eval_const_for_sort`
                    // already materializes `Sort::Bool` exactly (two values).
                    // Excluding it was stricter than its own justification and
                    // lost 9 of the 12 UFBV wrong-SATs before premise recovery
                    // was even attempted.
                    .any(|(_, sort)| {
                        !matches!(sort, ay_core::Sort::BitVec(_) | ay_core::Sort::Bool)
                    })
                || contains_quantifier(&self.ctx.terms, body)
            {
                continue;
            }
            let Some(premise) = self.forall_premise_candidate(body) else {
                continue;
            };
            if contains_quantifier(&self.ctx.terms, premise) {
                continue;
            }
            if !self.qpf_probe_preflight() {
                return None;
            }

            let candidate_ctx = self.ctx.clone();
            let mut candidate = self.qpf_probe_executor(candidate_ctx, 1000);
            if candidate
                .ctx
                .process_command(&ay_frontend::Command::ResetAssertions)
                .is_err()
            {
                continue;
            }
            let mut subst: HashMap<String, TermId> = HashMap::default();
            let mut fresh_terms = Vec::with_capacity(vars.len());
            let mut fresh_names = Vec::with_capacity(vars.len());
            let mut fresh_ok = true;
            for (name, sort) in &vars {
                let c = candidate.ctx.terms.mk_fresh_var("__ay_qpf", sort.clone());
                let cname = match candidate.ctx.terms.get(c) {
                    TermData::Var(n, _) => n.clone(),
                    _ => {
                        fresh_ok = false;
                        break;
                    }
                };
                candidate
                    .ctx
                    .register_native_global_symbol(cname.clone(), c, sort.clone());
                subst.insert(name.clone(), c);
                fresh_terms.push(c);
                fresh_names.push(cname);
            }
            if !fresh_ok || subst.len() != vars.len() {
                continue;
            }

            let premise_c = crate::ematching::subst_vars(&mut candidate.ctx.terms, premise, &subst);
            candidate.ctx.assertions.push(premise_c);
            if !matches!(candidate.check_sat(), Ok(SolveResult::Sat)) {
                continue;
            }
            let Some(model) = candidate.last_model.as_ref() else {
                continue;
            };
            let witness_values = {
                fresh_terms
                    .iter()
                    .map(|&term| candidate.evaluate_term(model, term))
                    .collect::<Vec<_>>()
            };

            let mut literal_subst: HashMap<String, TermId> = HashMap::default();
            for ((name, sort), value) in vars.iter().zip(&witness_values) {
                let Some(literal) = pin_eval_const_for_sort(&mut candidate.ctx.terms, sort, value)
                else {
                    continue 'quantifier;
                };
                literal_subst.insert(name.clone(), literal);
            }
            if literal_subst.len() != vars.len() {
                continue;
            }
            let body_k =
                crate::ematching::subst_vars(&mut candidate.ctx.terms, body, &literal_subst);
            if contains_quantifier(&candidate.ctx.terms, body_k) {
                continue;
            }

            if candidate
                .ctx
                .process_command(&ay_frontend::Command::ResetAssertions)
                .is_err()
            {
                continue;
            }
            candidate.ctx.remove_symbols(&fresh_names);
            let verifier_ctx = std::mem::take(&mut candidate.ctx);
            drop(candidate);
            if !self.qpf_probe_preflight() {
                return None;
            }
            let mut verifier = self.qpf_probe_executor(verifier_ctx, 2000);
            verifier.ctx.assertions.push(body_k);
            if matches!(verifier.check_sat(), Ok(SolveResult::Unsat(_))) {
                return Some(Ok(SolveResult::unsat()));
            }
        }
        None
    }

    /// Decline a disposable deep-context probe before it can breach the
    /// caller's deadline, interrupt, or memory envelope.
    ///
    /// The 50% checks are predictive: cloning the context roughly doubles its
    /// term/parser footprint. A term-count cap alone does not bound parsed AST,
    /// symbol, or string storage, so waiting until after `Context::clone` can
    /// already have crossed the process ceiling.
    fn qpf_probe_preflight(&self) -> bool {
        if self.external_stop_reason().is_some()
            || ay_core::TermStore::global_memory_exceeded()
            || ay_sys::process_memory_exceeded_at_percent(50)
            || crate::memory::memory_exceeded(self.memory_limit())
        {
            return false;
        }
        if let Some(limit) = self.memory_limit() {
            let current = crate::memory::current_memory_bytes();
            if current > 0 && current > limit / 2 {
                return false;
            }
        }
        self.ctx.terms.true_memory_bytes() <= ay_core::TermStore::per_engine_budget() / 2
    }

    /// Heuristically recover a premise candidate from a universal body.
    ///
    /// `(=> premise _)` yields `premise` directly. A body normalized to De
    /// Morgan disjunctive form `(=> (and p₁ … pₖ) C)` = `(or C (not p₁) … (not
    /// pₖ))` yields the FULL premise `(and p₁ … pₖ)` — every negated disjunct is
    /// a premise conjunct. (Grabbing only the first `(not p₁)` under-pins the
    /// binders — the SSA chain leaves later binders free and the instance is
    /// vacuously SAT.)
    ///
    /// `term_mentions_completable_uf` is deliberately an operational,
    /// name-oriented completion classifier, not a semantic partition oracle.
    /// Mispartitioning is harmless here because this term only proposes concrete
    /// binder values; [`Self::premise_forced_binder_refutation`] verifies the
    /// Probe-local: does `term` mention a user-DECLARED function symbol?
    ///
    /// Replaces `term_mentions_completable_uf` when `forall_premise_candidate`
    /// decides which `or` disjuncts form the CONCLUSION rather than premise
    /// conjuncts. That predicate bottoms out in
    /// `is_mbqi_completable_uf_symbol`, a hardcoded exclusion list plus
    /// `!name.starts_with("bv")`. SMT-LIB's structural bit-vector operators are
    /// named `concat`, `extract`, `zero_extend`, `sign_extend`, `rotate_left`,
    /// `rotate_right` and `repeat` — none of which start with `bv` — so every
    /// one was misread as a user UF. A premise conjunct mentioning one was then
    /// booked as conclusion and discarded, the binders it pins stayed free, the
    /// disposable candidate solve returned an arbitrary value for them, the
    /// substituted body was vacuously SAT on a false premise, and the probe
    /// returned None. That is how small-synabs-fixpoint-2/3/9 were lost: their
    /// `ite` conditions read `(= ((_ zero_extend 26) v) (_ bvN 32))`.
    ///
    /// It also failed in the other direction — a genuine user UF whose name
    /// happens to start with `bv` was not recognised as a UF at all.
    ///
    /// This asks the semantic question instead: is the head a user-declared
    /// symbol of arity > 0, per `ctx.symbol_iter()` — the same source
    /// `quantified_conjunct_defer_eligible` consults. Deliberately probe-local:
    /// `is_mbqi_completable_uf_symbol` is read by several other MBQI
    /// certificates and by `quantifier_consumer_ground_assertion_supported_by_completion`,
    /// so changing it globally would perturb quantified classification across
    /// every division and needs its own differential run.
    fn disjunct_mentions_declared_uf(&self, term: TermId) -> bool {
        use ay_core::kani_compat::DetHashSet as HashSet;
        let declared: HashSet<String> = self
            .ctx
            .symbol_iter()
            .filter(|(_, info)| !info.arg_sorts.is_empty())
            .map(|(name, info)| self.ctx.symbol_identity_name(name, info).to_string())
            .collect();
        let mut visited: HashSet<TermId> = HashSet::default();
        let mut stack = vec![term];
        while let Some(t) = stack.pop() {
            if !visited.insert(t) {
                continue;
            }
            match self.ctx.terms.get(t) {
                TermData::App(sym, args) => {
                    if !args.is_empty() && declared.contains(sym.name()) {
                        return true;
                    }
                    stack.extend(args.iter().copied());
                }
                TermData::Not(inner) => stack.push(*inner),
                TermData::Ite(c, th, el) => {
                    stack.push(*c);
                    stack.push(*th);
                    stack.push(*el);
                }
                TermData::Let(bindings, body) => {
                    for (_, v) in bindings {
                        stack.push(*v);
                    }
                    stack.push(*body);
                }
                TermData::Forall(_, body, _) | TermData::Exists(_, body, _) => stack.push(*body),
                _ => {}
            }
        }
        false
    }

    /// whole universal instance and never treats this candidate as an asserted
    /// fact.
    fn forall_premise_candidate(&mut self, body: TermId) -> Option<TermId> {
        match self.ctx.terms.get(body).clone() {
            TermData::App(sym, args) if sym.name() == "=>" && args.len() == 2 => Some(args[0]),
            TermData::App(sym, args) if sym.name() == "or" && args.len() >= 2 => {
                // `(or C (not p₁) … (not pₖ))` = `(=> (and p₁ … pₖ) C)` where the
                // conclusion `C` carries the UF applications and each premise
                // conjunct `pᵢ` is UF-FREE (a binder equality). Collect the
                // apparently UF-free disjuncts (robust to how preprocessing renders each
                // `(not pᵢ)` — `Not`, `distinct`, a folded comparison, …) and
                // NEGATE each to recover `pᵢ`.
                let mut conjs: Vec<TermId> = Vec::new();
                let mut has_uf_disjunct = false;
                for &d in &args {
                    if self.disjunct_mentions_declared_uf(d) {
                        has_uf_disjunct = true;
                    } else {
                        conjs.push(self.ctx.terms.mk_not(d));
                    }
                }
                // Require a UF-bearing conclusion disjunct (else this is a pure
                // universal handled elsewhere) and at least one premise conjunct.
                if !has_uf_disjunct || conjs.is_empty() {
                    return None;
                }
                match conjs.len() {
                    1 => Some(conjs[0]),
                    _ => Some(self.ctx.terms.mk_and(conjs)),
                }
            }
            _ => None,
        }
    }

    /// Build an isolated probe executor over `ctx` under the caller's resource
    /// envelope. The caller owns the cloned context, so solving may mutate every
    /// executor/context bookkeeping field without touching the outer query.
    fn qpf_probe_executor(&self, ctx: ay_frontend::Context, budget_ms: u64) -> Executor {
        let mut probe = Executor::new();
        probe.ctx = ctx;
        probe.set_verification_level(self.verification_level());
        probe.set_self_check(self.self_check());
        probe.set_learned_clause_limit(self.learned_clause_limit());
        probe.set_clause_db_bytes_limit(self.clause_db_bytes_limit());
        probe.set_resource_limit(self.resource_limit());
        probe.set_decision_limit(self.decision_limit());
        probe.set_ground_budget_enabled(self.ground_budget_enabled());
        probe.set_memory_limit(self.memory_limit());
        let tight = ay_core::time::Instant::now() + std::time::Duration::from_millis(budget_ms);
        let bounded = match self.solve_deadline.get() {
            Some(d) if d < tight => Some(d),
            _ => Some(tight),
        };
        probe.set_solve_controls(self.solve_interrupt.clone(), bounded);
        probe
    }

    /// Over-approximate each alternation `forall` to a NECESSARY condition on the
    /// universal alone and decide THAT with the ordinary quantifier procedure.
    ///
    /// Replace every existential-witness-dependent (Skolem-function) atom in the
    /// body with its polarity-permissive truth value, yielding `C'` with
    /// `(exists q1. body) => C'`. Hence `(forall q0 (exists q1. body)) =>
    /// (forall q0. C')`, so if `(forall q0. C')` is UNSAT the original is UNSAT.
    /// This catches whole-range / unbounded contradictions a value window cannot
    /// (e.g. `f(1) <= q0` required for ALL q0). Sound: it only ever returns UNSAT,
    /// and the differential fuzz validates no wrong-unsat is introduced.
    fn alternation_overapprox_unsat(
        &mut self,
        foralls: &[TermId],
        category: LogicCategory,
    ) -> Option<Result<SolveResult>> {
        for &q in foralls {
            let TermData::Forall(vars, body, triggers) = self.ctx.terms.get(q).clone() else {
                continue;
            };
            if vars.len() != 1 || contains_quantifier(&self.ctx.terms, body) {
                continue;
            }
            let Some(cprime) = self.abstract_skolem_atoms(body, true) else {
                continue;
            };
            if cprime == body {
                continue; // no Skolem atom abstracted — nothing gained
            }
            let new_forall =
                self.ctx
                    .terms
                    .mk_forall_with_triggers(vars.clone(), cprime, triggers.clone());

            let saved_assertions = std::mem::replace(&mut self.ctx.assertions, vec![new_forall]);
            let saved_theory_state = self.incr_theory_state.take();
            let saved_bv_state = self.incr_bv_state.take();
            let saved_model = self.last_model.clone();
            let saved_validated = self.last_model_validated;
            let saved_reason = self.last_unknown_reason;
            let saved_deadline = self.solve_deadline.get();
            let tight = ay_core::time::Instant::now() + std::time::Duration::from_millis(300);
            self.set_deadline(match saved_deadline {
                Some(d) if d < tight => Some(d),
                _ => Some(tight),
            });
            let _ = category;
            let res = self.solve_current_assertions_with_quantifier_support();
            self.set_deadline(saved_deadline);
            self.ctx.assertions = saved_assertions;
            self.incr_theory_state = saved_theory_state;
            self.incr_bv_state = saved_bv_state;
            if matches!(res, Ok(SolveResult::Unsat(_))) {
                return Some(Ok(SolveResult::unsat()));
            }
            self.last_model = saved_model;
            self.last_model_validated = saved_validated;
            self.last_unknown_reason = saved_reason;
        }
        None
    }

    /// Over-approximate each alternation `forall` by weakening only the atoms that
    /// apply an uninterpreted/non-arith function to a term mentioning the BINDER,
    /// while keeping binder-INDEPENDENT UF terms intact as opaque constants.
    ///
    /// A binder-dependent application (`(f (* 2 q0))`, a skolemized inner
    /// existential, …) is a value the model can choose freely per binder point, so
    /// replacing its enclosing atom with the polarity-permissive constant only
    /// WEAKENS the body (`body => C'`). A binder-independent application (`(f 1)`)
    /// is a single fixed unknown — keeping it lets the universal procedure refute
    /// `(forall q0 (or (< q0 2) (<= (- q0 1) (f 1))))` (no value of `f(1)` bounds
    /// `q0 - 1` for all `q0`). Hence `(forall q0. body) => (forall q0. C')` and an
    /// UNSAT `C'` refutes the original. Distinct from `alternation_overapprox_unsat`
    /// (which abstracts EVERY Skolem atom, including binder-independent ones, and so
    /// would erase the `(f 1)` constraint here). Sound: only ever returns UNSAT.
    fn alternation_uf_overapprox_unsat(
        &mut self,
        foralls: &[TermId],
        category: LogicCategory,
    ) -> Option<Result<SolveResult>> {
        let _ = category;
        for &q in foralls {
            let TermData::Forall(vars, body, triggers) = self.ctx.terms.get(q).clone() else {
                continue;
            };
            if vars.len() != 1 || contains_quantifier(&self.ctx.terms, body) {
                continue;
            }
            let bound: ay_core::kani_compat::DetHashSet<String> =
                vars.iter().map(|(n, _)| n.clone()).collect();
            let Some(cprime) = self.abstract_binder_dependent_uf_atoms(body, true, &bound) else {
                continue;
            };
            if cprime == body {
                continue; // nothing weakened — no gain
            }
            let new_forall =
                self.ctx
                    .terms
                    .mk_forall_with_triggers(vars.clone(), cprime, triggers.clone());

            let saved_assertions = std::mem::replace(&mut self.ctx.assertions, vec![new_forall]);
            let saved_theory_state = self.incr_theory_state.take();
            let saved_bv_state = self.incr_bv_state.take();
            let saved_model = self.last_model.clone();
            let saved_validated = self.last_model_validated;
            let saved_reason = self.last_unknown_reason;
            let saved_deadline = self.solve_deadline.get();
            let tight = ay_core::time::Instant::now() + std::time::Duration::from_millis(300);
            self.set_deadline(match saved_deadline {
                Some(d) if d < tight => Some(d),
                _ => Some(tight),
            });
            let res = self.solve_current_assertions_with_quantifier_support();
            self.set_deadline(saved_deadline);
            self.ctx.assertions = saved_assertions;
            self.incr_theory_state = saved_theory_state;
            self.incr_bv_state = saved_bv_state;
            if matches!(res, Ok(SolveResult::Unsat(_))) {
                return Some(Ok(SolveResult::unsat()));
            }
            self.last_model = saved_model;
            self.last_model_validated = saved_validated;
            self.last_unknown_reason = saved_reason;
        }
        None
    }

    /// Polarity-tracking NNF weakening: replace every atom that applies an
    /// uninterpreted/non-arith function to a BINDER-dependent subterm with its
    /// polarity-permissive constant (`true` positive, `false` negative). Atoms over
    /// binder-INDEPENDENT UF terms are kept verbatim. Returns `None` on a
    /// non-monotone Ite condition (a condition mentioning such an atom).
    fn abstract_binder_dependent_uf_atoms(
        &mut self,
        term: TermId,
        positive: bool,
        bound: &ay_core::kani_compat::DetHashSet<String>,
    ) -> Option<TermId> {
        match self.ctx.terms.get(term).clone() {
            TermData::Not(inner) => {
                let a = self.abstract_binder_dependent_uf_atoms(inner, !positive, bound)?;
                Some(self.ctx.terms.mk_not(a))
            }
            TermData::App(sym, args) if sym.name() == "and" => {
                let mut new = Vec::with_capacity(args.len());
                for a in args {
                    new.push(self.abstract_binder_dependent_uf_atoms(a, positive, bound)?);
                }
                Some(self.ctx.terms.mk_and(new))
            }
            TermData::App(sym, args) if sym.name() == "or" => {
                let mut new = Vec::with_capacity(args.len());
                for a in args {
                    new.push(self.abstract_binder_dependent_uf_atoms(a, positive, bound)?);
                }
                Some(self.ctx.terms.mk_or(new))
            }
            TermData::App(sym, args) if sym.name() == "=>" && args.len() == 2 => {
                let a = self.abstract_binder_dependent_uf_atoms(args[0], !positive, bound)?;
                let b = self.abstract_binder_dependent_uf_atoms(args[1], positive, bound)?;
                Some(self.ctx.terms.mk_implies(a, b))
            }
            TermData::Ite(c, t, e) => {
                if self.term_mentions_uninterpreted_of_bound_var(c, bound) {
                    return None; // non-monotone condition
                }
                let t2 = self.abstract_binder_dependent_uf_atoms(t, positive, bound)?;
                let e2 = self.abstract_binder_dependent_uf_atoms(e, positive, bound)?;
                Some(self.ctx.terms.mk_ite(c, t2, e2))
            }
            _ => {
                if self.term_mentions_uninterpreted_of_bound_var(term, bound) {
                    Some(self.ctx.terms.mk_bool(positive))
                } else {
                    Some(term)
                }
            }
        }
    }

    /// Decide `(forall q1 (exists q2 <body>))`-shaped alternations EXACTLY by
    /// Fourier-Motzkin projection of the (skolemized) existential witness.
    ///
    /// For a single-`Int`-binder `forall` whose body is a CONJUNCTION of linear
    /// atoms in which a single Skolem application `sk(q1)` occurs only with unit
    /// coefficient, eliminate `sk(q1)` exactly: each `sk >= L` paired with each
    /// `sk <= U` yields `L <= U`, plus the sk-free atoms. The projected
    /// `(forall q1. proj)` is EQUISATISFIABLE to the original (unit-coefficient FM
    /// is exact over the integers), so its UNSAT is the original's UNSAT — and it
    /// is a pure-arithmetic universal the ordinary procedure decides (e.g.
    /// `(forall q1 (exists q2 (and (<= q2 (+ c0 1)) (>= q2 (- q1)))))` projects to
    /// `(forall q1. (- q1) <= (+ c0 1))`, UNSAT). Returns `Some(Ok(unsat))` only on
    /// a definitive refutation.
    fn alternation_project_witness_unsat(
        &mut self,
        foralls: &[TermId],
        category: LogicCategory,
        aggressive: bool,
    ) -> Option<Result<SolveResult>> {
        for &q in foralls {
            let TermData::Forall(vars, body, trig) = self.ctx.terms.get(q).clone() else {
                continue;
            };
            if vars.len() != 1 || contains_quantifier(&self.ctx.terms, body) {
                continue;
            }
            // Try the EXACT single-Skolem projection first (base mode); in
            // aggressive mode fall back to the multi-Skolem relaxation (drops the
            // atoms it cannot FM, which only enlarges the existential witness set,
            // so a refuted projection still refutes the original).
            let Some(proj_body) = self
                .project_single_skolem(body)
                .or_else(|| self.project_single_skolem_dnf(body))
                .or_else(|| {
                    if aggressive {
                        self.project_multi_skolem(body)
                    } else {
                        None
                    }
                })
            else {
                continue;
            };
            let proj_forall =
                self.ctx
                    .terms
                    .mk_forall_with_triggers(vars.clone(), proj_body, trig.clone());

            let saved_assertions = std::mem::replace(&mut self.ctx.assertions, vec![proj_forall]);
            let saved_theory_state = self.incr_theory_state.take();
            let saved_bv_state = self.incr_bv_state.take();
            let saved_model = self.last_model.clone();
            let saved_validated = self.last_model_validated;
            let saved_reason = self.last_unknown_reason;
            let saved_deadline = self.solve_deadline.get();
            let tight = ay_core::time::Instant::now() + std::time::Duration::from_millis(300);
            self.set_deadline(match saved_deadline {
                Some(d) if d < tight => Some(d),
                _ => Some(tight),
            });
            let _ = category;
            let res = self.solve_current_assertions_with_quantifier_support();
            self.set_deadline(saved_deadline);
            self.ctx.assertions = saved_assertions;
            self.incr_theory_state = saved_theory_state;
            self.incr_bv_state = saved_bv_state;
            if matches!(res, Ok(SolveResult::Unsat(_))) {
                return Some(Ok(SolveResult::unsat()));
            }
            self.last_model = saved_model;
            self.last_model_validated = saved_validated;
            self.last_unknown_reason = saved_reason;

            // Per-conjunct isolated refutation: `(forall q (and c1..cn))` is
            // equivalent to `AND_i (forall q ci)`, so if ANY isolated `(forall q
            // ci)` is UNSAT the whole projection is UNSAT. This sidesteps a
            // downstream gap where the multi-conjunct universal (a binder-free
            // conjunct sharing a free var with the binder-dependent one) is
            // returned `unknown` even though one conjunct alone refutes. Sound:
            // isolation only removes constraints, never adds satisfiability, and we
            // act ONLY on a definitive isolated UNSAT.
            if aggressive {
                let mut conjs = Vec::new();
                collect_and_conjuncts(&self.ctx.terms, proj_body, &mut conjs);
                if conjs.len() >= 2 {
                    for ci in conjs {
                        let fi =
                            self.ctx
                                .terms
                                .mk_forall_with_triggers(vars.clone(), ci, trig.clone());
                        let sa = std::mem::replace(&mut self.ctx.assertions, vec![fi]);
                        let sts = self.incr_theory_state.take();
                        let sbv = self.incr_bv_state.take();
                        let sm = self.last_model.clone();
                        let sv = self.last_model_validated;
                        let sr = self.last_unknown_reason;
                        let sd = self.solve_deadline.get();
                        let tight2 =
                            ay_core::time::Instant::now() + std::time::Duration::from_millis(300);
                        self.set_deadline(match sd {
                            Some(d) if d < tight2 => Some(d),
                            _ => Some(tight2),
                        });
                        let ri = self.solve_current_assertions_with_quantifier_support();
                        self.set_deadline(sd);
                        self.ctx.assertions = sa;
                        self.incr_theory_state = sts;
                        self.incr_bv_state = sbv;
                        if matches!(ri, Ok(SolveResult::Unsat(_))) {
                            return Some(Ok(SolveResult::unsat()));
                        }
                        self.last_model = sm;
                        self.last_model_validated = sv;
                        self.last_unknown_reason = sr;
                    }
                }
            }
        }
        None
    }

    /// Project a single unit-coefficient Skolem application out of a conjunctive
    /// `Int` body by Fourier-Motzkin. Returns `None` when the shape is outside the
    /// exact fragment (not a conjunction of linear atoms, multiple Skolem
    /// applications, a non-unit/non-linear coefficient, or a Skolem application
    /// inside an uninterpreted/non-arith term).
    fn project_single_skolem(&mut self, body: TermId) -> Option<TermId> {
        // Exactly one distinct Skolem application in the body.
        let mut sk_apps: Vec<TermId> = Vec::new();
        self.collect_skolem_apps(body, &mut sk_apps);
        if sk_apps.len() != 1 {
            return None;
        }
        let sk = sk_apps[0];

        let mut conjuncts = Vec::new();
        collect_and_conjuncts(&self.ctx.terms, body, &mut conjuncts);
        if conjuncts.is_empty() {
            return None;
        }

        let zero = self.ctx.terms.mk_int(num_bigint::BigInt::from(0));
        let one = self.ctx.terms.mk_int(num_bigint::BigInt::from(1));

        let mut lowers: Vec<TermId> = Vec::new(); // sk >= L
        let mut uppers: Vec<TermId> = Vec::new(); // sk <= U
        let mut kept: Vec<TermId> = Vec::new();

        for c in conjuncts {
            // (d rel 0): rel in {>=, >, =}. Normalize each comparison.
            let (a, b, strict, is_eq) = match self.ctx.terms.get(c).clone() {
                TermData::App(sym, args) if args.len() == 2 => match sym.name() {
                    ">=" => (args[0], args[1], false, false),
                    ">" => (args[0], args[1], true, false),
                    "<=" => (args[1], args[0], false, false),
                    "<" => (args[1], args[0], true, false),
                    "=" if matches!(self.ctx.terms.sort(args[0]), ay_core::Sort::Int) => {
                        (args[0], args[1], false, true)
                    }
                    _ => {
                        // Non-(in)equality atom: keep iff sk-free, else bail.
                        if self.term_contains_id(c, sk) {
                            return None;
                        }
                        kept.push(c);
                        continue;
                    }
                },
                _ => {
                    if self.term_contains_id(c, sk) {
                        return None;
                    }
                    kept.push(c);
                    continue;
                }
            };
            // d = a - b, atom is `d (>= or >) 0` (or `= 0`).
            let d = self.ctx.terms.mk_sub(vec![a, b]);
            if !self.term_contains_id(d, sk) {
                kept.push(c);
                continue;
            }
            // SOUNDNESS (S2 disease, quantified-CE-lemma fuzz 2026-07-09): the
            // difference probe below measures a genuine linear coefficient ONLY
            // when `d` is AFFINE in `sk`. A quadratic occurrence (`sk*sk > -3`,
            // d = sk² + 3) folds to the FAKE constant coefficient 1 and turns a
            // vacuous bounded-below atom into a hard bound `sk >= -2` — the
            // projection then wrongly refutes a VALID alternation (wrong-UNSAT,
            // caught by the alternation differential fuzz). This projector
            // claims exactness, so bail out entirely.
            if self.var_under_nonarith(d, sk) {
                return None;
            }
            // coeff of sk = d[sk:=1] - d[sk:=0]; rest = d[sk:=0]; require coeff = ±1.
            let d1 = self.subst_term(d, sk, one);
            let d0 = self.subst_term(d, sk, zero);
            let coeff = self.ctx.terms.mk_sub(vec![d1, d0]);
            let coeff_val = match self.ctx.terms.get(coeff) {
                TermData::Const(ay_core::Constant::Int(n)) => n.clone(),
                _ => return None, // non-constant => sk non-linear / under UF
            };
            let rest = d0; // d = coeff*sk + rest
            if coeff_val == num_bigint::BigInt::from(1) {
                // sk + rest (>= or >) 0  =>  sk >= -rest (+1 if strict, int)
                let neg_rest = self.ctx.terms.mk_sub(vec![zero, rest]);
                let l = if strict {
                    self.ctx.terms.mk_add(vec![neg_rest, one])
                } else {
                    neg_rest
                };
                lowers.push(l);
                if is_eq {
                    uppers.push(neg_rest);
                }
            } else if coeff_val == num_bigint::BigInt::from(-1) {
                // -sk + rest (>= or >) 0  =>  sk <= rest (-1 if strict, int)
                let u = if strict {
                    self.ctx.terms.mk_sub(vec![rest, one])
                } else {
                    rest
                };
                uppers.push(u);
                if is_eq {
                    lowers.push(rest);
                }
            } else {
                return None; // non-unit coefficient: outside the exact fragment
            }
        }

        // FM: every lower bound <= every upper bound, plus kept atoms.
        let mut proj: Vec<TermId> = kept;
        for &l in &lowers {
            for &u in &uppers {
                let le = self.ctx.terms.mk_le(l, u);
                proj.push(le);
            }
        }
        if proj.is_empty() {
            return None;
        }
        Some(self.ctx.terms.mk_and(proj))
    }

    /// Exact Fourier-Motzkin projection of a SINGLE unit-coefficient `Int` Skolem
    /// application out of a CONJUNCTION of atoms (`atoms` is the implicit `and`).
    /// `atoms` may mix sk-comparison atoms (FM-eliminated) and sk-free atoms (kept
    /// verbatim). Returns the sk-free formula `≡ ∃sk. AND(atoms)`:
    ///   * `Some(true)` when the projection is unconstrained (`∃sk` always holds —
    ///     e.g. only upper bounds on `sk` and no kept atoms),
    ///   * `Some(φ)` for the exact projected formula,
    ///   * `None` when an sk-containing atom is outside the unit-coefficient linear
    ///     fragment (the caller must then bail — it cannot soundly project).
    /// Over the integers this is EXACT: each strict atom is integer-tightened
    /// (`sk+rest>0 ⟺ sk >= 1-rest`), and `∃ integer sk. l<=sk<=u ⟺ l<=u` because
    /// `l,u` are integer-valued. Used by [`project_single_skolem_dnf`].
    fn fm_project_sk_conjunction(&mut self, atoms: &[TermId], sk: TermId) -> Option<TermId> {
        let zero = self.ctx.terms.mk_int(num_bigint::BigInt::from(0));
        let one = self.ctx.terms.mk_int(num_bigint::BigInt::from(1));
        let mut lowers: Vec<TermId> = Vec::new(); // sk >= L
        let mut uppers: Vec<TermId> = Vec::new(); // sk <= U
        let mut kept: Vec<TermId> = Vec::new();
        for &c in atoms {
            let (a, b, strict, is_eq) = match self.ctx.terms.get(c).clone() {
                TermData::App(sym, args) if args.len() == 2 => match sym.name() {
                    ">=" => (args[0], args[1], false, false),
                    ">" => (args[0], args[1], true, false),
                    "<=" => (args[1], args[0], false, false),
                    "<" => (args[1], args[0], true, false),
                    "=" if matches!(self.ctx.terms.sort(args[0]), ay_core::Sort::Int) => {
                        (args[0], args[1], false, true)
                    }
                    _ => {
                        if self.term_contains_id(c, sk) {
                            return None;
                        }
                        kept.push(c);
                        continue;
                    }
                },
                _ => {
                    if self.term_contains_id(c, sk) {
                        return None;
                    }
                    kept.push(c);
                    continue;
                }
            };
            let d = self.ctx.terms.mk_sub(vec![a, b]);
            if !self.term_contains_id(d, sk) {
                kept.push(c);
                continue;
            }
            // SOUNDNESS (S2 disease): the probe needs `d` AFFINE in `sk` — a
            // quadratic occurrence folds to a fake constant coefficient and
            // manufactures a bound that wrongly refutes a valid alternation.
            // This projector claims exactness, so bail out entirely.
            if self.var_under_nonarith(d, sk) {
                return None;
            }
            let d1 = self.subst_term(d, sk, one);
            let d0 = self.subst_term(d, sk, zero);
            let coeff = self.ctx.terms.mk_sub(vec![d1, d0]);
            let coeff_val = match self.ctx.terms.get(coeff) {
                TermData::Const(ay_core::Constant::Int(n)) => n.clone(),
                _ => return None,
            };
            let rest = d0;
            if coeff_val == num_bigint::BigInt::from(1) {
                let neg_rest = self.ctx.terms.mk_sub(vec![zero, rest]);
                let l = if strict {
                    self.ctx.terms.mk_add(vec![neg_rest, one])
                } else {
                    neg_rest
                };
                lowers.push(l);
                if is_eq {
                    uppers.push(neg_rest);
                }
            } else if coeff_val == num_bigint::BigInt::from(-1) {
                let u = if strict {
                    self.ctx.terms.mk_sub(vec![rest, one])
                } else {
                    rest
                };
                uppers.push(u);
                if is_eq {
                    lowers.push(rest);
                }
            } else {
                return None;
            }
        }
        let mut proj: Vec<TermId> = kept;
        for &l in &lowers {
            for &u in &uppers {
                let le = self.ctx.terms.mk_le(l, u);
                proj.push(le);
            }
        }
        if proj.is_empty() {
            // Unconstrained: `∃sk` is satisfiable for every value of the free vars.
            return Some(self.ctx.terms.mk_bool(true));
        }
        Some(self.ctx.terms.mk_and(proj))
    }

    /// DNF-aware EXACT projection of a single unit-coefficient `Int` Skolem out of a
    /// conjunctive body in which some conjuncts are DISJUNCTIONS that mention the
    /// Skolem (which the pure-conjunctive [`project_single_skolem`] rejects). `∃sk`
    /// distributes over `∨` but not `∧`, so expand the body's sk-containing
    /// conjuncts to DNF, FM-project `sk` from each disjunct's conjunction, and OR
    /// the results:  `∃sk.(A ∧ (B∨C)) = (∃sk.A∧B) ∨ (∃sk.A∧C)`. Each disjunction's
    /// alternatives must be sk-comparison atoms or sk-free terms (deeper sk-nesting
    /// bails). EXACT (neither relaxes nor strengthens), so a refuted projection
    /// refutes the original AND it can never manufacture a wrong-UNSAT on a
    /// genuinely-SAT alternation. Bounded cross-product keeps it off the hot path.
    ///
    /// Catches the alternation wrong-sats where the existential witness must thread
    /// a DISJUNCTIVE choice (`(forall q0 (exists q1 (and (> -1 (+ q1 q0))
    /// (or (< c (- 1 q0)) (= q1 -2)))))`, UNSAT): projects to
    /// `(forall q0. (or (< c (- 1 q0)) (<= q0 0)))`, decided UNSAT.
    fn project_single_skolem_dnf(&mut self, body: TermId) -> Option<TermId> {
        let mut sk_apps: Vec<TermId> = Vec::new();
        self.collect_skolem_apps(body, &mut sk_apps);
        if sk_apps.len() != 1 {
            return None;
        }
        let sk = sk_apps[0];

        let mut conjuncts = Vec::new();
        collect_and_conjuncts(&self.ctx.terms, body, &mut conjuncts);
        if conjuncts.is_empty() {
            return None;
        }

        // Partition: sk-free conjuncts (kept), sk-comparison atoms, sk-containing
        // disjunctions (each alternative an sk-comparison atom or sk-free term).
        let mut kept_free: Vec<TermId> = Vec::new();
        let mut sk_atoms: Vec<TermId> = Vec::new();
        let mut disjunctions: Vec<Vec<TermId>> = Vec::new();
        for c in conjuncts {
            if !self.term_contains_id(c, sk) {
                kept_free.push(c);
                continue;
            }
            if self.is_int_comparison_atom(c) {
                sk_atoms.push(c);
                continue;
            }
            match self.ctx.terms.get(c).clone() {
                TermData::App(sym, args) if sym.name() == "or" => {
                    // Every alternative that mentions sk must be a plain
                    // comparison atom (no deeper nesting) so the cross-product
                    // FM stays exact; sk-free alternatives are kept verbatim.
                    for &a in &args {
                        if self.term_contains_id(a, sk) && !self.is_int_comparison_atom(a) {
                            return None;
                        }
                    }
                    disjunctions.push(args);
                }
                _ => return None,
            }
        }
        // A pure conjunction (no disjunction) is the exact-projection job of
        // `project_single_skolem`; only act when there is a real DNF to expand.
        if disjunctions.is_empty() {
            return None;
        }

        // Bound the cross-product.
        let mut combos = 1usize;
        for d in &disjunctions {
            combos = combos.saturating_mul(d.len());
        }
        if combos == 0 || combos > 32 {
            return None;
        }

        // Odometer over the disjunctions: each combination picks one alternative
        // per disjunction, joins with the shared sk-atoms, and FM-projects sk.
        let mut projected: Vec<TermId> = Vec::new();
        let mut idx = vec![0usize; disjunctions.len()];
        loop {
            let mut atoms = sk_atoms.clone();
            for (di, &ai) in idx.iter().enumerate() {
                atoms.push(disjunctions[di][ai]);
            }
            let proj = self.fm_project_sk_conjunction(&atoms, sk)?;
            // A `true` disjunct makes `∃sk.body` hold for all q0 -> nothing to
            // refute; abandon (the universal is satisfiable on this branch).
            if matches!(
                self.ctx.terms.get(proj),
                TermData::Const(ay_core::Constant::Bool(true))
            ) {
                return None;
            }
            projected.push(proj);
            // Advance the odometer.
            let mut k = 0;
            loop {
                if k == idx.len() {
                    // Wrapped past the most-significant digit: done.
                    let or_term = if projected.len() == 1 {
                        projected[0]
                    } else {
                        self.ctx.terms.mk_or(projected.clone())
                    };
                    let mut out = kept_free;
                    out.push(or_term);
                    return Some(self.ctx.terms.mk_and(out));
                }
                idx[k] += 1;
                if idx[k] < disjunctions[k].len() {
                    break;
                }
                idx[k] = 0;
                k += 1;
            }
        }
    }

    /// True iff `t` is a binary `Int` (in)equality comparison atom (`>=,>,<=,<,=`).
    fn is_int_comparison_atom(&self, t: TermId) -> bool {
        match self.ctx.terms.get(t) {
            TermData::App(sym, args) if args.len() == 2 => match sym.name() {
                ">=" | ">" | "<=" | "<" => true,
                "=" => matches!(self.ctx.terms.sort(args[0]), ay_core::Sort::Int),
                _ => false,
            },
            _ => false,
        }
    }

    /// Project ALL Skolem applications out of a conjunctive `Int` body by ITERATED
    /// Fourier-Motzkin, DROPPING any conjunct outside the unit-coefficient linear
    /// fragment (a disequality, a Skolem under a UF, a non-unit coefficient). Each
    /// drop only RELAXES the existential witness — it removes a constraint the
    /// witness must satisfy — so `(exists sk1..skn. body) => proj`, hence
    /// `(forall q (exists sk. body)) => (forall q. proj)` and an UNSAT projection
    /// refutes the original (relaxation is one-directional: sound for UNSAT only).
    /// Handles the multi-witness `(forall q (exists q1 q2 ...))` shapes the exact
    /// single-Skolem projection cannot, e.g. `(forall q0 (exists q1 q2 (and
    /// (< q1 (* 2 c0)) (<= 1 (+ q0 q1)) (< 2 (+ c0 q2)) (distinct ...))))` projects
    /// (after dropping the disequality and FM-eliminating q1,q2) to
    /// `(forall q0. (>= (+ (* 2 c0) q0 -2) 0))`, UNSAT.
    /// Repeatedly substitute any Skolem application uniquely DETERMINED by an
    /// equality conjunct `(= L R)` (over Int, where the Skolem occurs with unit
    /// coefficient so `sk = -rest`/`sk = rest`) by its forced value throughout the
    /// body. Exact: the existential witness is pinned by the equality, so this is
    /// neither a relaxation nor a strengthening. Iterates so a chain of equalities
    /// resolves. Bounded iteration count (each step removes one Skolem occurrence).
    fn substitute_equality_determined_skolems(&mut self, body: TermId) -> TermId {
        let zero = self.ctx.terms.mk_int(num_bigint::BigInt::from(0));
        let one = self.ctx.terms.mk_int(num_bigint::BigInt::from(1));
        let mut cur = body;
        // At most one Skolem is removed per pass; cap passes by the Skolem count.
        let mut sk_all: Vec<TermId> = Vec::new();
        self.collect_skolem_apps(cur, &mut sk_all);
        let max_passes = sk_all.len().min(8);
        for _ in 0..max_passes {
            let mut conjuncts = Vec::new();
            collect_and_conjuncts(&self.ctx.terms, cur, &mut conjuncts);
            let mut substituted = false;
            'outer: for c in conjuncts {
                let TermData::App(sym, args) = self.ctx.terms.get(c).clone() else {
                    continue;
                };
                if sym.name() != "=" || args.len() != 2 {
                    continue;
                }
                if !matches!(self.ctx.terms.sort(args[0]), ay_core::Sort::Int) {
                    continue;
                }
                let d = self.ctx.terms.mk_sub(vec![args[0], args[1]]); // L - R
                let mut local_sk: Vec<TermId> = Vec::new();
                self.collect_skolem_apps(d, &mut local_sk);
                for sk in local_sk {
                    // SOUNDNESS (S2 disease): an equality NON-AFFINE in `sk`
                    // (`sk*sk = x`) does NOT determine `sk`; the difference
                    // probe would fold to a fake unit coefficient and
                    // "solve" `sk := x`, corrupting the (claimed-exact)
                    // substitution. Skip such equalities.
                    if self.var_under_nonarith(d, sk) {
                        continue;
                    }
                    // coeff of sk in d, and rest = d[sk:=0] (skolem-free in sk).
                    let d1 = self.subst_term(d, sk, one);
                    let d0 = self.subst_term(d, sk, zero);
                    let coeff = self.ctx.terms.mk_sub(vec![d1, d0]);
                    let cv = match self.ctx.terms.get(coeff) {
                        TermData::Const(ay_core::Constant::Int(n)) => n.clone(),
                        _ => continue, // sk nonlinear / under UF in this equality
                    };
                    let rest = d0; // d = coeff*sk + rest, atom is d = 0
                    let solved = if cv == num_bigint::BigInt::from(1) {
                        self.ctx.terms.mk_sub(vec![zero, rest]) // sk = -rest
                    } else if cv == num_bigint::BigInt::from(-1) {
                        rest // sk = rest
                    } else {
                        continue; // non-unit: not exactly solvable over the integers
                    };
                    // `solved` is built from d[sk:=0], hence free of `sk`; substitute
                    // the forced value for every occurrence of the witness.
                    cur = self.subst_term(cur, sk, solved);
                    substituted = true;
                    break 'outer;
                }
            }
            if !substituted {
                break;
            }
        }
        cur
    }

    fn project_multi_skolem(&mut self, body: TermId) -> Option<TermId> {
        const GE: u8 = 0; // d >= 0
        const GT: u8 = 1; // d > 0
        const EQ: u8 = 2; // d = 0

        // Phase 0: exactly eliminate any witness UNIQUELY DETERMINED by an
        // equality conjunct (`sk = T`). Substitution is exact (the witness is
        // forced), so it neither over- nor under-approximates AND it sidesteps the
        // FM fragment limits: a determined `sk` carried into a non-unit atom
        // (`2*sk <= ...`) or a disequality becomes a pure binder constraint instead
        // of being dropped. Decides the equality-determined family, e.g.
        // `(forall q0 (exists q1 q2 (and (= (- q0 3) (+ q2 c0)) (<= (* 2 q2) (+ q0
        // 3)) (> (+ q2 q0) (+ q1 q2)))))`: q2 is forced to q0-3-c0, the non-unit
        // bound becomes `2*(q0-3-c0) <= q0+3`, and q1 then FM-eliminates freely.
        let body = self.substitute_equality_determined_skolems(body);

        let mut sk_apps: Vec<TermId> = Vec::new();
        self.collect_skolem_apps(body, &mut sk_apps);
        if sk_apps.is_empty() {
            // Every witness was exactly eliminated by equality substitution; the
            // residual is a pure (skolem-free) universal body the ordinary
            // procedure decides.
            return Some(body);
        }
        let mut conjuncts = Vec::new();
        collect_and_conjuncts(&self.ctx.terms, body, &mut conjuncts);
        if conjuncts.is_empty() {
            return None;
        }
        let zero = self.ctx.terms.mk_int(num_bigint::BigInt::from(0));
        let one = self.ctx.terms.mk_int(num_bigint::BigInt::from(1));

        // (d, kind) constraints; skolem-free non-linear conjuncts kept verbatim
        // (they constrain the binder), skolem-bearing non-fragment ones dropped.
        let mut cons: Vec<(TermId, u8)> = Vec::new();
        let mut kept_raw: Vec<TermId> = Vec::new();
        for c in conjuncts {
            let parsed = match self.ctx.terms.get(c).clone() {
                TermData::App(sym, args) if args.len() == 2 => match sym.name() {
                    ">=" => Some((self.ctx.terms.mk_sub(vec![args[0], args[1]]), GE)),
                    ">" => Some((self.ctx.terms.mk_sub(vec![args[0], args[1]]), GT)),
                    "<=" => Some((self.ctx.terms.mk_sub(vec![args[1], args[0]]), GE)),
                    "<" => Some((self.ctx.terms.mk_sub(vec![args[1], args[0]]), GT)),
                    "=" if matches!(self.ctx.terms.sort(args[0]), ay_core::Sort::Int) => {
                        Some((self.ctx.terms.mk_sub(vec![args[0], args[1]]), EQ))
                    }
                    _ => None,
                },
                _ => None,
            };
            match parsed {
                Some(dk) => cons.push(dk),
                None => {
                    if !sk_apps.iter().any(|&sk| self.term_contains_id(c, sk)) {
                        kept_raw.push(c);
                    }
                }
            }
        }

        // Eliminate each Skolem application in turn.
        for &sk in &sk_apps {
            let mut next: Vec<(TermId, u8)> = Vec::new();
            // (a>0, L): the bound `a*sk >= L`.  (b>0, U): the bound `b*sk <= U`.
            // Keeping the coefficient lets the FM combine use the REAL (rational)
            // shadow `a*U - b*L >= 0` for NON-UNIT coefficients (Omega real shadow),
            // instead of dropping non-unit atoms. The rational projection
            // over-approximates sk's integer solution set, so it can only add a
            // NECESSARY condition on the universal — never a wrong UNSAT.
            let mut lowers: Vec<(num_bigint::BigInt, TermId)> = Vec::new();
            let mut uppers: Vec<(num_bigint::BigInt, TermId)> = Vec::new();
            for (d, k) in cons.drain(..) {
                if !self.term_contains_id(d, sk) {
                    next.push((d, k));
                    continue;
                }
                // SOUNDNESS (S2 disease): a NON-AFFINE `sk` occurrence
                // (`sk*sk > -3`) folds the difference probe to a fake constant
                // coefficient, minting a bound the atom never implied. This
                // projector is a RELAXATION, so dropping the atom is sound (it
                // only enlarges the witness set) — drop, never mis-project.
                if self.var_under_nonarith(d, sk) {
                    continue;
                }
                let d1 = self.subst_term(d, sk, one);
                let d0 = self.subst_term(d, sk, zero);
                let coeff = self.ctx.terms.mk_sub(vec![d1, d0]);
                let coeff_val = match self.ctx.terms.get(coeff) {
                    TermData::Const(ay_core::Constant::Int(n)) => n.clone(),
                    _ => continue, // sk nonlinear / under UF here -> drop (relax)
                };
                let rest = d0; // d = coeff_val*sk + rest, atom is `d (k) 0`
                use num_traits::Zero;
                if coeff_val.is_zero() {
                    next.push((rest, k)); // sk cancels; keep the sk-free atom
                    continue;
                }
                if coeff_val > num_bigint::BigInt::zero() {
                    // coeff*sk + rest (k) 0  =>  coeff*sk (k) -rest
                    let neg_rest = self.ctx.terms.mk_sub(vec![zero, rest]);
                    match k {
                        GE => lowers.push((coeff_val, neg_rest)),
                        // int-tighten `> 0` to `>= 1`: coeff*sk >= 1 - rest
                        GT => lowers.push((coeff_val, self.ctx.terms.mk_add(vec![neg_rest, one]))),
                        EQ => {
                            lowers.push((coeff_val.clone(), neg_rest));
                            uppers.push((coeff_val, neg_rest));
                        }
                        _ => unreachable!(),
                    }
                } else {
                    // coeff < 0: let a = -coeff > 0; -a*sk + rest (k) 0 => a*sk (k') rest
                    let a = -coeff_val;
                    match k {
                        GE => uppers.push((a, rest)),
                        GT => uppers.push((a, self.ctx.terms.mk_sub(vec![rest, one]))),
                        EQ => {
                            uppers.push((a.clone(), rest));
                            lowers.push((a, rest));
                        }
                        _ => unreachable!(),
                    }
                }
            }
            // Real-shadow FM: a*sk>=L and b*sk<=U give b*L <= a*b*sk <= a*U, hence
            // `a*U - b*L >= 0`. (Unit coeffs a=b=1 reduce to the prior `U-L>=0`.)
            for (a, l) in &lowers {
                for (b, u) in &uppers {
                    let a_t = self.ctx.terms.mk_int(a.clone());
                    let b_t = self.ctx.terms.mk_int(b.clone());
                    let a_u = self.ctx.terms.mk_mul(vec![a_t, *u]);
                    let b_l = self.ctx.terms.mk_mul(vec![b_t, *l]);
                    let d = self.ctx.terms.mk_sub(vec![a_u, b_l]); // a*U - b*L >= 0
                    next.push((d, GE));
                }
            }
            cons = next;
        }

        // Rebuild atoms. Any residual still mentioning a Skolem means elimination
        // was incomplete -> bail (never emit an over-tight body).
        let mut proj: Vec<TermId> = kept_raw;
        for (d, k) in &cons {
            if sk_apps.iter().any(|&sk| self.term_contains_id(*d, sk)) {
                return None;
            }
            let atom = match *k {
                GE => self.ctx.terms.mk_ge(*d, zero),
                GT => self.ctx.terms.mk_gt(*d, zero),
                EQ => self.ctx.terms.mk_eq(*d, zero),
                _ => unreachable!(),
            };
            proj.push(atom);
        }
        if proj.is_empty() {
            return None;
        }
        Some(self.ctx.terms.mk_and(proj))
    }

    /// Rewrite `term` so every `(+ ...)` node is re-normalized to a canonical
    /// argument order, recursively. Rebuilding each sum through `mk_add` puts the
    /// folded constant in a fixed position (Phase-3 partition: non-constant
    /// summands first, constant last), so a parse-built `(+ sk0 -2)` and a
    /// substitution/coefficient-collected `(+ -2 sk0)` — both denoting `sk0-2` —
    /// re-normalize to the SAME interned node. `+` is commutative, so this is
    /// semantics-preserving; its only effect is to make sums equal up to summand
    /// order hash-cons together, restoring E-graph congruence across
    /// `f(<sum1>)` / `f(<sum2>)`. Applied only to the alternation validation's
    /// throwaway instance set (never the global term graph, whose order other
    /// solver heuristics depend on).
    fn canonicalize_sums(&mut self, term: TermId) -> TermId {
        match self.ctx.terms.get(term).clone() {
            TermData::App(sym, args) => {
                let new_args: Vec<TermId> =
                    args.iter().map(|&a| self.canonicalize_sums(a)).collect();
                if sym.name() == "+" && new_args.len() >= 2 {
                    self.ctx.terms.mk_add(new_args)
                } else if new_args == args {
                    term
                } else {
                    let sort = self.ctx.terms.sort(term).clone();
                    self.ctx.terms.mk_app(sym, new_args, sort)
                }
            }
            TermData::Not(inner) => {
                let i = self.canonicalize_sums(inner);
                self.ctx.terms.mk_not(i)
            }
            TermData::Ite(c, t, e) => {
                let nc = self.canonicalize_sums(c);
                let nt = self.canonicalize_sums(t);
                let ne = self.canonicalize_sums(e);
                self.ctx.terms.mk_ite(nc, nt, ne)
            }
            _ => term,
        }
    }

    fn collect_skolem_apps(&self, root: TermId, out: &mut Vec<TermId>) {
        use ay_core::kani_compat::DetHashSet as HashSet;
        let mut visited: HashSet<TermId> = HashSet::default();
        let mut stack = vec![root];
        while let Some(t) = stack.pop() {
            if !visited.insert(t) {
                continue;
            }
            match self.ctx.terms.get(t) {
                TermData::App(sym, args) => {
                    if sym.name().starts_with("__ay_sk_") {
                        if !out.contains(&t) {
                            out.push(t);
                        }
                    } else {
                        stack.extend(args.iter().copied());
                    }
                }
                TermData::Not(inner) => stack.push(*inner),
                TermData::Ite(c, th, e) => {
                    stack.push(*c);
                    stack.push(*th);
                    stack.push(*e);
                }
                TermData::Let(binds, b) => {
                    for (_, v) in binds {
                        stack.push(*v);
                    }
                    stack.push(*b);
                }
                _ => {}
            }
        }
    }

    fn term_contains_id(&self, root: TermId, target: TermId) -> bool {
        use ay_core::kani_compat::DetHashSet as HashSet;
        let mut visited: HashSet<TermId> = HashSet::default();
        let mut stack = vec![root];
        while let Some(t) = stack.pop() {
            if t == target {
                return true;
            }
            if !visited.insert(t) {
                continue;
            }
            match self.ctx.terms.get(t) {
                TermData::App(_, args) => stack.extend(args.iter().copied()),
                TermData::Not(inner) => stack.push(*inner),
                TermData::Ite(c, th, e) => {
                    stack.push(*c);
                    stack.push(*th);
                    stack.push(*e);
                }
                TermData::Let(binds, b) => {
                    for (_, v) in binds {
                        stack.push(*v);
                    }
                    stack.push(*b);
                }
                _ => {}
            }
        }
        false
    }

    fn subst_term(&mut self, root: TermId, target: TermId, repl: TermId) -> TermId {
        if root == target {
            return repl;
        }
        match self.ctx.terms.get(root).clone() {
            TermData::App(sym, args) => {
                let new: Vec<TermId> = args
                    .iter()
                    .map(|&a| self.subst_term(a, target, repl))
                    .collect();
                if new == args {
                    root
                } else {
                    // Use SIMPLIFYING arithmetic constructors so a substituted
                    // product like `(* 1 2)` folds to `2`. Without this, the FM
                    // projection's coefficient probe `d[sk:=1] - d[sk:=0]` over a
                    // term `(* sk 2)` produced the non-constant `(* 1 2)` and the
                    // atom was wrongly dropped as non-linear (missing the `2*sk>=4`
                    // bound). Folding is semantics-preserving.
                    match sym.name() {
                        "+" => self.ctx.terms.mk_add(new),
                        "-" if new.len() == 1 => self.ctx.terms.mk_neg(new[0]),
                        "-" if new.len() == 2 => self.ctx.terms.mk_sub(new),
                        "*" => self.ctx.terms.mk_mul(new),
                        _ => {
                            let sort = self.ctx.terms.sort(root).clone();
                            self.ctx.terms.mk_app(sym, new, sort)
                        }
                    }
                }
            }
            TermData::Not(inner) => {
                let i = self.subst_term(inner, target, repl);
                self.ctx.terms.mk_not(i)
            }
            TermData::Ite(c, t, e) => {
                let c2 = self.subst_term(c, target, repl);
                let t2 = self.subst_term(t, target, repl);
                let e2 = self.subst_term(e, target, repl);
                self.ctx.terms.mk_ite(c2, t2, e2)
            }
            _ => root,
        }
    }

    /// Replace each Skolem-function-containing atom in `term` with its
    /// polarity-permissive truth value (`true` in positive position, `false` in
    /// negative), tracking polarity through the boolean connectives. Returns
    /// `None` when a Skolem atom occurs in a non-monotonic position (an `ite`
    /// condition) where the weakening is not valid. The result is implied by the
    /// original (a necessary condition), so a `forall` over it that is UNSAT
    /// witnesses the original `forall`-`exists` UNSAT.
    fn abstract_skolem_atoms(&mut self, term: TermId, positive: bool) -> Option<TermId> {
        match self.ctx.terms.get(term).clone() {
            TermData::Not(inner) => {
                let a = self.abstract_skolem_atoms(inner, !positive)?;
                Some(self.ctx.terms.mk_not(a))
            }
            TermData::App(sym, args) if sym.name() == "and" => {
                let mut new = Vec::with_capacity(args.len());
                for a in args {
                    new.push(self.abstract_skolem_atoms(a, positive)?);
                }
                Some(self.ctx.terms.mk_and(new))
            }
            TermData::App(sym, args) if sym.name() == "or" => {
                let mut new = Vec::with_capacity(args.len());
                for a in args {
                    new.push(self.abstract_skolem_atoms(a, positive)?);
                }
                Some(self.ctx.terms.mk_or(new))
            }
            TermData::App(sym, args) if sym.name() == "=>" && args.len() == 2 => {
                let a = self.abstract_skolem_atoms(args[0], !positive)?;
                let b = self.abstract_skolem_atoms(args[1], positive)?;
                Some(self.ctx.terms.mk_implies(a, b))
            }
            TermData::Ite(c, t, e) => {
                if self.term_mentions_a_skolem_fn(c) {
                    return None; // non-monotonic condition
                }
                let t2 = self.abstract_skolem_atoms(t, positive)?;
                let e2 = self.abstract_skolem_atoms(e, positive)?;
                Some(self.ctx.terms.mk_ite(c, t2, e2))
            }
            // Atom / opaque sub-formula: if it mentions a Skolem function, replace
            // the whole thing with the polarity-permissive constant (weakening).
            _ => {
                if self.term_mentions_a_skolem_fn(term) {
                    Some(self.ctx.terms.mk_bool(positive))
                } else {
                    Some(term)
                }
            }
        }
    }

    fn term_mentions_a_skolem_fn(&self, root: TermId) -> bool {
        use ay_core::kani_compat::DetHashSet as HashSet;
        let mut visited: HashSet<TermId> = HashSet::default();
        let mut stack = vec![root];
        while let Some(t) = stack.pop() {
            if !visited.insert(t) {
                continue;
            }
            match self.ctx.terms.get(t) {
                TermData::App(sym, args) => {
                    if sym.name().starts_with("__ay_sk_") {
                        return true;
                    }
                    stack.extend(args.iter().copied());
                }
                TermData::Not(inner) => stack.push(*inner),
                TermData::Ite(c, t2, e) => {
                    stack.push(*c);
                    stack.push(*t2);
                    stack.push(*e);
                }
                TermData::Let(binds, b) => {
                    for (_, v) in binds {
                        stack.push(*v);
                    }
                    stack.push(*b);
                }
                TermData::Forall(_, b, _) | TermData::Exists(_, b, _) => stack.push(*b),
                _ => {}
            }
        }
        false
    }

    /// Fold linear equalities to constants inside every QUANTIFIED top-level
    /// assertion, before quantifier processing.
    ///
    /// `(= a b)` over Int/Real where `a - b` is a constant is `false`/`true`
    /// (e.g. `(= (- q1 0) (- q1 1))` -> `false`). The ground LIA/LRA solver
    /// decides these, but inside a `forall`/`exists` body the un-folded atom — if
    /// it mentions the bound variable — survives the quantifier classification as
    /// a live, existential-witness-dependent literal and can route a genuinely
    /// arithmetic universal down the (unsound-for-it) UF-completion path. Folding
    /// it here normalises the body so `body_is_pure_arith_bool` / CEGQI see the
    /// real shape. Restricted to quantified assertions so ground problems (and
    /// their proof structure) are untouched.
    pub(in crate::executor) fn fold_quantified_linear_eqs(&mut self) {
        let mut forall_provenance = Vec::new();
        for i in 0..self.ctx.assertions.len() {
            let a = self.ctx.assertions[i];
            if contains_quantifier(&self.ctx.terms, a) {
                // The proof tracker has a dedicated, strict derivation for a
                // top-level negative single-binder forall: it starts from the
                // exact authored `not(forall ...)`, applies `sko_forall`, and
                // derives the Skolemized NNF body with Boolean rules. Folding
                // comparisons inside that source first would instead create a
                // semantically equivalent but unauthored Assume leaf. Preserve
                // the source shape only when it matches that certified lane;
                // Skolemization still performs the required NNF conversion.
                let preserve_certified_skolem_source = self.produce_proofs_enabled()
                    && match self.ctx.terms.get(a) {
                        TermData::Not(quantified) => match self.ctx.terms.get(*quantified) {
                            TermData::Forall(bindings, body, _) if bindings.len() == 1 => {
                                matches!(
                                    self.ctx.terms.get(*body),
                                    TermData::App(sym, args)
                                        if sym.name() == "or" && args.len() >= 2
                                ) && !contains_quantifier(&self.ctx.terms, *body)
                            }
                            _ => false,
                        },
                        _ => false,
                    };
                if preserve_certified_skolem_source {
                    continue;
                }
                let folded = self.fold_linear_eqs(a, &mut forall_provenance);
                self.ctx.assertions[i] = folded;
            }
        }
        if !self.produce_proofs_enabled() || forall_provenance.is_empty() {
            return;
        }
        let Some(assertion_provenance) = self.proof_problem_assertion_provenance.as_mut() else {
            return;
        };
        for record in forall_provenance {
            // A nested/derived forall is not a free problem premise. Only an
            // exact constructor record rooted at an immutable authored
            // assertion may be consulted by E-matching proof registration.
            if !assertion_provenance
                .original_problem_assertions
                .contains(&record.source_forall)
            {
                continue;
            }
            let source_set = vec![record.source_forall];
            let entry = assertion_provenance
                .assertion_sources
                .entry(record.normalized_forall)
                .or_default();
            if !entry.contains(&source_set) {
                entry.push(source_set);
            }
        }
    }

    /// Drop bound variables that never occur in their quantifier body, and
    /// collapse a fully-vacuous quantifier to its body. Over non-empty SMT sorts,
    /// `(forall x. P) == P` and `(exists x. P) == P` when `P` does not mention `x`
    /// — an unconditionally valid equivalence, so this never changes
    /// satisfiability. It removes spurious quantifiers that otherwise misroute a
    /// ground constraint into the alternation/CEGQI machinery and yield a wrong
    /// SAT (e.g. a vacuous `(forall ((y Int)) (> b 0))` alongside a genuine
    /// `(forall ((y Int)) (< z (+ y 3)))`, #quant-alt-WS). Runs after
    /// `fold_quantified_linear_eqs`, so a body folded to a constant is then seen
    /// as vacuous and collapsed.
    pub(in crate::executor) fn simplify_vacuous_quantifiers(&mut self) {
        for i in 0..self.ctx.assertions.len() {
            let a = self.ctx.assertions[i];
            if contains_quantifier(&self.ctx.terms, a) {
                let mut simplified = self.drop_unused_bound_vars(a);
                // Hoist conjuncts out of quantifiers they don't mention BEFORE the
                // infeasibility check, so a deep binder-independent conjunct like
                // `(= b (* 3 x))` buried under `(exists y (forall z ...))` reaches
                // the outer `(forall x ...)` where its nonzero x-coefficient refutes.
                simplified = self.hoist_binder_independent_conjuncts(simplified);
                simplified = self.simplify_infeasible_forall_eq(simplified);
                self.ctx.assertions[i] = simplified;
            }
        }
    }

    /// #quantprod-g2: fold `select` over a KNOWN-CONSTANT array inside
    /// quantified assertions, before quantifier classification.
    ///
    /// Two equivalence-preserving rewrites, applied only INSIDE assertions
    /// that contain a quantifier (ground problems and their proof structure
    /// are untouched):
    ///
    /// 1. `(select ((as const (Array I E)) k) i) -> k` — valid at any binder
    ///    depth and polarity (the const array maps every index to `k`).
    /// 2. When a TOP-LEVEL assertion pins a ground array term to a literal
    ///    constant array — `(= a ((as const …) k))` with `k` a literal — every
    ///    `(select a i)` elsewhere folds to `k`. The pin assertion itself is
    ///    KEPT (it is ground, so this pass never touches it): in every model
    ///    of the retained pin `select a i = k`, so the conjunction is
    ///    logically unchanged in both polarities, and the array solver still
    ///    produces/validates `a`'s model value from the pin.
    ///
    /// This makes `(forall ((x Int)) (= (select a x) k))` collapse to a
    /// vacuous-binder tautology that `simplify_vacuous_quantifiers` (which
    /// runs next) removes — instead of the whole problem failing closed
    /// through the deliberate MBQI-unsafe quantified-array degrade. Every
    /// non-foldable quantified-array shape flows on byte-identically, so that
    /// fail-close stays intact.
    pub(in crate::executor) fn fold_pinned_const_array_selects(&mut self) {
        use ay_core::kani_compat::DetHashMap;
        // Phase 1: collect literal const-array pins from top-level unit
        // equalities. Only a `Const`-element const-array qualifies; the
        // pinned side may be any ground array-sorted term that is not itself
        // a const-array literal. Conflicting pins keep the LAST one — sound
        // either way, because the retained pin equalities ground-refute the
        // problem regardless of which entailed fold was applied.
        let mut pins: DetHashMap<TermId, TermId> = Default::default();
        for &a in &self.ctx.assertions {
            let TermData::App(ay_core::term::Symbol::Named(op), args) = self.ctx.terms.get(a)
            else {
                continue;
            };
            if op != "=" || args.len() != 2 {
                continue;
            }
            for (x, y) in [(args[0], args[1]), (args[1], args[0])] {
                if self.ctx.terms.get_const_array(x).is_some() {
                    continue;
                }
                let Some(elem) = self.ctx.terms.get_const_array(y) else {
                    continue;
                };
                if matches!(self.ctx.terms.get(elem), TermData::Const(_)) {
                    pins.insert(x, elem);
                }
            }
        }
        // Phase 2: fold inside quantified assertions.
        for i in 0..self.ctx.assertions.len() {
            let a = self.ctx.assertions[i];
            if contains_quantifier(&self.ctx.terms, a) {
                self.ctx.assertions[i] = self.fold_const_array_selects_rec(a, &pins);
            }
        }
    }

    /// Recursive worker for [`Self::fold_pinned_const_array_selects`]:
    /// rewrite `(select arr i)` to the constant element when `arr` is a
    /// literal const-array or a pinned ground array term. Quantifiers are
    /// rebuilt with their trigger lists intact; `Let` is left untouched
    /// (conservative — a let-bound shadow could alias the pinned name).
    fn fold_const_array_selects_rec(
        &mut self,
        term: TermId,
        pins: &ay_core::kani_compat::DetHashMap<TermId, TermId>,
    ) -> TermId {
        match self.ctx.terms.get(term).clone() {
            TermData::App(sym, args) => {
                let new: Vec<TermId> = args
                    .iter()
                    .map(|&a| self.fold_const_array_selects_rec(a, pins))
                    .collect();
                if let ay_core::term::Symbol::Named(name) = &sym {
                    if name == "select" && new.len() == 2 {
                        let arr = new[0];
                        // A pinned ground array (`pins` keys are ground
                        // TermIds, so a binder variable can never collide) or
                        // a direct const-array literal.
                        if let Some(&elem) = pins.get(&arr) {
                            return elem;
                        }
                        if let Some(elem) = self.ctx.terms.get_const_array(arr) {
                            if matches!(self.ctx.terms.get(elem), TermData::Const(_)) {
                                return elem;
                            }
                        }
                    }
                }
                if new == args {
                    term
                } else {
                    let sort = self.ctx.terms.sort(term).clone();
                    self.ctx.terms.mk_app(sym, new, sort)
                }
            }
            TermData::Not(inner) => {
                let ni = self.fold_const_array_selects_rec(inner, pins);
                if ni == inner {
                    term
                } else {
                    self.ctx.terms.mk_not(ni)
                }
            }
            TermData::Ite(c, t, e) => {
                let (nc, nt, ne) = (
                    self.fold_const_array_selects_rec(c, pins),
                    self.fold_const_array_selects_rec(t, pins),
                    self.fold_const_array_selects_rec(e, pins),
                );
                if nc == c && nt == t && ne == e {
                    term
                } else {
                    self.ctx.terms.mk_ite(nc, nt, ne)
                }
            }
            TermData::Forall(vars, body, triggers) | TermData::Exists(vars, body, triggers) => {
                let is_forall = matches!(self.ctx.terms.get(term), TermData::Forall(..));
                let nb = self.fold_const_array_selects_rec(body, pins);
                if nb == body {
                    term
                } else {
                    self.rebuild_quant(is_forall, vars, nb, triggers)
                }
            }
            _ => term,
        }
    }

    /// Recursively hoist conjuncts out of a quantifier whose binder they do not
    /// mention: `(Q vars. (and A B))` with `A` free of every `vars` binder equals
    /// `(and A (Q vars. (and B)))` for both `Q ∈ {forall, exists}` (the universal
    /// distributes over the conjunction, and a binder-independent conjunct passes
    /// through an existential unchanged). Sound and equivalence-preserving. Lifts a
    /// deep binder-independent atom to the enclosing scope so the infeasibility
    /// rewrite can see it as a top-level conjunct of an OUTER universal.
    fn hoist_binder_independent_conjuncts(&mut self, term: TermId) -> TermId {
        match self.ctx.terms.get(term).clone() {
            TermData::App(sym, args) => {
                let new: Vec<TermId> = args
                    .iter()
                    .map(|&a| self.hoist_binder_independent_conjuncts(a))
                    .collect();
                if new == args {
                    term
                } else {
                    let sort = self.ctx.terms.sort(term).clone();
                    self.ctx.terms.mk_app(sym, new, sort)
                }
            }
            TermData::Not(i) => {
                let ni = self.hoist_binder_independent_conjuncts(i);
                if ni == i {
                    term
                } else {
                    self.ctx.terms.mk_not(ni)
                }
            }
            TermData::Ite(c, t, e) => {
                let (nc, nt, ne) = (
                    self.hoist_binder_independent_conjuncts(c),
                    self.hoist_binder_independent_conjuncts(t),
                    self.hoist_binder_independent_conjuncts(e),
                );
                if nc == c && nt == t && ne == e {
                    term
                } else {
                    self.ctx.terms.mk_ite(nc, nt, ne)
                }
            }
            TermData::Forall(vars, body, triggers) | TermData::Exists(vars, body, triggers) => {
                let is_forall = matches!(self.ctx.terms.get(term), TermData::Forall(..));
                let nb = self.hoist_binder_independent_conjuncts(body);
                let mut conjs = Vec::new();
                collect_and_conjuncts(&self.ctx.terms, nb, &mut conjs);
                if conjs.len() < 2 {
                    if nb == body {
                        return term;
                    }
                    return self.rebuild_quant(is_forall, vars, nb, triggers);
                }
                let (indep, dep): (Vec<TermId>, Vec<TermId>) = conjs
                    .into_iter()
                    .partition(|&c| !vars.iter().any(|(n, _)| self.term_mentions_name(c, n)));
                if indep.is_empty() {
                    if nb == body {
                        return term;
                    }
                    return self.rebuild_quant(is_forall, vars, nb, triggers);
                }
                // Re-wrap the dependent conjuncts under the quantifier; conjoin the
                // hoisted binder-independent ones at this (enclosing) level.
                let inner_body = if dep.is_empty() {
                    self.ctx.terms.mk_bool(true)
                } else if dep.len() == 1 {
                    dep[0]
                } else {
                    self.ctx.terms.mk_and(dep)
                };
                let mut out = indep;
                if !matches!(
                    self.ctx.terms.get(inner_body),
                    TermData::Const(ay_core::Constant::Bool(true))
                ) {
                    out.push(self.rebuild_quant(is_forall, vars, inner_body, triggers));
                }
                self.ctx.terms.mk_and(out)
            }
            TermData::Let(bindings, body) => {
                let nb = self.hoist_binder_independent_conjuncts(body);
                if nb == body {
                    term
                } else {
                    self.ctx.terms.mk_let(bindings, nb)
                }
            }
            _ => term,
        }
    }

    fn rebuild_quant(
        &mut self,
        is_forall: bool,
        vars: Vec<(String, ay_core::Sort)>,
        body: TermId,
        triggers: Vec<Vec<TermId>>,
    ) -> TermId {
        if is_forall {
            self.ctx.terms.mk_forall_with_triggers(vars, body, triggers)
        } else {
            self.ctx.terms.mk_exists_with_triggers(vars, body, triggers)
        }
    }

    /// Recursively rewrite `(forall vars. body)` to `false` when a TOP-LEVEL
    /// conjunct of `body` is an `Int` linear equality `(= L R)` whose difference
    /// `L - R` has a NONZERO constant coefficient in one of `vars`: such an
    /// equality cannot hold for every value of that binder, so the universal is
    /// false. Sound — a conjunct that is false for some binder value makes the
    /// whole `(forall ...)` false (forall distributes over the conjunction), and
    /// `false` then propagates through any enclosing quantifiers. Catches the
    /// inner `(forall z (and (= x (+ (* 3 b) z)) ...))` of a forall-exists-forall
    /// alternation that no existential witness can repair
    /// (#quant-inner-forall-infeasible-eq).
    fn simplify_infeasible_forall_eq(&mut self, term: TermId) -> TermId {
        match self.ctx.terms.get(term).clone() {
            TermData::App(sym, args) => {
                let new: Vec<TermId> = args
                    .iter()
                    .map(|&a| self.simplify_infeasible_forall_eq(a))
                    .collect();
                if new == args {
                    term
                } else {
                    let sort = self.ctx.terms.sort(term).clone();
                    self.ctx.terms.mk_app(sym, new, sort)
                }
            }
            TermData::Not(i) => {
                let ni = self.simplify_infeasible_forall_eq(i);
                if ni == i {
                    term
                } else {
                    self.ctx.terms.mk_not(ni)
                }
            }
            TermData::Ite(c, t, e) => {
                let (nc, nt, ne) = (
                    self.simplify_infeasible_forall_eq(c),
                    self.simplify_infeasible_forall_eq(t),
                    self.simplify_infeasible_forall_eq(e),
                );
                if nc == c && nt == t && ne == e {
                    term
                } else {
                    self.ctx.terms.mk_ite(nc, nt, ne)
                }
            }
            TermData::Forall(vars, body, triggers) => {
                let nb = self.simplify_infeasible_forall_eq(body);
                if self.forall_has_infeasible_linear_eq(nb, &vars) {
                    return self.ctx.terms.mk_bool(false);
                }
                // Disjunction-infeasible: `(forall v. (or A(v) B))` where EVERY
                // binder-DEPENDENT disjunct is a binder-infeasible linear equality
                // and the rest are binder-INDEPENDENT equals `(or <indep>)` —
                // `∀v.(or Ai(v) Bj) = (∀v.(or Ai)) ∨ (or Bj)`, and a finite union
                // of single-point exceptions cannot cover the infinite Int domain,
                // so `(∀v.(or Ai))` is false. Computed DIRECTLY (no intermediate
                // forall-in-disjunction, which the instantiation loop mishandles).
                if let Some(reduced) = self.forall_or_drop_infeasible_disjuncts(nb, &vars) {
                    return reduced;
                }
                // A universal whose (simplified) body is a boolean CONSTANT equals
                // that constant over a non-empty sort — collapse it so a nested
                // `(forall x false)` produced by the rewrite above propagates.
                if let TermData::Const(ay_core::Constant::Bool(_)) = self.ctx.terms.get(nb) {
                    return nb;
                }
                if nb == body {
                    term
                } else {
                    self.ctx.terms.mk_forall_with_triggers(vars, nb, triggers)
                }
            }
            TermData::Exists(vars, body, triggers) => {
                let nb = self.simplify_infeasible_forall_eq(body);
                // `(exists x <bool const>)` = that constant over a non-empty sort.
                if let TermData::Const(ay_core::Constant::Bool(_)) = self.ctx.terms.get(nb) {
                    return nb;
                }
                if nb == body {
                    term
                } else {
                    self.ctx.terms.mk_exists_with_triggers(vars, nb, triggers)
                }
            }
            TermData::Let(bindings, body) => {
                let nb = self.simplify_infeasible_forall_eq(body);
                if nb == body {
                    term
                } else {
                    self.ctx.terms.mk_let(bindings, nb)
                }
            }
            _ => term,
        }
    }

    /// True when a top-level conjunct of `body` is an `Int` equality `(= L R)`
    /// whose `L - R` is LINEAR in some binder of `vars` with a nonzero constant
    /// coefficient (so `(forall <that binder>. (= L R))` is false). The
    /// coefficient is read by the same `d[v:=1] - d[v:=0]` probe as the FM
    /// projection; a non-constant result (binder under a UF / nonlinear) is
    /// skipped — fail open (never a wrong rewrite).
    fn forall_has_infeasible_linear_eq(
        &mut self,
        body: TermId,
        vars: &[(String, ay_core::Sort)],
    ) -> bool {
        let mut conjuncts = Vec::new();
        collect_and_conjuncts(&self.ctx.terms, body, &mut conjuncts);
        // `collect_and_conjuncts` only descends an `and`; a body that is itself a
        // single atom (e.g. a bare `(= L R)` or a single disjunct) is the lone
        // conjunct.
        if conjuncts.is_empty() {
            conjuncts.push(body);
        }
        // Conjunct position: a single conjunct false at SOME v makes the whole
        // `(forall v. (and ..))` false, so inequalities are admissible here (a
        // nonzero-coefficient inequality is false at an extreme v).
        conjuncts
            .into_iter()
            .any(|c| self.atom_is_binder_infeasible(c, vars, true))
    }

    /// True when `c` is an `Int` (in)equality `(REL L R)` (`REL ∈ {=,<,<=,>,>=}`)
    /// whose `L - R` has a NONZERO coefficient in some binder of `vars`, so
    /// `(forall <that binder>. c)` is false. For `=` the difference is not
    /// identically zero (fails at some v); for an inequality a nonzero
    /// v-coefficient makes `L-R` UNBOUNDED in v, so it crosses 0 and violates the
    /// bound at an extreme v. The coefficient is `d[v:=1] - d[v:=0]` evaluated with
    /// every OTHER free Int atom (Var or 0-ary constant) set to 0 — independent of
    /// them — so the probe folds even with a term like `(* x 4)`. A non-constant
    /// residue (binder under a UF / nonlinear in another var) yields no firing —
    /// fail open, never a wrong rewrite.
    fn atom_is_binder_infeasible(
        &mut self,
        c: TermId,
        vars: &[(String, ay_core::Sort)],
        allow_inequalities: bool,
    ) -> bool {
        let TermData::App(sym, args) = self.ctx.terms.get(c).clone() else {
            return false;
        };
        let ineq = matches!(sym.name(), "<" | "<=" | ">" | ">=");
        if !(sym.name() == "=" || (allow_inequalities && ineq)) || args.len() != 2 {
            return false;
        }
        if !matches!(self.ctx.terms.sort(args[0]), ay_core::Sort::Int) {
            return false;
        }
        let zero = self.ctx.terms.mk_int(num_bigint::BigInt::from(0));
        let one = self.ctx.terms.mk_int(num_bigint::BigInt::from(1));
        let d = self.ctx.terms.mk_sub(vec![args[0], args[1]]);
        for (name, sort) in vars {
            if !matches!(sort, ay_core::Sort::Int) {
                continue;
            }
            // The parser creates fresh per-scope bound vars, so `mk_var(name)`
            // does NOT recover the body's binder; find its actual hash-consed
            // `Var(name, _)` TermId inside the difference instead.
            let Some(v) = self.find_bound_var_id(d, name) else {
                continue;
            };
            if !self.term_contains_id(d, v) {
                continue;
            }
            // SOUNDNESS: the v-coefficient is only well-defined (and the UF-app
            // zeroing in int_const_zeroing_vars only sound) when v occurs PURELY
            // ARITHMETICALLY. If v sits under an uninterpreted/other app (e.g.
            // `z + f(z)`), then `f(1)` and `f(0)` differ and zeroing both would
            // manufacture a spurious nonzero coefficient (f could be `-z`, making
            // the universal SAT). Skip that binder.
            if self.var_under_nonarith(d, v) {
                continue;
            }
            let d1 = self.subst_term(d, v, one);
            let d0 = self.subst_term(d, v, zero);
            let (Some(c1), Some(c0)) = (
                self.int_const_zeroing_vars(d1),
                self.int_const_zeroing_vars(d0),
            ) else {
                continue;
            };
            if c1 != c0 {
                return true;
            }
        }
        false
    }

    /// True when binder `v` has any NON-AFFINE occurrence in `root` — i.e. the
    /// `d[v:=1] - d[v:=0]` probe in `atom_is_binder_infeasible` would NOT measure
    /// a genuine linear coefficient.
    ///
    /// SOUNDNESS (S2 wrong-UNSAT closure, 2026-07-08): the probe's argument ("a
    /// nonzero v-coefficient makes `L-R` unbounded in v, so it crosses 0") is
    /// only valid when `d` is AFFINE in v. The previous guard admitted every
    /// occurrence under `+ - * div mod abs` — so `(forall x. (>= (* x x) 0))`
    /// (VALID; d = x², d1−d0 = 1) was collapsed to FALSE and the whole assertion
    /// set refuted (RED suite S2). `abs(x) >= 0` and `(mod x k) >= 0` are the
    /// same disease: bounded-below terms with a fake "coefficient" of 1. Affine
    /// transparency is therefore restricted to `+`/`-`, and to `*` ONLY when v
    /// occurs in exactly one factor (v·v is quadratic); `div`/`mod`/`abs` are
    /// non-affine in their argument (floor steps / clamping break the
    /// crosses-zero argument entirely). Fail-open: a skipped binder just means
    /// no rewrite.
    fn var_under_nonarith(&self, root: TermId, v: TermId) -> bool {
        // stack of (term, currently-under-a-non-affine-position)
        let mut stack = vec![(root, false)];
        while let Some((t, under)) = stack.pop() {
            if t == v {
                if under {
                    return true;
                }
                continue;
            }
            match self.ctx.terms.get(t) {
                TermData::App(sym, args) => {
                    let affine = match sym.name() {
                        "+" | "-" => true,
                        "*" => {
                            // Affine in v only when v occurs in AT MOST ONE factor;
                            // v in two factors is (at least) quadratic in v.
                            args.iter()
                                .filter(|&&a| self.term_contains_id(a, v))
                                .count()
                                <= 1
                        }
                        _ => false,
                    };
                    let child_under = under || !affine;
                    for &a in args {
                        stack.push((a, child_under));
                    }
                }
                TermData::Not(i) => stack.push((*i, true)),
                TermData::Ite(c, a, b) => {
                    stack.push((*c, true));
                    stack.push((*a, true));
                    stack.push((*b, true));
                }
                _ => {}
            }
        }
        false
    }

    /// Substitute every Int-sorted `Var` in `term` with 0 (folding) and return the
    /// resulting integer constant, or `None` if a non-constant residue remains
    /// (e.g. an uninterpreted application). Used to read a v-free coefficient term
    /// reliably regardless of which other free variables it mentions.
    fn int_const_zeroing_vars(&mut self, term: TermId) -> Option<num_bigint::BigInt> {
        let mut vars: Vec<TermId> = Vec::new();
        let mut stack = vec![term];
        let mut seen: ay_core::kani_compat::DetHashSet<TermId> = Default::default();
        while let Some(t) = stack.pop() {
            if !seen.insert(t) {
                continue;
            }
            let is_int = matches!(self.ctx.terms.sort(t), ay_core::Sort::Int);
            match self.ctx.terms.get(t) {
                // A free Int atom (a bound/free Var or a 0-ary declared constant)
                // is independent of the binder's coefficient, so zero it.
                TermData::Var(_, _) if is_int => {
                    if !vars.contains(&t) {
                        vars.push(t);
                    }
                }
                // An Int-sorted application: recurse into ARITHMETIC operators
                // (their args may hold the binder/atoms), but treat any OTHER Int
                // app (a declared 0-ary constant, an uninterpreted `(g ..)`, a
                // `seq.len`, etc.) as an OPAQUE atom and zero it. Since this is
                // called on `d[v:=1]`/`d[v:=0]` — the binder is already substituted
                // out — every such app is binder-free, so zeroing it is exact for
                // the v-coefficient and lets `g(-1,b-y) - z` resolve coeff -1.
                TermData::App(sym, args)
                    if is_int && matches!(sym.name(), "+" | "-" | "*" | "div" | "mod" | "abs") =>
                {
                    stack.extend(args.iter().copied());
                }
                TermData::App(_, _) if is_int => {
                    if !vars.contains(&t) {
                        vars.push(t);
                    }
                }
                TermData::App(_, args) => stack.extend(args.iter().copied()),
                TermData::Not(i) => stack.push(*i),
                TermData::Ite(c, a, b) => {
                    stack.push(*c);
                    stack.push(*a);
                    stack.push(*b);
                }
                _ => {}
            }
        }
        let zero = self.ctx.terms.mk_int(num_bigint::BigInt::from(0));
        let mut t = term;
        for v in vars {
            t = self.subst_term(t, v, zero);
        }
        match self.ctx.terms.get(t) {
            TermData::Const(ay_core::Constant::Int(n)) => Some(n.clone()),
            _ => None,
        }
    }

    /// For `(forall vars. (or operands))`: when EVERY binder-dependent operand is a
    /// binder-infeasible linear equality, return `(or <binder-independent operands>)`
    /// (or `false` if none remain) — the universal of the infeasible disjuncts is
    /// false (finite single-point exceptions can't cover the infinite Int domain),
    /// so it drops out. Returns `None` (keep the forall) if the body is not an `or`,
    /// nothing infeasible drops, or a binder-dependent operand cannot be proven
    /// infeasible. Computing the result here — rather than hoisting `(∀v.(or Ai))`
    /// into a disjunction — avoids leaving a forall in a non-conjunctive position,
    /// where the instantiation loop conjoins instances unsoundly (#quant-or-infeasible).
    fn forall_or_drop_infeasible_disjuncts(
        &mut self,
        body: TermId,
        vars: &[(String, ay_core::Sort)],
    ) -> Option<TermId> {
        let TermData::App(sym, args) = self.ctx.terms.get(body).clone() else {
            return None;
        };
        if sym.name() != "or" || args.len() < 2 {
            return None;
        }
        let mut indep: Vec<TermId> = Vec::new();
        let mut dropped_any = false;
        for op in args {
            let mentions = vars.iter().any(|(n, _)| self.term_mentions_name(op, n));
            if !mentions {
                indep.push(op);
            } else if self.atom_is_binder_infeasible(op, vars, false) {
                // EQUALITY disjuncts only: an infeasible equality is true at <=1
                // point, so a finite set of them can't cover the infinite domain
                // and `(forall v. (or eqs))` is false. An INEQUALITY is true on a
                // half-line, so dropping it would be UNSOUND (e.g.
                // `(forall z. (or (> z 5) (<= z 6)))` is TRUE) — excluded here.
                dropped_any = true;
            } else {
                return None;
            }
        }
        if !dropped_any {
            return None;
        }
        Some(if indep.is_empty() {
            self.ctx.terms.mk_bool(false)
        } else if indep.len() == 1 {
            indep[0]
        } else {
            self.ctx.terms.mk_or(indep)
        })
    }

    /// Find the hash-consed `TermData::Var(name, _)` TermId for binder `name`
    /// inside `root` (all occurrences of a bound var in a body share one TermId).
    fn find_bound_var_id(&self, root: TermId, name: &str) -> Option<TermId> {
        let mut stack = vec![root];
        let mut seen: ay_core::kani_compat::DetHashSet<TermId> = Default::default();
        while let Some(t) = stack.pop() {
            if !seen.insert(t) {
                continue;
            }
            match self.ctx.terms.get(t) {
                TermData::Var(n, _) if n == name => return Some(t),
                TermData::App(_, args) => stack.extend(args.iter().copied()),
                TermData::Not(i) => stack.push(*i),
                TermData::Ite(c, a, b) => {
                    stack.push(*c);
                    stack.push(*a);
                    stack.push(*b);
                }
                TermData::Let(binds, b) => {
                    for (_, v) in binds {
                        stack.push(*v);
                    }
                    stack.push(*b);
                }
                _ => {}
            }
        }
        None
    }

    fn drop_unused_bound_vars(&mut self, term: TermId) -> TermId {
        match self.ctx.terms.get(term).clone() {
            TermData::App(sym, args) => {
                let new_args: Vec<TermId> = args
                    .iter()
                    .map(|&a| self.drop_unused_bound_vars(a))
                    .collect();
                if new_args == args {
                    term
                } else {
                    let sort = self.ctx.terms.sort(term).clone();
                    self.ctx.terms.mk_app(sym, new_args, sort)
                }
            }
            TermData::Not(inner) => {
                let ni = self.drop_unused_bound_vars(inner);
                if ni == inner {
                    term
                } else {
                    self.ctx.terms.mk_not(ni)
                }
            }
            TermData::Ite(c, t, e) => {
                let (nc, nt, ne) = (
                    self.drop_unused_bound_vars(c),
                    self.drop_unused_bound_vars(t),
                    self.drop_unused_bound_vars(e),
                );
                if nc == c && nt == t && ne == e {
                    term
                } else {
                    self.ctx.terms.mk_ite(nc, nt, ne)
                }
            }
            TermData::Forall(vars, body, triggers) => {
                let nb = self.drop_unused_bound_vars(body);
                let kept: Vec<(String, ay_core::Sort)> = vars
                    .iter()
                    .filter(|(n, _)| self.term_mentions_name(nb, n))
                    .cloned()
                    .collect();
                if kept.is_empty() {
                    return nb;
                }
                if kept.len() == vars.len() && nb == body {
                    return term;
                }
                let new_triggers = self.retain_quant_triggers(&triggers, &vars, &kept);
                self.ctx
                    .terms
                    .mk_forall_with_triggers(kept, nb, new_triggers)
            }
            TermData::Exists(vars, body, triggers) => {
                let nb = self.drop_unused_bound_vars(body);
                let kept: Vec<(String, ay_core::Sort)> = vars
                    .iter()
                    .filter(|(n, _)| self.term_mentions_name(nb, n))
                    .cloned()
                    .collect();
                if kept.is_empty() {
                    return nb;
                }
                if kept.len() == vars.len() && nb == body {
                    return term;
                }
                let new_triggers = self.retain_quant_triggers(&triggers, &vars, &kept);
                self.ctx
                    .terms
                    .mk_exists_with_triggers(kept, nb, new_triggers)
            }
            TermData::Let(bindings, body) => {
                let new_bindings: Vec<(String, TermId)> = bindings
                    .iter()
                    .map(|(n, v)| (n.clone(), self.drop_unused_bound_vars(*v)))
                    .collect();
                let nb = self.drop_unused_bound_vars(body);
                if new_bindings == bindings && nb == body {
                    term
                } else {
                    self.ctx.terms.mk_let(new_bindings, nb)
                }
            }
            _ => term,
        }
    }

    /// Keep only trigger groups whose every term avoids any DROPPED binder name
    /// (a trigger referencing an eliminated binder is invalid). Sound either way
    /// — triggers are E-matching hints, not semantics.
    fn retain_quant_triggers(
        &self,
        triggers: &[Vec<TermId>],
        all_vars: &[(String, ay_core::Sort)],
        kept: &[(String, ay_core::Sort)],
    ) -> Vec<Vec<TermId>> {
        let dropped: Vec<&str> = all_vars
            .iter()
            .filter(|(n, _)| !kept.iter().any(|(k, _)| k == n))
            .map(|(n, _)| n.as_str())
            .collect();
        triggers
            .iter()
            .filter(|grp| {
                grp.iter()
                    .all(|&t| !dropped.iter().any(|d| self.term_mentions_name(t, d)))
            })
            .cloned()
            .collect()
    }

    /// True when `name` occurs as a `Var` anywhere in `term`. Does not stop at
    /// shadowing inner quantifiers — that only CONSERVES the binder (never wrongly
    /// drops it), so the rewrite stays sound.
    fn term_mentions_name(&self, term: TermId, name: &str) -> bool {
        match self.ctx.terms.get(term) {
            TermData::Var(n, _) => n == name,
            TermData::App(_, args) => args.iter().any(|&a| self.term_mentions_name(a, name)),
            TermData::Not(i) => self.term_mentions_name(*i, name),
            TermData::Ite(c, t, e) => {
                self.term_mentions_name(*c, name)
                    || self.term_mentions_name(*t, name)
                    || self.term_mentions_name(*e, name)
            }
            TermData::Forall(_, b, _) | TermData::Exists(_, b, _) => {
                self.term_mentions_name(*b, name)
            }
            TermData::Let(bindings, b) => {
                bindings
                    .iter()
                    .any(|(_, v)| self.term_mentions_name(*v, name))
                    || self.term_mentions_name(*b, name)
            }
            _ => false,
        }
    }

    /// `(= A (* k T))`: true when `A` is an Int constant, the product side is
    /// `(* k _)` with `k` an Int constant, `|k| >= 2`, and `k ∤ A` — so there is no
    /// integer `T` making the equality hold. Exact infeasibility over the integers.
    fn int_eq_divis_infeasible(&self, const_side: TermId, prod_side: TermId) -> bool {
        use num_traits::Zero;
        let a = match self.ctx.terms.get(const_side) {
            TermData::Const(ay_core::Constant::Int(n)) => n.clone(),
            _ => return false,
        };
        let margs = match self.ctx.terms.get(prod_side) {
            TermData::App(sym, margs) if sym.name() == "*" && margs.len() == 2 => margs.clone(),
            _ => return false,
        };
        for k_id in margs {
            if let TermData::Const(ay_core::Constant::Int(k)) = self.ctx.terms.get(k_id) {
                // |k| >= 2  <=>  k not in {-1, 0, 1}
                let unit_or_zero = k.is_zero()
                    || *k == num_bigint::BigInt::from(1)
                    || *k == num_bigint::BigInt::from(-1);
                if !unit_or_zero && (&a % k) != num_bigint::BigInt::zero() {
                    return true;
                }
            }
        }
        false
    }

    fn fold_linear_eqs(
        &mut self,
        term: TermId,
        provenance: &mut Vec<QuantifiedLinearNnfProvenance>,
    ) -> TermId {
        match self.ctx.terms.get(term).clone() {
            // Fold a comparison over Int whose two sides differ by a CONSTANT to
            // its truth value (`(= (- x 0) (- x 1))` -> false, `(> 2 (- c0 c0))`
            // -> true). `mk_sub` collects per-base coefficients, so the bound
            // variable / constants cancel when the difference is constant.
            TermData::App(sym, args)
                if matches!(sym.name(), "=" | ">" | ">=" | "<" | "<=")
                    && args.len() == 2
                    && matches!(self.ctx.terms.sort(args[0]), ay_core::Sort::Int) =>
            {
                let diff = self.ctx.terms.mk_sub(vec![args[0], args[1]]); // a - b
                if let TermData::Const(ay_core::Constant::Int(n)) = self.ctx.terms.get(diff) {
                    use num_traits::Zero;
                    let v = n.clone();
                    let truth = match sym.name() {
                        "=" => v.is_zero(),
                        ">" => v > num_bigint::BigInt::zero(),
                        ">=" => v >= num_bigint::BigInt::zero(),
                        "<" => v < num_bigint::BigInt::zero(),
                        "<=" => v <= num_bigint::BigInt::zero(),
                        _ => unreachable!(),
                    };
                    return self.ctx.terms.mk_bool(truth);
                }
                // Integer divisibility infeasibility: `(= A (* k T))` with `A`,`k`
                // Int constants, `|k| >= 2`, `k ∤ A` has NO integer solution for any
                // `T` — fold to false. Exact over Int (NOT over Real). Lets the dead
                // existential-witness branch collapse (`(= -1 (* 3 q2))` -> false).
                if sym.name() == "="
                    && (self.int_eq_divis_infeasible(args[0], args[1])
                        || self.int_eq_divis_infeasible(args[1], args[0]))
                {
                    return self.ctx.terms.mk_bool(false);
                }
                term
            }
            // NNF: push negations to atoms (De Morgan + comparison flips) so the
            // downstream FM projection / instantiation see a flat conjunction of
            // comparison atoms rather than `(not (or (distinct a b) p))`.
            TermData::Not(inner) => match self.ctx.terms.get(inner).clone() {
                TermData::Not(inner2) => self.fold_linear_eqs(inner2, provenance),
                TermData::App(s, a) if s.name() == "and" => {
                    let neg: Vec<TermId> = a.iter().map(|&x| self.ctx.terms.mk_not(x)).collect();
                    let or = self.ctx.terms.mk_or(neg);
                    self.fold_linear_eqs(or, provenance)
                }
                TermData::App(s, a) if s.name() == "or" => {
                    let neg: Vec<TermId> = a.iter().map(|&x| self.ctx.terms.mk_not(x)).collect();
                    let and = self.ctx.terms.mk_and(neg);
                    self.fold_linear_eqs(and, provenance)
                }
                TermData::App(s, a)
                    if a.len() == 2 && matches!(self.ctx.terms.sort(a[0]), ay_core::Sort::Int) =>
                {
                    let flipped = match s.name() {
                        ">" => Some(self.ctx.terms.mk_le(a[0], a[1])),
                        ">=" => Some(self.ctx.terms.mk_lt(a[0], a[1])),
                        "<" => Some(self.ctx.terms.mk_ge(a[0], a[1])),
                        "<=" => Some(self.ctx.terms.mk_lt(a[1], a[0])),
                        "distinct" => Some(self.ctx.terms.mk_eq(a[0], a[1])),
                        _ => None,
                    };
                    match flipped {
                        Some(f) => self.fold_linear_eqs(f, provenance),
                        None => {
                            let i = self.fold_linear_eqs(inner, provenance);
                            self.ctx.terms.mk_not(i)
                        }
                    }
                }
                _ => {
                    let i = self.fold_linear_eqs(inner, provenance);
                    self.ctx.terms.mk_not(i)
                }
            },
            TermData::App(sym, args) if matches!(sym.name(), "and" | "or") => {
                let new: Vec<TermId> = args
                    .iter()
                    .map(|&a| self.fold_linear_eqs(a, provenance))
                    .collect();
                if sym.name() == "and" {
                    self.ctx.terms.mk_and(new)
                } else {
                    self.ctx.terms.mk_or(new)
                }
            }
            TermData::App(sym, args) if sym.name() == "=>" && args.len() == 2 => {
                let a = self.fold_linear_eqs(args[0], provenance);
                let b = self.fold_linear_eqs(args[1], provenance);
                self.ctx.terms.mk_implies(a, b)
            }
            TermData::Ite(c, t, e) => {
                let c2 = self.fold_linear_eqs(c, provenance);
                let t2 = self.fold_linear_eqs(t, provenance);
                let e2 = self.fold_linear_eqs(e, provenance);
                self.ctx.terms.mk_ite(c2, t2, e2)
            }
            TermData::Forall(vars, body, trig) => {
                let b = self.fold_linear_eqs(body, provenance);
                if b == body {
                    term
                } else {
                    let normalized_forall = self.ctx.terms.mk_forall_with_triggers(vars, b, trig);
                    provenance.push(QuantifiedLinearNnfProvenance {
                        source_forall: term,
                        normalized_forall,
                    });
                    normalized_forall
                }
            }
            TermData::Exists(vars, body, trig) => {
                let b = self.fold_linear_eqs(body, provenance);
                if b == body {
                    term
                } else {
                    self.ctx.terms.mk_exists_with_triggers(vars, b, trig)
                }
            }
            _ => term,
        }
    }

    /// Instantiation values for a single `Int` binder derived by E-MATCHING the
    /// body's UF applications against ground UF applications in `ground`.
    ///
    /// For a body application `(uf a)` where `a` is linear in the binder and a
    /// ground `(uf g)` exists, return the binder value that makes `a == g` (so
    /// congruence merges the two): `a == bound ⟹ g`; `a == (+ bound e) ⟹ (- g
    /// e)`; `a == (- bound e) ⟹ (+ g e)` (and symmetric `+`). Used to reach the
    /// forall-over-UF-range contradiction a concrete value window cannot.
    fn ematching_binder_values(
        &mut self,
        body: TermId,
        bound_name: &str,
        ground: &[TermId],
    ) -> Vec<TermId> {
        use ay_core::kani_compat::DetHashSet as HashSet;
        let bound_set: HashSet<String> = std::iter::once(bound_name.to_string()).collect();

        // Ground single-argument UF applications: (uf_name, arg).
        let mut ground_uf: Vec<(String, TermId)> = Vec::new();
        let mut gseen: HashSet<TermId> = HashSet::default();
        let mut gstack: Vec<TermId> = ground.to_vec();
        while let Some(t) = gstack.pop() {
            if !gseen.insert(t) {
                continue;
            }
            if let TermData::App(sym, args) = self.ctx.terms.get(t).clone() {
                if args.len() == 1
                    && !is_pure_arith_bool_symbol(sym.name())
                    && !self.term_mentions_bound_var(args[0], &bound_set)
                {
                    ground_uf.push((sym.name().to_string(), args[0]));
                }
                for a in args {
                    gstack.push(a);
                }
            }
        }
        if ground_uf.is_empty() {
            return Vec::new();
        }

        // Body single-argument UF applications whose arg mentions the binder.
        let mut values: Vec<TermId> = Vec::new();
        let mut bseen: HashSet<TermId> = HashSet::default();
        let mut bstack = vec![body];
        while let Some(t) = bstack.pop() {
            if !bseen.insert(t) {
                continue;
            }
            match self.ctx.terms.get(t).clone() {
                TermData::App(sym, args) => {
                    if args.len() == 1
                        && !is_pure_arith_bool_symbol(sym.name())
                        && self.term_mentions_bound_var(args[0], &bound_set)
                    {
                        for (gname, garg) in &ground_uf {
                            if *gname != sym.name() {
                                continue;
                            }
                            if let Some(v) = self.binder_value_for_arg(args[0], bound_name, *garg) {
                                values.push(v);
                            }
                        }
                    }
                    for a in args {
                        bstack.push(a);
                    }
                }
                TermData::Not(inner) => bstack.push(inner),
                TermData::Ite(c, th, e) => {
                    bstack.push(c);
                    bstack.push(th);
                    bstack.push(e);
                }
                TermData::Let(binds, b) => {
                    for (_, v) in binds {
                        bstack.push(v);
                    }
                    bstack.push(b);
                }
                _ => {}
            }
        }
        values
    }

    /// Ground witness-point bases: for each `Int`-sorted Skolem application
    /// `(__ay_sk_* a)` in `body` whose argument mentions the binder, substitute
    /// the binder with a few small concrete values to obtain GROUND Skolem terms
    /// `(__ay_sk_* c)`. Instantiating the binder near these aligns a whole-range
    /// universal conjunct with the existential witness point.
    fn skolem_app_bases(&mut self, body: TermId, bound_name: &str) -> Vec<TermId> {
        use ay_core::kani_compat::DetHashSet as HashSet;
        const MAX_SK_APPS: usize = 3;
        let bound_set: HashSet<String> = std::iter::once(bound_name.to_string()).collect();

        // Collect Int-sorted Skolem applications whose arg mentions the binder.
        let mut sk_apps: Vec<TermId> = Vec::new();
        let mut visited: HashSet<TermId> = HashSet::default();
        let mut stack = vec![body];
        while let Some(t) = stack.pop() {
            if !visited.insert(t) {
                continue;
            }
            match self.ctx.terms.get(t).clone() {
                TermData::App(sym, args) => {
                    if sym.name().starts_with("__ay_sk_")
                        && matches!(self.ctx.terms.sort(t), ay_core::Sort::Int)
                        && self.term_mentions_bound_var(t, &bound_set)
                        && sk_apps.len() < MAX_SK_APPS
                        && !sk_apps.contains(&t)
                    {
                        sk_apps.push(t);
                    }
                    stack.extend(args);
                }
                TermData::Not(inner) => stack.push(inner),
                TermData::Ite(c, th, e) => {
                    stack.push(c);
                    stack.push(th);
                    stack.push(e);
                }
                TermData::Let(binds, b) => {
                    for (_, v) in binds {
                        stack.push(v);
                    }
                    stack.push(b);
                }
                _ => {}
            }
        }
        if sk_apps.is_empty() {
            return Vec::new();
        }

        let mut out: Vec<TermId> = Vec::new();
        for &sk in &sk_apps {
            for c in [-1i64, 0, 1] {
                let cval = self.ctx.terms.mk_int(num_bigint::BigInt::from(c));
                let mut subst: HashMap<String, TermId> = HashMap::default();
                subst.insert(bound_name.to_string(), cval);
                let ground_sk = crate::ematching::subst_vars(&mut self.ctx.terms, sk, &subst);
                if !out.contains(&ground_sk) {
                    out.push(ground_sk);
                }
            }
        }
        out
    }

    /// Distinct free `Int` variables occurring in `body` other than the binder
    /// `bound_name` (outer-quantified vars / Skolem constants), capped to a small
    /// number. Used as bases for OFFSET instantiations of the binder.
    fn free_int_binder_bases(&self, body: TermId, bound_name: &str) -> Vec<TermId> {
        use ay_core::kani_compat::DetHashSet as HashSet;
        const MAX_BASES: usize = 4;
        let mut out: Vec<TermId> = Vec::new();
        let mut seen_terms: HashSet<TermId> = HashSet::default();
        let mut seen_names: HashSet<String> = HashSet::default();
        let mut visited: HashSet<TermId> = HashSet::default();
        let mut stack = vec![body];
        while let Some(t) = stack.pop() {
            if !visited.insert(t) {
                continue;
            }
            match self.ctx.terms.get(t).clone() {
                TermData::Var(name, _) => {
                    if name != bound_name
                        && matches!(self.ctx.terms.sort(t), ay_core::Sort::Int)
                        && seen_names.insert(name)
                        && seen_terms.insert(t)
                    {
                        out.push(t);
                        if out.len() >= MAX_BASES {
                            break;
                        }
                    }
                }
                TermData::App(_, args) => stack.extend(args.iter().copied()),
                TermData::Not(inner) => stack.push(inner),
                TermData::Ite(c, th, e) => {
                    stack.push(c);
                    stack.push(th);
                    stack.push(e);
                }
                TermData::Let(binds, b) => {
                    for (_, v) in binds {
                        stack.push(v);
                    }
                    stack.push(b);
                }
                _ => {}
            }
        }
        out
    }

    /// Boundary values of the binder: for each `Int` comparison atom in `body`
    /// that is linear in the binder with UNIT coefficient, the value at which the
    /// atom flips (`a < b` over `q0-2 < 3*c0` flips at `q0 = 3*c0 + 2`; `sk0-q1 >
    /// c0` flips at `q1 = sk0 - c0`). The falsifying instantiation of a universal
    /// over an unbounded binder is at (or just past) such a boundary — possibly a
    /// scaled/combined expression of the free variables that the per-variable
    /// offset bases cannot reach. Instantiating the binder at `boundary + k` makes
    /// the critical atom flip, exposing the conflict. Real instances ⇒ sound.
    fn atom_boundary_binder_bases(&mut self, body: TermId, bound_name: &str) -> Vec<TermId> {
        use ay_core::kani_compat::DetHashSet as HashSet;
        const MAX_BASES: usize = 6;
        let bound_set: HashSet<String> = std::iter::once(bound_name.to_string()).collect();
        let zero = self.ctx.terms.mk_int(num_bigint::BigInt::from(0));
        let one = self.ctx.terms.mk_int(num_bigint::BigInt::from(1));
        let mut one_subst: HashMap<String, TermId> = HashMap::default();
        one_subst.insert(bound_name.to_string(), one);
        let mut zero_subst: HashMap<String, TermId> = HashMap::default();
        zero_subst.insert(bound_name.to_string(), zero);

        // Collect comparison atoms (any structural position).
        let mut atoms: Vec<TermId> = Vec::new();
        let mut visited: HashSet<TermId> = HashSet::default();
        let mut stack = vec![body];
        while let Some(t) = stack.pop() {
            if !visited.insert(t) {
                continue;
            }
            match self.ctx.terms.get(t).clone() {
                TermData::App(sym, args) => {
                    if args.len() == 2
                        && matches!(sym.name(), "=" | ">" | ">=" | "<" | "<=")
                        && matches!(self.ctx.terms.sort(args[0]), ay_core::Sort::Int)
                        && self.term_mentions_bound_var(t, &bound_set)
                    {
                        atoms.push(t);
                    }
                    stack.extend(args.iter().copied());
                }
                TermData::Not(inner) => stack.push(inner),
                TermData::Ite(c, th, e) => {
                    stack.push(c);
                    stack.push(th);
                    stack.push(e);
                }
                TermData::Let(binds, b) => {
                    for (_, v) in binds {
                        stack.push(v);
                    }
                    stack.push(b);
                }
                _ => {}
            }
        }

        let mut out: Vec<TermId> = Vec::new();
        for atom in atoms {
            let TermData::App(_, args) = self.ctx.terms.get(atom).clone() else {
                continue;
            };
            let d = self.ctx.terms.mk_sub(vec![args[0], args[1]]); // a - b
            let d1 = crate::ematching::subst_vars(&mut self.ctx.terms, d, &one_subst);
            let d0 = crate::ematching::subst_vars(&mut self.ctx.terms, d, &zero_subst);
            let coeff = self.ctx.terms.mk_sub(vec![d1, d0]);
            let TermData::Const(ay_core::Constant::Int(c)) = self.ctx.terms.get(coeff) else {
                continue;
            };
            let c = c.clone();
            use num_traits::{One, Zero};
            // d = c*binder + rest (rest = d0); flip at binder = -rest/c.
            let boundary = if c.is_one() {
                self.ctx.terms.mk_sub(vec![zero, d0]) // -rest
            } else if c == num_bigint::BigInt::from(-1) {
                d0 // rest
            } else if !c.is_zero() {
                // DIVISIBILITY boundary: integer point nearest the rational flip
                // `-rest/c`, via `div`. The ±k window around it (in the caller)
                // covers the residue classes for small |c|. `div`'s constant
                // divisor keeps this a real integer instantiation point.
                let (num, den) = if c > num_bigint::BigInt::zero() {
                    (self.ctx.terms.mk_sub(vec![zero, d0]), c.clone()) // (-rest)/c
                } else {
                    (d0, -c.clone()) // rest/|c|
                };
                let den_t = self.ctx.terms.mk_int(den);
                self.ctx.terms.mk_div(num, den_t)
            } else {
                continue;
            };
            if !out.contains(&boundary) {
                out.push(boundary);
                if out.len() >= MAX_BASES {
                    break;
                }
            }
        }
        out
    }

    /// Pairwise and limited-triple sums/differences of the binder's anchor
    /// expressions (free Int variables, binder-independent UF values, atom
    /// boundaries). The point at which SEVERAL atoms are simultaneously violated
    /// can be a linear COMBINATION of their individual boundaries that no single
    /// anchor reaches; instantiating the binder there is a real universal instance,
    /// so any resulting UNSAT is sound. Capped to keep the instance set bounded.
    fn combination_binder_bases(&mut self, body: TermId, bound_name: &str) -> Vec<TermId> {
        use ay_core::kani_compat::DetHashSet as HashSet;
        const MAX_ANCHORS: usize = 5;
        const MAX_OUT: usize = 28;

        let mut anchors: Vec<TermId> = self.free_int_binder_bases(body, bound_name);
        for u in self.uf_value_binder_bases(body, bound_name) {
            if !anchors.contains(&u) {
                anchors.push(u);
            }
        }
        for b in self.atom_boundary_binder_bases(body, bound_name) {
            if !anchors.contains(&b) {
                anchors.push(b);
            }
        }
        anchors.truncate(MAX_ANCHORS);
        if anchors.len() < 2 {
            return Vec::new();
        }

        let mut seen: HashSet<TermId> = HashSet::default();
        let mut out: Vec<TermId> = Vec::new();
        // Pairwise: a_i + a_j and a_i - a_j (i < j; differences both orders).
        for i in 0..anchors.len() {
            for j in (i + 1)..anchors.len() {
                let combos = [
                    self.ctx.terms.mk_add(vec![anchors[i], anchors[j]]),
                    self.ctx.terms.mk_sub(vec![anchors[i], anchors[j]]),
                    self.ctx.terms.mk_sub(vec![anchors[j], anchors[i]]),
                ];
                for cmb in combos {
                    if seen.insert(cmb) && out.len() < MAX_OUT {
                        out.push(cmb);
                    }
                }
            }
        }
        // Limited triples: a_i + a_j - a_k over the first three anchors only.
        if anchors.len() >= 3 {
            let (a0, a1, a2) = (anchors[0], anchors[1], anchors[2]);
            let sum01 = self.ctx.terms.mk_add(vec![a0, a1]);
            let t0 = self.ctx.terms.mk_sub(vec![sum01, a2]);
            let sum02 = self.ctx.terms.mk_add(vec![a0, a2]);
            let t1 = self.ctx.terms.mk_sub(vec![sum02, a1]);
            let sum12 = self.ctx.terms.mk_add(vec![a1, a2]);
            let t2 = self.ctx.terms.mk_sub(vec![sum12, a0]);
            for cmb in [t0, t1, t2] {
                if seen.insert(cmb) && out.len() < MAX_OUT {
                    out.push(cmb);
                }
            }
        }
        out
    }

    /// Binder-INDEPENDENT `Int`-sorted uninterpreted/non-arith application terms
    /// in `body` (e.g. `(f 3)`, `(f sk0)` where the argument does not mention the
    /// binder). Their values are fixed unknown integers; the falsifying point of a
    /// universal over an unbounded binder is frequently AT one of these values
    /// (`q1 = f(3)`) or just past its negation (`q1 = 1 - f(sk0)` from `f(sk0) >
    /// -q1`). Instantiating the binder at `±base + k` turns the alignment into two
    /// concrete instances whose conjunction is contradictory — a SOUND refutation
    /// (real instances of the universal), no abstraction needed.
    fn uf_value_binder_bases(&self, body: TermId, bound_name: &str) -> Vec<TermId> {
        use ay_core::kani_compat::DetHashSet as HashSet;
        const MAX_BASES: usize = 4;
        let bound_set: HashSet<String> = std::iter::once(bound_name.to_string()).collect();
        let mut out: Vec<TermId> = Vec::new();
        let mut seen: HashSet<TermId> = HashSet::default();
        let mut visited: HashSet<TermId> = HashSet::default();
        let mut stack = vec![body];
        while let Some(t) = stack.pop() {
            if !visited.insert(t) {
                continue;
            }
            if let TermData::App(sym, args) = self.ctx.terms.get(t).clone() {
                let is_uf = !is_pure_arith_bool_symbol(sym.name());
                if is_uf
                    && matches!(self.ctx.terms.sort(t), ay_core::Sort::Int)
                    && !self.term_mentions_bound_var(t, &bound_set)
                    && seen.insert(t)
                {
                    out.push(t);
                    if out.len() >= MAX_BASES {
                        break;
                    }
                }
                stack.extend(args.iter().copied());
            } else {
                match self.ctx.terms.get(t).clone() {
                    TermData::Not(inner) => stack.push(inner),
                    TermData::Ite(c, th, e) => {
                        stack.push(c);
                        stack.push(th);
                        stack.push(e);
                    }
                    TermData::Let(binds, b) => {
                        for (_, v) in binds {
                            stack.push(v);
                        }
                        stack.push(b);
                    }
                    _ => {}
                }
            }
        }
        out
    }

    /// Solve `a[bound = v] == garg` for `v` when `a` is linear in `bound` with
    /// unit coefficient. Returns `None` for non-linear / higher-degree shapes.
    fn binder_value_for_arg(
        &mut self,
        a: TermId,
        bound_name: &str,
        garg: TermId,
    ) -> Option<TermId> {
        use ay_core::kani_compat::DetHashSet as HashSet;
        let bound_set: HashSet<String> = std::iter::once(bound_name.to_string()).collect();
        let is_bound = |this: &Self, t: TermId| matches!(this.ctx.terms.get(t), TermData::Var(n, _) if n == bound_name);
        match self.ctx.terms.get(a).clone() {
            TermData::Var(n, _) if n == bound_name => Some(garg),
            TermData::App(sym, args) if sym.name() == "+" && args.len() == 2 => {
                if is_bound(self, args[0]) && !self.term_mentions_bound_var(args[1], &bound_set) {
                    Some(self.ctx.terms.mk_sub(vec![garg, args[1]]))
                } else if is_bound(self, args[1])
                    && !self.term_mentions_bound_var(args[0], &bound_set)
                {
                    Some(self.ctx.terms.mk_sub(vec![garg, args[0]]))
                } else {
                    None
                }
            }
            TermData::App(sym, args) if sym.name() == "-" && args.len() == 2 => {
                if is_bound(self, args[0]) && !self.term_mentions_bound_var(args[1], &bound_set) {
                    Some(self.ctx.terms.mk_add(vec![garg, args[1]]))
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    /// SOUNDNESS (#forall-alternation wrong-sat): decide whether a CEGQI
    /// "forall valid ⟹ SAT" disambiguation over `snapshot` is UNRELIABLE because
    /// the snapshot contains a skolemized-alternation `forall` with a
    /// WITNESS-INDEPENDENT arithmetic conjunct.
    ///
    /// When an existential under a universal is skolemized into a Skolem FUNCTION
    /// (`__ay_sk_*`) of the bound variable, the arithmetic CE search treats that
    /// application as an opaque per-instance value. That is harmless for a body
    /// like `(> sk(x) x)` — for every `x` the existential witness `sk(x)` is free
    /// to satisfy it, so the universal genuinely holds (this is the canonical
    /// SAT `(forall x (exists y (> y x)))`). It is UNSOUND, however, when the
    /// body also has a conjunct that mentions the bound variable but NO Skolem
    /// function: such a conjunct is a hard universal constraint no existential
    /// witness can repair, and CEGQI's ground-SAT certificate can miss its
    /// falsifying instantiation. Example: `(forall x (and (>= sk(x) (- x 5))
    /// (<= -6 x)))` from `(forall x (exists y (and (>= y (- x 5)) (<= -6 x))))`
    /// is UNSAT (the sk-free conjunct `(<= -6 x)` fails at x = -7), yet
    /// disambiguation reports SAT. Fail closed only in that precise shape, so the
    /// witness-driven SAT cases (`(> sk(x) x)`) keep deciding SAT.
    fn snapshot_has_witness_independent_skolem_alternation(&mut self, snapshot: &[TermId]) -> bool {
        let mut quants: Vec<TermId> = Vec::new();
        for &a in snapshot {
            crate::ematching::collect_quantifiers(&mut self.ctx.terms, a, &mut quants);
        }
        quants.into_iter().any(|q| {
            let TermData::Forall(vars, body, _) = self.ctx.terms.get(q).clone() else {
                return false;
            };
            let bound: ay_core::kani_compat::DetHashSet<String> =
                vars.iter().map(|(n, _)| n.clone()).collect();
            // CEGQI's arithmetic counterexample search is incomplete over the
            // bound variable when the body applies an uninterpreted / non-arith
            // function to it — whether a Skolem function `__ay_sk_*(x)` from a
            // skolemized inner existential, or a declared `(f x)`. Such an
            // application is treated as an opaque per-instance value, so the
            // "ground SAT ⟹ forall valid" verdict can miss a falsifying
            // instantiation.
            if !self.term_mentions_uninterpreted_of_bound_var(body, &bound) {
                return false;
            }
            let mut conjuncts = Vec::new();
            collect_and_conjuncts(&self.ctx.terms, body, &mut conjuncts);
            // A conjunct that constrains a bound variable but applies no
            // uninterpreted/non-arith function to it is WITNESS-INDEPENDENT: it is
            // a hard universal arithmetic constraint no existential witness (or
            // opaque UF value) can repair, so CEGQI's "valid" verdict over it is
            // unreliable — fail closed. The witness-driven shape `(> sk(x) x)` has
            // no such conjunct (its only constraint applies the UF to `x`), so it
            // keeps deciding SAT.
            conjuncts.into_iter().any(|c| {
                self.term_mentions_bound_var(c, &bound)
                    && !self.term_mentions_uninterpreted_of_bound_var(c, &bound)
            })
        })
    }

    /// Whether a restored universal applies a declared/non-Skolem opaque
    /// function to one of its bound variables (possibly through an interpreted
    /// argument such as `f(x + 1)`). A ground graph samples only finitely many
    /// points of such a function and is not, by itself, a total interpretation.
    fn restored_has_bound_dependent_non_skolem_application(&mut self) -> bool {
        let assertions = self.ctx.assertions.clone();
        let mut quants = Vec::new();
        for assertion in assertions {
            crate::ematching::collect_quantifiers(&mut self.ctx.terms, assertion, &mut quants);
        }
        quants.into_iter().any(|quant| {
            let TermData::Forall(vars, body, _) = self.ctx.terms.get(quant).clone() else {
                return false;
            };
            let bound: ay_core::kani_compat::DetHashSet<String> =
                vars.into_iter().map(|(name, _)| name).collect();
            self.term_mentions_non_skolem_uninterpreted_of_bound_var(body, &bound)
        })
    }

    fn term_mentions_non_skolem_uninterpreted_of_bound_var(
        &self,
        root: TermId,
        bound: &ay_core::kani_compat::DetHashSet<String>,
    ) -> bool {
        use ay_core::kani_compat::DetHashSet as HashSet;
        let mut visited: HashSet<TermId> = HashSet::default();
        let mut stack = vec![root];
        while let Some(term) = stack.pop() {
            if !visited.insert(term) {
                continue;
            }
            match self.ctx.terms.get(term) {
                TermData::App(sym, args) => {
                    if !is_pure_arith_bool_symbol(sym.name())
                        && !self.ctx.terms.is_skolem_symbol(sym.name())
                        && args
                            .iter()
                            .any(|&arg| self.term_mentions_bound_var(arg, bound))
                    {
                        return true;
                    }
                    stack.extend(args.iter().copied());
                }
                TermData::Not(inner) => stack.push(*inner),
                TermData::Ite(condition, then_term, else_term) => {
                    stack.push(*condition);
                    stack.push(*then_term);
                    stack.push(*else_term);
                }
                TermData::Let(bindings, body) => {
                    stack.extend(bindings.iter().map(|(_, value)| *value));
                    stack.push(*body);
                }
                TermData::Forall(_, body, _) | TermData::Exists(_, body, _) => stack.push(*body),
                TermData::Const(_) | TermData::Var(_, _) => {}
                _ => {}
            }
        }
        false
    }

    /// True when `root` applies an uninterpreted or non-arithmetic function — any
    /// symbol that is NOT a builtin LIA/LRA/Bool operator (so a UF, Skolem
    /// function, array/seq/string/bv/datatype op) — to a subterm that mentions a
    /// bound variable from `bound`. Marks where CEGQI's arithmetic CE search
    /// loses completeness over the bound variable.
    fn term_mentions_uninterpreted_of_bound_var(
        &self,
        root: TermId,
        bound: &ay_core::kani_compat::DetHashSet<String>,
    ) -> bool {
        use ay_core::kani_compat::DetHashSet as HashSet;
        let mut visited: HashSet<TermId> = HashSet::default();
        let mut stack = vec![root];
        while let Some(term) = stack.pop() {
            if !visited.insert(term) {
                continue;
            }
            match self.ctx.terms.get(term) {
                TermData::App(sym, args) => {
                    if !is_pure_arith_bool_symbol(sym.name())
                        && self.term_mentions_bound_var(term, bound)
                    {
                        return true;
                    }
                    stack.extend(args.iter().copied());
                }
                TermData::Not(inner) => stack.push(*inner),
                TermData::Ite(c, t, e) => {
                    stack.push(*c);
                    stack.push(*t);
                    stack.push(*e);
                }
                TermData::Let(bindings, body) => {
                    for (_, v) in bindings {
                        stack.push(*v);
                    }
                    stack.push(*body);
                }
                TermData::Forall(_, body, _) | TermData::Exists(_, body, _) => stack.push(*body),
                _ => {}
            }
        }
        false
    }

    fn term_mentions_bound_var(
        &self,
        root: TermId,
        bound: &ay_core::kani_compat::DetHashSet<String>,
    ) -> bool {
        use ay_core::kani_compat::DetHashSet as HashSet;
        let mut visited: HashSet<TermId> = HashSet::default();
        let mut stack = vec![root];
        while let Some(term) = stack.pop() {
            if !visited.insert(term) {
                continue;
            }
            match self.ctx.terms.get(term) {
                TermData::Var(name, _) if bound.contains(name) => return true,
                TermData::App(_, args) => stack.extend(args.iter().copied()),
                TermData::Not(inner) => stack.push(*inner),
                TermData::Ite(c, t, e) => {
                    stack.push(*c);
                    stack.push(*t);
                    stack.push(*e);
                }
                TermData::Let(bindings, body) => {
                    for (_, v) in bindings {
                        stack.push(*v);
                    }
                    stack.push(*body);
                }
                TermData::Forall(_, body, _) | TermData::Exists(_, body, _) => stack.push(*body),
                _ => {}
            }
        }
        false
    }
}

/// Red zone size for `stacker::maybe_grow` in the de-Skolemization rebuild.
const DESKOLEM_STACK_RED_ZONE: usize = 32 * 1024;

/// Stack segment size allocated by stacker for the de-Skolemization rebuild.
const DESKOLEM_STACK_SIZE: usize = 1024 * 1024;

/// Rebuild the DE-SKOLEMIZED counterexample obligation of a post-Skolemization
/// CEGQI universal (#quantified-ce-lemma).
///
/// `quant` is the stored `forall x⃗. B(x⃗)` where `B = psi0[y⃗ := sk(x⃗)]` is
/// the Skolemized body of an original `forall x⃗ (exists y⃗ psi0)`; `inst` is
/// its CEGQI instantiator (supplying the binder → counterexample-variable map
/// `x⃗ ↦ e⃗`). Returns the obligation `L_q = forall y⃗. ¬psi0(y⃗, e⃗)` as
/// `(binders, rho)` with `rho = ¬psi0(y⃗, e⃗)` over fresh binder variables —
/// the lemma the stored ground CE lemma `¬psi0(sk(e⃗), e⃗)` can never encode
/// (the free Skolem application keeps it satisfiable). For a universal with NO
/// Skolem applications the binder list is empty and `rho` IS the stored ground
/// CE lemma.
///
/// # Exactness
///
/// Skolem symbols are registered at their single creation site
/// (`skolemize_quantifier_body` → `TermStore::mark_skolem_symbol`) and are
/// globally fresh, so every occurrence in `B` originates from the one
/// substitution `y⃗ ↦ sk(x⃗)` on `psi0` — replacing each distinct Skolem
/// application by a fresh bound variable recovers `psi0` exactly (up to
/// hash-consing).
///
/// # v1 gates (fail-closed `None` on anything unrecognized)
///
/// - 1 or 2 binders, all `Int`, each with a CE variable;
/// - body within the `Const`/`Var`/`App`/`Not`/`Ite` fragment, quantifier-free;
/// - at most 2 distinct Skolem applications, each `Int`-sorted with every
///   argument a CE variable (`sk(e⃗)` — the shape the Skolemizer produces);
/// - NO Skolem *constant* occurrences: a Skolem constant stems from an OUTER
///   existential (`exists y forall x. psi`), and de-Skolemizing it into a
///   universal binder would be the invalid `∀∃ ⟸ ∃∀` quantifier swap.
pub(super) fn rebuild_quantified_ce_lemma(
    terms: &mut ay_core::TermStore,
    quant: TermId,
    inst: &CegqiInstantiator,
) -> Option<(Vec<(String, ay_core::Sort)>, TermId)> {
    use ay_core::kani_compat::DetHashSet as HashSet;
    const MAX_QUANT_BINDERS: usize = 2;
    const MAX_SKOLEM_APPS: usize = 2;

    let TermData::Forall(vars, body, _) = terms.get(quant).clone() else {
        return None;
    };
    if vars.is_empty() || vars.len() > MAX_QUANT_BINDERS {
        return None;
    }
    if !vars
        .iter()
        .all(|(_, sort)| matches!(sort, ay_core::Sort::Int))
    {
        return None;
    }
    let ce = inst.ce_variables();
    if !vars.iter().all(|(name, _)| ce.contains_key(name)) {
        return None;
    }
    let ce_vars: HashSet<TermId> = ce.values().copied().collect();

    // B(e⃗): the body at the counterexample variables — exactly the term the
    // stored CE lemma negates.
    let body_e = crate::ematching::subst_vars(terms, body, ce);

    // Collect the distinct registered-Skolem applications, enforcing the v1
    // fragment/provenance gates along the walk.
    let mut skolem_apps: Vec<TermId> = Vec::new();
    let mut visited: HashSet<TermId> = HashSet::default();
    let mut stack = vec![body_e];
    while let Some(t) = stack.pop() {
        if !visited.insert(t) {
            continue;
        }
        match terms.get(t).clone() {
            TermData::Const(_) => {}
            TermData::Var(name, _) => {
                if terms.is_skolem_symbol(&name) {
                    return None; // Skolem constant: outer existential — fail closed.
                }
            }
            TermData::App(sym, args) => {
                if terms.is_skolem_symbol(sym.name()) {
                    if matches!(terms.sort(t), ay_core::Sort::Int)
                        && !args.is_empty()
                        && args.iter().all(|arg| ce_vars.contains(arg))
                    {
                        if !skolem_apps.contains(&t) {
                            if skolem_apps.len() >= MAX_SKOLEM_APPS {
                                return None;
                            }
                            skolem_apps.push(t);
                        }
                        // Arguments are CE variables — nothing further below.
                        continue;
                    }
                    return None; // unrecognized Skolem occurrence — fail closed.
                }
                stack.extend(args);
            }
            TermData::Not(inner) => stack.push(inner),
            TermData::Ite(c, a, b) => {
                stack.push(c);
                stack.push(a);
                stack.push(b);
            }
            // Let bindings, nested quantifiers, or any future variant are
            // outside the exactly-rebuildable v1 fragment.
            _ => return None,
        }
    }

    let mut binders: Vec<(String, ay_core::Sort)> = Vec::with_capacity(skolem_apps.len());
    let mut replace: HashMap<TermId, TermId> = HashMap::default();
    for &app in &skolem_apps {
        let name = terms.mk_internal_symbol("deskolem");
        let fresh = terms.mk_var(name.clone(), ay_core::Sort::Int);
        binders.push((name, ay_core::Sort::Int));
        replace.insert(app, fresh);
    }
    let psi0_e = replace_mapped_terms(terms, body_e, &replace);
    Some((binders, terms.mk_not(psi0_e)))
}

/// Replace every occurrence of the map's key TERMS by their value terms,
/// rebuilding the containing structure. Total on the
/// `Const`/`Var`/`App`/`Not`/`Ite` fragment `rebuild_quantified_ce_lemma`
/// gates to; other variants are returned unchanged (the caller has already
/// failed closed on them). Uses `stacker::maybe_grow` for stack safety.
fn replace_mapped_terms(
    terms: &mut ay_core::TermStore,
    term: TermId,
    map: &HashMap<TermId, TermId>,
) -> TermId {
    stacker::maybe_grow(DESKOLEM_STACK_RED_ZONE, DESKOLEM_STACK_SIZE, || {
        if let Some(&mapped) = map.get(&term) {
            return mapped;
        }
        match terms.get(term).clone() {
            TermData::Const(_) | TermData::Var(_, _) => term,
            TermData::App(sym, args) => {
                let new_args: Vec<TermId> = args
                    .iter()
                    .map(|&arg| replace_mapped_terms(terms, arg, map))
                    .collect();
                if new_args == args {
                    term
                } else {
                    let sort = terms.sort(term).clone();
                    terms.mk_app(sym, new_args, sort)
                }
            }
            TermData::Not(inner) => {
                let new_inner = replace_mapped_terms(terms, inner, map);
                if new_inner == inner {
                    term
                } else {
                    terms.mk_not(new_inner)
                }
            }
            TermData::Ite(c, a, b) => {
                let nc = replace_mapped_terms(terms, c, map);
                let na = replace_mapped_terms(terms, a, map);
                let nb = replace_mapped_terms(terms, b, map);
                if nc == c && na == a && nb == b {
                    term
                } else {
                    terms.mk_ite(nc, na, nb)
                }
            }
            _ => term,
        }
    }) // stacker::maybe_grow
}

#[allow(clippy::panic)]
#[cfg(test)]
mod rebuild_tests {
    use super::*;
    use ay_core::term::Symbol;
    use ay_core::{Sort, TermStore};
    use num_rational::BigRational;

    fn load_assertions(smt: &str) -> Executor {
        let commands = ay_frontend::parse(smt).expect("parse qpf fixture");
        let mut exec = Executor::new();
        for command in &commands {
            let output = exec.execute(command).expect("execute qpf fixture");
            assert!(output.is_none(), "fixture must not contain a query command");
        }
        exec
    }

    fn run_premise_probe(exec: &mut Executor) -> Option<Result<SolveResult>> {
        let snapshot = exec.ctx.assertions.clone();
        let mut quantifiers = Vec::new();
        for &assertion in &snapshot {
            crate::ematching::collect_quantifiers(&mut exec.ctx.terms, assertion, &mut quantifiers);
        }
        let foralls = quantifiers
            .into_iter()
            .filter(|&q| matches!(exec.ctx.terms.get(q), TermData::Forall(..)))
            .collect::<Vec<_>>();
        exec.premise_forced_binder_refutation(&foralls, &snapshot)
    }

    fn symbol_identities(exec: &Executor) -> Vec<String> {
        let mut names = exec
            .ctx
            .symbol_iter()
            .map(|(name, info)| exec.ctx.symbol_identity_name(name, info).to_string())
            .collect::<Vec<_>>();
        names.sort();
        names
    }

    #[test]
    fn qpf_probe_refutes_only_a_verified_concrete_instance_and_preserves_outer_state() {
        let mut exec = load_assertions(
            r#"
                (set-logic UFBV)
                (declare-fun f ((_ BitVec 1)) (_ BitVec 1))
                (assert (forall ((x (_ BitVec 1)))
                  (=> (= x #b0)
                      (and (= (f x) #b0) (= (f x) #b1)))))
            "#,
        );
        exec.original_problem_had_quantifiers = true;
        exec.last_result = Some(SolveResult::Sat);
        exec.last_unknown_reason = Some(UnknownReason::Incomplete);
        let symbols_before = symbol_identities(&exec);
        let assertions_before = exec.ctx.assertions.clone();
        let parsed_before = exec.ctx.assertions_parsed().to_vec();
        let proof_enabled_before = exec.proof_tracker.is_enabled();
        let proof_steps_before = exec.proof_tracker.num_steps();
        let core_before = exec.last_assumption_core.clone();
        let core_names_before = exec.last_core_term_to_name.clone();

        let result = run_premise_probe(&mut exec);

        assert!(
            matches!(result, Some(Ok(SolveResult::Unsat(_)))),
            "the x=#b0 instance is ground-UNSAT"
        );
        assert!(
            exec.original_problem_had_quantifiers,
            "a disposable ground probe must not enable QF-only outer routes"
        );
        assert!(
            matches!(exec.last_result, Some(SolveResult::Sat)),
            "a probe must preserve the outer verdict bookkeeping"
        );
        assert_eq!(
            exec.last_unknown_reason,
            Some(UnknownReason::Incomplete),
            "a probe must preserve the outer diagnostic"
        );
        assert_eq!(
            symbol_identities(&exec),
            symbols_before,
            "fresh qpf constants must stay inside the disposable context"
        );
        assert_eq!(exec.ctx.assertions, assertions_before);
        assert_eq!(exec.ctx.assertions_parsed(), parsed_before);
        assert_eq!(exec.proof_tracker.is_enabled(), proof_enabled_before);
        assert_eq!(exec.proof_tracker.num_steps(), proof_steps_before);
        assert_eq!(exec.last_assumption_core, core_before);
        assert_eq!(exec.last_core_term_to_name, core_names_before);

        let repeated = run_premise_probe(&mut exec);
        assert!(matches!(repeated, Some(Ok(SolveResult::Unsat(_)))));
        assert_eq!(symbol_identities(&exec), symbols_before);
        assert_eq!(exec.ctx.assertions, assertions_before);
        assert_eq!(exec.ctx.assertions_parsed(), parsed_before);
    }

    #[test]
    fn qpf_probe_rejects_nonconjunctive_and_non_bv_carrier_adversaries() {
        for (label, smt) in [
            (
                "nonconjunctive",
                r#"
                    (set-logic UFBV)
                    (declare-const g Bool)
                    (declare-fun p ((_ BitVec 1)) Bool)
                    (assert (or g
                      (forall ((x (_ BitVec 1)))
                        (=> (= x x) (and (p x) (not (p x)))))))
                "#,
            ),
            (
                "model-varying carrier",
                r#"
                    (set-logic UF)
                    (declare-sort U 0)
                    (declare-const a U)
                    (declare-fun p (U U) Bool)
                    (assert (forall ((z U)) (= z a)))
                    (assert (forall ((x U) (y U))
                      (=> (distinct x y) (and (p x y) (not (p x y))))))
                "#,
            ),
            (
                "underspecified division",
                r#"
                    (set-logic UFNIA)
                    (declare-fun p (Int) Bool)
                    (assert (distinct (div 0 0) 0))
                    (assert (forall ((x Int))
                      (=> (and (= x 0) (= (div x 0) 0)) (p x))))
                "#,
            ),
            (
                "user bv-prefix direct",
                r#"
                    (set-logic UFBV)
                    (declare-fun bvtrap ((_ BitVec 1)) Bool)
                    (declare-fun p ((_ BitVec 1)) Bool)
                    (assert (not (bvtrap #b0)))
                    (assert (not (bvtrap #b1)))
                    (assert (forall ((x (_ BitVec 1)))
                      (=> (bvtrap x) (p x))))
                "#,
            ),
            (
                "user bv-prefix De Morgan",
                r#"
                    (set-logic UFBV)
                    (declare-fun bvtrap ((_ BitVec 1)) Bool)
                    (declare-fun p ((_ BitVec 1)) Bool)
                    (assert (not (bvtrap #b0)))
                    (assert (not (bvtrap #b1)))
                    (assert (forall ((x (_ BitVec 1)))
                      (or (not (bvtrap x)) (p x))))
                "#,
            ),
        ] {
            let mut exec = load_assertions(smt);
            assert!(
                run_premise_probe(&mut exec).is_none(),
                "{label} must stay outside the concrete-BV-instance refutation"
            );
        }
    }

    #[test]
    fn qpf_probe_skips_an_ineligible_first_forall_and_reaches_a_later_refutation() {
        let mut exec = load_assertions(
            r#"
                (set-logic UFBV)
                (declare-fun f ((_ BitVec 1)) (_ BitVec 1))
                (assert (forall ((unused (_ BitVec 1))) (=> true true)))
                (assert (forall ((x (_ BitVec 1)))
                  (=> (= x #b0)
                      (and (= (f x) #b0) (= (f x) #b1)))))
            "#,
        );

        assert!(
            matches!(
                run_premise_probe(&mut exec),
                Some(Ok(SolveResult::Unsat(_)))
            ),
            "an ineligible first forall must not abort the remaining forall scan"
        );
    }

    /// Build `forall x. B` where `B = psi0[y := sk_y(x)]` the way the
    /// Skolemizer does (registered internal symbol), plus its instantiator.
    fn skolemized_alternation(
        terms: &mut TermStore,
        mk_psi0: impl Fn(
            &mut TermStore,
            TermId, /* y-slot (sk app) */
            TermId, /* x */
        ) -> TermId,
    ) -> (TermId, CegqiInstantiator) {
        let x = terms.mk_var("x", Sort::Int);
        let sk_name = terms.mk_internal_symbol("sk_y");
        terms.mark_skolem_symbol(sk_name.clone());
        let sk_app = terms.mk_app(Symbol::named(sk_name), vec![x], Sort::Int);
        let body = mk_psi0(terms, sk_app, x);
        let forall = terms.mk_forall(vec![("x".to_string(), Sort::Int)], body);
        let inst = CegqiInstantiator::new(forall, terms).expect("CEGQI instantiator");
        (forall, inst)
    }

    fn negative_single_forall_with_foldable_comparison(exec: &mut Executor) -> (TermId, TermId) {
        let x = exec.ctx.terms.mk_var("x", Sort::Int);
        let lower = exec.ctx.terms.mk_var("lower", Sort::Int);
        let predicate = exec.ctx.terms.mk_var("predicate", Sort::Bool);
        let le = exec.ctx.terms.mk_le(lower, x);
        let not_le = exec.ctx.terms.mk_not(le);
        let body = exec.ctx.terms.mk_or(vec![predicate, not_le]);
        let forall = exec
            .ctx
            .terms
            .mk_forall(vec![("x".to_string(), Sort::Int)], body);
        let negative = exec.ctx.terms.mk_not(forall);
        (negative, forall)
    }

    #[test]
    fn proof_fold_preserves_certified_negative_forall_source_only() {
        let mut proof_exec = Executor::new();
        proof_exec.set_produce_proofs(true);
        let (negative, positive) = negative_single_forall_with_foldable_comparison(&mut proof_exec);
        proof_exec.ctx.assertions = vec![negative, positive];

        proof_exec.fold_quantified_linear_eqs();

        assert_eq!(
            proof_exec.ctx.assertions[0], negative,
            "proof mode must retain the exact authored source for sko_forall"
        );
        assert_ne!(
            proof_exec.ctx.assertions[1], positive,
            "positive foralls must retain the existing linear folding"
        );

        let outer_x = proof_exec.ctx.terms.mk_var("outer_x", Sort::Int);
        let inner_y = proof_exec.ctx.terms.mk_var("inner_y", Sort::Int);
        let lower = proof_exec.ctx.terms.mk_var("nested_lower", Sort::Int);
        let outer_atom = proof_exec.ctx.terms.mk_le(lower, outer_x);
        let le = proof_exec.ctx.terms.mk_le(lower, inner_y);
        let not_le = proof_exec.ctx.terms.mk_not(le);
        let exists = proof_exec
            .ctx
            .terms
            .mk_exists(vec![("inner_y".to_string(), Sort::Int)], not_le);
        let nested_body = proof_exec.ctx.terms.mk_or(vec![outer_atom, exists]);
        let nested_forall = proof_exec
            .ctx
            .terms
            .mk_forall(vec![("outer_x".to_string(), Sort::Int)], nested_body);
        let nested_negative = proof_exec.ctx.terms.mk_not(nested_forall);
        proof_exec.ctx.assertions = vec![nested_negative];

        proof_exec.fold_quantified_linear_eqs();

        assert_ne!(
            proof_exec.ctx.assertions[0], nested_negative,
            "nested quantifiers are outside the certified Skolem lane and must still fold"
        );

        let mut ordinary_exec = Executor::new();
        let (ordinary_negative, _) =
            negative_single_forall_with_foldable_comparison(&mut ordinary_exec);
        ordinary_exec.ctx.assertions = vec![ordinary_negative];

        ordinary_exec.fold_quantified_linear_eqs();

        assert_ne!(
            ordinary_exec.ctx.assertions[0], ordinary_negative,
            "non-proof solving must retain the existing NNF folding"
        );
    }

    /// 1-binder exact reconstruction: `forall x. sk(x) > x` (from
    /// `forall x exists y. y > x`) rebuilds to `forall y'. ¬(y' > e)`.
    #[test]
    fn rebuild_one_binder_alternation_exact() {
        let mut terms = TermStore::new();
        let (forall, inst) = skolemized_alternation(&mut terms, |t, y, x| t.mk_gt(y, x));
        let (binders, rho) = rebuild_quantified_ce_lemma(&mut terms, forall, &inst)
            .expect("rebuild must succeed on the canonical 1-binder alternation");
        assert_eq!(binders.len(), 1);
        assert_eq!(binders[0].1, Sort::Int);
        // rho = ¬(y' > e): the fresh binder replaces the Skolem app and the CE
        // variable replaces the universal binder.
        let e = *inst.ce_variables().get("x").expect("CE var for x");
        let fresh = terms.mk_var(binders[0].0.clone(), Sort::Int);
        let expected_inner = terms.mk_gt(fresh, e);
        let expected = terms.mk_not(expected_inner);
        assert_eq!(rho, expected, "exact syntactic reconstruction expected");
    }

    /// 2-binder exact reconstruction: `forall x. sk1(x) + sk2(x) = x` (from
    /// `forall x exists y1 y2. y1 + y2 = x`) rebuilds with two fresh binders.
    #[test]
    fn rebuild_two_binder_alternation_exact() {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::Int);
        let sk1_name = terms.mk_internal_symbol("sk_y1");
        terms.mark_skolem_symbol(sk1_name.clone());
        let sk2_name = terms.mk_internal_symbol("sk_y2");
        terms.mark_skolem_symbol(sk2_name.clone());
        let sk1 = terms.mk_app(Symbol::named(sk1_name), vec![x], Sort::Int);
        let sk2 = terms.mk_app(Symbol::named(sk2_name), vec![x], Sort::Int);
        let sum = terms.mk_add(vec![sk1, sk2]);
        let body = terms.mk_eq(sum, x);
        let forall = terms.mk_forall(vec![("x".to_string(), Sort::Int)], body);
        let inst = CegqiInstantiator::new(forall, &mut terms).expect("CEGQI instantiator");
        let (binders, rho) = rebuild_quantified_ce_lemma(&mut terms, forall, &inst)
            .expect("rebuild must succeed on the 2-binder alternation");
        assert_eq!(binders.len(), 2);
        let e = *inst.ce_variables().get("x").expect("CE var for x");
        let y1 = terms.mk_var(binders[0].0.clone(), Sort::Int);
        let y2 = terms.mk_var(binders[1].0.clone(), Sort::Int);
        // Discovery order of the two sk apps is deterministic but not
        // spec'd here; accept either assignment.
        let sum_a = terms.mk_add(vec![y1, y2]);
        let eq_a = terms.mk_eq(sum_a, e);
        let expected_a = terms.mk_not(eq_a);
        let sum_b = terms.mk_add(vec![y2, y1]);
        let eq_b = terms.mk_eq(sum_b, e);
        let expected_b = terms.mk_not(eq_b);
        assert!(
            rho == expected_a || rho == expected_b,
            "exact syntactic reconstruction expected"
        );
    }

    /// Fail-closed: non-Int binder.
    #[test]
    fn rebuild_fails_closed_on_non_int_binder() {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::Real);
        let sk_name = terms.mk_internal_symbol("sk_y");
        terms.mark_skolem_symbol(sk_name.clone());
        let sk_app = terms.mk_app(Symbol::named(sk_name), vec![x], Sort::Real);
        let body = terms.mk_gt(sk_app, x);
        let forall = terms.mk_forall(vec![("x".to_string(), Sort::Real)], body);
        let inst = CegqiInstantiator::new(forall, &mut terms).expect("CEGQI instantiator");
        assert!(rebuild_quantified_ce_lemma(&mut terms, forall, &inst).is_none());
    }

    /// Fail-closed: more than two binders.
    #[test]
    fn rebuild_fails_closed_on_three_binders() {
        let mut terms = TermStore::new();
        let x1 = terms.mk_var("x1", Sort::Int);
        let x2 = terms.mk_var("x2", Sort::Int);
        let x3 = terms.mk_var("x3", Sort::Int);
        let s12 = terms.mk_add(vec![x1, x2]);
        let sum = terms.mk_add(vec![s12, x3]);
        let zero = terms.mk_int(0.into());
        let body = terms.mk_ge(sum, zero);
        let forall = terms.mk_forall(
            vec![
                ("x1".to_string(), Sort::Int),
                ("x2".to_string(), Sort::Int),
                ("x3".to_string(), Sort::Int),
            ],
            body,
        );
        let inst = CegqiInstantiator::new(forall, &mut terms).expect("CEGQI instantiator");
        assert!(rebuild_quantified_ce_lemma(&mut terms, forall, &inst).is_none());
    }

    /// Fail-closed: a Skolem application whose argument is NOT a CE variable
    /// (here a ground constant) — outside the exact-provenance fragment.
    #[test]
    fn rebuild_fails_closed_on_skolem_app_over_non_ce_args() {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::Int);
        let five = terms.mk_int(5.into());
        let sk_name = terms.mk_internal_symbol("sk_y");
        terms.mark_skolem_symbol(sk_name.clone());
        let sk_app = terms.mk_app(Symbol::named(sk_name), vec![five], Sort::Int);
        let sum = terms.mk_add(vec![sk_app, x]);
        let zero = terms.mk_int(0.into());
        let body = terms.mk_ge(sum, zero);
        let forall = terms.mk_forall(vec![("x".to_string(), Sort::Int)], body);
        let inst = CegqiInstantiator::new(forall, &mut terms).expect("CEGQI instantiator");
        assert!(rebuild_quantified_ce_lemma(&mut terms, forall, &inst).is_none());
    }

    /// Fail-closed: a Skolem CONSTANT (outer existential `exists y forall x`)
    /// must never be de-Skolemized into a universal binder (`∀∃ ⇒ ∃∀` swap).
    #[test]
    fn rebuild_fails_closed_on_skolem_constant() {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::Int);
        let sk = terms.mk_fresh_var("sk!y", Sort::Int);
        if let TermData::Var(name, _) = terms.get(sk) {
            let name = name.clone();
            terms.mark_skolem_symbol(name);
        }
        let body = terms.mk_gt(sk, x);
        let forall = terms.mk_forall(vec![("x".to_string(), Sort::Int)], body);
        let inst = CegqiInstantiator::new(forall, &mut terms).expect("CEGQI instantiator");
        assert!(rebuild_quantified_ce_lemma(&mut terms, forall, &inst).is_none());
    }

    /// No Skolem occurrences at all: the obligation degenerates to the stored
    /// ground CE lemma (empty binder list).
    #[test]
    fn rebuild_ground_lemma_degenerate() {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::Int);
        let zero = terms.mk_int(0.into());
        let body = terms.mk_ge(x, zero);
        let forall = terms.mk_forall(vec![("x".to_string(), Sort::Int)], body);
        let inst = CegqiInstantiator::new(forall, &mut terms).expect("CEGQI instantiator");
        let (binders, rho) = rebuild_quantified_ce_lemma(&mut terms, forall, &inst)
            .expect("ground universal must rebuild to its ground CE lemma");
        assert!(binders.is_empty());
        let expected = inst
            .create_ce_lemma(&mut terms)
            .expect("stored CE lemma must build");
        assert_eq!(rho, expected, "must equal the stored ground CE lemma");
    }

    #[test]
    fn pin_eval_const_preserves_expected_scalar_sort() {
        let mut terms = TermStore::new();

        let bool_term = pin_eval_const_for_sort(&mut terms, &Sort::Bool, &EvalValue::Bool(true))
            .expect("Bool value must rebuild as Bool");
        assert_eq!(terms.sort(bool_term), &Sort::Bool);

        let two = BigRational::from_integer(2.into());
        let int_term =
            pin_eval_const_for_sort(&mut terms, &Sort::Int, &EvalValue::Rational(two.clone()))
                .expect("integral rational must rebuild as Int when Int is expected");
        assert_eq!(terms.sort(int_term), &Sort::Int);

        let integral_real =
            pin_eval_const_for_sort(&mut terms, &Sort::Real, &EvalValue::Rational(two))
                .expect("integral Real must remain Real");
        assert_eq!(terms.sort(integral_real), &Sort::Real);

        let half = BigRational::new(1.into(), 2.into());
        let fractional_real =
            pin_eval_const_for_sort(&mut terms, &Sort::Real, &EvalValue::Rational(half))
                .expect("nonintegral Real must rebuild exactly");
        assert_eq!(terms.sort(fractional_real), &Sort::Real);

        let bv8 = Sort::bitvec(8);
        let bv_term = pin_eval_const_for_sort(
            &mut terms,
            &bv8,
            &EvalValue::BitVec {
                value: 0x1ff.into(),
                width: 8,
            },
        )
        .expect("matching bit-vector width must rebuild");
        assert_eq!(terms.sort(bv_term), &bv8);
    }

    #[test]
    fn pin_eval_const_rejects_incompatible_value_sort_pairs() {
        let mut terms = TermStore::new();
        let half = EvalValue::Rational(BigRational::new(1.into(), 2.into()));

        assert!(pin_eval_const_for_sort(&mut terms, &Sort::Int, &half).is_none());
        assert!(pin_eval_const_for_sort(&mut terms, &Sort::Bool, &half).is_none());
        assert!(pin_eval_const_for_sort(&mut terms, &Sort::Real, &EvalValue::Bool(true)).is_none());
        assert!(pin_eval_const_for_sort(
            &mut terms,
            &Sort::bitvec(8),
            &EvalValue::BitVec {
                value: 7.into(),
                width: 16,
            },
        )
        .is_none());
    }
}
