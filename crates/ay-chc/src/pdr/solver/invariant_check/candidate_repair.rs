// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Counterexample-guided repair of demoted Safe candidates (#4751 L4).
//!
//! When strict final validation demotes a direct-safety Safe candidate
//! (#9227), the failure is frequently caused by a handful of "poison"
//! conjuncts that were admitted into frame[1] through OPTIMISTIC relative
//! oracles (entry-domain-conditioned self-inductiveness, prev-level-0
//! init-only must-summary entry checks). Example (bouncy two counters):
//! `(<= a0 0)` is a VALID frame[1] lemma but globally non-inductive; the
//! whole-frame conjunction is then claimed as a global invariant and strict
//! `verify_model` correctly rejects it with a concrete counterexample.
//!
//! Pre-repair, that demotion sent the solve back into a main loop whose
//! frames still carried the poison, where every blocking query paid for the
//! bloated frame — bouncy went from a 0.1s conclude to a 60s wall-clock
//! timeout after #4751's demote-continue change.
//!
//! This pass runs the standard Houdini-with-teacher argument at the demotion
//! boundary: the strict verifier IS the teacher. Each round:
//! 1. strict per-rule verification returns the failing clause plus the
//!    concrete SAT model (as a `canonical_var = value` post-state cube);
//! 2. every candidate conjunct of the failing head predicate that concretely
//!    evaluates to FALSE under that model is dropped from the CANDIDATE
//!    (frames are untouched);
//! 3. immediately run the full strict verifier on the weakened candidate,
//!    before observing cancellation at another search boundary;
//! 4. repeat, bounded by `MAX_REPAIR_ROUNDS` per call and
//!    `MAX_REPAIR_ROUNDS_PER_SOLVE` per solve.
//!
//! SOUNDNESS: repair only ever REMOVES conjuncts from an invariant
//! CANDIDATE, i.e. weakens it — it can never manufacture a false Safe. The
//! result type can only be constructed after the full unmodified fresh-context
//! strict gate succeeds. A candidate weakened below the safety threshold
//! simply fails that gate and demotes exactly as before. The strict checker
//! itself is never loosened, and it still observes the existing solve deadline
//! and cancellation token.

use super::{ChcExpr, ChcOp, InvariantModel, PdrSolver, PredicateId};
use crate::expr::evaluate_expr;
use crate::smt::SmtValue;
use ay_core::kani_compat::DetHashMap as FxHashMap;

/// Maximum teacher/repair rounds for one demoted candidate.
pub(crate) const MAX_REPAIR_ROUNDS: usize = 8;

/// Total repair-round budget per solve. Repeated demotions in a long main
/// loop (e.g. s_multipl_12's obligation-budget path) must not turn into an
/// unbounded sequence of full strict verifications.
pub(crate) const MAX_REPAIR_ROUNDS_PER_SOLVE: usize = 32;

pub(in crate::pdr::solver) type CandidateValidationFailure =
    (PredicateId, ChcExpr, PredicateId, ChcExpr);

/// A repaired candidate that already passed fresh-context strict verification.
///
/// Keeping this wrapper private to the PDR solver prevents a caller from
/// publishing a merely weakened candidate without the mandatory recheck.
pub(in crate::pdr::solver) struct StrictlyVerifiedRepair(InvariantModel);

impl StrictlyVerifiedRepair {
    pub(in crate::pdr::solver) fn into_model(self) -> InvariantModel {
        self.0
    }
}

impl PdrSolver {
    fn strict_candidate_validation_failure(
        &mut self,
        model: &InvariantModel,
    ) -> Option<CandidateValidationFailure> {
        let previous_strict_proofs = self.config.strict_proofs;
        self.config.strict_proofs = true;
        let failure = self.verify_model_fresh_with_failure(model);
        self.config.strict_proofs = previous_strict_proofs;
        failure
    }

    /// Try to repair a strictly-demoted Safe candidate by dropping the
    /// conjuncts falsified by the verifier's concrete counterexamples.
    ///
    /// The standalone entry point obtains its own initial teacher failure.
    /// Production demotion handling uses
    /// [`repair_demoted_candidate_after_failure`](Self::repair_demoted_candidate_after_failure)
    /// to reuse the failure from the mandatory publication gate.
    #[cfg(test)]
    pub(in crate::pdr::solver) fn repair_demoted_candidate(
        &mut self,
        model: InvariantModel,
    ) -> Option<StrictlyVerifiedRepair> {
        if self.is_cancelled() {
            return None;
        }
        let failure = self.strict_candidate_validation_failure(&model)?;
        self.repair_demoted_candidate_after_failure(model, failure)
    }

    /// Repair a candidate using the failure already produced by the strict
    /// publication gate.
    ///
    /// Every mutation is followed immediately by a fresh-context strict
    /// recheck. There is deliberately no cancellation check between weakening
    /// the candidate and invoking that verifier: the verifier itself observes
    /// the unchanged deadline/token and fails closed, while avoiding the old
    /// race where cancellation at the next loop boundary skipped the recheck
    /// entirely.
    pub(in crate::pdr::solver) fn repair_demoted_candidate_after_failure(
        &mut self,
        mut model: InvariantModel,
        mut failure: CandidateValidationFailure,
    ) -> Option<StrictlyVerifiedRepair> {
        // The array-scalarized flow validates through a dedicated verifier on
        // the original problem; keep it on the pre-existing path.
        if !self.array_scalarization_maps.is_empty() {
            return None;
        }
        if model.has_quantified_array_certificate() || model.is_empty() {
            return None;
        }
        if self.candidate_repair_rounds_used >= MAX_REPAIR_ROUNDS_PER_SOLVE {
            return None;
        }

        let mut dropped_optimistic_fallback = false;
        for _round in 0..MAX_REPAIR_ROUNDS {
            if self.is_cancelled()
                || self.candidate_repair_rounds_used >= MAX_REPAIR_ROUNDS_PER_SOLVE
            {
                return None;
            }
            let (_body_pred, _pre_state, fail_pred, cex_state) = failure;

            // Learner step: drop exactly the concretely-falsified conjuncts.
            let dropped =
                self.drop_falsified_candidate_conjuncts(&mut model, fail_pred, &cex_state);
            if dropped > 0 {
                if self.config.verbose {
                    safe_eprintln!(
                        "PDR: candidate-repair: dropped {} falsified conjunct(s) for pred {} (#4751 L4)",
                        dropped,
                        fail_pred.index()
                    );
                }
            } else if !dropped_optimistic_fallback {
                // No conjunct is concretely falsified (e.g. the verifier could
                // not extract a usable model). Fall back ONCE to dropping the
                // conjuncts that entered frame[1] through the OPTIMISTIC
                // entry-domain admission oracle — the known poison source.
                dropped_optimistic_fallback = true;
                let dropped_opt = self.drop_optimistic_candidate_conjuncts(&mut model, fail_pred);
                if dropped_opt == 0 {
                    return None;
                }
                if self.config.verbose {
                    safe_eprintln!(
                        "PDR: candidate-repair: dropped {} optimistic-entry conjunct(s) for pred {} (#4751 L4 fallback)",
                        dropped_opt,
                        fail_pred.index()
                    );
                }
            } else {
                return None;
            }

            // The modified candidate no longer carries whatever per-lemma
            // evidence justified these flags; fail closed to full validation.
            model.individually_inductive = false;
            model.convergence_proven = false;

            // Recheck the modified candidate immediately. The strict verifier
            // observes the same global deadline and cancellation token, so this
            // cannot extend the solve budget. `None` is the verified outcome.
            self.candidate_repair_rounds_used += 1;
            match self.strict_candidate_validation_failure(&model) {
                None => return Some(StrictlyVerifiedRepair(model)),
                Some(next_failure) => failure = next_failure,
            }
        }
        None
    }

    /// Drop every conjunct of `pred`'s candidate interpretation that
    /// concretely evaluates to FALSE under the counterexample post-state
    /// `cex_state` (a conjunction of `canonical_var = value` equalities).
    /// Returns the number of dropped conjuncts. Only weakens the candidate.
    pub(in crate::pdr::solver) fn drop_falsified_candidate_conjuncts(
        &self,
        model: &mut InvariantModel,
        pred: PredicateId,
        cex_state: &ChcExpr,
    ) -> usize {
        let assignment = Self::assignment_from_state_conjunction(cex_state);
        if assignment.is_empty() {
            return 0;
        }
        let Some(canonical) = self.canonical_vars(pred) else {
            return 0;
        };
        let Some(interp) = model.get(&pred) else {
            return 0;
        };
        if canonical.len() != interp.vars.len() {
            return 0;
        }
        // The cube is over canonical var names; the interpretation may use its
        // own binder names. Rebind positionally.
        let mut named: FxHashMap<String, SmtValue> = FxHashMap::default();
        for (canon_var, interp_var) in canonical.iter().zip(interp.vars.iter()) {
            if let Some(value) = assignment.get(&canon_var.name) {
                named.insert(interp_var.name.clone(), value.clone());
            }
        }
        if named.is_empty() {
            return 0;
        }

        let conjuncts = interp.formula.collect_conjuncts();
        let mut kept: Vec<ChcExpr> = Vec::with_capacity(conjuncts.len());
        let mut dropped = 0usize;
        for conjunct in conjuncts {
            if evaluate_expr(&conjunct, &named) == Some(SmtValue::Bool(false)) {
                if self.config.verbose {
                    safe_eprintln!(
                        "PDR: candidate-repair: pred {} conjunct falsified by counterexample: {}",
                        pred.index(),
                        conjunct
                    );
                }
                dropped += 1;
            } else {
                kept.push(conjunct);
            }
        }
        if dropped == 0 {
            return 0;
        }
        let new_formula = if kept.is_empty() {
            ChcExpr::Bool(true)
        } else {
            ChcExpr::and_all(kept)
        };
        if let Some(interp) = model.interpretations.get_mut(&pred) {
            interp.formula = new_formula;
        }
        dropped
    }

    /// Drop every conjunct of `pred`'s candidate interpretation that matches
    /// a frame[1] lemma admitted through the OPTIMISTIC entry-domain oracle
    /// (`is_self_inductive_blocking_with_entry_domain`, cand4 hardening).
    /// Returns the number of dropped conjuncts. Only weakens the candidate;
    /// frame lemmas themselves are untouched.
    fn drop_optimistic_candidate_conjuncts(
        &self,
        model: &mut InvariantModel,
        pred: PredicateId,
    ) -> usize {
        let Some(frame1) = self.frames.get(1) else {
            return 0;
        };
        let mut optimistic: Vec<ChcExpr> = Vec::new();
        for lemma in frame1
            .lemmas
            .iter()
            .filter(|l| l.predicate == pred && l.optimistic_entry)
        {
            optimistic.extend(lemma.formula.collect_conjuncts());
        }
        if optimistic.is_empty() {
            return 0;
        }
        let Some(interp) = model.get(&pred) else {
            return 0;
        };
        let conjuncts = interp.formula.collect_conjuncts();
        let mut kept: Vec<ChcExpr> = Vec::with_capacity(conjuncts.len());
        let mut dropped = 0usize;
        for conjunct in conjuncts {
            if optimistic.contains(&conjunct) {
                dropped += 1;
            } else {
                kept.push(conjunct);
            }
        }
        if dropped == 0 {
            return 0;
        }
        let new_formula = if kept.is_empty() {
            ChcExpr::Bool(true)
        } else {
            ChcExpr::and_all(kept)
        };
        if let Some(interp) = model.interpretations.get_mut(&pred) {
            interp.formula = new_formula;
        }
        dropped
    }

    /// Extract a `var_name -> value` assignment from a conjunction of
    /// `var = constant` equalities (the shape produced by
    /// `extract_state_from_args`). Non-conforming conjuncts are skipped.
    pub(in crate::pdr::solver) fn assignment_from_state_conjunction(
        state: &ChcExpr,
    ) -> FxHashMap<String, SmtValue> {
        let empty: FxHashMap<String, SmtValue> = FxHashMap::default();
        let mut assignment: FxHashMap<String, SmtValue> = FxHashMap::default();
        for conjunct in state.collect_conjuncts() {
            let ChcExpr::Op(ChcOp::Eq, args) = &conjunct else {
                continue;
            };
            if args.len() != 2 {
                continue;
            }
            let (var, value_expr) = match (args[0].as_ref(), args[1].as_ref()) {
                (ChcExpr::Var(v), value) => (v, value),
                (value, ChcExpr::Var(v)) => (v, value),
                _ => continue,
            };
            if let Some(value) = evaluate_expr(value_expr, &empty) {
                assignment.insert(var.name.clone(), value);
            }
        }
        assignment
    }
}
