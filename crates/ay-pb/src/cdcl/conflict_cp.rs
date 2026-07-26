// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Proof-logging (VeriPB) conflict analysis over `CpConstraint`s for
//! `PbCdclSolver`: the trusted heuristic reference path and the
//! `resolve_*_with_proof` cutting-plane resolution. Extracted from `cdcl.rs`;
//! these remain methods on [`super::PbCdclSolver`].

use super::*;
use crate::cutting_planes::{add_coeff, gcd_i64, lcm_i64, negate_lit, CpConstraint};
#[cfg(debug_assertions)]
use crate::types::PbConstraint;

impl PbCdclSolver {
    /// Debug-only side-effect-free re-run of the trusted heuristic
    /// `CpConstraint` conflict analysis. Returns `(backtrack_level, learned
    /// PbConstraint)`. Performs NO activity bumping, stats mutation, decay, or
    /// proof logging.
    ///
    /// Retained as a documented trusted reference for the heuristic
    /// (add-then-divide) round-to-one. It is NOT used as a differential oracle
    /// for the proven round-to-one dense path, which deliberately produces a
    /// different (stronger) learned constraint; that path's soundness is
    /// asserted via the RoundingSat-slack / asserting invariants in
    /// `analyze_conflict_dense_inner` plus the exhaustive
    /// `proven_round_to_one_semantic_entailment` property test.
    #[cfg(debug_assertions)]
    #[allow(dead_code)]
    fn analyze_conflict_cp_reference(&mut self, conflict_cid: usize) -> (u32, PbConstraint) {
        let Some(mut learned) = self.cp_constraint_by_index(conflict_cid) else {
            return (0, PbConstraint::from(&CpConstraint::new(HashMap::new(), 0)));
        };

        learned.saturate();

        let trail_snapshot: Vec<(Lit, Option<usize>)> = self
            .trail
            .iter()
            .rev()
            .map(|entry| (entry.lit, entry.reason))
            .collect();

        for (trail_lit, reason_opt) in &trail_snapshot {
            if self.count_current_level_falsified_literals(&learned) <= 1 {
                break;
            }
            let falsified_lit = dimacs_to_pb_lit(-*trail_lit);
            if learned.coefficient(falsified_lit) == 0 {
                continue;
            }
            let Some(reason_cid) = reason_opt else {
                continue;
            };
            let Some(reason) = self.cp_constraint_by_index(*reason_cid) else {
                continue;
            };
            let pivot = dimacs_to_pb_lit(*trail_lit);
            let asserting_candidate = self.asserting_candidate_after_resolve(&learned, pivot);
            // proof_writer is None on this path, so the `_with_proof` helper logs
            // nothing and is side-effect-free.
            let resolved = self.resolve_round_to_one_with_proof(
                &learned,
                &reason,
                pivot,
                asserting_candidate,
                None,
                None,
            );
            let Some((resolved_constraint, _pid, _used)) = resolved else {
                continue;
            };
            learned = resolved_constraint;
        }

        learned.saturate();
        learned
            .gcd_divide()
            .expect("reference learned PB constraint must support GCD division");

        let asserting_lit = self.unique_current_level_falsified_literal(&learned);

        let trail_levels: Vec<(u32, u32)> = self
            .trail
            .iter()
            .map(|entry| (entry.lit.unsigned_abs(), entry.level))
            .collect();
        let propagator_snapshot: Vec<(PbLit, bool)> = learned
            .coefficients()
            .keys()
            .map(|&lit| {
                let dimacs = pb_lit_to_dimacs(lit);
                let is_false = self.propagator.value(dimacs) == LitValue::False;
                (lit, is_false)
            })
            .collect();
        learned.weaken_conservative(asserting_lit, |lit| {
            let is_false = propagator_snapshot
                .iter()
                .find(|(l, _)| *l == lit)
                .map_or(false, |(_, f)| *f);
            if !is_false {
                return None;
            }
            trail_levels
                .iter()
                .rev()
                .find(|(var, _)| *var == lit.var)
                .map(|(_, level)| *level)
        });

        learned.saturate();
        learned
            .gcd_divide()
            .expect("reference post-weakening GCD division must succeed");

        let backtrack_level = self
            .unique_current_level_falsified_literal(&learned)
            .map_or(0, |al| self.backtrack_level_for_constraint(&learned, al));

        (backtrack_level, PbConstraint::from(&learned))
    }

    /// Resolves two CP constraints on a pivot, logging proof steps for each
    /// sub-operation (multiply, add, saturate).
    fn resolve_cp_constraints_with_proof(
        &mut self,
        conflict: &CpConstraint,
        reason: &CpConstraint,
        pivot: PbLit,
        conflict_proof_id: Option<ConstraintId>,
        reason_proof_id: Option<ConstraintId>,
    ) -> Option<(CpConstraint, Option<ConstraintId>)> {
        let negated_pivot = negate_lit(pivot);

        let (pivot_side, negated_side, pivot_pid, negated_pid) =
            if conflict.coefficient(pivot) > 0 && reason.coefficient(negated_pivot) > 0 {
                (conflict, reason, conflict_proof_id, reason_proof_id)
            } else if conflict.coefficient(negated_pivot) > 0 && reason.coefficient(pivot) > 0 {
                (reason, conflict, reason_proof_id, conflict_proof_id)
            } else {
                return None;
            };

        let pivot_coeff = pivot_side.coefficient(pivot);
        let negated_coeff = negated_side.coefficient(negated_pivot);
        let lcm = lcm_i64(pivot_coeff, negated_coeff);
        let pivot_factor = lcm / pivot_coeff;
        let negated_factor = lcm / negated_coeff;

        let mut scaled_pivot = pivot_side.clone();
        scaled_pivot.multiply(pivot_factor).ok()?;

        let mut scaled_negated = negated_side.clone();
        scaled_negated.multiply(negated_factor).ok()?;

        // Log multiply steps for each side (only when factor > 1).
        let mut logged_pivot_pid = pivot_pid;
        if pivot_factor > 1 {
            if let Some(pid) = pivot_pid {
                logged_pivot_pid = self.log_proof_step(ProofStep::Multiply(pid, pivot_factor));
            }
        }

        let mut logged_negated_pid = negated_pid;
        if negated_factor > 1 {
            if let Some(pid) = negated_pid {
                logged_negated_pid = self.log_proof_step(ProofStep::Multiply(pid, negated_factor));
            }
        }

        let mut coeffs = HashMap::new();
        for (lit, coeff) in scaled_pivot.coefficients() {
            if *lit != pivot {
                add_coeff(&mut coeffs, *lit, *coeff);
            }
        }
        for (lit, coeff) in scaled_negated.coefficients() {
            if *lit != negated_pivot {
                add_coeff(&mut coeffs, *lit, *coeff);
            }
        }

        let degree = scaled_pivot
            .degree()
            .checked_add(scaled_negated.degree())
            .and_then(|sum| sum.checked_sub(lcm))?;

        let mut resolved = CpConstraint::new(coeffs, degree);

        // Log addition step.
        let mut result_pid = match (logged_pivot_pid, logged_negated_pid) {
            (Some(left), Some(right)) => self.log_proof_step(ProofStep::Addition(left, right)),
            _ => None,
        };

        // Log saturation step.
        resolved.saturate();
        if let Some(pid) = result_pid {
            result_pid = self.log_proof_step(ProofStep::Saturate(pid));
        }

        Some((resolved, result_pid))
    }

    /// Returns the asserting literal candidate after resolving away `pivot`.
    ///
    /// This is the unique falsified literal at the current decision level
    /// whose variable differs from the pivot variable. If there are multiple
    /// such literals (i.e., the result would not yet be asserting), returns
    /// `None` because division would not help at this step.
    pub(super) fn asserting_candidate_after_resolve(
        &self,
        constraint: &CpConstraint,
        pivot: PbLit,
    ) -> Option<PbLit> {
        let mut candidate = None;
        let mut count = 0;

        for &lit in constraint.coefficients().keys() {
            // Skip the pivot literal itself (it will be resolved away).
            if lit.var == pivot.var {
                continue;
            }
            if self.false_literal_level(lit) != Some(self.decision_level) {
                continue;
            }
            count += 1;
            if count > 1 {
                return None; // More than one remaining at current level.
            }
            candidate = Some(lit);
        }

        candidate
    }

    /// Round-to-one resolution with proof logging.
    ///
    /// Uses the cutting-planes division rule when the asserting literal would
    /// have coefficient > 1 after standard addition. This produces shorter
    /// constraints (exponentially in some cases) compared to pure addition.
    ///
    /// Returns `(resolved_constraint, proof_id, used_division)`.
    pub(super) fn resolve_round_to_one_with_proof(
        &mut self,
        conflict: &CpConstraint,
        reason: &CpConstraint,
        pivot: PbLit,
        asserting_lit: Option<PbLit>,
        conflict_proof_id: Option<ConstraintId>,
        reason_proof_id: Option<ConstraintId>,
    ) -> Option<(CpConstraint, Option<ConstraintId>, bool)> {
        let negated_pivot = negate_lit(pivot);

        // Determine sides: pivot_side has `pivot`, negated_side has `~pivot`.
        let (pivot_side, negated_side, pivot_pid, negated_pid) =
            if conflict.coefficient(pivot) > 0 && reason.coefficient(negated_pivot) > 0 {
                (conflict, reason, conflict_proof_id, reason_proof_id)
            } else if conflict.coefficient(negated_pivot) > 0 && reason.coefficient(pivot) > 0 {
                (reason, conflict, reason_proof_id, conflict_proof_id)
            } else {
                return None;
            };

        let a = pivot_side.coefficient(pivot);
        let b = negated_side.coefficient(negated_pivot);
        let g = gcd_i64(a, b);
        let left_factor = b / g;
        let right_factor = a / g;

        let mut scaled_pivot = pivot_side.clone();
        let mut scaled_negated = negated_side.clone();

        // Try checked multiplication; fall back to standard resolve on overflow.
        if left_factor > 1 {
            if scaled_pivot.multiply_checked(left_factor).is_err() {
                return self
                    .resolve_cp_constraints_with_proof(
                        conflict,
                        reason,
                        pivot,
                        conflict_proof_id,
                        reason_proof_id,
                    )
                    .map(|(c, pid)| (c, pid, false));
            }
        }
        if right_factor > 1 {
            if scaled_negated.multiply_checked(right_factor).is_err() {
                return self
                    .resolve_cp_constraints_with_proof(
                        conflict,
                        reason,
                        pivot,
                        conflict_proof_id,
                        reason_proof_id,
                    )
                    .map(|(c, pid)| (c, pid, false));
            }
        }

        // Build resolvent.
        let mut coeffs = HashMap::new();
        for (&lit, &coeff) in scaled_pivot.coefficients() {
            if lit != pivot {
                add_coeff(&mut coeffs, lit, coeff);
            }
        }
        for (&lit, &coeff) in scaled_negated.coefficients() {
            if lit != negated_pivot {
                add_coeff(&mut coeffs, lit, coeff);
            }
        }

        let lcm_val = a / g * b;
        let degree = scaled_pivot
            .degree()
            .checked_add(scaled_negated.degree())
            .and_then(|sum| sum.checked_sub(lcm_val))?;

        let mut resolved = CpConstraint::new(coeffs, degree);

        // Log proof steps: multiply each side.
        let mut logged_pivot_pid = pivot_pid;
        if left_factor > 1 {
            if let Some(pid) = pivot_pid {
                logged_pivot_pid = self.log_proof_step(ProofStep::Multiply(pid, left_factor));
            }
        }

        let mut logged_negated_pid = negated_pid;
        if right_factor > 1 {
            if let Some(pid) = negated_pid {
                logged_negated_pid = self.log_proof_step(ProofStep::Multiply(pid, right_factor));
            }
        }

        // Log addition step.
        let mut result_pid = match (logged_pivot_pid, logged_negated_pid) {
            (Some(left), Some(right)) => self.log_proof_step(ProofStep::Addition(left, right)),
            _ => None,
        };

        // Log saturation step.
        resolved.saturate();
        if let Some(pid) = result_pid {
            result_pid = self.log_proof_step(ProofStep::Saturate(pid));
        }

        // Apply round-to-one division if an asserting literal has coefficient
        // > 1. The caller passes a cheap pre-resolution candidate, but
        // cancellation during resolution can remove it or expose a different
        // unique current-level literal. Fall back to the actual resolvent in
        // that case so round-to-one is not missed.
        let mut used_division = false;
        let division_lit = match asserting_lit {
            Some(alit) if resolved.coefficient(alit) > 1 => Some(alit),
            _ => self.unique_current_level_falsified_literal(&resolved),
        };
        if let Some(alit) = division_lit {
            let a_coeff = resolved.coefficient(alit);
            if a_coeff > 1 {
                if resolved.divide(a_coeff).is_ok() {
                    used_division = true;
                    if let Some(pid) = result_pid {
                        result_pid = self.log_proof_step(ProofStep::Divide(pid, a_coeff));
                    }
                    // Re-saturate after division (may create new opportunities).
                    resolved.saturate();
                    if let Some(pid) = result_pid {
                        result_pid = self.log_proof_step(ProofStep::Saturate(pid));
                    }
                }
            }
        }

        Some((resolved, result_pid, used_division))
    }
}
