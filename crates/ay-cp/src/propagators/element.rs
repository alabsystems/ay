// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Element constraint propagator: `result = array[index]`.
//!
//! Bounds-consistency: propagates index→result, result→index, and
//! bidirectionally when index is fixed. O(ub(index) - lb(index)) per round.
//!
//! References: Van Hentenryck & Carillon (AAAI 1988), OR-Tools CP-SAT,
//! Chuffed `chuffed/globals/element.c`.

use crate::encoder::IntegerEncoder;
use crate::propagator::{Explanation, PropagationResult, Propagator, PropagatorPriority};
use crate::trail::IntegerTrail;
use crate::variable::IntVarId;

/// Element constraint propagator: `result = array[index]`.
///
/// The index is 0-based. If `array` has length n, then index ∈ [0, n-1].
#[derive(Debug)]
pub struct Element {
    /// The index variable (0-based)
    index: IntVarId,
    /// The array of variables
    array: Vec<IntVarId>,
    /// The result variable (= array[index])
    result: IntVarId,
    /// All watched variables (index, array elements, result)
    all_vars: Vec<IntVarId>,
}

impl Element {
    /// Create a new element constraint: `result = array[index]`.
    pub fn new(index: IntVarId, array: Vec<IntVarId>, result: IntVarId) -> Self {
        assert!(
            !array.is_empty(),
            "element constraint needs non-empty array"
        );
        let mut all_vars = vec![index, result];
        all_vars.extend_from_slice(&array);
        Self {
            index,
            array,
            result,
            all_vars,
        }
    }

    /// Build explanation from index bounds + array element bounds for given indices.
    ///
    /// Returns `None` if any required literal lookup fails (#5910, #5986).
    fn build_reasons_from_index_and_array(
        &self,
        trail: &IntegerTrail,
        encoder: &IntegerEncoder,
        index_range: std::ops::RangeInclusive<i64>,
    ) -> Option<Vec<ay_sat::Literal>> {
        let mut reasons = Vec::new();

        // Index bounds
        reasons.push(encoder.lookup_ge(self.index, trail.lb(self.index))?);
        reasons.push(encoder.lookup_le(self.index, trail.ub(self.index))?);

        // Array element bounds for the index range
        for i in index_range {
            if i >= 0 && (i as usize) < self.array.len() {
                let arr_var = self.array[i as usize];
                reasons.push(encoder.lookup_ge(arr_var, trail.lb(arr_var))?);
                reasons.push(encoder.lookup_le(arr_var, trail.ub(arr_var))?);
            }
        }

        Some(reasons)
    }

    /// Build explanation from result bounds + index bounds.
    ///
    /// Returns `None` if any required literal lookup fails (#5910, #5986).
    fn build_reasons_result_and_index(
        &self,
        trail: &IntegerTrail,
        encoder: &IntegerEncoder,
    ) -> Option<Vec<ay_sat::Literal>> {
        // Result bounds + index bounds
        let a = encoder.lookup_ge(self.result, trail.lb(self.result))?;
        let b = encoder.lookup_le(self.result, trail.ub(self.result))?;
        let c = encoder.lookup_ge(self.index, trail.lb(self.index))?;
        let d = encoder.lookup_le(self.index, trail.ub(self.index))?;
        Some(vec![a, b, c, d])
    }

    /// Propagate: index → result bounds.
    /// For each valid index, union the array variable's bounds into result.
    fn propagate_index_to_result(
        &self,
        trail: &IntegerTrail,
        encoder: &IntegerEncoder,
        clauses: &mut Vec<Vec<ay_sat::Literal>>,
    ) -> Option<Vec<ay_sat::Literal>> {
        let idx_lb = trail.lb(self.index).max(0) as usize;
        let idx_ub = trail.ub(self.index).min(self.array.len() as i64 - 1) as usize;

        if idx_lb > idx_ub {
            // No valid index → conflict
            if let Some(reasons) = self.build_reasons_result_and_index(trail, encoder) {
                return Some(Explanation::new(reasons).into_conflict_clause());
            }
            // Explanation incomplete — cannot report conflict (#5986).
            return None;
        }

        // Compute union of array[i]'s bounds across valid index values
        let mut result_min = i64::MAX;
        let mut result_max = i64::MIN;
        for i in idx_lb..=idx_ub {
            let arr_var = self.array[i];
            result_min = result_min.min(trail.lb(arr_var));
            result_max = result_max.max(trail.ub(arr_var));
        }

        // Tighten result lower bound
        if result_min > trail.lb(self.result) {
            if let Some(conclusion) = encoder.lookup_ge(self.result, result_min) {
                if let Some(reasons) = self.build_reasons_from_index_and_array(
                    trail,
                    encoder,
                    idx_lb as i64..=idx_ub as i64,
                ) {
                    clauses.push(Explanation::new(reasons).into_clause(conclusion));
                }
            }
        }

        // Tighten result upper bound
        if result_max < trail.ub(self.result) {
            if let Some(conclusion) = encoder.lookup_le(self.result, result_max) {
                if let Some(reasons) = self.build_reasons_from_index_and_array(
                    trail,
                    encoder,
                    idx_lb as i64..=idx_ub as i64,
                ) {
                    clauses.push(Explanation::new(reasons).into_clause(conclusion));
                }
            }
        }

        None
    }

    /// Propagate: result → index bounds.
    /// Remove index values where array[i]'s domain doesn't intersect result's domain.
    fn propagate_result_to_index(
        &self,
        trail: &IntegerTrail,
        encoder: &IntegerEncoder,
        clauses: &mut Vec<Vec<ay_sat::Literal>>,
    ) -> Option<Vec<ay_sat::Literal>> {
        let idx_lb = trail.lb(self.index).max(0);
        let idx_ub = trail.ub(self.index).min(self.array.len() as i64 - 1);

        let result_lb = trail.lb(self.result);
        let result_ub = trail.ub(self.result);

        // Find new index bounds by filtering out incompatible indices
        let mut new_idx_lb = None;
        let mut new_idx_ub = None;

        for i in idx_lb..=idx_ub {
            let arr_var = self.array[i as usize];
            let arr_lb = trail.lb(arr_var);
            let arr_ub = trail.ub(arr_var);

            // Check if array[i]'s domain intersects result's domain
            if arr_lb <= result_ub && arr_ub >= result_lb {
                if new_idx_lb.is_none() {
                    new_idx_lb = Some(i);
                }
                new_idx_ub = Some(i);
            }
        }

        match (new_idx_lb, new_idx_ub) {
            (None, _) | (_, None) => {
                // No valid index → conflict
                // Build complete explanation: result + index + all array element bounds.
                // If any lookup fails, skip conflict (#5986).
                let conflict_reasons = (|| -> Option<Vec<ay_sat::Literal>> {
                    let mut all_reasons = self.build_reasons_result_and_index(trail, encoder)?;
                    for i in idx_lb..=idx_ub {
                        let arr_var = self.array[i as usize];
                        all_reasons.push(encoder.lookup_ge(arr_var, trail.lb(arr_var))?);
                        all_reasons.push(encoder.lookup_le(arr_var, trail.ub(arr_var))?);
                    }
                    Some(all_reasons)
                })();
                conflict_reasons.map(|reasons| Explanation::new(reasons).into_conflict_clause())
            }
            (Some(new_lb), Some(new_ub)) => {
                // Tighten index lower bound
                if new_lb > trail.lb(self.index) {
                    if let Some(conclusion) = encoder.lookup_ge(self.index, new_lb) {
                        // Reasons: result bounds + index bounds + array element bounds
                        // for the EXCLUDED indices [idx_lb, new_lb-1]. Without the
                        // array bounds, the lemma is unsound: after backtracking, the
                        // excluded array elements' domains may widen and become
                        // compatible with the result (#5910, #5986).
                        let reasons = (|| -> Option<Vec<ay_sat::Literal>> {
                            let mut r = self.build_reasons_result_and_index(trail, encoder)?;
                            for i in idx_lb..new_lb {
                                let arr_var = self.array[i as usize];
                                r.push(encoder.lookup_ge(arr_var, trail.lb(arr_var))?);
                                r.push(encoder.lookup_le(arr_var, trail.ub(arr_var))?);
                            }
                            Some(r)
                        })();
                        if let Some(reasons) = reasons {
                            clauses.push(Explanation::new(reasons).into_clause(conclusion));
                        }
                    }
                }

                // Tighten index upper bound
                if new_ub < trail.ub(self.index) {
                    if let Some(conclusion) = encoder.lookup_le(self.index, new_ub) {
                        // Reasons: result bounds + index bounds + array element bounds
                        // for the EXCLUDED indices [new_ub+1, idx_ub] (#5910, #5986).
                        let reasons = (|| -> Option<Vec<ay_sat::Literal>> {
                            let mut r = self.build_reasons_result_and_index(trail, encoder)?;
                            for i in (new_ub + 1)..=idx_ub {
                                let arr_var = self.array[i as usize];
                                r.push(encoder.lookup_ge(arr_var, trail.lb(arr_var))?);
                                r.push(encoder.lookup_le(arr_var, trail.ub(arr_var))?);
                            }
                            Some(r)
                        })();
                        if let Some(reasons) = reasons {
                            clauses.push(Explanation::new(reasons).into_clause(conclusion));
                        }
                    }
                }

                None
            }
        }
    }

    /// Propagate when index is fixed: result = array[fixed_index].
    fn propagate_fixed_index(
        &self,
        trail: &IntegerTrail,
        encoder: &IntegerEncoder,
        clauses: &mut Vec<Vec<ay_sat::Literal>>,
    ) {
        if !trail.is_fixed(self.index) {
            return;
        }
        let idx = trail.lb(self.index);
        if idx < 0 || idx as usize >= self.array.len() {
            return;
        }

        let arr_var = self.array[idx as usize];

        // Helper: build reasons for index-is-fixed + one additional literal.
        // Returns None if any lookup fails (#5986).
        let build_fixed_index_reasons = |encoder: &IntegerEncoder,
                                         extra_lit: ay_sat::Literal|
         -> Option<Vec<ay_sat::Literal>> {
            let a = encoder.lookup_ge(self.index, idx)?;
            let b = encoder.lookup_le(self.index, idx)?;
            Some(vec![a, b, extra_lit])
        };

        // result >= lb(array[idx])
        let arr_lb = trail.lb(arr_var);
        if arr_lb > trail.lb(self.result) {
            if let Some(conclusion) = encoder.lookup_ge(self.result, arr_lb) {
                if let Some(extra) = encoder.lookup_ge(arr_var, arr_lb) {
                    if let Some(reasons) = build_fixed_index_reasons(encoder, extra) {
                        clauses.push(Explanation::new(reasons).into_clause(conclusion));
                    }
                }
            }
        }

        // result <= ub(array[idx])
        let arr_ub = trail.ub(arr_var);
        if arr_ub < trail.ub(self.result) {
            if let Some(conclusion) = encoder.lookup_le(self.result, arr_ub) {
                if let Some(extra) = encoder.lookup_le(arr_var, arr_ub) {
                    if let Some(reasons) = build_fixed_index_reasons(encoder, extra) {
                        clauses.push(Explanation::new(reasons).into_clause(conclusion));
                    }
                }
            }
        }

        // array[idx] >= lb(result)
        let res_lb = trail.lb(self.result);
        if res_lb > trail.lb(arr_var) {
            if let Some(conclusion) = encoder.lookup_ge(arr_var, res_lb) {
                if let Some(extra) = encoder.lookup_ge(self.result, res_lb) {
                    if let Some(reasons) = build_fixed_index_reasons(encoder, extra) {
                        clauses.push(Explanation::new(reasons).into_clause(conclusion));
                    }
                }
            }
        }

        // array[idx] <= ub(result)
        let res_ub = trail.ub(self.result);
        if res_ub < trail.ub(arr_var) {
            if let Some(conclusion) = encoder.lookup_le(arr_var, res_ub) {
                if let Some(extra) = encoder.lookup_le(self.result, res_ub) {
                    if let Some(reasons) = build_fixed_index_reasons(encoder, extra) {
                        clauses.push(Explanation::new(reasons).into_clause(conclusion));
                    }
                }
            }
        }
    }
}

impl Propagator for Element {
    fn variables(&self) -> &[IntVarId] {
        &self.all_vars
    }

    fn priority(&self) -> PropagatorPriority {
        PropagatorPriority::Linear
    }

    fn propagate(&mut self, trail: &IntegerTrail, encoder: &IntegerEncoder) -> PropagationResult {
        let mut clauses = Vec::new();

        // Propagation 1: index → result
        if let Some(conflict) = self.propagate_index_to_result(trail, encoder, &mut clauses) {
            return PropagationResult::Conflict(conflict);
        }

        // Propagation 2: result → index
        if let Some(conflict) = self.propagate_result_to_index(trail, encoder, &mut clauses) {
            return PropagationResult::Conflict(conflict);
        }

        // Propagation 3: fixed index → bidirectional
        self.propagate_fixed_index(trail, encoder, &mut clauses);

        if clauses.is_empty() {
            PropagationResult::NoChange
        } else {
            PropagationResult::Propagated(clauses)
        }
    }

    fn name(&self) -> &'static str {
        "element"
    }
}

#[cfg(test)]
#[path = "element_tests.rs"]
mod tests;
