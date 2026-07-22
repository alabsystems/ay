// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Property-directed array index extraction for PDR (#8660).
//!
//! Extracts which concrete array indices appear in query clauses (ClauseHead::False).
//! These are the only indices that matter for the property being verified.
//!
//! When a CHC problem has >=2 Array-sorted parameters, the PDR solver generates
//! blocking cubes with `select(arr, idx) = val` constraints for every model entry.
//! This is wasteful because the property typically only checks a small number of
//! concrete indices. By tracking which indices appear in the property, we can:
//!
//! 1. Build smaller cubes (only property-relevant selects)
//! 2. Make inductiveness checks faster (fewer array constraints)
//! 3. Enable scalar-only blocking when the property doesn't use arrays at all
//!
//! Reference: Z3 Spacer's approach in `spacer_qe_project.cpp` where array
//! projection only considers property-relevant indices.

use super::super::*;

/// Property-relevant array index information extracted from query clauses.
#[derive(Debug, Clone, Default)]
pub(in crate::pdr::solver) struct PropertyArrayIndices {
    /// Per-predicate, per-array-param position -> concrete index expressions from property.
    ///
    /// Example: if predicate `inv` has signature `(Array Int Int) Int (Array Int Bool)` and
    /// the query clause checks `select(arg0, 0) = 42` and `select(arg2, 5)`, then:
    /// ```text
    /// indices[inv] = { 0 -> [Int(0)], 2 -> [Int(5)] }
    /// ```
    pub(in crate::pdr::solver) indices: FxHashMap<PredicateId, FxHashMap<usize, Vec<ChcExpr>>>,

    /// True if any query clause references array operations (select/store/const-array).
    /// When false, the property is purely scalar and array constraints in cubes are unnecessary.
    pub(in crate::pdr::solver) property_uses_arrays: bool,

    /// True if any query clause references array variables (even without select/store).
    /// This catches cases like `(= arr1 arr2)` in the property.
    pub(in crate::pdr::solver) property_references_array_vars: bool,
}

impl PropertyArrayIndices {
    /// Get the property-relevant indices for a specific predicate and array parameter position.
    pub(in crate::pdr::solver) fn indices_for(
        &self,
        predicate: PredicateId,
        array_param_pos: usize,
    ) -> &[ChcExpr] {
        self.indices
            .get(&predicate)
            .and_then(|m| m.get(&array_param_pos))
            .map(|v| v.as_slice())
            .unwrap_or(&[])
    }

    /// Check if a predicate has any property-relevant array indices.
    pub(in crate::pdr::solver) fn has_indices_for(&self, predicate: PredicateId) -> bool {
        self.indices
            .get(&predicate)
            .map_or(false, |m| m.values().any(|v| !v.is_empty()))
    }
}

impl PdrSolver {
    /// Extract property-relevant array indices from query clauses.
    ///
    /// Scans all clauses with `ClauseHead::False` (query/safety clauses) and extracts
    /// concrete indices used in `select(arr, idx)` patterns. Maps these back to the
    /// canonical predicate parameter positions.
    pub(in crate::pdr::solver) fn extract_property_array_indices(
        problem: &ChcProblem,
    ) -> PropertyArrayIndices {
        let mut result = PropertyArrayIndices::default();

        for clause in problem.clauses() {
            // Only look at query clauses (head is false)
            if !matches!(&clause.head, crate::ClauseHead::False) {
                continue;
            }

            let constraint = match &clause.body.constraint {
                Some(c) => c,
                None => continue,
            };

            // Check if the constraint uses any array operations
            if constraint.contains_array_ops() {
                result.property_uses_arrays = true;
            }

            // Check if the constraint references array-sorted variables
            for var in constraint.vars() {
                if matches!(var.sort, ChcSort::Array(_, _)) {
                    result.property_references_array_vars = true;
                }
            }

            // For each body predicate in the query clause, extract select indices
            for (body_pred, body_args) in &clause.body.predicates {
                // Find array-sorted arguments and their positions
                let pred_info = problem.predicates().iter().find(|p| p.id == *body_pred);
                let pred_info = match pred_info {
                    Some(p) => p,
                    None => continue,
                };

                // Build mapping from body_arg variable names to predicate param positions
                let mut arg_to_pos: FxHashMap<String, usize> = FxHashMap::default();
                for (pos, (arg, sort)) in
                    body_args.iter().zip(pred_info.arg_sorts.iter()).enumerate()
                {
                    if matches!(sort, ChcSort::Array(_, _)) {
                        if let ChcExpr::Var(v) = arg {
                            arg_to_pos.insert(v.name.clone(), pos);
                        }
                    }
                }

                if arg_to_pos.is_empty() {
                    continue;
                }

                // Extract select indices from the constraint
                let select_indices = extract_select_indices(constraint, &arg_to_pos);
                if !select_indices.is_empty() {
                    let pred_entry = result.indices.entry(*body_pred).or_default();
                    for (param_pos, indices) in select_indices {
                        let entry = pred_entry.entry(param_pos).or_default();
                        for idx in indices {
                            if !entry.contains(&idx) {
                                entry.push(idx);
                            }
                        }
                    }
                }
            }
        }

        result
    }
}

/// Extract `select(arr_var, idx)` patterns from an expression and map them to
/// predicate parameter positions.
///
/// Returns a map from array param position to the concrete index expressions used.
fn extract_select_indices(
    expr: &ChcExpr,
    arg_to_pos: &FxHashMap<String, usize>,
) -> FxHashMap<usize, Vec<ChcExpr>> {
    let mut result: FxHashMap<usize, Vec<ChcExpr>> = FxHashMap::default();
    collect_select_indices_recursive(expr, arg_to_pos, &mut result);
    result
}

fn collect_select_indices_recursive(
    expr: &ChcExpr,
    arg_to_pos: &FxHashMap<String, usize>,
    result: &mut FxHashMap<usize, Vec<ChcExpr>>,
) {
    match expr {
        ChcExpr::Op(ChcOp::Select, args) if args.len() == 2 => {
            // Check if the array argument is a variable we're tracking
            if let ChcExpr::Var(arr_var) = args[0].as_ref() {
                if let Some(&param_pos) = arg_to_pos.get(&arr_var.name) {
                    let index_expr = args[1].as_ref();
                    let entry = result.entry(param_pos).or_default();
                    if !entry.contains(index_expr) {
                        entry.push(index_expr.clone());
                    }
                }
            }
            // Also recurse into the index expression (it might contain nested selects)
            collect_select_indices_recursive(args[1].as_ref(), arg_to_pos, result);
        }
        ChcExpr::Op(_, args) => {
            for arg in args {
                collect_select_indices_recursive(arg.as_ref(), arg_to_pos, result);
            }
        }
        ChcExpr::PredicateApp(_, _, args) | ChcExpr::FuncApp(_, _, args) => {
            for arg in args {
                collect_select_indices_recursive(arg.as_ref(), arg_to_pos, result);
            }
        }
        ChcExpr::Bool(_)
        | ChcExpr::Int(_)
        | ChcExpr::Real(_, _)
        | ChcExpr::BitVec(_, _)
        | ChcExpr::Var(_)
        | ChcExpr::ConstArrayMarker(_)
        | ChcExpr::IsTesterMarker(_)
        | ChcExpr::ConstArray(_, _) => {}
    }
}
