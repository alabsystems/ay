// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Point-blocking formula extraction and evaluation.
//!
//! Constructs concrete-state blocking formulas from proof obligations.
//! Used as a fallback when generalized lemmas fail self-inductiveness (#710).

use super::super::{ChcExpr, ChcOp, ChcSort, FxHashMap, PdrSolver, ProofObligation, SmtValue};

impl PdrSolver {
    pub(in crate::pdr::solver) fn point_values_satisfy_cube(
        &self,
        cube: &ChcExpr,
        values: &FxHashMap<String, SmtValue>,
    ) -> bool {
        match cube {
            ChcExpr::Bool(true) => return true,
            ChcExpr::Bool(false) => return false,
            _ => {}
        }

        for conjunct in cube.collect_conjuncts() {
            match &conjunct {
                ChcExpr::Bool(true) => continue,
                ChcExpr::Bool(false) => return false,
                ChcExpr::Op(op, args) if args.len() == 2 => {
                    let (lhs, rhs) = (args[0].as_ref(), args[1].as_ref());
                    // Use get_constant to handle both Int(n) and Op(Neg, [Int(n)])
                    // — negative constants in SMT-LIB are (- n), not -n.
                    let (var_name, k, effective_op) =
                        if let (ChcExpr::Var(v), Some(n)) = (lhs, Self::get_constant(rhs)) {
                            (v.name.as_str(), n, *op)
                        } else if let (Some(n), ChcExpr::Var(v)) = (Self::get_constant(lhs), rhs) {
                            let swapped = match op {
                                ChcOp::Eq => ChcOp::Eq,
                                ChcOp::Lt => ChcOp::Gt,
                                ChcOp::Le => ChcOp::Ge,
                                ChcOp::Gt => ChcOp::Lt,
                                ChcOp::Ge => ChcOp::Le,
                                _ => {
                                    // Pattern not matched — fall back to full evaluator.
                                    match self.mbp.eval_bool(&conjunct, values) {
                                        Some(false) => return false,
                                        _ => continue,
                                    }
                                }
                            };
                            (v.name.as_str(), n, swapped)
                        } else {
                            // Complex expression (e.g., modular, multi-variable) —
                            // fall back to Mbp::eval_bool which handles all ChcExpr types.
                            match self.mbp.eval_bool(&conjunct, values) {
                                Some(false) => return false,
                                _ => continue,
                            }
                        };

                    let v = match values.get(var_name) {
                        Some(SmtValue::Int(v)) => *v,
                        _ => {
                            // Variable not in model — fall back to full evaluator.
                            match self.mbp.eval_bool(&conjunct, values) {
                                Some(false) => return false,
                                _ => continue,
                            }
                        }
                    };

                    let ok = match effective_op {
                        ChcOp::Eq => v == k,
                        ChcOp::Le => v <= k,
                        ChcOp::Lt => v < k,
                        ChcOp::Ge => v >= k,
                        ChcOp::Gt => v > k,
                        _ => match self.mbp.eval_bool(&conjunct, values) {
                            Some(false) => return false,
                            _ => continue,
                        },
                    };
                    if !ok {
                        return false;
                    }
                }
                _ => {
                    // Non-binary-op conjunct (e.g., Not(Or(...)), Var) —
                    // fall back to Mbp::eval_bool.
                    match self.mbp.eval_bool(&conjunct, values) {
                        Some(false) => return false,
                        _ => continue,
                    }
                }
            }
        }

        true
    }

    /// Extract a point-blocking formula from a POB state.
    ///
    /// Returns a conjunction of (var = value) for each canonical variable that has
    /// a concrete assignment in the POB's state formula. Point blocking is always
    /// sound because it blocks the exact concrete state that was found by SMT.
    ///
    /// This is used as a fallback when generalized lemmas fail self-inductiveness.
    /// See #710 for details.
    pub(in crate::pdr::solver) fn extract_point_blocking(
        &self,
        pob: &ProofObligation,
    ) -> Option<ChcExpr> {
        // Get canonical variables for this predicate
        let canonical_vars = self.canonical_vars(pob.predicate)?;

        // Extract variable assignments from the state
        let mut state_values = self.extract_point_values_from_state(&pob.state);

        // Fallback to smt_model if state parsing incomplete (#801)
        // This handles POB states with only inequalities (e.g., `(< x 0)`)
        if let Some(model) = &pob.smt_model {
            for (var, value) in model {
                state_values.entry(var.clone()).or_insert(value.clone());
            }
        }

        if state_values.is_empty() {
            return None;
        }

        // Build conjunction of literals for each non-array canonical variable.
        // Require full coverage to ensure this is true point-blocking.
        let point_vars: Vec<_> = canonical_vars
            .iter()
            .filter(|v| !matches!(v.sort, ChcSort::Array { .. }))
            .collect();

        let mut conjuncts = Vec::with_capacity(point_vars.len());
        for var in &point_vars {
            match (&var.sort, state_values.get(&var.name)) {
                (ChcSort::Int, Some(SmtValue::Int(val))) => {
                    conjuncts.push(ChcExpr::eq(
                        ChcExpr::var((*var).clone()),
                        ChcExpr::int(*val),
                    ));
                }
                (ChcSort::Bool, Some(SmtValue::Bool(true))) => {
                    conjuncts.push(ChcExpr::var((*var).clone()));
                }
                (ChcSort::Bool, Some(SmtValue::Bool(false))) => {
                    conjuncts.push(ChcExpr::not(ChcExpr::var((*var).clone())));
                }
                (ChcSort::BitVec(_), Some(SmtValue::BitVec(val, width))) => {
                    conjuncts.push(ChcExpr::eq(
                        ChcExpr::var((*var).clone()),
                        ChcExpr::BitVec(*val, *width),
                    ));
                }
                (ChcSort::Datatype { .. }, Some(SmtValue::Datatype(ctor, fields))) => {
                    let field_exprs: Vec<std::sync::Arc<ChcExpr>> = fields
                        .iter()
                        .enumerate()
                        .map(|(i, f)| {
                            std::sync::Arc::new(Self::smt_value_to_blocking_expr_for_field(
                                &var.sort, ctor, i, f,
                            ))
                        })
                        .collect();
                    let ctor_app = ChcExpr::FuncApp(ctor.clone(), var.sort.clone(), field_exprs);
                    conjuncts.push(ChcExpr::eq(ChcExpr::var((*var).clone()), ctor_app));
                }
                // Nullary DT constructor stored as Opaque string.
                (ChcSort::Datatype { constructors, .. }, Some(SmtValue::Opaque(name)))
                    if constructors.iter().any(|c| c.name == *name) =>
                {
                    let ctor_app = ChcExpr::FuncApp(name.clone(), var.sort.clone(), vec![]);
                    conjuncts.push(ChcExpr::eq(ChcExpr::var((*var).clone()), ctor_app));
                }
                (_, _) => {
                    // Missing assignment for a non-array argument: not a concrete state.
                    if self.config.verbose {
                        safe_eprintln!(
                            "PDR: Couldn't extract full point blocking (missing {})",
                            var.name
                        );
                    }
                    return None;
                }
            }
        }

        if conjuncts.is_empty() {
            None
        } else {
            Some(Self::build_conjunction(&conjuncts))
        }
    }

    fn datatype_field_sort(sort: &ChcSort, ctor: &str, field_index: usize) -> Option<ChcSort> {
        let ChcSort::Datatype { constructors, .. } = sort else {
            return None;
        };
        constructors
            .iter()
            .find(|candidate| candidate.name == ctor)
            .and_then(|candidate| candidate.selectors.get(field_index))
            .map(|selector| selector.sort.clone())
    }

    fn smt_value_to_blocking_expr_for_field(
        parent_sort: &ChcSort,
        ctor: &str,
        field_index: usize,
        val: &SmtValue,
    ) -> ChcExpr {
        let expected_sort = Self::datatype_field_sort(parent_sort, ctor, field_index);
        Self::smt_value_to_blocking_expr(val, expected_sort.as_ref())
    }

    /// Convert an SmtValue to a ChcExpr for point-blocking formulas.
    pub(super) fn smt_value_to_blocking_expr(
        val: &SmtValue,
        expected_sort: Option<&ChcSort>,
    ) -> ChcExpr {
        match (val, expected_sort) {
            (SmtValue::Bool(b), _) => ChcExpr::Bool(*b),
            (SmtValue::Int(n), _) => ChcExpr::Int(*n),
            (SmtValue::BitVec(v, w), _) => ChcExpr::BitVec(*v, *w),
            (SmtValue::Real(r), _) => {
                use num_traits::ToPrimitive;
                let n = r.numer().to_i64().unwrap_or(0);
                let d = r.denom().to_i64().unwrap_or(1);
                ChcExpr::Real(n, d)
            }
            (SmtValue::Datatype(ctor, fields), Some(sort @ ChcSort::Datatype { .. })) => {
                let field_exprs: Vec<std::sync::Arc<ChcExpr>> = fields
                    .iter()
                    .enumerate()
                    .map(|(i, f)| {
                        std::sync::Arc::new(Self::smt_value_to_blocking_expr_for_field(
                            sort, ctor, i, f,
                        ))
                    })
                    .collect();
                ChcExpr::FuncApp(ctor.clone(), sort.clone(), field_exprs)
            }
            (SmtValue::Datatype(ctor, fields), _) => {
                let field_exprs: Vec<std::sync::Arc<ChcExpr>> = fields
                    .iter()
                    .map(|f| std::sync::Arc::new(Self::smt_value_to_blocking_expr(f, None)))
                    .collect();
                ChcExpr::FuncApp(
                    ctor.clone(),
                    ChcSort::Uninterpreted(ctor.clone()),
                    field_exprs,
                )
            }
            // Opaque, Array: fallback to Int(0)
            (SmtValue::Opaque(name), Some(sort @ ChcSort::Datatype { constructors, .. }))
                if constructors.iter().any(|ctor| ctor.name == *name) =>
            {
                ChcExpr::FuncApp(name.clone(), sort.clone(), vec![])
            }
            _ => ChcExpr::Int(0),
        }
    }

    /// Convert a FuncApp (constructor application) to SmtValue::Datatype.
    pub(super) fn funcapp_to_smt_value(
        ctor: &str,
        args: &[std::sync::Arc<ChcExpr>],
    ) -> Option<SmtValue> {
        let fields: Vec<SmtValue> = args
            .iter()
            .filter_map(|a| Self::expr_to_smt_value(a))
            .collect();
        if fields.len() == args.len() {
            Some(SmtValue::Datatype(ctor.to_string(), fields))
        } else {
            // If we can't convert all fields, use Opaque as fallback.
            Some(SmtValue::Opaque(ctor.to_string()))
        }
    }

    /// Convert a ChcExpr to SmtValue (inverse of smt_value_to_blocking_expr).
    pub(super) fn expr_to_smt_value(expr: &ChcExpr) -> Option<SmtValue> {
        match expr {
            ChcExpr::Bool(b) => Some(SmtValue::Bool(*b)),
            ChcExpr::Int(n) => Some(SmtValue::Int(*n)),
            ChcExpr::BitVec(v, w) => Some(SmtValue::BitVec(*v, *w)),
            ChcExpr::FuncApp(ctor, _, args) => Self::funcapp_to_smt_value(ctor, args),
            _ => None,
        }
    }
}
