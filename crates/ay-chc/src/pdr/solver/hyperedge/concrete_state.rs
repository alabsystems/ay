// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Concrete predicate-state extraction from SMT models.

use crate::smt::SmtValue;
use crate::{ChcExpr, ChcSort, ChcVar};
use ay_core::kani_compat::DetHashMap as FxHashMap;
use std::sync::Arc;

use super::PdrSolver;

impl PdrSolver {
    /// Extract concrete state equalities from a model for predicate args.
    ///
    /// #2492: Handles expression args by substituting model values and
    /// simplifying, rather than only matching direct Var args.
    pub(super) fn extract_concrete_state(
        args: &[ChcExpr],
        canonical_vars: &[ChcVar],
        model: &FxHashMap<String, SmtValue>,
    ) -> Vec<ChcExpr> {
        let mut concrete_parts: Vec<ChcExpr> = Vec::new();
        for (i, arg) in args.iter().enumerate() {
            let Some(canonical_var) = canonical_vars.get(i) else {
                continue;
            };
            // #6047: For array canonical vars, extract select-based constraints
            // from the model instead of trying scalar equality (which fails for arrays).
            if matches!(canonical_var.sort, ChcSort::Array(_, _)) {
                if let ChcExpr::Var(v) = arg {
                    if let Some(select_conjuncts) =
                        Self::array_select_constraints_from_model(canonical_var, model.get(&v.name))
                    {
                        concrete_parts.extend(select_conjuncts);
                    }
                }
                continue;
            }
            let canonical_expr = ChcExpr::Var(canonical_var.clone());
            match arg {
                ChcExpr::Var(v) => {
                    if let Some(val_expr) = model.get(&v.name).and_then(Self::smt_value_to_expr) {
                        concrete_parts.push(ChcExpr::eq(canonical_expr, val_expr));
                    }
                }
                expr => {
                    // Substitute all constituent vars with model values, then
                    // simplify to reduce to a constant if possible.
                    let subst: Vec<(ChcVar, ChcExpr)> = expr
                        .vars()
                        .into_iter()
                        .filter_map(|v| {
                            model
                                .get(&v.name)
                                .and_then(Self::smt_value_to_expr)
                                .map(|val| (v, val))
                        })
                        .collect();
                    if !subst.is_empty() {
                        let evaluated = expr.substitute(&subst).simplify_constants();
                        concrete_parts.push(ChcExpr::eq(canonical_expr, evaluated));
                    }
                }
            }
        }
        concrete_parts
    }

    fn smt_value_to_expr(val: &SmtValue) -> Option<ChcExpr> {
        Some(match val {
            SmtValue::Bool(b) => ChcExpr::Bool(*b),
            SmtValue::Int(n) => ChcExpr::Int(*n),
            // Beyond-i128 witness: exact Horner encoding (never wraps).
            SmtValue::BigInt(b) => ChcExpr::from_bigint(b.as_ref().clone()),
            SmtValue::Real(r) => {
                use num_traits::ToPrimitive;
                let n = r.numer().to_i64()?;
                let d = r.denom().to_i64()?;
                ChcExpr::Real(n, d)
            }
            // #5523: Preserve bitvector sort to avoid BV→Int sort mismatches.
            SmtValue::BitVec(..) | SmtValue::BigBitVec(..) => val.bitvec_to_chc_expr()?,
            // #7016: DT constructor applications for counterexample concretization.
            SmtValue::Datatype(ctor, fields) => {
                let field_exprs: Vec<Arc<ChcExpr>> = fields
                    .iter()
                    .map(|f| Self::smt_value_to_expr(f).map(Arc::new))
                    .collect::<Option<Vec<_>>>()?;
                ChcExpr::FuncApp(
                    ctor.clone(),
                    ChcSort::Uninterpreted(ctor.clone()),
                    field_exprs,
                )
            }
            SmtValue::Opaque(name) => {
                ChcExpr::FuncApp(name.clone(), ChcSort::Uninterpreted(name.clone()), vec![])
            }
            // Array values have no scalar ChcExpr representation here.
            SmtValue::ConstArray(_) | SmtValue::ArrayMap { .. } => {
                return None;
            }
        })
    }
}
