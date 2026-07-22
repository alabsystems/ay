// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

impl Mbp {
    /// Evaluate an array expression to its model value.
    pub(in crate::mbp) fn eval_array_model(
        &self,
        expr: &ChcExpr,
        model: &FxHashMap<String, SmtValue>,
    ) -> Option<SmtValue> {
        match expr {
            ChcExpr::Var(v) => model.get(&v.name).cloned(),
            ChcExpr::ConstArray(_, val) => Some(SmtValue::ConstArray(Box::new(
                self.eval_model_value(val, model)?,
            ))),
            ChcExpr::Op(ChcOp::Store, args) if args.len() == 3 => {
                let base = self.eval_array_model(&args[0], model)?;
                let idx = self.eval_model_value(&args[1], model)?;
                let val = self.eval_model_value(&args[2], model)?;
                Self::apply_store_model(base, idx, val)
            }
            _ => None,
        }
    }

    pub(in crate::mbp) fn eval_model_value(
        &self,
        expr: &ChcExpr,
        model: &FxHashMap<String, SmtValue>,
    ) -> Option<SmtValue> {
        self.eval_smt_value(expr, model)
            .or_else(|| self.eval_array_model(expr, model))
    }

    pub(in crate::mbp) fn apply_store_model(
        base: SmtValue,
        idx: SmtValue,
        val: SmtValue,
    ) -> Option<SmtValue> {
        match base {
            SmtValue::ConstArray(default) => Some(SmtValue::ArrayMap {
                default,
                entries: vec![(idx, val)],
            }),
            SmtValue::ArrayMap {
                default,
                mut entries,
            } => {
                if let Some((_, existing)) = entries
                    .iter_mut()
                    .find(|(existing_idx, _)| *existing_idx == idx)
                {
                    *existing = val;
                } else {
                    entries.push((idx, val));
                }
                Some(SmtValue::ArrayMap { default, entries })
            }
            _ => None,
        }
    }

    /// Find a concrete witnessing index where two array model values differ.
    pub(in crate::mbp) fn find_witnessing_index(
        lhs: &SmtValue,
        rhs: &SmtValue,
        idx_sort: &ChcSort,
        _val_sort: &ChcSort,
    ) -> Option<ChcExpr> {
        let (lhs_default, lhs_entries) = Self::array_model_parts(lhs)?;
        let (rhs_default, rhs_entries) = Self::array_model_parts(rhs)?;

        // Check entries in lhs that differ from rhs at the same index.
        for (idx_val, lhs_val) in &lhs_entries {
            let rhs_val_at_idx = rhs_entries
                .iter()
                .find(|(k, _)| k == idx_val)
                .map(|(_, v)| v)
                .unwrap_or(&rhs_default);
            if lhs_val != rhs_val_at_idx {
                return Self::smt_value_to_index_expr(idx_val, idx_sort);
            }
        }
        // Check entries in rhs not in lhs (compare against lhs default).
        for (idx_val, rhs_val) in &rhs_entries {
            let in_lhs = lhs_entries.iter().any(|(k, _)| k == idx_val);
            if !in_lhs && *rhs_val != lhs_default {
                return Self::smt_value_to_index_expr(idx_val, idx_sort);
            }
        }
        // Defaults differ and no entry shadows it — use index 0.
        if lhs_default != rhs_default {
            return Some(match idx_sort {
                ChcSort::Int => ChcExpr::Int(0),
                ChcSort::BitVec(w) => ChcExpr::BitVec(0, *w),
                _ => ChcExpr::Int(0),
            });
        }
        None
    }

    /// Decompose an array SmtValue into (default, entries).
    pub(in crate::mbp) fn array_model_parts(
        val: &SmtValue,
    ) -> Option<(SmtValue, Vec<(SmtValue, SmtValue)>)> {
        match val {
            SmtValue::ConstArray(default) => Some((*default.clone(), vec![])),
            SmtValue::ArrayMap { default, entries } => Some((*default.clone(), entries.clone())),
            _ => None,
        }
    }

    /// Convert an SmtValue to a ChcExpr for use as an array index.
    pub(in crate::mbp) fn smt_value_to_index_expr(
        val: &SmtValue,
        _sort: &ChcSort,
    ) -> Option<ChcExpr> {
        match val {
            SmtValue::Int(n) => Some(ChcExpr::Int(*n)),
            SmtValue::BitVec(v, w) => Some(ChcExpr::BitVec(*v, *w)),
            SmtValue::Bool(b) => Some(ChcExpr::Bool(*b)),
            _ => None,
        }
    }

    pub(in crate::mbp) fn is_var_expr(&self, expr: &Arc<ChcExpr>, var: &ChcVar) -> bool {
        matches!(expr.as_ref(), ChcExpr::Var(v) if v == var)
    }

    pub(in crate::mbp) fn select_sort(&self, sort: &ChcSort) -> ChcSort {
        match sort {
            ChcSort::Array(_, val) => val.as_ref().clone(),
            _ => ChcSort::Int,
        }
    }
}
