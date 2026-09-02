// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Model evaluation under partial models.
//!
//! Tri-valued recursive evaluation of boolean and arithmetic expressions.
//! These are the most widely-used MBP functions externally (9+ call sites).
//!
//! Bitvector evaluation is in the sibling `eval_bv` module.

use crate::bv_util::bv_to_signed;
use crate::{ChcExpr, ChcOp, ChcSort, SmtValue};
use ay_core::kani_compat::DetHashMap as FxHashMap;

use super::Mbp;

// Note: eval_bool and eval_arith are mutually recursive.
// Per-function #[allow(clippy::only_used_in_recursion)] is used where needed.

impl Mbp {
    /// Evaluate a boolean expression under a model
    pub fn eval_bool(&self, expr: &ChcExpr, model: &FxHashMap<String, SmtValue>) -> Option<bool> {
        crate::expr::maybe_grow_expr_stack(|| {
            let _g = crate::expr::ExprDepthGuard::check()?;
            match expr {
                ChcExpr::Bool(b) => Some(*b),
                ChcExpr::Var(v) if v.sort == ChcSort::Bool => {
                    if let Some(SmtValue::Bool(b)) = model.get(&v.name) {
                        Some(*b)
                    } else {
                        None
                    }
                }
                ChcExpr::Op(ChcOp::Not, args) if args.len() == 1 => {
                    self.eval_bool(&args[0], model).map(|b| !b)
                }
                ChcExpr::Op(ChcOp::And, args) => {
                    let mut result = true;
                    for arg in args {
                        match self.eval_bool(arg, model) {
                            Some(false) => return Some(false),
                            Some(true) => {}
                            None => result = false,
                        }
                    }
                    if result {
                        Some(true)
                    } else {
                        None
                    }
                }
                ChcExpr::Op(ChcOp::Or, args) => {
                    // Tri-valued Or: true if any disjunct is true, false if all are false,
                    // unknown (None) if no true disjunct but at least one unknown.
                    // This matches the And behavior and prevents collapsing unknown to false.
                    let mut has_unknown = false;
                    for arg in args {
                        match self.eval_bool(arg, model) {
                            Some(true) => return Some(true),
                            Some(false) => {}
                            None => has_unknown = true,
                        }
                    }
                    if has_unknown {
                        None
                    } else {
                        Some(false)
                    }
                }
                ChcExpr::Op(ChcOp::Implies, args) if args.len() == 2 => {
                    let a = self.eval_bool(&args[0], model);
                    match a {
                        Some(false) => Some(true),
                        Some(true) => self.eval_bool(&args[1], model),
                        None => match self.eval_bool(&args[1], model) {
                            Some(true) => Some(true),
                            Some(false) | None => None,
                        },
                    }
                }
                ChcExpr::Op(ChcOp::Iff, args) if args.len() == 2 => {
                    let a = self.eval_bool(&args[0], model)?;
                    let b = self.eval_bool(&args[1], model)?;
                    Some(a == b)
                }
                ChcExpr::Op(ChcOp::Ite, args)
                    if args.len() == 3 && expr.sort() == ChcSort::Bool =>
                {
                    match self.eval_bool(&args[0], model) {
                        Some(true) => self.eval_bool(&args[1], model),
                        Some(false) => self.eval_bool(&args[2], model),
                        None => {
                            // If both branches collapse to the same known value, we can still decide.
                            let t = self.eval_bool(&args[1], model);
                            let e = self.eval_bool(&args[2], model);
                            if t.is_some() && t == e {
                                t
                            } else {
                                None
                            }
                        }
                    }
                }
                ChcExpr::Op(ChcOp::Eq, args) if args.len() == 2 => {
                    match (args[0].sort(), args[1].sort()) {
                        (ChcSort::Bool, ChcSort::Bool) => {
                            let b1 = self.eval_bool(&args[0], model)?;
                            let b2 = self.eval_bool(&args[1], model)?;
                            Some(b1 == b2)
                        }
                        (ChcSort::Int, ChcSort::Int) => {
                            let v1 = self.eval_arith(&args[0], model)?;
                            let v2 = self.eval_arith(&args[1], model)?;
                            Some(v1 == v2)
                        }
                        (ChcSort::BitVec(_), ChcSort::BitVec(_)) => {
                            let (v1, _) = self.eval_bv(&args[0], model)?;
                            let (v2, _) = self.eval_bv(&args[1], model)?;
                            Some(v1 == v2)
                        }
                        // DT, Uninterpreted, Real, Array — fall back to generic comparison
                        _ => {
                            let v1 = self.eval_generic(&args[0], model)?;
                            let v2 = self.eval_generic(&args[1], model)?;
                            Some(v1 == v2)
                        }
                    }
                }
                ChcExpr::Op(ChcOp::Ne, args) if args.len() == 2 => {
                    match (args[0].sort(), args[1].sort()) {
                        (ChcSort::Bool, ChcSort::Bool) => {
                            let b1 = self.eval_bool(&args[0], model)?;
                            let b2 = self.eval_bool(&args[1], model)?;
                            Some(b1 != b2)
                        }
                        (ChcSort::Int, ChcSort::Int) => {
                            let v1 = self.eval_arith(&args[0], model)?;
                            let v2 = self.eval_arith(&args[1], model)?;
                            Some(v1 != v2)
                        }
                        (ChcSort::BitVec(_), ChcSort::BitVec(_)) => {
                            let (v1, _) = self.eval_bv(&args[0], model)?;
                            let (v2, _) = self.eval_bv(&args[1], model)?;
                            Some(v1 != v2)
                        }
                        // DT, Uninterpreted, Real, Array — fall back to generic comparison
                        _ => {
                            let v1 = self.eval_generic(&args[0], model)?;
                            let v2 = self.eval_generic(&args[1], model)?;
                            Some(v1 != v2)
                        }
                    }
                }
                // BV unsigned comparisons
                ChcExpr::Op(ChcOp::BvULt, args) if args.len() == 2 => {
                    let (v1, _) = self.eval_bv(&args[0], model)?;
                    let (v2, _) = self.eval_bv(&args[1], model)?;
                    Some(v1 < v2)
                }
                ChcExpr::Op(ChcOp::BvULe, args) if args.len() == 2 => {
                    let (v1, _) = self.eval_bv(&args[0], model)?;
                    let (v2, _) = self.eval_bv(&args[1], model)?;
                    Some(v1 <= v2)
                }
                ChcExpr::Op(ChcOp::BvUGt, args) if args.len() == 2 => {
                    let (v1, _) = self.eval_bv(&args[0], model)?;
                    let (v2, _) = self.eval_bv(&args[1], model)?;
                    Some(v1 > v2)
                }
                ChcExpr::Op(ChcOp::BvUGe, args) if args.len() == 2 => {
                    let (v1, _) = self.eval_bv(&args[0], model)?;
                    let (v2, _) = self.eval_bv(&args[1], model)?;
                    Some(v1 >= v2)
                }
                // BV signed comparisons
                ChcExpr::Op(ChcOp::BvSLt, args) if args.len() == 2 => {
                    let (v1, w1) = self.eval_bv(&args[0], model)?;
                    let (v2, w2) = self.eval_bv(&args[1], model)?;
                    Some(bv_to_signed(v1, w1) < bv_to_signed(v2, w2))
                }
                ChcExpr::Op(ChcOp::BvSLe, args) if args.len() == 2 => {
                    let (v1, w1) = self.eval_bv(&args[0], model)?;
                    let (v2, w2) = self.eval_bv(&args[1], model)?;
                    Some(bv_to_signed(v1, w1) <= bv_to_signed(v2, w2))
                }
                ChcExpr::Op(ChcOp::BvSGt, args) if args.len() == 2 => {
                    let (v1, w1) = self.eval_bv(&args[0], model)?;
                    let (v2, w2) = self.eval_bv(&args[1], model)?;
                    Some(bv_to_signed(v1, w1) > bv_to_signed(v2, w2))
                }
                ChcExpr::Op(ChcOp::BvSGe, args) if args.len() == 2 => {
                    let (v1, w1) = self.eval_bv(&args[0], model)?;
                    let (v2, w2) = self.eval_bv(&args[1], model)?;
                    Some(bv_to_signed(v1, w1) >= bv_to_signed(v2, w2))
                }
                ChcExpr::Op(ChcOp::Lt, args) if args.len() == 2 => {
                    let v1 = self.eval_arith(&args[0], model)?;
                    let v2 = self.eval_arith(&args[1], model)?;
                    Some(v1 < v2)
                }
                ChcExpr::Op(ChcOp::Le, args) if args.len() == 2 => {
                    let v1 = self.eval_arith(&args[0], model)?;
                    let v2 = self.eval_arith(&args[1], model)?;
                    Some(v1 <= v2)
                }
                ChcExpr::Op(ChcOp::Gt, args) if args.len() == 2 => {
                    let v1 = self.eval_arith(&args[0], model)?;
                    let v2 = self.eval_arith(&args[1], model)?;
                    Some(v1 > v2)
                }
                ChcExpr::Op(ChcOp::Ge, args) if args.len() == 2 => {
                    let v1 = self.eval_arith(&args[0], model)?;
                    let v2 = self.eval_arith(&args[1], model)?;
                    Some(v1 >= v2)
                }
                // DT tester: is-CtorName(x) evaluates to true/false based on
                // x's model value constructor. Ref: Z3 mbp_datatypes.cpp.
                // Handles both bare variable args (fast path) and general
                // expressions (#7045 Gap A).
                ChcExpr::FuncApp(name, ChcSort::Bool, args)
                    if name.starts_with("is-") && args.len() == 1 =>
                {
                    let ctor_name = &name[3..];
                    // Variable lookup (fast path) or general expression evaluation
                    let arg_val = if let ChcExpr::Var(v) = args[0].as_ref() {
                        model.get(&v.name).cloned()
                    } else {
                        self.eval_generic(&args[0], model)
                    };
                    match arg_val {
                        Some(SmtValue::Opaque(ref model_ctor)) => Some(model_ctor == ctor_name),
                        Some(SmtValue::Datatype(ref model_ctor, _)) => {
                            Some(model_ctor == ctor_name)
                        }
                        _ => None,
                    }
                }
                _ => None,
            }
        })
    }

    /// Evaluate an arithmetic expression under a model
    pub(crate) fn eval_arith(
        &self,
        expr: &ChcExpr,
        model: &FxHashMap<String, SmtValue>,
    ) -> Option<i128> {
        use crate::expr::{smt_euclid_div, smt_euclid_mod};
        crate::expr::maybe_grow_expr_stack(|| {
            let _g = crate::expr::ExprDepthGuard::check()?;
            match expr {
                ChcExpr::Int(n) => Some(*n),
                ChcExpr::Var(v) if v.sort == ChcSort::Int => {
                    if let Some(SmtValue::Int(n)) = model.get(&v.name) {
                        Some(*n)
                    } else {
                        None
                    }
                }
                ChcExpr::Op(ChcOp::Ite, args) if args.len() == 3 => {
                    let cond = self.eval_bool(&args[0], model)?;
                    if cond {
                        self.eval_arith(&args[1], model)
                    } else {
                        self.eval_arith(&args[2], model)
                    }
                }
                ChcExpr::Op(ChcOp::Add, args) if args.len() == 2 => {
                    let v1 = self.eval_arith(&args[0], model)?;
                    let v2 = self.eval_arith(&args[1], model)?;
                    v1.checked_add(v2)
                }
                ChcExpr::Op(ChcOp::Sub, args) if args.len() == 2 => {
                    let v1 = self.eval_arith(&args[0], model)?;
                    let v2 = self.eval_arith(&args[1], model)?;
                    v1.checked_sub(v2)
                }
                ChcExpr::Op(ChcOp::Mul, args) if args.len() == 2 => {
                    let v1 = self.eval_arith(&args[0], model)?;
                    let v2 = self.eval_arith(&args[1], model)?;
                    v1.checked_mul(v2)
                }
                ChcExpr::Op(ChcOp::Neg, args) if args.len() == 1 => {
                    let v = self.eval_arith(&args[0], model)?;
                    v.checked_neg()
                }
                ChcExpr::Op(ChcOp::Div, args) if args.len() == 2 => {
                    let v1 = self.eval_arith(&args[0], model)?;
                    let v2 = self.eval_arith(&args[1], model)?;
                    smt_euclid_div(v1, v2)
                }
                ChcExpr::Op(ChcOp::Mod, args) if args.len() == 2 => {
                    let v1 = self.eval_arith(&args[0], model)?;
                    let v2 = self.eval_arith(&args[1], model)?;
                    smt_euclid_mod(v1, v2)
                }
                // DT selector returning Int: delegate to eval_generic (#7045).
                ChcExpr::FuncApp(_, _, _) => {
                    if let Some(SmtValue::Int(n)) = self.eval_generic(expr, model) {
                        Some(n)
                    } else {
                        None
                    }
                }
                _ => None,
            }
        })
    }

    /// Generic expression evaluation returning SmtValue for any sort.
    /// Used for index comparison in Array MBP and select-store reduction.
    pub(super) fn eval_generic(
        &self,
        expr: &ChcExpr,
        model: &FxHashMap<String, SmtValue>,
    ) -> Option<SmtValue> {
        match expr {
            ChcExpr::Int(n) => Some(SmtValue::Int(*n)),
            ChcExpr::Bool(b) => Some(SmtValue::Bool(*b)),
            ChcExpr::BitVec(v, w) => Some(SmtValue::bitvec_from_u128(*v, *w)),
            ChcExpr::Var(v) => model.get(&v.name).cloned(),
            ChcExpr::Op(_, _) => {
                if let Some(n) = self.eval_arith(expr, model) {
                    return Some(SmtValue::Int(n));
                }
                if let Some(b) = self.eval_bool(expr, model) {
                    return Some(SmtValue::Bool(b));
                }
                if let Some((v, w)) = self.eval_bv(expr, model) {
                    return Some(SmtValue::BitVec(v, w));
                }
                // The legacy MBP-local evaluator intentionally stops at 128
                // bits.  The canonical evaluator supplies exact BigUint-backed
                // results for wide, fully concrete BV expressions.
                crate::expr::evaluate_expr(expr, model)
            }
            // DT selector, constructor, or tester via FuncApp.
            ChcExpr::FuncApp(name, sort, args) => {
                // Bool-sorted FuncApp (e.g. is-Ctor tester): delegate to eval_bool.
                if *sort == ChcSort::Bool {
                    return self.eval_bool(expr, model).map(SmtValue::Bool);
                }
                // 1-arg FuncApp: try as DT selector.
                // sel(x) where x evaluates to Datatype(ctor, fields) — look up
                // the selector index in the arg's DT sort metadata.
                if args.len() == 1 {
                    if let Some(SmtValue::Datatype(ctor_name, fields)) =
                        self.eval_generic(&args[0], model)
                    {
                        if let ChcSort::Datatype { constructors, .. } = args[0].sort() {
                            for ctor in constructors.iter() {
                                if ctor.name == ctor_name {
                                    for (i, sel) in ctor.selectors.iter().enumerate() {
                                        if sel.name == *name {
                                            return fields.get(i).cloned();
                                        }
                                    }
                                }
                            }
                        }
                    }
                    return None;
                }
                // Multi-arg or nullary FuncApp with DT/Uninterpreted result sort:
                // try as constructor application — evaluate all args.
                if matches!(sort, ChcSort::Datatype { .. } | ChcSort::Uninterpreted(_)) {
                    let field_vals: Option<Vec<SmtValue>> =
                        args.iter().map(|a| self.eval_generic(a, model)).collect();
                    return field_vals.map(|fv| SmtValue::Datatype(name.clone(), fv));
                }
                None
            }
            _ => None,
        }
    }

    /// Evaluate an expression to SmtValue for index comparison.
    /// Returns `None` when the expression cannot be evaluated under the model,
    /// so callers can treat unevaluable indices as unique (#6096).
    pub(super) fn eval_smt_value(
        &self,
        expr: &ChcExpr,
        model: &FxHashMap<String, SmtValue>,
    ) -> Option<SmtValue> {
        self.eval_generic(expr, model)
    }

    /// Compare two SmtValues for ordering (used to sort index classes in Ackermannization).
    pub(super) fn cmp_smt_values(a: &SmtValue, b: &SmtValue) -> std::cmp::Ordering {
        match (a, b) {
            (SmtValue::Int(x), SmtValue::Int(y)) => x.cmp(y),
            (
                lhs @ (SmtValue::BitVec(..) | SmtValue::BigBitVec(..)),
                rhs @ (SmtValue::BitVec(..) | SmtValue::BigBitVec(..)),
            ) => {
                let Some((lhs_value, lhs_width)) = lhs.bitvec_to_biguint() else {
                    return std::cmp::Ordering::Equal;
                };
                let Some((rhs_value, rhs_width)) = rhs.bitvec_to_biguint() else {
                    return std::cmp::Ordering::Equal;
                };
                lhs_width
                    .cmp(&rhs_width)
                    .then_with(|| lhs_value.cmp(&rhs_value))
            }
            (SmtValue::Bool(x), SmtValue::Bool(y)) => x.cmp(y),
            // Heterogeneous: arbitrary but deterministic ordering
            _ => std::cmp::Ordering::Equal,
        }
    }

    /// Like `reduce_select_store`, but also collects index conditions that
    /// justify each select-through-store reduction step.
    ///
    /// These conditions (`idx = ik` for hits, `idx != ik` for misses) are
    /// required for MBP soundness: `select(store(a, i, v), j) → v` is only
    /// valid when `i = j`, and that must appear in the output formula.
    ///
    /// Ref: Z3 `mbp_arrays.cpp:672-710`.
    pub(super) fn reduce_select_store_with_conditions(
        &self,
        expr: &ChcExpr,
        model: &FxHashMap<String, SmtValue>,
        conditions: &mut Vec<super::Literal>,
    ) -> ChcExpr {
        crate::expr::maybe_grow_expr_stack(|| {
            if crate::expr::ExprDepthGuard::check().is_none() {
                return expr.clone();
            }
            match expr {
                ChcExpr::Op(ChcOp::Select, args) if args.len() == 2 => {
                    let arr = self.reduce_select_store_with_conditions(&args[0], model, conditions);
                    let idx = self.reduce_select_store_with_conditions(&args[1], model, conditions);
                    self.reduce_select_store_chain_with_conditions(&arr, &idx, model, conditions)
                }
                ChcExpr::Op(op, args) => {
                    let new_args: Vec<std::sync::Arc<ChcExpr>> = args
                        .iter()
                        .map(|a| {
                            std::sync::Arc::new(
                                self.reduce_select_store_with_conditions(a, model, conditions),
                            )
                        })
                        .collect();
                    ChcExpr::Op(*op, new_args)
                }
                ChcExpr::ConstArray(sort, val) => ChcExpr::ConstArray(
                    sort.clone(),
                    std::sync::Arc::new(
                        self.reduce_select_store_with_conditions(val, model, conditions),
                    ),
                ),
                _ => expr.clone(),
            }
        })
    }

    /// Walk a store chain resolving `select(arr, idx)`, collecting index
    /// conditions that justify each reduction step.
    ///
    /// For `select(store(...store(base, i1, v1)..., in, vn), idx)`:
    /// - If `M(idx) = M(ik)`: returns `vk` with condition `idx = ik`
    /// - If `M(idx) != M(ik)`: adds condition `idx != ik`, recurse to inner
    ///
    /// Ref: Z3 `mbp_arrays.cpp:672-710` (`reduce_core`).
    pub(super) fn reduce_select_store_chain_with_conditions(
        &self,
        arr: &ChcExpr,
        idx: &ChcExpr,
        model: &FxHashMap<String, SmtValue>,
        conditions: &mut Vec<super::Literal>,
    ) -> ChcExpr {
        match arr {
            ChcExpr::Op(ChcOp::Store, args) if args.len() == 3 => {
                let idx_val = self.eval_generic(idx, model);
                let store_idx_val = self.eval_generic(args[1].as_ref(), model);
                if idx_val.is_some() && idx_val == store_idx_val {
                    // Hit: select reads from this store layer.
                    // Emit condition: idx = store_idx
                    conditions.push(super::Literal::new(
                        ChcExpr::eq(idx.clone(), args[1].as_ref().clone()),
                        true,
                    ));
                    args[2].as_ref().clone()
                } else {
                    // Miss: select reads through this store layer.
                    // Emit condition: idx != store_idx (if both are evaluable)
                    if idx_val.is_some() && store_idx_val.is_some() {
                        conditions.push(super::Literal::new(
                            ChcExpr::ne(idx.clone(), args[1].as_ref().clone()),
                            true,
                        ));
                    }
                    self.reduce_select_store_chain_with_conditions(&args[0], idx, model, conditions)
                }
            }
            ChcExpr::ConstArray(_, val) => val.as_ref().clone(),
            _ => ChcExpr::select(arr.clone(), idx.clone()),
        }
    }
}
