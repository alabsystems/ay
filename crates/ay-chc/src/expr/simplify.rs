// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Constant simplification for CHC expressions.
//!
//! Extracted from methods.rs — the `simplify_constants` method and its
//! helper `bv_signed_cmp`.

use std::sync::Arc;

use ay_core::kani_compat::DetHashMap as FxHashMap;

use super::{
    maybe_grow_expr_stack, smt_euclid_div, smt_euclid_mod, ChcExpr, ChcOp, ChcSort,
    MAX_EXPR_RECURSION_DEPTH, MAX_PREPROCESSING_NODES,
};

/// Memoization table for `simplify_constants`, keyed by `Arc` pointer identity.
///
/// Maps an input subtree (identified by its stable heap address while the
/// top-level call holds it alive) to its simplified form, so a shared `Arc`
/// reachable N distinct ways is simplified once rather than N times. This
/// collapses the previous exponential DAG traversal to linear (#7060).
type SimplifyMemo = FxHashMap<*const ChcExpr, Arc<ChcExpr>>;

fn datatype_selector_projection(
    selector_name: &str,
    selector_sort: &ChcSort,
    value: &ChcExpr,
) -> Option<ChcExpr> {
    let ChcExpr::FuncApp(ctor_name, ChcSort::Datatype { constructors, .. }, ctor_args) = value
    else {
        return None;
    };

    for ctor in constructors.iter() {
        if ctor.name != *ctor_name {
            continue;
        }
        for (field_idx, selector) in ctor.selectors.iter().enumerate() {
            if selector.name == selector_name && selector.sort == *selector_sort {
                return ctor_args.get(field_idx).map(|field| field.as_ref().clone());
            }
        }
    }

    None
}

fn datatype_tester_result(
    tester_name: &str,
    tester_sort: &ChcSort,
    value: &ChcExpr,
) -> Option<bool> {
    if *tester_sort != ChcSort::Bool {
        return None;
    }
    let ChcExpr::FuncApp(ctor_name, ChcSort::Datatype { constructors, .. }, _) = value else {
        return None;
    };
    let tested_ctor = tester_name.strip_prefix("is-")?;
    let _value_ctor = constructors.iter().find(|ctor| ctor.name == *ctor_name)?;
    let _tested_ctor = constructors.iter().find(|ctor| ctor.name == tested_ctor)?;
    Some(ctor_name == tested_ctor)
}

fn is_datatype_constructor_app(name: &str, sort: &ChcSort) -> bool {
    let ChcSort::Datatype { constructors, .. } = sort else {
        return false;
    };
    constructors.iter().any(|ctor| ctor.name == name)
}

fn eval_nonnegative_const_u128(expr: &ChcExpr, depth: usize) -> Option<u128> {
    if depth >= MAX_EXPR_RECURSION_DEPTH {
        return None;
    }
    maybe_grow_expr_stack(|| match expr {
        ChcExpr::Int(n) if *n >= 0 => Some(*n as u128),
        ChcExpr::Op(ChcOp::Add, args) => {
            let mut acc = 0u128;
            for arg in args {
                acc = acc.checked_add(eval_nonnegative_const_u128(arg, depth + 1)?)?;
            }
            Some(acc)
        }
        ChcExpr::Op(ChcOp::Mul, args) => {
            let mut acc = 1u128;
            for arg in args {
                acc = acc.checked_mul(eval_nonnegative_const_u128(arg, depth + 1)?)?;
            }
            Some(acc)
        }
        ChcExpr::Op(ChcOp::Sub, args) if args.len() == 2 => {
            let lhs = eval_nonnegative_const_u128(&args[0], depth + 1)?;
            let rhs = eval_nonnegative_const_u128(&args[1], depth + 1)?;
            lhs.checked_sub(rhs)
        }
        ChcExpr::Op(ChcOp::Mod, args) if args.len() == 2 => {
            let lhs = eval_nonnegative_const_u128(&args[0], depth + 1)?;
            let rhs = eval_nonnegative_const_u128(&args[1], depth + 1)?;
            (rhs != 0).then_some(lhs % rhs)
        }
        ChcExpr::Op(ChcOp::Div, args) if args.len() == 2 => {
            let lhs = eval_nonnegative_const_u128(&args[0], depth + 1)?;
            let rhs = eval_nonnegative_const_u128(&args[1], depth + 1)?;
            (rhs != 0).then_some(lhs / rhs)
        }
        _ => None,
    })
}

impl ChcExpr {
    /// Simplify constant expressions, especially mod with constant arguments.
    ///
    /// Uses a node budget (#2771) to prevent unbounded heap allocation on
    /// pathological expression trees. On budget exhaustion, returns `self`
    /// unchanged — semantically correct, just unsimplified.
    pub(crate) fn simplify_constants(&self) -> Self {
        use std::cell::Cell;

        let budget = Cell::new(MAX_PREPROCESSING_NODES);
        let mut memo: SimplifyMemo = SimplifyMemo::default();

        /// Simplify a child `Arc` subtree, memoizing on pointer identity so each
        /// shared `Arc` subtree is simplified at most once per top-level call.
        /// `depth` is the depth of the *child* being simplified.
        ///
        /// SOUNDNESS: within one top-level `simplify_constants` call every input
        /// subtree stays alive (reachable from the borrowed `self`), so
        /// `Arc::as_ptr` is a stable, unique key for that subtree. A cached
        /// `Some` result is, by construction, a valid (semantically equal)
        /// simplification of that subtree. The budget/depth-exhaustion `None`
        /// case is never cached, so an earlier/shallower path that reaches the
        /// same subtree with budget to spare can still simplify it. Two distinct
        /// `Arc`s that happen to be structurally equal simply do not dedup —
        /// sound, just less sharing.
        fn simplify_arg(
            a: &Arc<ChcExpr>,
            budget: &Cell<usize>,
            depth: usize,
            memo: &mut SimplifyMemo,
        ) -> Arc<ChcExpr> {
            let key = Arc::as_ptr(a);
            if let Some(cached) = memo.get(&key) {
                return Arc::clone(cached);
            }
            match simplify_inner(a.as_ref(), budget, depth, memo) {
                Some(simplified) => {
                    let result = Arc::new(simplified);
                    memo.insert(key, Arc::clone(&result));
                    result
                }
                // Budget/depth exhausted: keep the original subtree (sound, and
                // preserves sharing) without caching.
                None => Arc::clone(a),
            }
        }

        /// Re-simplify a freshly constructed expression, threading the SAME
        /// `budget` and current `depth`. Reusing the budget makes nested
        /// re-simplification do strictly LESS work than a fresh budget would —
        /// on exhaustion `simplify_inner` returns the expression unsimplified,
        /// which is always semantically correct. A *fresh* memo is used because
        /// the temporary's subtree pointers are unrelated to the input's and may
        /// alias freed addresses once the temporary is dropped; scoping the memo
        /// to this sub-call keeps pointer identity sound.
        fn resimplify(e: ChcExpr, budget: &Cell<usize>, depth: usize) -> ChcExpr {
            let mut memo: SimplifyMemo = SimplifyMemo::default();
            simplify_inner(&e, budget, depth, &mut memo).unwrap_or(e)
        }

        fn simplify_inner(
            expr: &ChcExpr,
            budget: &Cell<usize>,
            depth: usize,
            memo: &mut SimplifyMemo,
        ) -> Option<ChcExpr> {
            maybe_grow_expr_stack(|| {
                // Depth bound (#2988): prevent unbounded stacker heap allocation.
                // At depth 500, stacker has allocated up to 1 GB of heap segments.
                if depth >= MAX_EXPR_RECURSION_DEPTH {
                    return None;
                }
                let remaining = budget.get();
                if remaining == 0 {
                    return None;
                }
                budget.set(remaining - 1);

                Some(match expr {
                    ChcExpr::Bool(_)
                    | ChcExpr::Int(_)
                    | ChcExpr::Real(_, _)
                    | ChcExpr::BitVec(_, _)
                    | ChcExpr::Var(_) => expr.clone(),
                    ChcExpr::Op(op, args) => {
                        // First simplify all arguments (memoized on Arc identity)
                        let simplified_args: Vec<Arc<ChcExpr>> = args
                            .iter()
                            .map(|a| simplify_arg(a, budget, depth + 1, memo))
                            .collect();

                        // Track whether any argument actually changed (#3665)
                        let args_changed = !args
                            .iter()
                            .zip(simplified_args.iter())
                            .all(|(old, new)| old.as_ref() == new.as_ref());

                        // Then try to simplify this operation
                        match op {
                            ChcOp::Ite if simplified_args.len() == 3 => {
                                // ITE with constant condition or Boolean branches.
                                match (
                                    simplified_args[0].as_ref(),
                                    simplified_args[1].as_ref(),
                                    simplified_args[2].as_ref(),
                                ) {
                                    (ChcExpr::Bool(true), then_expr, _) => then_expr.clone(),
                                    (ChcExpr::Bool(false), _, else_expr) => else_expr.clone(),
                                    (_, then_expr, else_expr) if then_expr == else_expr => {
                                        then_expr.clone()
                                    }
                                    (_, ChcExpr::Bool(true), ChcExpr::Bool(false)) => {
                                        simplified_args[0].as_ref().clone()
                                    }
                                    (_, ChcExpr::Bool(false), ChcExpr::Bool(true)) => resimplify(
                                        ChcExpr::not(simplified_args[0].as_ref().clone()),
                                        budget,
                                        depth,
                                    ),
                                    _ => {
                                        if args_changed {
                                            ChcExpr::Op(*op, simplified_args)
                                        } else {
                                            expr.clone()
                                        }
                                    }
                                }
                            }
                            ChcOp::Add if simplified_args.len() >= 2 => {
                                // Flatten nested additions and collect terms with coefficients.
                                // i128-lockstep: checked i128 folding; overflow beyond i128
                                // still refuses to fold (opaque term), never wraps.
                                let mut constant_sum: i128 = 0;
                                let mut var_terms: Vec<Arc<ChcExpr>> = Vec::new();

                                /// Push an expression scaled by `coeff` into `var_terms`.
                                /// coeff=1 → push as-is; coeff=-1 → wrap in Neg; else → wrap in Mul.
                                fn push_scaled_term(
                                    var_terms: &mut Vec<Arc<ChcExpr>>,
                                    expr: &ChcExpr,
                                    coeff: i128,
                                ) {
                                    if coeff == 1 {
                                        var_terms.push(Arc::new(expr.clone()));
                                    } else if coeff == -1 {
                                        var_terms.push(Arc::new(ChcExpr::Op(
                                            ChcOp::Neg,
                                            vec![Arc::new(expr.clone())],
                                        )));
                                    } else {
                                        var_terms.push(Arc::new(ChcExpr::Op(
                                            ChcOp::Mul,
                                            vec![
                                                Arc::new(ChcExpr::Int(coeff)),
                                                Arc::new(expr.clone()),
                                            ],
                                        )));
                                    }
                                }

                                fn collect_add_terms(
                                    expr: &ChcExpr,
                                    coeff: i128,
                                    constant_sum: &mut i128,
                                    var_terms: &mut Vec<Arc<ChcExpr>>,
                                    budget: &Cell<usize>,
                                    depth: usize,
                                ) {
                                    // Depth bound (#2988)
                                    if depth >= MAX_EXPR_RECURSION_DEPTH {
                                        push_scaled_term(var_terms, expr, coeff);
                                        return;
                                    }
                                    let remaining = budget.get();
                                    if remaining == 0 {
                                        push_scaled_term(var_terms, expr, coeff);
                                        return;
                                    }
                                    budget.set(remaining - 1);

                                    maybe_grow_expr_stack(|| match expr {
                                        ChcExpr::Int(n) => {
                                            // Checked arithmetic: overflow → treat as opaque term (#3693)
                                            // Use coeff-aware push on bailout (same as depth/budget
                                            // bailout above) to preserve the sign when coeff = -1.
                                            if let Some(product) = coeff.checked_mul(*n) {
                                                if let Some(new_sum) =
                                                    constant_sum.checked_add(product)
                                                {
                                                    *constant_sum = new_sum;
                                                } else {
                                                    // Sum overflows: push coeff*n as separate term
                                                    var_terms.push(Arc::new(ChcExpr::Int(product)));
                                                }
                                            } else {
                                                // coeff * n overflows: preserve coeff in expression
                                                push_scaled_term(var_terms, expr, coeff);
                                            }
                                        }
                                        // (#3121) Propagate coeff through Add/Sub/Neg for
                                        // proper flattening.  Previous `coeff == 1` guards
                                        // prevented simplification of nested arithmetic
                                        // (e.g. `Add(Neg(Sub(a,b)), a)` → `b`).
                                        ChcExpr::Op(ChcOp::Add, args) => {
                                            for arg in args {
                                                collect_add_terms(
                                                    arg.as_ref(),
                                                    coeff,
                                                    constant_sum,
                                                    var_terms,
                                                    budget,
                                                    depth + 1,
                                                );
                                            }
                                        }
                                        ChcExpr::Op(ChcOp::Sub, args) if args.len() == 2 => {
                                            collect_add_terms(
                                                args[0].as_ref(),
                                                coeff,
                                                constant_sum,
                                                var_terms,
                                                budget,
                                                depth + 1,
                                            );
                                            collect_add_terms(
                                                args[1].as_ref(),
                                                -coeff,
                                                constant_sum,
                                                var_terms,
                                                budget,
                                                depth + 1,
                                            );
                                        }
                                        ChcExpr::Op(ChcOp::Neg, args) if args.len() == 1 => {
                                            collect_add_terms(
                                                args[0].as_ref(),
                                                -coeff,
                                                constant_sum,
                                                var_terms,
                                                budget,
                                                depth + 1,
                                            );
                                        }
                                        _ => {
                                            push_scaled_term(var_terms, expr, coeff);
                                        }
                                    });
                                }

                                for arg in &simplified_args {
                                    collect_add_terms(
                                        arg.as_ref(),
                                        1,
                                        &mut constant_sum,
                                        &mut var_terms,
                                        budget,
                                        depth + 1,
                                    );
                                }

                                // Build result
                                if var_terms.is_empty() {
                                    ChcExpr::Int(constant_sum)
                                } else if constant_sum == 0 {
                                    if var_terms.len() == 1 {
                                        return Some(var_terms[0].as_ref().clone());
                                    }
                                    ChcExpr::Op(ChcOp::Add, var_terms)
                                } else {
                                    var_terms.push(Arc::new(ChcExpr::Int(constant_sum)));
                                    ChcExpr::Op(ChcOp::Add, var_terms)
                                }
                            }
                            ChcOp::Mul if simplified_args.len() >= 2 => {
                                if simplified_args
                                    .iter()
                                    .all(|a| matches!(a.as_ref(), ChcExpr::Int(_)))
                                {
                                    // Checked arithmetic: overflow → return unsimplified (#3693)
                                    let prod = simplified_args.iter().try_fold(1i128, |acc, a| {
                                        if let ChcExpr::Int(n) = a.as_ref() {
                                            acc.checked_mul(*n)
                                        } else {
                                            Some(acc)
                                        }
                                    });
                                    if let Some(p) = prod {
                                        return Some(ChcExpr::Int(p));
                                    }
                                }
                                if args_changed {
                                    ChcExpr::Op(*op, simplified_args)
                                } else {
                                    expr.clone()
                                }
                            }
                            ChcOp::Sub | ChcOp::Div | ChcOp::Mod if simplified_args.len() == 2 => {
                                if let (ChcExpr::Int(a), ChcExpr::Int(b)) =
                                    (simplified_args[0].as_ref(), simplified_args[1].as_ref())
                                {
                                    // Checked arithmetic: overflow → return unsimplified (#3693)
                                    let result = match op {
                                        ChcOp::Sub => a.checked_sub(*b),
                                        ChcOp::Div => smt_euclid_div(*a, *b),
                                        ChcOp::Mod => smt_euclid_mod(*a, *b),
                                        _ => None, // #6091: defensive
                                    };
                                    if let Some(val) = result {
                                        return Some(ChcExpr::Int(val));
                                    }
                                }
                                if matches!(op, ChcOp::Div | ChcOp::Mod) {
                                    if let (Some(a), Some(b)) = (
                                        eval_nonnegative_const_u128(
                                            simplified_args[0].as_ref(),
                                            depth + 1,
                                        ),
                                        eval_nonnegative_const_u128(
                                            simplified_args[1].as_ref(),
                                            depth + 1,
                                        ),
                                    ) {
                                        let result = if matches!(op, ChcOp::Div) {
                                            a.checked_div(b)
                                        } else {
                                            a.checked_rem(b)
                                        };
                                        if let Some(result) = result {
                                            // i128-lockstep: fold only when the u128 result
                                            // fits i128 (fail-closed: stays symbolic otherwise).
                                            if let Ok(val) = i128::try_from(result) {
                                                return Some(ChcExpr::Int(val));
                                            }
                                        }
                                    }
                                }
                                if args_changed {
                                    ChcExpr::Op(*op, simplified_args)
                                } else {
                                    expr.clone()
                                }
                            }
                            ChcOp::Neg if simplified_args.len() == 1 => {
                                if let ChcExpr::Int(n) = simplified_args[0].as_ref() {
                                    // Checked arithmetic: -i64::MIN overflows (#3693)
                                    if let Some(neg) = n.checked_neg() {
                                        return Some(ChcExpr::Int(neg));
                                    }
                                }
                                if args_changed {
                                    ChcExpr::Op(*op, simplified_args)
                                } else {
                                    expr.clone()
                                }
                            }
                            ChcOp::Eq | ChcOp::Ne if simplified_args.len() == 2 => {
                                let is_eq = matches!(op, ChcOp::Eq);
                                let make_cmp = |a: ChcExpr, b: ChcExpr| {
                                    resimplify(
                                        if is_eq {
                                            ChcExpr::eq(a, b)
                                        } else {
                                            ChcExpr::ne(a, b)
                                        },
                                        budget,
                                        depth,
                                    )
                                };
                                if let (ChcExpr::Int(a), ChcExpr::Int(b)) =
                                    (simplified_args[0].as_ref(), simplified_args[1].as_ref())
                                {
                                    return Some(ChcExpr::Bool((a == b) == is_eq));
                                }
                                if let (ChcExpr::Bool(a), ChcExpr::Bool(b)) =
                                    (simplified_args[0].as_ref(), simplified_args[1].as_ref())
                                {
                                    return Some(ChcExpr::Bool((a == b) == is_eq));
                                }
                                if matches!(simplified_args[0].as_ref(), ChcExpr::Bool(true)) {
                                    let result = simplified_args[1].as_ref().clone();
                                    return Some(if is_eq {
                                        result
                                    } else {
                                        resimplify(ChcExpr::not(result), budget, depth)
                                    });
                                }
                                if matches!(simplified_args[1].as_ref(), ChcExpr::Bool(true)) {
                                    let result = simplified_args[0].as_ref().clone();
                                    return Some(if is_eq {
                                        result
                                    } else {
                                        resimplify(ChcExpr::not(result), budget, depth)
                                    });
                                }
                                if matches!(simplified_args[0].as_ref(), ChcExpr::Bool(false)) {
                                    let result = resimplify(
                                        ChcExpr::not(simplified_args[1].as_ref().clone()),
                                        budget,
                                        depth,
                                    );
                                    return Some(if is_eq {
                                        result
                                    } else {
                                        resimplify(ChcExpr::not(result), budget, depth)
                                    });
                                }
                                if matches!(simplified_args[1].as_ref(), ChcExpr::Bool(false)) {
                                    let result = resimplify(
                                        ChcExpr::not(simplified_args[0].as_ref().clone()),
                                        budget,
                                        depth,
                                    );
                                    return Some(if is_eq {
                                        result
                                    } else {
                                        resimplify(ChcExpr::not(result), budget, depth)
                                    });
                                }
                                if let (ChcExpr::BitVec(a, _), ChcExpr::BitVec(b, _)) =
                                    (simplified_args[0].as_ref(), simplified_args[1].as_ref())
                                {
                                    return Some(ChcExpr::Bool((a == b) == is_eq));
                                }
                                if simplified_args[0] == simplified_args[1] {
                                    return Some(ChcExpr::Bool(is_eq));
                                }
                                if let ChcExpr::Op(ChcOp::Ite, ite_args) =
                                    simplified_args[0].as_ref()
                                {
                                    if ite_args.len() == 3 {
                                        return Some(resimplify(
                                            ChcExpr::ite(
                                                ite_args[0].as_ref().clone(),
                                                make_cmp(
                                                    ite_args[1].as_ref().clone(),
                                                    simplified_args[1].as_ref().clone(),
                                                ),
                                                make_cmp(
                                                    ite_args[2].as_ref().clone(),
                                                    simplified_args[1].as_ref().clone(),
                                                ),
                                            ),
                                            budget,
                                            depth,
                                        ));
                                    }
                                }
                                if let ChcExpr::Op(ChcOp::Ite, ite_args) =
                                    simplified_args[1].as_ref()
                                {
                                    if ite_args.len() == 3 {
                                        return Some(resimplify(
                                            ChcExpr::ite(
                                                ite_args[0].as_ref().clone(),
                                                make_cmp(
                                                    simplified_args[0].as_ref().clone(),
                                                    ite_args[1].as_ref().clone(),
                                                ),
                                                make_cmp(
                                                    simplified_args[0].as_ref().clone(),
                                                    ite_args[2].as_ref().clone(),
                                                ),
                                            ),
                                            budget,
                                            depth,
                                        ));
                                    }
                                }
                                if let (
                                    ChcExpr::FuncApp(lhs_name, lhs_sort, lhs_args),
                                    ChcExpr::FuncApp(rhs_name, rhs_sort, rhs_args),
                                ) = (simplified_args[0].as_ref(), simplified_args[1].as_ref())
                                {
                                    if matches!(lhs_sort, super::ChcSort::Datatype { .. })
                                        && lhs_sort == rhs_sort
                                        && is_datatype_constructor_app(lhs_name, lhs_sort)
                                        && is_datatype_constructor_app(rhs_name, rhs_sort)
                                    {
                                        if lhs_name != rhs_name {
                                            return Some(ChcExpr::Bool(!is_eq));
                                        }
                                        if lhs_args.len() == rhs_args.len() {
                                            let fields = lhs_args.iter().zip(rhs_args.iter()).map(
                                                |(lhs, rhs)| {
                                                    ChcExpr::eq(
                                                        lhs.as_ref().clone(),
                                                        rhs.as_ref().clone(),
                                                    )
                                                },
                                            );
                                            let result =
                                                resimplify(ChcExpr::and_all(fields), budget, depth);
                                            return Some(if is_eq {
                                                result
                                            } else {
                                                resimplify(ChcExpr::not(result), budget, depth)
                                            });
                                        }
                                    }
                                }
                                if args_changed {
                                    ChcExpr::Op(*op, simplified_args)
                                } else {
                                    expr.clone()
                                }
                            }
                            ChcOp::Lt | ChcOp::Le | ChcOp::Gt | ChcOp::Ge
                                if simplified_args.len() == 2 =>
                            {
                                if let (ChcExpr::Int(a), ChcExpr::Int(b)) =
                                    (simplified_args[0].as_ref(), simplified_args[1].as_ref())
                                {
                                    let result = match op {
                                        ChcOp::Lt => Some(a < b),
                                        ChcOp::Le => Some(a <= b),
                                        ChcOp::Gt => Some(a > b),
                                        ChcOp::Ge => Some(a >= b),
                                        _ => None, // #6091: defensive
                                    };
                                    if let Some(r) = result {
                                        return Some(ChcExpr::Bool(r));
                                    }
                                }
                                // #1362: Simplify reflexive comparisons (>= x x) → true, (> x x) → false
                                if simplified_args[0] == simplified_args[1] {
                                    return Some(ChcExpr::Bool(matches!(
                                        op,
                                        ChcOp::Le | ChcOp::Ge
                                    )));
                                }
                                if args_changed {
                                    ChcExpr::Op(*op, simplified_args)
                                } else {
                                    expr.clone()
                                }
                            }
                            ChcOp::Not if simplified_args.len() == 1 => {
                                if let ChcExpr::Bool(b) = simplified_args[0].as_ref() {
                                    return Some(ChcExpr::Bool(!b));
                                }
                                if let ChcExpr::Op(ChcOp::Not, args) = simplified_args[0].as_ref() {
                                    if args.len() == 1 {
                                        return Some(args[0].as_ref().clone());
                                    }
                                }
                                if let ChcExpr::Op(ChcOp::Ite, args) = simplified_args[0].as_ref() {
                                    if args.len() == 3 {
                                        return Some(resimplify(
                                            ChcExpr::ite(
                                                args[0].as_ref().clone(),
                                                resimplify(
                                                    ChcExpr::not(args[1].as_ref().clone()),
                                                    budget,
                                                    depth,
                                                ),
                                                resimplify(
                                                    ChcExpr::not(args[2].as_ref().clone()),
                                                    budget,
                                                    depth,
                                                ),
                                            ),
                                            budget,
                                            depth,
                                        ));
                                    }
                                }
                                if args_changed {
                                    ChcExpr::Op(*op, simplified_args)
                                } else {
                                    expr.clone()
                                }
                            }
                            ChcOp::And => {
                                fn flatten_and(
                                    expr: &ChcExpr,
                                    result: &mut Vec<Arc<ChcExpr>>,
                                    depth: usize,
                                ) -> bool {
                                    // Depth bound (#2988)
                                    if depth >= MAX_EXPR_RECURSION_DEPTH {
                                        result.push(Arc::new(expr.clone()));
                                        return true;
                                    }
                                    maybe_grow_expr_stack(|| match expr {
                                        ChcExpr::Bool(true) => true,
                                        ChcExpr::Bool(false) => false,
                                        ChcExpr::Op(ChcOp::And, args) => {
                                            for arg in args {
                                                if !flatten_and(arg.as_ref(), result, depth + 1) {
                                                    return false;
                                                }
                                            }
                                            true
                                        }
                                        _ => {
                                            result.push(Arc::new(expr.clone()));
                                            true
                                        }
                                    })
                                }

                                let mut new_args = Vec::new();
                                for arg in &simplified_args {
                                    if !flatten_and(arg.as_ref(), &mut new_args, depth + 1) {
                                        return Some(ChcExpr::Bool(false));
                                    }
                                }

                                if new_args.is_empty() {
                                    return Some(ChcExpr::Bool(true));
                                }
                                if new_args.len() == 1 {
                                    return Some(new_args[0].as_ref().clone());
                                }

                                let mut positive_conjuncts: Vec<&ChcExpr> = Vec::new();
                                let mut negated_conjuncts: Vec<&ChcExpr> = Vec::new();

                                for arg in &new_args {
                                    if let ChcExpr::Op(ChcOp::Not, not_args) = arg.as_ref() {
                                        if not_args.len() == 1 {
                                            negated_conjuncts.push(not_args[0].as_ref());
                                        }
                                    } else {
                                        positive_conjuncts.push(arg.as_ref());
                                    }
                                }

                                for pos in &positive_conjuncts {
                                    for neg in &negated_conjuncts {
                                        if pos == neg {
                                            return Some(ChcExpr::Bool(false));
                                        }
                                    }
                                }

                                ChcExpr::Op(ChcOp::And, new_args)
                            }
                            ChcOp::Or => {
                                let mut new_args = Vec::new();
                                for arg in &simplified_args {
                                    match arg.as_ref() {
                                        ChcExpr::Bool(false) => {}
                                        ChcExpr::Bool(true) => return Some(ChcExpr::Bool(true)),
                                        _ => new_args.push(arg.clone()),
                                    }
                                }
                                if new_args.is_empty() {
                                    return Some(ChcExpr::Bool(false));
                                }
                                if new_args.len() == 1 {
                                    return Some(new_args[0].as_ref().clone());
                                }
                                ChcExpr::Op(ChcOp::Or, new_args)
                            }
                            ChcOp::Implies if simplified_args.len() == 2 => {
                                let lhs = simplified_args[0].as_ref();
                                let rhs = simplified_args[1].as_ref();
                                match (lhs, rhs) {
                                    (ChcExpr::Bool(false), _) => ChcExpr::Bool(true),
                                    (ChcExpr::Bool(true), _) => rhs.clone(),
                                    (_, ChcExpr::Bool(true)) => ChcExpr::Bool(true),
                                    (_, ChcExpr::Bool(false)) => {
                                        ChcExpr::Op(ChcOp::Not, vec![simplified_args[0].clone()])
                                    }
                                    _ => {
                                        if args_changed {
                                            ChcExpr::Op(*op, simplified_args)
                                        } else {
                                            expr.clone()
                                        }
                                    }
                                }
                            }
                            // BV constant folding: concat, extract, zero/sign-extend
                            ChcOp::BvConcat if simplified_args.len() == 2 => {
                                if let (ChcExpr::BitVec(a, wa), ChcExpr::BitVec(b, wb)) =
                                    (simplified_args[0].as_ref(), simplified_args[1].as_ref())
                                {
                                    let width = wa + wb;
                                    // Can only fold if result fits in u128
                                    if width <= 128 {
                                        let mask = if width >= 128 {
                                            u128::MAX
                                        } else {
                                            (1u128 << width) - 1
                                        };
                                        return Some(ChcExpr::BitVec(
                                            ((a << wb) | b) & mask,
                                            width,
                                        ));
                                    }
                                    // width > 128: leave as BvConcat tree (can't fit in u128)
                                }
                                if args_changed {
                                    ChcExpr::Op(*op, simplified_args)
                                } else {
                                    expr.clone()
                                }
                            }
                            ChcOp::BvExtract(hi, lo) if simplified_args.len() == 1 => {
                                if let ChcExpr::BitVec(v, _w) = simplified_args[0].as_ref() {
                                    let width = hi - lo + 1;
                                    let mask = if width >= 128 {
                                        u128::MAX
                                    } else {
                                        (1u128 << width) - 1
                                    };
                                    return Some(ChcExpr::BitVec((v >> lo) & mask, width));
                                }
                                if args_changed {
                                    ChcExpr::Op(*op, simplified_args)
                                } else {
                                    expr.clone()
                                }
                            }
                            ChcOp::Bv2Nat if simplified_args.len() == 1 => {
                                if let ChcExpr::BitVec(v, w) = simplified_args[0].as_ref() {
                                    let mask = if *w >= 128 {
                                        u128::MAX
                                    } else {
                                        (1u128 << w) - 1
                                    };
                                    // i128-lockstep: fold only when the bv2nat value fits
                                    // i128 (fail-closed: stays symbolic otherwise).
                                    if let Ok(value) = i128::try_from(v & mask) {
                                        return Some(ChcExpr::Int(value));
                                    }
                                }
                                if args_changed {
                                    ChcExpr::Op(*op, simplified_args)
                                } else {
                                    expr.clone()
                                }
                            }
                            ChcOp::BvZeroExtend(n) if simplified_args.len() == 1 => {
                                if let ChcExpr::BitVec(v, w) = simplified_args[0].as_ref() {
                                    return Some(ChcExpr::BitVec(*v, w + n));
                                }
                                if args_changed {
                                    ChcExpr::Op(*op, simplified_args)
                                } else {
                                    expr.clone()
                                }
                            }
                            ChcOp::BvSignExtend(n) if simplified_args.len() == 1 => {
                                if let ChcExpr::BitVec(v, w) = simplified_args[0].as_ref() {
                                    // Sign-extend: replicate the sign bit
                                    let sign_bit = if *w > 0 { (v >> (w - 1)) & 1 } else { 0 };
                                    let new_width = w + n;
                                    let result = if sign_bit == 1 {
                                        let upper_mask = if new_width >= 128 {
                                            u128::MAX
                                        } else {
                                            (1u128 << new_width) - 1
                                        };
                                        let lower_mask = if *w >= 128 {
                                            u128::MAX
                                        } else {
                                            (1u128 << w) - 1
                                        };
                                        (v & lower_mask) | (upper_mask & !lower_mask)
                                    } else {
                                        *v
                                    };
                                    return Some(ChcExpr::BitVec(result, new_width));
                                }
                                if args_changed {
                                    ChcExpr::Op(*op, simplified_args)
                                } else {
                                    expr.clone()
                                }
                            }
                            ChcOp::BvNot if simplified_args.len() == 1 => {
                                if let ChcExpr::BitVec(v, w) = simplified_args[0].as_ref() {
                                    let mask = if *w >= 128 {
                                        u128::MAX
                                    } else {
                                        (1u128 << w) - 1
                                    };
                                    return Some(ChcExpr::BitVec(!v & mask, *w));
                                }
                                if args_changed {
                                    ChcExpr::Op(*op, simplified_args)
                                } else {
                                    expr.clone()
                                }
                            }
                            ChcOp::BvNeg if simplified_args.len() == 1 => {
                                if let ChcExpr::BitVec(v, w) = simplified_args[0].as_ref() {
                                    let mask = if *w >= 128 {
                                        u128::MAX
                                    } else {
                                        (1u128 << w) - 1
                                    };
                                    return Some(ChcExpr::BitVec(v.wrapping_neg() & mask, *w));
                                }
                                if args_changed {
                                    ChcExpr::Op(*op, simplified_args)
                                } else {
                                    expr.clone()
                                }
                            }
                            ChcOp::BvAdd
                            | ChcOp::BvSub
                            | ChcOp::BvMul
                            | ChcOp::BvAnd
                            | ChcOp::BvOr
                            | ChcOp::BvXor
                                if simplified_args.len() == 2 =>
                            {
                                if let (ChcExpr::BitVec(a, wa), ChcExpr::BitVec(b, wb)) =
                                    (simplified_args[0].as_ref(), simplified_args[1].as_ref())
                                {
                                    // SOUNDNESS: only fold when operand widths agree.
                                    // Sort-changing substitutions can produce ill-typed
                                    // BV atoms (see smt/convert.rs #6047 notes); masking
                                    // by the LEFT width would silently truncate/misread
                                    // the right operand and fold to a wrong constant,
                                    // which const-prop short-circuits (Bool(false)
                                    // fast-paths in inductiveness/verification) then
                                    // trust without SMT. Width-mismatched terms stay
                                    // symbolic — fail-closed, matching BvUDiv/BvURem.
                                    if wa == wb {
                                        let mask = if *wa >= 128 {
                                            u128::MAX
                                        } else {
                                            (1u128 << wa) - 1
                                        };
                                        let result = match op {
                                            ChcOp::BvAdd => Some(a.wrapping_add(*b) & mask),
                                            ChcOp::BvSub => Some(a.wrapping_sub(*b) & mask),
                                            ChcOp::BvMul => Some(a.wrapping_mul(*b) & mask),
                                            ChcOp::BvAnd => Some((a & b) & mask),
                                            ChcOp::BvOr => Some((a | b) & mask),
                                            ChcOp::BvXor => Some((a ^ b) & mask),
                                            _ => None, // #6091: defensive
                                        };
                                        if let Some(r) = result {
                                            return Some(ChcExpr::BitVec(r, *wa));
                                        }
                                    }
                                }
                                if args_changed {
                                    ChcExpr::Op(*op, simplified_args)
                                } else {
                                    expr.clone()
                                }
                            }
                            ChcOp::BvUDiv | ChcOp::BvURem if simplified_args.len() == 2 => {
                                if let (ChcExpr::BitVec(a, wa), ChcExpr::BitVec(b, wb)) =
                                    (simplified_args[0].as_ref(), simplified_args[1].as_ref())
                                {
                                    if wa == wb {
                                        let mask = if *wa >= 128 {
                                            u128::MAX
                                        } else {
                                            (1u128 << wa) - 1
                                        };
                                        let dividend = a & mask;
                                        let divisor = b & mask;
                                        let result = match op {
                                            // SMT-LIB: bvudiv by 0 returns all-ones.
                                            ChcOp::BvUDiv => {
                                                Some(dividend.checked_div(divisor).unwrap_or(mask))
                                            }
                                            // SMT-LIB: bvurem by 0 returns the dividend.
                                            ChcOp::BvURem => Some(if divisor == 0 {
                                                dividend
                                            } else {
                                                dividend % divisor
                                            }),
                                            _ => None, // #6091: defensive
                                        };
                                        if let Some(r) = result {
                                            return Some(ChcExpr::BitVec(r & mask, *wa));
                                        }
                                    }
                                }
                                // Power-of-two constant divisor with a NON-constant
                                // dividend: rewrite to shift/mask — exact SMT-LIB
                                // equivalences (wishlist rank 3, 2026-07-08):
                                //   bvudiv(x, 2^k) = bvlshr(x, k)
                                //   bvurem(x, 2^k) = bvand(x, 2^k - 1)
                                // Shifts/masks are structure every lane decides
                                // precisely; the division op must not survive into
                                // lanes that abstract it to havoc bits (the
                                // safe-midpoint `x / 2` class). Sound for all x,
                                // incl. k = 0 (bvlshr by 0 / bvand with 0).
                                if let ChcExpr::BitVec(b, wb) = simplified_args[1].as_ref() {
                                    let mask = if *wb >= 128 {
                                        u128::MAX
                                    } else {
                                        (1u128 << wb) - 1
                                    };
                                    let divisor = b & mask;
                                    if divisor.is_power_of_two() {
                                        let k = u128::from(divisor.trailing_zeros());
                                        let dividend = simplified_args[0].clone();
                                        return Some(match op {
                                            ChcOp::BvUDiv => ChcExpr::Op(
                                                ChcOp::BvLShr,
                                                vec![dividend, Arc::new(ChcExpr::BitVec(k, *wb))],
                                            ),
                                            _ => ChcExpr::Op(
                                                ChcOp::BvAnd,
                                                vec![
                                                    dividend,
                                                    Arc::new(ChcExpr::BitVec(divisor - 1, *wb)),
                                                ],
                                            ),
                                        });
                                    }
                                }
                                if args_changed {
                                    ChcExpr::Op(*op, simplified_args)
                                } else {
                                    expr.clone()
                                }
                            }
                            // BV comparison constant folding
                            ChcOp::BvULt
                            | ChcOp::BvULe
                            | ChcOp::BvUGt
                            | ChcOp::BvUGe
                            | ChcOp::BvSLt
                            | ChcOp::BvSLe
                            | ChcOp::BvSGt
                            | ChcOp::BvSGe
                                if simplified_args.len() == 2 =>
                            {
                                if let (ChcExpr::BitVec(a, wa), ChcExpr::BitVec(b, wb)) =
                                    (simplified_args[0].as_ref(), simplified_args[1].as_ref())
                                {
                                    // SOUNDNESS: same width guard as the arithmetic
                                    // fold above — an ill-typed cross-width compare
                                    // has no defined SMT-LIB value; folding it to a
                                    // Bool constant would flow into unchecked
                                    // Bool(false)/Bool(true) fast-paths. Stay symbolic.
                                    if wa == wb {
                                        let result = match op {
                                            ChcOp::BvULt => a < b,
                                            ChcOp::BvULe => a <= b,
                                            ChcOp::BvUGt => a > b,
                                            ChcOp::BvUGe => a >= b,
                                            ChcOp::BvSLt => {
                                                bv_signed_cmp(*a, *b, *wa)
                                                    == std::cmp::Ordering::Less
                                            }
                                            ChcOp::BvSLe => {
                                                bv_signed_cmp(*a, *b, *wa)
                                                    != std::cmp::Ordering::Greater
                                            }
                                            ChcOp::BvSGt => {
                                                bv_signed_cmp(*a, *b, *wa)
                                                    == std::cmp::Ordering::Greater
                                            }
                                            ChcOp::BvSGe => {
                                                bv_signed_cmp(*a, *b, *wa)
                                                    != std::cmp::Ordering::Less
                                            }
                                            _ => unreachable!(),
                                        };
                                        return Some(ChcExpr::Bool(result));
                                    }
                                }
                                if args_changed {
                                    ChcExpr::Op(*op, simplified_args)
                                } else {
                                    expr.clone()
                                }
                            }
                            _ => {
                                if args_changed {
                                    ChcExpr::Op(*op, simplified_args)
                                } else {
                                    expr.clone()
                                }
                            }
                        }
                    }
                    ChcExpr::FuncApp(name, sort, args) => {
                        let simplified_args: Vec<Arc<ChcExpr>> = args
                            .iter()
                            .map(|arg| simplify_arg(arg, budget, depth + 1, memo))
                            .collect();
                        if simplified_args.len() == 1 {
                            if let Some(field) = datatype_selector_projection(
                                name,
                                sort,
                                simplified_args[0].as_ref(),
                            ) {
                                return Some(field);
                            }
                            if let Some(result) =
                                datatype_tester_result(name, sort, simplified_args[0].as_ref())
                            {
                                return Some(ChcExpr::Bool(result));
                            }
                        }

                        let args_changed = !args
                            .iter()
                            .zip(simplified_args.iter())
                            .all(|(old, new)| old.as_ref() == new.as_ref());
                        if args_changed {
                            ChcExpr::FuncApp(name.clone(), sort.clone(), simplified_args)
                        } else {
                            expr.clone()
                        }
                    }
                    // Explicit arm (rather than the `map_children_with` fallback)
                    // so the predicate's argument `Arc`s are memoized by pointer
                    // identity too — this is the multi-argument case (e.g. one
                    // transition predicate over 100+ vars with shared subterms).
                    ChcExpr::PredicateApp(name, id, args) => {
                        let simplified_args: Vec<Arc<ChcExpr>> = args
                            .iter()
                            .map(|arg| simplify_arg(arg, budget, depth + 1, memo))
                            .collect();
                        let args_changed = !args
                            .iter()
                            .zip(simplified_args.iter())
                            .all(|(old, new)| old.as_ref() == new.as_ref());
                        if args_changed {
                            ChcExpr::PredicateApp(name.clone(), *id, simplified_args)
                        } else {
                            expr.clone()
                        }
                    }
                    _ => expr.map_children_with(|child| {
                        simplify_inner(child, budget, depth + 1, memo)
                            .unwrap_or_else(|| child.clone())
                    }),
                })
            })
        }

        simplify_inner(self, &budget, 0, &mut memo).unwrap_or_else(|| self.clone())
    }
}

/// Compare two BV values as signed (two's complement) for constant folding.
fn bv_signed_cmp(a: u128, b: u128, width: u32) -> std::cmp::Ordering {
    if width == 0 || width > 128 {
        return a.cmp(&b);
    }
    if width == 128 {
        return (a as i128).cmp(&(b as i128));
    }
    let sign_bit = 1u128 << (width - 1);
    let a_neg = a & sign_bit != 0;
    let b_neg = b & sign_bit != 0;
    match (a_neg, b_neg) {
        (true, false) => std::cmp::Ordering::Less, // negative < positive
        (false, true) => std::cmp::Ordering::Greater, // positive > negative
        _ => a.cmp(&b),                            // same sign: unsigned comparison is correct
    }
}
