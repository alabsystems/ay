// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#[allow(unused_imports)]
use super::*;
#[allow(unused_imports)]
use super::{
    evaluate::evaluate_expr, expr_depth, maybe_grow_expr_stack, smt_euclid_div, smt_euclid_mod,
    walk_linear_expr, ExprDepthGuard, LinearTermsProd, EXPR_STACK_SIZE, MAX_EXPR_RECURSION_DEPTH,
};
#[allow(unused_imports)]
use ay_core::kani_compat::DetHashMap as FxHashMap;
#[allow(unused_imports)]
use std::sync::Arc;

mod bigint_escape;
mod budget_and_simplify;
mod bv_const_fold_differential;
mod bv_sort_and_arrays;
mod evaluator;
mod i128_widening;
mod linear_and_constructors;
mod normalize_negations;

fn right_leaf_of_left_associated_and_chain(mut expr: &ChcExpr, depth: usize) -> &ChcExpr {
    for _ in 0..depth {
        match expr {
            ChcExpr::Op(ChcOp::And, args) if args.len() == 2 => {
                expr = args[1].as_ref();
            }
            _ => panic!("expected left-associated binary and chain"),
        }
    }
    expr
}
