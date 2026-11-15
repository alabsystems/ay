// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::smt::SmtContext;
use crate::ChcSort;
use std::sync::Arc;

fn bv(name: &str, width: u32) -> ChcVar {
    ChcVar::new(name, ChcSort::BitVec(width))
}

fn op(operator: ChcOp, args: Vec<ChcExpr>) -> ChcExpr {
    ChcExpr::Op(operator, args.into_iter().map(Arc::new).collect())
}

fn below(x: &ChcVar, bound: u128, width: u32) -> ChcExpr {
    op(
        ChcOp::BvULt,
        vec![ChcExpr::var(x.clone()), ChcExpr::BitVec(bound, width)],
    )
}

fn times(x: &ChcVar, factor: u128, width: u32) -> ChcExpr {
    op(
        ChcOp::BvMul,
        vec![ChcExpr::var(x.clone()), ChcExpr::BitVec(factor, width)],
    )
}

fn equivalent(left: &ChcExpr, right: &ChcExpr) -> bool {
    let differ = ChcExpr::not(ChcExpr::eq(left.clone(), right.clone()));
    SmtContext::new().check_sat(&differ).is_unsat()
}

fn any_of(a: &ChcVar, values: &[u128], width: u32) -> ChcExpr {
    ChcExpr::or_all(
        values
            .iter()
            .map(|v| ChcExpr::eq(ChcExpr::var(a.clone()), ChcExpr::BitVec(*v, width))),
    )
}

/// `∃x. x < 3 ∧ a = 4x` is `a ∈ {0, 4, 8}`; the multiplier is even, so no
/// inverse eliminates `x`.
#[test]
fn a_bounded_local_splits_into_its_cases() {
    let (x, a) = (bv("x", 4), bv("a", 4));
    let formula = ChcExpr::and(
        below(&x, 3, 4),
        ChcExpr::eq(ChcExpr::var(a.clone()), times(&x, 4, 4)),
    );
    let cases = split(&formula, std::slice::from_ref(&a)).expect("x is bounded");
    assert!(!cases.vars().contains(&x), "{cases}");
    assert!(equivalent(&cases, &any_of(&a, &[0, 4, 8], 4)), "{cases}");
}

/// Two bounded locals in one disjunct, an inclusive bound, and an empty one.
#[test]
fn every_bounded_local_of_every_disjunct_splits() {
    let (x, y, a) = (bv("x", 4), bv("y", 4), bv("a", 4));
    let sum = op(ChcOp::BvAdd, vec![times(&x, 4, 4), ChcExpr::var(y.clone())]);
    let formula = ChcExpr::and_all([
        below(&x, 2, 4),
        op(
            ChcOp::BvULe,
            vec![ChcExpr::var(y.clone()), ChcExpr::BitVec(1, 4)],
        ),
        ChcExpr::eq(ChcExpr::var(a.clone()), sum),
    ]);
    let cases = split(&formula, std::slice::from_ref(&a)).expect("x and y are bounded");
    assert!(
        !cases.vars().contains(&x) && !cases.vars().contains(&y),
        "{cases}"
    );
    assert!(equivalent(&cases, &any_of(&a, &[0, 1, 4, 5], 4)), "{cases}");

    let empty = ChcExpr::and(
        below(&x, 0, 4),
        ChcExpr::eq(ChcExpr::var(a.clone()), times(&x, 4, 4)),
    );
    let cases = split(&empty, std::slice::from_ref(&a)).expect("x is bounded");
    assert!(equivalent(&cases, &ChcExpr::Bool(false)), "{cases}");
}

#[test]
fn kept_and_wide_bounds_are_not_split() {
    let (x, a) = (bv("x", 8), bv("a", 8));
    let kept = ChcExpr::and(
        below(&a, 3, 8),
        ChcExpr::eq(ChcExpr::var(a.clone()), times(&x, 4, 8)),
    );
    assert!(split(&kept, std::slice::from_ref(&a)).is_none());
    let wide = ChcExpr::and(
        below(&x, 9, 8),
        ChcExpr::eq(ChcExpr::var(a.clone()), times(&x, 4, 8)),
    );
    assert!(split(&wide, std::slice::from_ref(&a)).is_none());
}
