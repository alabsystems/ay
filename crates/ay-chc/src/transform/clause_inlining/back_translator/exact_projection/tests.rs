// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

mod arrays;
mod boolean_pins;
mod checked_pair;
mod closed_arrays;
mod closed_image;
mod consumer;
mod factored_formula;
mod inverse;
mod oracle;
mod original_owner;
mod resources;
mod retained_formula;
mod shift;
mod source;
mod sum_carry;

fn var(name: &str, width: u32) -> ChcVar {
    ChcVar::new(name, ChcSort::BitVec(width))
}

fn expr(var: &ChcVar) -> ChcExpr {
    ChcExpr::Var(var.clone())
}

fn op(op: ChcOp, args: Vec<ChcExpr>) -> ChcExpr {
    ChcExpr::Op(op, args.into_iter().map(Arc::new).collect())
}

fn eq(a: ChcExpr, b: ChcExpr) -> ChcExpr {
    op(ChcOp::Eq, vec![a, b])
}

fn quotient(x: &ChcVar, divisor: u128) -> ChcExpr {
    let ChcSort::BitVec(width) = x.sort else {
        panic!("bitvector fixture")
    };
    op(
        ChcOp::BvUDiv,
        vec![expr(x), ChcExpr::BitVec(divisor, width)],
    )
}

fn closed(formula: &ChcExpr, keep: &[ChcVar]) -> ChcExpr {
    match run(formula, keep, &mut Scope::new(Limits::default(), &|| true)) {
        Projection::Closed(expr) => expr,
        Projection::Declined => panic!("expected exact projection, got decline"),
        Projection::Stopped => panic!("fixture exhausted the projection scope"),
    }
}

fn declined(formula: &ChcExpr, keep: &[ChcVar]) {
    assert!(matches!(
        run(formula, keep, &mut Scope::new(Limits::default(), &|| true)),
        Projection::Declined
    ));
}

fn has_neutral_true(image: &ChcExpr) -> bool {
    matches!(image, ChcExpr::Op(ChcOp::And, args)
        if args.iter().any(|arg| matches!(**arg, ChcExpr::Bool(true))))
}

#[test]
fn closed_images_drop_neutral_true_conjuncts() {
    let a = var("a", 4);
    let x = var("x", 4);
    let keep = std::slice::from_ref(&a);
    let bound = op(ChcOp::BvULe, vec![expr(&a), ChcExpr::BitVec(5, 4)]);
    let t = || ChcExpr::Bool(true);
    // Every variable retained (the closed shortcut), and a retained factor
    // beside a local whose elimination leaves the image true.
    let shortcut = closed(&op(ChcOp::And, vec![t(), bound.clone(), t()]), keep);
    let local = eq(expr(&x), expr(&a));
    let factor = closed(&op(ChcOp::And, vec![t(), bound, local]), keep);
    for image in [&shortcut, &factor] {
        assert!(!has_neutral_true(image), "{image:?}");
        for value in 0..16 {
            assert_eq!(oracle::truth(image, &[("a", value)]), value <= 5);
        }
    }
    assert_eq!(closed(&op(ChcOp::And, vec![t(), t()]), keep), t());
}

#[test]
fn quotient_image_preserves_repeated_and_correlated_uses() {
    let x = var("x", 4);
    let a = var("a", 4);
    let b = var("b", 4);
    let formula = op(
        ChcOp::And,
        vec![eq(expr(&a), quotient(&x, 2)), eq(expr(&b), quotient(&x, 2))],
    );
    let projected = closed(&formula, &[a, b]);
    for a in 0..16 {
        for b in 0..16 {
            assert_eq!(
                oracle::truth(&projected, &[("a", a), ("b", b)]),
                a == b && a < 8
            );
        }
    }
}

#[test]
fn branchwise_projection_preserves_common_constraints_and_every_alternative() {
    let x = var("x", 3);
    let a = var("a", 3);
    let flag = ChcVar::new("flag", ChcSort::Bool);
    let body = op(
        ChcOp::Or,
        vec![
            eq(expr(&a), quotient(&x, 2)),
            eq(expr(&a), ChcExpr::BitVec(7, 3)),
        ],
    );
    let formula = op(ChcOp::And, vec![expr(&flag), body]);
    let projected = closed(&formula, &[a, flag]);
    for a in 0..8 {
        for flag in 0..2 {
            assert_eq!(
                oracle::truth(&projected, &[("a", a), ("flag", flag)]),
                flag == 1 && (a < 4 || a == 7)
            );
        }
    }
}

#[test]
fn more_than_eight_typed_aliases_close_without_enumeration() {
    let a = var("a", 4);
    let locals: Vec<_> = (0..24).map(|i| var(&format!("v{i}"), 4)).collect();
    let mut atoms = vec![eq(expr(&a), expr(&locals[0]))];
    for pair in locals.windows(2) {
        atoms.push(eq(expr(&pair[0]), expr(&pair[1])));
    }
    atoms.push(eq(expr(locals.last().unwrap()), ChcExpr::BitVec(9, 4)));
    let projected = closed(&op(ChcOp::And, atoms), &[a]);
    for a in 0..16 {
        assert_eq!(oracle::truth(&projected, &[("a", a)]), a == 9);
    }
}

#[test]
fn raw_dividend_differing_divisors_and_partial_alternatives_decline() {
    let x = var("x", 4);
    let a = var("a", 4);
    let binding = eq(expr(&a), quotient(&x, 2));
    for extra in [
        op(ChcOp::BvULt, vec![expr(&x), ChcExpr::BitVec(9, 4)]),
        op(ChcOp::BvULt, vec![quotient(&x, 3), expr(&a)]),
    ] {
        declined(
            &op(ChcOp::And, vec![binding.clone(), extra]),
            std::slice::from_ref(&a),
        );
    }
    let unsupported = op(ChcOp::BvULt, vec![expr(&x), expr(&a)]);
    declined(
        &op(ChcOp::Or, vec![binding, unsupported.clone()]),
        std::slice::from_ref(&a),
    );
    declined(&op(ChcOp::Or, vec![ChcExpr::Bool(true), unsupported]), &[a]);
}

#[test]
fn cycles_zero_nonconstant_divisors_and_unbound_locals_decline() {
    let x = var("x", 4);
    let y = var("y", 4);
    let a = var("a", 4);
    for formula in [
        eq(expr(&x), op(ChcOp::BvNot, vec![expr(&x)])),
        op(
            ChcOp::And,
            vec![
                eq(expr(&x), expr(&y)),
                eq(
                    expr(&y),
                    op(ChcOp::BvAdd, vec![expr(&x), ChcExpr::BitVec(1, 4)]),
                ),
            ],
        ),
        eq(expr(&a), quotient(&x, 0)),
        eq(expr(&a), op(ChcOp::BvUDiv, vec![expr(&x), expr(&y)])),
        op(ChcOp::BvULt, vec![expr(&x), expr(&a)]),
    ] {
        declined(&formula, std::slice::from_ref(&a));
    }
}

#[test]
fn full_source_typing_precedes_dead_arm_simplification() {
    let a = var("a", 4);
    let x = var("x", 4);
    let malformed = [
        op(ChcOp::BvUDiv, vec![expr(&x)]),
        op(ChcOp::BvUDiv, vec![expr(&x), ChcExpr::BitVec(2, 3)]),
        op(
            ChcOp::BvUDiv,
            vec![ChcExpr::Bool(true), ChcExpr::BitVec(2, 4)],
        ),
        op(ChcOp::BvUDiv, vec![expr(&x), ChcExpr::BitVec(16, 4)]),
    ];
    for bad in malformed {
        let formula = op(ChcOp::And, vec![ChcExpr::Bool(false), eq(expr(&a), bad)]);
        declined(&formula, std::slice::from_ref(&a));
    }
    for boolean_op in [ChcOp::And, ChcOp::Or] {
        for args in [vec![], vec![ChcExpr::Bool(true)]] {
            // Internal joins use identities/singletons, but source arities
            // must still pass the ordinary strict operation validator.
            declined(
                &op(ChcOp::And, vec![ChcExpr::Bool(false), op(boolean_op, args)]),
                std::slice::from_ref(&a),
            );
        }
    }
    declined(&eq(expr(&a), expr(&var("a", 3))), std::slice::from_ref(&a));
    declined(&ChcExpr::Bool(true), &[a.clone(), a]);
    declined(
        &eq(expr(&var("wide", 129)), expr(&var("local", 129))),
        &[var("wide", 129)],
    );
}

#[test]
fn source_free_closed_false_is_not_confused_with_a_failed_branch() {
    let x = var("x", 4);
    let formula = op(
        ChcOp::And,
        vec![
            ChcExpr::Bool(false),
            op(ChcOp::BvULt, vec![expr(&x), ChcExpr::BitVec(7, 4)]),
        ],
    );
    assert!(!oracle::truth(&closed(&formula, &[]), &[]));
    assert!(oracle::truth(&closed(&ChcExpr::Bool(true), &[]), &[]));
    let y = var("y", 4);
    let cycle = op(
        ChcOp::And,
        vec![eq(expr(&x), expr(&y)), eq(expr(&y), expr(&x))],
    );
    assert!(oracle::truth(&closed(&cycle, &[]), &[]));
}
