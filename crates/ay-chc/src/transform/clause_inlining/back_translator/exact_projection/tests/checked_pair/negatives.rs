// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

fn assert_closed_matches_existential_operands(formula: &ChcExpr, keep: &[ChcVar]) {
    let projected = closed(formula, keep);
    for result in 0..16 {
        for flag in 0..2 {
            let exists = (0..16).any(|x| {
                (0..16).any(|y| {
                    oracle::truth(
                        formula,
                        &[("x", x), ("y", y), ("result", result), ("flag", flag)],
                    )
                })
            });
            assert_eq!(
                oracle::truth(&projected, &[("result", result), ("flag", flag)]),
                exists,
                "result={result}, flag={flag}"
            );
        }
    }
}

fn assert_closed_with_retained_left_operand(formula: &ChcExpr, keep: &[ChcVar]) {
    let projected = closed(formula, keep);
    for result in 0..16 {
        for flag in 0..2 {
            for x in 0..16 {
                let exists = (0..16).any(|y| {
                    oracle::truth(
                        formula,
                        &[("x", x), ("y", y), ("result", result), ("flag", flag)],
                    )
                });
                assert_eq!(
                    oracle::truth(&projected, &[("x", x), ("result", result), ("flag", flag)]),
                    exists,
                    "result={result}, flag={flag}, x={x}"
                );
            }
        }
    }
}

#[test]
fn raw_operands_side_constraints_and_nonindependent_variables_decline() {
    for arithmetic in [Arithmetic::Difference, Arithmetic::Product] {
        let (binding, keep) = fixture(arithmetic, 4, Polarity::Direct, Orientation::Forward);
        let x = var("x", 4);
        let y = var("y", 4);
        for extra in [
            op(ChcOp::BvULt, vec![expr(&x), ChcExpr::BitVec(3, 4)]),
            op(ChcOp::BvULt, vec![expr(&y), ChcExpr::BitVec(3, 4)]),
            eq(expr(&x), expr(&y)),
            eq(expr(&keep[0]), low(arithmetic, &y, &x)),
        ] {
            declined(&op(ChcOp::And, vec![binding.clone(), extra]), &keep);
        }
        let fixed_left = op(
            ChcOp::And,
            vec![binding.clone(), eq(expr(&x), ChcExpr::BitVec(0, 4))],
        );
        match arithmetic {
            Arithmetic::Difference => {
                assert_closed_matches_existential_operands(&fixed_left, &keep)
            }
            Arithmetic::Product => declined(&fixed_left, &keep),
        }
        let aliased = op(
            ChcOp::And,
            vec![
                eq(expr(&keep[0]), low(arithmetic, &x, &x)),
                eq(expr(&keep[1]), observation(arithmetic, &x, &x, 4)),
            ],
        );
        declined(&aliased, &keep);
        let mut one_kept = keep;
        one_kept.push(x);
        match arithmetic {
            Arithmetic::Difference => assert_closed_with_retained_left_operand(&binding, &one_kept),
            Arithmetic::Product => declined(&binding, &one_kept),
        }
    }
}

#[test]
fn signed_nonstrict_reversed_and_mismatched_borrow_observations_decline() {
    let x = var("x", 4);
    let y = var("y", 4);
    let z = var("z", 4);
    let (_, keep) = fixture(
        Arithmetic::Difference,
        4,
        Polarity::Direct,
        Orientation::Forward,
    );
    for wrong in [
        op(ChcOp::BvSLt, vec![expr(&x), expr(&y)]),
        op(ChcOp::BvULe, vec![expr(&x), expr(&y)]),
        op(ChcOp::BvULt, vec![expr(&y), expr(&x)]),
        op(ChcOp::BvULt, vec![expr(&x), expr(&z)]),
        op(ChcOp::BvULt, vec![expr(&z), expr(&y)]),
    ] {
        declined(
            &op(
                ChcOp::And,
                vec![
                    eq(expr(&keep[0]), low(Arithmetic::Difference, &x, &y)),
                    eq(expr(&keep[1]), wrong),
                ],
            ),
            &keep,
        );
    }
}

#[test]
fn mismatched_high_slices_extensions_zero_tests_and_operands_decline() {
    let x = var("x", 4);
    let y = var("y", 4);
    let z = var("z", 4);
    let (_, keep) = fixture(
        Arithmetic::Product,
        4,
        Polarity::Direct,
        Orientation::Forward,
    );
    let signed_product = op(
        ChcOp::BvMul,
        vec![
            op(ChcOp::BvSignExtend(4), vec![expr(&x)]),
            op(ChcOp::BvSignExtend(4), vec![expr(&y)]),
        ],
    );
    let wider_product = wide(&x, &y, 5);
    for wrong in [
        eq(high(&x, &y, 4), ChcExpr::BitVec(1, 4)),
        eq(
            op(ChcOp::BvExtract(6, 3), vec![wide(&x, &y, 4)]),
            ChcExpr::BitVec(0, 4),
        ),
        eq(
            op(ChcOp::BvExtract(7, 5), vec![wide(&x, &y, 4)]),
            ChcExpr::BitVec(0, 3),
        ),
        eq(
            op(ChcOp::BvExtract(7, 4), vec![signed_product]),
            ChcExpr::BitVec(0, 4),
        ),
        eq(
            op(ChcOp::BvExtract(8, 5), vec![wider_product]),
            ChcExpr::BitVec(0, 4),
        ),
        eq(high(&y, &x, 4), ChcExpr::BitVec(0, 4)),
        eq(high(&x, &z, 4), ChcExpr::BitVec(0, 4)),
        op(ChcOp::Ne, vec![high(&x, &y, 4), ChcExpr::BitVec(0, 4)]),
        op(ChcOp::BvULt, vec![high(&x, &y, 4), ChcExpr::BitVec(1, 4)]),
    ] {
        declined(
            &op(
                ChcOp::And,
                vec![
                    eq(expr(&keep[0]), low(Arithmetic::Product, &x, &y)),
                    eq(expr(&keep[1]), wrong),
                ],
            ),
            &keep,
        );
    }
}

#[test]
fn independently_observed_high_or_full_product_is_not_erased() {
    let (binding, keep) = fixture(
        Arithmetic::Product,
        4,
        Polarity::Complement,
        Orientation::Forward,
    );
    let x = var("x", 4);
    let y = var("y", 4);
    for (term, width) in [(high(&x, &y, 4), 4), (wide(&x, &y, 4), 8)] {
        let extra = var("additional", width);
        let mut retained = keep.clone();
        retained.push(extra.clone());
        declined(
            &op(ChcOp::And, vec![binding.clone(), eq(expr(&extra), term)]),
            &retained,
        );
    }
}

#[test]
fn missing_bindings_and_an_unsupported_disjunct_cannot_publish_partial_images() {
    for arithmetic in [Arithmetic::Difference, Arithmetic::Product] {
        let (binding, keep) = fixture(arithmetic, 4, Polarity::Direct, Orientation::Forward);
        let x = var("x", 4);
        let y = var("y", 4);
        let result_only = eq(expr(&keep[0]), low(arithmetic, &x, &y));
        let flag_only = eq(expr(&keep[1]), observation(arithmetic, &x, &y, 4));
        match arithmetic {
            Arithmetic::Difference => {
                assert_closed_matches_existential_operands(&result_only, &keep)
            }
            Arithmetic::Product => declined(&result_only, &keep),
        }
        declined(&flag_only, &keep);
        let alternative = op(ChcOp::Or, vec![binding, result_only]);
        match arithmetic {
            Arithmetic::Difference => {
                assert_closed_matches_existential_operands(&alternative, &keep)
            }
            Arithmetic::Product => declined(&alternative, &keep),
        }
    }
}

#[test]
fn malformed_types_and_arity_are_rejected_even_in_a_dead_alternative() {
    for arithmetic in [Arithmetic::Difference, Arithmetic::Product] {
        let (binding, keep) = fixture(arithmetic, 4, Polarity::Direct, Orientation::Forward);
        let x = var("x", 4);
        for malformed in [
            low(arithmetic, &x, &var("bad_width", 3)),
            low(arithmetic, &x, &ChcVar::new("bad_sort", ChcSort::Bool)),
            op(ChcOp::BvMul, vec![expr(&x)]),
            op(ChcOp::BvExtract(8, 4), vec![wide(&x, &var("y", 4), 4)]),
            op(ChcOp::BvZeroExtend(4), vec![]),
        ] {
            let dead = op(
                ChcOp::And,
                vec![ChcExpr::Bool(false), eq(expr(&keep[0]), malformed)],
            );
            declined(&op(ChcOp::Or, vec![binding.clone(), dead]), &keep);
        }
        declined(
            &op(
                ChcOp::And,
                vec![binding, eq(expr(&keep[1]), ChcExpr::BitVec(0, 4))],
            ),
            &keep,
        );
    }
}
