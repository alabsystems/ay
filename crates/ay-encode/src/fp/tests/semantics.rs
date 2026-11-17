// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn nan_structural_identity_is_not_ieee_fp_equality_in_the_public_clause_entry() {
    let problem = ChcProblem::new();
    with_owner(|budget| {
        for (e, s) in [(8, 24), (11, 53)] {
            let nan = Expr::fp_nan(&crate::Sort::fp(e, s));
            for (root, expected) in [
                (nan.clone().eq(nan.clone()), true),
                (nan.clone().fp_eq(nan.clone()), false),
                (nan.clone().fp_eq(nan).not(), true),
            ] {
                let roots = [root];
                {
                    let output = relation(&roots, &[], &problem, budget);
                    let (body, _source) = output.into_parts().unwrap();
                    assert_eq!(units::consistent(&body, budget), expected);
                    drop(body);
                }
                budget.charge(0).unwrap();
            }
        }
    });
}

#[test]
fn signed_zero_structural_identity_and_ieee_equality_keep_their_distinction() {
    let problem = ChcProblem::new();
    with_owner(|budget| {
        for (e, s) in [(8, 24), (11, 53)] {
            let sort = crate::Sort::fp(e, s);
            let positive = Expr::fp_plus_zero(&sort);
            let negative = Expr::fp_minus_zero(&sort);
            for (root, expected) in [
                (positive.clone().eq(negative.clone()), false),
                (positive.fp_eq(negative), true),
            ] {
                let roots = [root];
                {
                    let output = relation(&roots, &[], &problem, budget);
                    let (body, _source) = output.into_parts().unwrap();
                    assert_eq!(units::consistent(&body, budget), expected);
                    drop(body);
                }
                budget.charge(0).unwrap();
            }
        }
    });
}

#[test]
fn all_five_literal_modes_use_the_real_public_whole_relation_entry() {
    let problem = ChcProblem::new();
    with_owner(|budget| {
        for (e, s) in [(8, 24), (11, 53)] {
            let sort = crate::Sort::fp(e, s);
            let zero = Expr::fp_plus_zero(&sort);
            for rm in [
                RoundingMode::RNE,
                RoundingMode::RNA,
                RoundingMode::RTP,
                RoundingMode::RTN,
                RoundingMode::RTZ,
            ] {
                let root = zero.clone().fp_add(rm, zero.clone()).fp_is_zero();
                let roots = [root];
                {
                    let output = relation(&roots, &[], &problem, budget);
                    assert!(output.body().constraint.is_some());
                    assert!(
                        matches!(output.source().roots()[0].value(),ExprValue::FpIsZero(value)
                        if matches!(value.value(),ExprValue::FpAdd(actual,_,_) if *actual==rm))
                    );
                    let (body, _source) = output.into_parts().unwrap();
                    drop(body);
                }
                budget.charge(0).unwrap();
            }
        }
    });
}

#[test]
fn constant_condition_still_preserves_both_typed_arms_in_the_stable_source() {
    let sort = crate::Sort::fp(8, 24);
    let selected = Expr::ite(
        Expr::true_(),
        Expr::fp_plus_zero(&sort),
        Expr::fp_minus_infinity(&sort),
    );
    let roots = [selected.fp_is_zero()];
    let problem = ChcProblem::new();
    with_owner(|budget| {
        {
            let output = relation(&roots, &[], &problem, budget);
            assert!(
                matches!(output.source().roots()[0].value(),ExprValue::FpIsZero(inner)
                if matches!(inner.value(),ExprValue::Ite { else_expr,.. }
                    if matches!(else_expr.value(),ExprValue::FpMinusInfinity { .. })))
            );
            let (body, _source) = output.into_parts().unwrap();
            assert!(units::consistent(&body, budget));
            drop(body);
        }
        budget.charge(0).unwrap();
    });
}
