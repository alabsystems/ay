// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Real public whole-clause DATA checks; no compiler/proof or CHC verdict credit.
use super::*;

pub(super) mod native;
mod ownership;

fn word(value: u64, width: u32) -> Expr {
    let raw = Expr::bitvec_const(value, width);
    fields(raw, width)
}

fn fields(word: Expr, width: u32) -> Expr {
    let fraction = if width == 32 { 23 } else { 52 };
    Expr::fp_from_bvs(
        word.clone().extract(width - 1, width - 1),
        word.clone().extract(width - 2, fraction),
        word.extract(fraction - 1, 0),
    )
}

fn root(width: u32) -> Expr {
    let (three, two, one) = if width == 32 {
        (0x40400000, 0x40000000, 0x3f800000)
    } else {
        (0x4008000000000000, 0x4000000000000000, 0x3ff0000000000000)
    };
    word(three, width)
        .fp_truncating_rem(word(two, width))
        .eq(word(one, width))
}

fn attempt(budget: &mut WorkBudget<'_>) -> Result<(), FpAdapterError> {
    let roots = [root(32)];
    let problem = ChcProblem::new();
    let output = lower_fp_expr_clause(&roots, &[], &problem, budget)?;
    let (body, source) = output.into_body(ClauseBody::empty())?.into_parts()?;
    drop(body);
    drop(source);
    budget.charge(0)?;
    Ok(())
}

#[test]
fn only_distinct_typed_truncating_variant_can_mint_the_private_intrinsic() {
    let sort = crate::Sort::fp(8, 24);
    let a = Expr::fp_plus_zero(&sort);
    let b = Expr::fp_plus_infinity(&sort);
    let genuine = a.clone().fp_truncating_rem(b.clone());
    let shape = typed::describe(&genuine).unwrap();
    assert!(matches!(
        shape.op,
        typed::Operator::Apply("__ay_fp_truncating_rem", None)
    ));
    let children = shape.children.collect::<Vec<_>>();
    assert_eq!(children.len(), 2);
    assert!(std::ptr::eq(children[0].value(), a.value()));
    assert!(std::ptr::eq(children[1].value(), b.value()));
    let forged = Expr::func_app_with_sort("__ay_fp_truncating_rem", vec![a, b], sort);
    let problem = ChcProblem::new();
    with_owner(|budget| {
        assert!(matches!(
            lower_fp_expr_clause(&[forged.fp_is_zero()], &[], &problem, budget),
            Err(FpAdapterError::Unsupported(_))
        ));
    });
}

#[test]
fn unchosen_unsupported_operands_and_non_binary_formats_still_refuse() {
    let sort = crate::Sort::fp(8, 24);
    let zero = Expr::fp_plus_zero(&sort);
    let unsupported = zero.clone().fp_round_to_integral(RoundingMode::RNE);
    let nested = Expr::ite(Expr::true_(), zero.clone(), unsupported);
    let fp16 = Expr::fp_plus_zero(&crate::Sort::fp(5, 11));
    let problem = ChcProblem::new();
    with_owner(|budget| {
        for value in [
            zero.clone().fp_truncating_rem(nested),
            fp16.clone().fp_truncating_rem(fp16),
        ] {
            assert!(matches!(
                lower_fp_expr_clause(&[value.fp_is_zero()], &[], &problem, budget),
                Err(FpAdapterError::Unsupported(_))
            ));
        }
    });
}

#[test]
fn raw_word_inputs_and_every_repeated_root_keep_their_complete_source_links() {
    with_owner(|budget| {
        let x = Expr::var("raw_x", crate::Sort::bitvec(32));
        let a = ChcVar::new("raw_x", ChcSort::BitVec(32));
        let y = Expr::var("raw_y", crate::Sort::bitvec(32));
        let b = ChcVar::new("raw_y", ChcSort::BitVec(32));
        let value = fields(x.clone(), 32).fp_truncating_rem(fields(y.clone(), 32));
        let first = value.clone().fp_is_zero();
        let roots = [first.clone(), value.fp_is_nan(), first];
        let bindings = [
            FpExprInputBinding {
                source: &x,
                target: &a,
            },
            FpExprInputBinding {
                source: &y,
                target: &b,
            },
        ];
        let mut problem = ChcProblem::new();
        let p = problem.declare_predicate("p", vec![ChcSort::BitVec(32), ChcSort::BitVec(32)]);
        let old = ClauseBody::new(
            vec![(p, vec![ChcExpr::Var(a.clone()), ChcExpr::Var(b.clone())])],
            None,
        );
        assert!(matches!(
            lower_fp_expr_clause(&roots, &bindings[..1], &problem, budget),
            Err(FpAdapterError::Invalid(_))
        ));
        let output = lower_fp_expr_clause(&roots, &bindings, &problem, budget).unwrap();
        let (body, source) = output.into_body(old).unwrap().into_parts().unwrap();
        assert!(std::ptr::eq(source.roots(), roots.as_slice()));
        assert_eq!(source.bindings().len(), 2);
        assert_eq!(
            body.predicates[0].1,
            [ChcExpr::Var(a.clone()), ChcExpr::Var(b.clone())]
        );
        assert!(body.constraint.is_some());
        drop(body);
        drop(source);
        budget.charge(0).unwrap();
    });
}

#[test]
fn ieee_remainder_remains_a_distinct_standard_operator_in_the_same_whole_batch() {
    let problem = ChcProblem::new();
    with_owner(|budget| {
        for width in [32, 64] {
            let (three, two, minus_one) = if width == 32 {
                (0x40400000, 0x40000000, 0xbf800000)
            } else {
                (0x4008000000000000, 0x4000000000000000, 0xbff0000000000000)
            };
            let ieee = word(three, width)
                .fp_rem(word(two, width))
                .eq(word(minus_one, width));
            let roots = [root(width), ieee];
            let output = relation(&roots, &[], &problem, budget);
            let (body, source) = output.into_parts().unwrap();
            assert!(units::consistent(&body, budget));
            drop(body);
            drop(source);
            budget.charge(0).unwrap();
        }
    });
}
