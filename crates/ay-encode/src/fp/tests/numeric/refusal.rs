// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

fn refuses(root: Expr, budget: &mut WorkBudget<'_>) {
    let problem = ChcProblem::new();
    assert!(matches!(
        lower_fp_expr_clause(&[root], &[], &problem, budget),
        Err(FpAdapterError::Unsupported(_)) | Err(FpAdapterError::Invalid(_))
    ));
}

#[test]
fn non_rne_numeric_modes_widths_and_formats_refuse_before_any_partial_data() {
    super::super::raw_words::native::original_owner(|budget, _| {
        budget.admit(1_048_576, 1_048_576).unwrap();
        for rm in [
            RoundingMode::RNA,
            RoundingMode::RTP,
            RoundingMode::RTN,
            RoundingMode::RTZ,
        ] {
            let word = Expr::bitvec_const(1u8, 8);
            refuses(word.clone().bv_to_fp(rm, 8, 24).fp_is_normal(), budget);
            refuses(word.bv_to_fp_unsigned(rm, 11, 53).fp_is_normal(), budget);
        }
        for n in [1, 7, 65] {
            refuses(
                Expr::bitvec_const(1u8, n)
                    .bv_to_fp(RoundingMode::RNE, 8, 24)
                    .fp_is_normal(),
                budget,
            );
        }
        refuses(
            Expr::bitvec_const(1u8, 8)
                .bv_to_fp(RoundingMode::RNE, 5, 11)
                .fp_is_normal(),
            budget,
        );
    });
}

#[test]
fn numeric_compound_words_forged_ufs_and_unsupported_unchosen_children_refuse() {
    super::super::raw_words::native::original_owner(|budget, _| {
        budget.admit(1_048_576, 1_048_576).unwrap();
        let word = Expr::bitvec_const(1u8, 32);
        let compound = word.clone().bvadd(word.clone());
        let nested = word.clone().extract(15, 0).extract(7, 0);
        let forged = Expr::func_app_with_sort("to_fp", vec![word.clone()], crate::Sort::fp(8, 24));
        let good = cast(word.clone(), Kind::Signed, 32);
        let bad_mode = word.bv_to_fp(RoundingMode::RNA, 8, 24);
        for bad in [
            cast(compound, Kind::Signed, 32),
            cast(nested, Kind::Signed, 32),
            forged,
            bad_mode,
        ] {
            for condition in [Expr::true_(), Expr::false_()] {
                refuses(
                    Expr::ite(condition, good.clone(), bad.clone()).fp_is_normal(),
                    budget,
                );
            }
        }
    });
}

#[test]
fn numeric_original_raw_base_cannot_be_omitted_or_replaced_by_slice_alias() {
    super::super::raw_words::native::original_owner(|budget, _| {
        budget.admit(1_048_576, 1_048_576).unwrap();
        let base = Expr::var("numeric_original", crate::Sort::bitvec(64));
        let slice = base.clone().extract(7, 0);
        let roots = [cast(slice.clone(), Kind::Signed, 32).fp_is_normal()];
        let problem = ChcProblem::new();
        assert!(matches!(
            lower_fp_expr_clause(&roots, &[], &problem, budget),
            Err(FpAdapterError::Invalid(_))
        ));
        let target = ChcVar::new("numeric_original", ChcSort::BitVec(8));
        let binding = [FpExprInputBinding {
            source: &slice,
            target: &target,
        }];
        assert!(matches!(
            lower_fp_expr_clause(&roots, &binding, &problem, budget),
            Err(FpAdapterError::Invalid(_))
        ));
    });
}
