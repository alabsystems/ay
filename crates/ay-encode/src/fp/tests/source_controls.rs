// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn omitted_duplicate_and_same_name_distinct_inputs_refuse_without_projection() {
    let (x, target) = input(32);
    let roots = [x.clone().fp_is_normal()];
    let problem = ChcProblem::new();
    with_owner(|budget| {
        assert!(matches!(
            lower_fp_expr_clause(&roots, &[], &problem, budget),
            Err(FpAdapterError::Invalid(_))
        ));
        let binding = FpExprInputBinding {
            source: &x,
            target: &target,
        };
        assert!(matches!(
            lower_fp_expr_clause(&roots, &[binding, binding], &problem, budget),
            Err(FpAdapterError::Invalid(_))
        ));
        let other = Expr::var("original_x", crate::Sort::fp(8, 24));
        let bindings = [
            binding,
            FpExprInputBinding {
                source: &other,
                target: &target,
            },
        ];
        assert!(matches!(
            lower_fp_expr_clause(&roots, &bindings, &problem, budget),
            Err(FpAdapterError::Invalid(_))
        ));
        let other_root = [other.fp_is_normal()];
        assert!(matches!(
            lower_fp_expr_clause(&other_root, &[binding], &problem, budget),
            Err(FpAdapterError::Invalid(_))
        ));
    });
}

#[test]
fn raw_input_name_width_and_compound_aliases_are_not_guessed() {
    let (x, target) = input(64);
    let roots = [x.clone().fp_is_normal()];
    let problem = ChcProblem::new();
    let wrong_name = ChcVar::new("other", ChcSort::BitVec(64));
    let wrong_width = ChcVar::new("original_x", ChcSort::BitVec(32));
    let compound = x.clone().fp_to_ieee_bv();
    with_owner(|budget| {
        for wrong in [&wrong_name, &wrong_width] {
            let bindings = [FpExprInputBinding {
                source: &x,
                target: wrong,
            }];
            assert!(matches!(
                lower_fp_expr_clause(&roots, &bindings, &problem, budget),
                Err(FpAdapterError::Invalid(_))
            ));
        }
        let bindings = [FpExprInputBinding {
            source: &compound,
            target: &target,
        }];
        assert!(matches!(
            lower_fp_expr_clause(&roots, &bindings, &problem, budget),
            Err(FpAdapterError::Invalid(_))
        ));
    });
}

#[test]
fn hidden_unsupported_unchosen_arms_and_numeric_raw_conversions_refuse() {
    let sort = crate::Sort::fp(8, 24);
    let zero = Expr::fp_plus_zero(&sort);
    let unsupported = zero.clone().fp_round_to_integral(RoundingMode::RNE);
    let selected = Expr::ite(Expr::true_(), zero.clone(), unsupported);
    let problem = ChcProblem::new();
    let numeric = Expr::bitvec_const(1u8, 32).bv_to_fp(RoundingMode::RNA, 8, 24);
    with_owner(|budget| {
        for root in [selected.fp_is_zero(), numeric.fp_is_normal()] {
            assert!(matches!(
                lower_fp_expr_clause(&[root], &[], &problem, budget),
                Err(FpAdapterError::Unsupported(_))
            ));
        }
    });
}

#[test]
fn uf_unsupported_formats_and_non_bool_roots_are_never_partial_data() {
    let problem = ChcProblem::new();
    let uf = Expr::func_app_with_sort("fp.isZero", vec![], crate::Sort::bool());
    let fp16 = Expr::fp_plus_zero(&crate::Sort::fp(5, 11)).fp_is_zero();
    let scalar = Expr::bitvec_const(1u8, 8);
    with_owner(|budget| {
        assert!(matches!(
            lower_fp_expr_clause(&[uf], &[], &problem, budget),
            Err(FpAdapterError::Unsupported(_))
        ));
        assert!(matches!(
            lower_fp_expr_clause(&[fp16], &[], &problem, budget),
            Err(FpAdapterError::Unsupported(_))
        ));
        assert!(matches!(
            lower_fp_expr_clause(&[scalar], &[], &problem, budget),
            Err(FpAdapterError::Invalid(_))
        ));
    });
}

#[test]
fn unused_declarations_and_pruned_queries_block_reserved_auxiliary_capture() {
    let (x, target) = input(32);
    let roots = [x.clone().fp_is_zero()];
    let bindings = [FpExprInputBinding {
        source: &x,
        target: &target,
    }];
    let mut declared = ChcProblem::new();
    declared.declare_predicate("__ay_fp_bits_unused", vec![]);
    let mut pruned = ChcProblem::new();
    let poison = ChcExpr::Var(ChcVar::new("__ay_fp_bits_old", ChcSort::Bool));
    pruned.add_clause(HornClause::query(ClauseBody::constraint(ChcExpr::Op(
        ChcOp::And,
        vec![
            std::sync::Arc::new(ChcExpr::Bool(false)),
            std::sync::Arc::new(poison),
        ],
    ))));
    assert_eq!(pruned.pruned_false_query_count(), 1);
    with_owner(|budget| {
        for namespace in [&declared, &pruned] {
            assert!(matches!(
                lower_fp_expr_clause(&roots, &bindings, namespace, budget),
                Err(FpAdapterError::Invalid(_))
            ));
        }
    });
}

#[test]
fn boolean_and_field_inputs_link_only_their_exact_original_scalar_words() {
    let c = Expr::var("c", crate::Sort::bool());
    let sign = Expr::var("sign", crate::Sort::bitvec(1));
    let exponent = Expr::var("exponent", crate::Sort::bitvec(8));
    let fraction = Expr::var("fraction", crate::Sort::bitvec(23));
    let fp = Expr::fp_from_bvs(sign.clone(), exponent.clone(), fraction.clone());
    let roots = [c.clone().implies(fp.fp_is_normal())];
    let targets = [
        ChcVar::new("c", ChcSort::Bool),
        ChcVar::new("sign", ChcSort::BitVec(1)),
        ChcVar::new("exponent", ChcSort::BitVec(8)),
        ChcVar::new("fraction", ChcSort::BitVec(23)),
    ];
    let bindings = [
        FpExprInputBinding {
            source: &c,
            target: &targets[0],
        },
        FpExprInputBinding {
            source: &sign,
            target: &targets[1],
        },
        FpExprInputBinding {
            source: &exponent,
            target: &targets[2],
        },
        FpExprInputBinding {
            source: &fraction,
            target: &targets[3],
        },
    ];
    let problem = ChcProblem::new();
    with_owner(|budget| {
        let output = relation(&roots, &bindings, &problem, budget);
        assert_eq!(output.source().bindings().len(), 4);
        assert!(output.body().constraint.is_some());
    });
}

#[test]
fn deep_shared_repeated_and_oversized_sources_obey_original_static_caps() {
    let problem = ChcProblem::new();
    let mut deep = Expr::true_();
    for _ in 0..64 {
        deep = deep.not();
    }
    let mut repeated = Expr::true_();
    for _ in 0..13 {
        repeated = repeated.clone().and(repeated);
    }
    let many = vec![Expr::true_(); 501];
    with_owner(|budget| {
        for root in [deep, repeated] {
            assert!(lower_fp_expr_clause(&[root], &[], &problem, budget).is_err());
        }
        assert!(matches!(
            lower_fp_expr_clause(&many, &[], &problem, budget),
            Err(FpAdapterError::Unsupported(_))
        ));
    });
}
