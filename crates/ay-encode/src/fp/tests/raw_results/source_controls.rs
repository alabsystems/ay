// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
use super::*;

#[test]
fn source_keeps_all_ordered_roots_raw_operands_policy_and_output_links() {
    original_owner(|budget, _end| {
        budget.admit(FIXTURE, FIXTURE).unwrap();
        let (a, va) = raw("operand_a", 64);
        let (b, vb) = raw("operand_b", 64);
        let (c, vc) = raw("operand_c", 64);
        let (out, vo) = raw("ssa_output", 64);
        let inputs = [&a, &b, &c];
        let results = [FpRawResultRelation {
            operation: FpRawOperation::Arithmetic {
                operation: RustFpArithmetic::FusedMultiplyAdd,
                inputs: &inputs,
                nan_policy: RustNanPolicy::WasmConditional,
            },
            output: &out,
        }];
        let bindings = [
            FpExprInputBinding {
                source: &a,
                target: &va,
            },
            FpExprInputBinding {
                source: &b,
                target: &vb,
            },
            FpExprInputBinding {
                source: &c,
                target: &vc,
            },
            FpExprInputBinding {
                source: &out,
                target: &vo,
            },
        ];
        let first = a.clone().eq(a.clone());
        let roots = [first.clone(), Expr::true_(), first];
        let mut namespace = ChcProblem::new();
        let p = namespace.declare_predicate("all_raw_state", vec![ChcSort::BitVec(64); 4]);
        let old = ClauseBody::new(
            vec![(
                p,
                vec![
                    ChcExpr::Var(va.clone()),
                    ChcExpr::Var(vb.clone()),
                    ChcExpr::Var(vc.clone()),
                    ChcExpr::Var(vo.clone()),
                ],
            )],
            None,
        );
        {
            let (body, source) =
                lower_fp_raw_result_clause(&roots, &results, &bindings, &namespace, budget)
                    .unwrap()
                    .into_body(old)
                    .unwrap()
                    .into_parts()
                    .unwrap();
            assert!(std::ptr::eq(source.roots(), roots.as_slice()));
            assert!(std::ptr::eq(source.raw_results(), results.as_slice()));
            assert!(std::ptr::eq(source.namespace(), &raw const namespace));
            let FpRawOperation::Arithmetic {
                operation,
                inputs: retained,
                nan_policy,
            } = source.raw_results()[0].operation
            else {
                panic!()
            };
            assert_eq!(operation, RustFpArithmetic::FusedMultiplyAdd);
            assert_eq!(nan_policy, RustNanPolicy::WasmConditional);
            for (retained, original) in retained.iter().zip(inputs) {
                assert!(std::ptr::eq(*retained, original));
            }
            assert_eq!(
                body.predicates[0].1,
                [
                    ChcExpr::Var(va.clone()),
                    ChcExpr::Var(vb.clone()),
                    ChcExpr::Var(vc.clone()),
                    ChcExpr::Var(vo.clone())
                ]
            );
            let clause = HornClause::new(
                body,
                ClauseHead::Predicate(
                    p,
                    vec![
                        ChcExpr::Var(va.clone()),
                        ChcExpr::Var(vb.clone()),
                        ChcExpr::Var(vc.clone()),
                        ChcExpr::Var(vo.clone()),
                    ],
                ),
            );
            assert!(clause.body.constraint.is_some());
            drop(clause);
        }
        budget.charge(0).unwrap();
    });
}

#[test]
fn duplicate_self_and_forward_ssa_descriptors_refuse_before_publication() {
    original_owner(|budget, _end| {
        budget.admit(FIXTURE, FIXTURE).unwrap();
        let zero = Expr::bitvec_const(0u8, 32);
        let (a, va) = raw("ssa_a", 32);
        let (b, vb) = raw("ssa_b", 32);
        let bindings = [
            FpExprInputBinding {
                source: &a,
                target: &va,
            },
            FpExprInputBinding {
                source: &b,
                target: &vb,
            },
        ];
        let good = FpRawResultRelation {
            operation: FpRawOperation::Copy(&zero),
            output: &a,
        };
        let duplicate = [good, good];
        let self_reference = [FpRawResultRelation {
            operation: FpRawOperation::Copy(&a),
            output: &a,
        }];
        let forward = [
            FpRawResultRelation {
                operation: FpRawOperation::Copy(&b),
                output: &a,
            },
            FpRawResultRelation {
                operation: FpRawOperation::Copy(&zero),
                output: &b,
            },
        ];
        let namespace = ChcProblem::new();
        for results in [&duplicate[..], &self_reference[..], &forward[..]] {
            assert!(matches!(
                lower_fp_raw_result_clause(&[], results, &bindings, &namespace, budget),
                Err(FpAdapterError::Invalid(_))
            ));
        }
    });
}

#[test]
fn missing_nonvar_width_arity_compound_and_omitted_operands_refuse() {
    original_owner(|budget, _end| {
        budget.admit(FIXTURE, FIXTURE).unwrap();
        let (input, vi) = raw("raw_input", 32);
        let (output, vo) = raw("raw_output", 32);
        let wrong_width = Expr::bitvec_const(0u8, 64);
        let constant = Expr::bitvec_const(0u8, 32);
        let compound = input.clone().bvadd(constant.clone());
        let inputs = [&input];
        let short_arity = FpRawOperation::Arithmetic {
            operation: RustFpArithmetic::Add,
            inputs: &inputs,
            nan_policy: RustNanPolicy::NoExtra,
        };
        let namespace = ChcProblem::new();
        let bindings = [
            FpExprInputBinding {
                source: &input,
                target: &vi,
            },
            FpExprInputBinding {
                source: &output,
                target: &vo,
            },
        ];
        for (operation, result_word) in [
            (FpRawOperation::Copy(&input), &constant),
            (FpRawOperation::Copy(&wrong_width), &output),
            (short_arity, &output),
            (FpRawOperation::Copy(&compound), &output),
        ] {
            let results = [FpRawResultRelation {
                operation,
                output: result_word,
            }];
            assert!(
                lower_fp_raw_result_clause(&[], &results, &bindings, &namespace, budget).is_err()
            );
        }
        let results = [FpRawResultRelation {
            operation: FpRawOperation::Copy(&input),
            output: &output,
        }];
        assert!(matches!(
            lower_fp_raw_result_clause(&[], &results, &bindings[..1], &namespace, budget),
            Err(FpAdapterError::Invalid(_))
        ));
        assert!(matches!(
            lower_fp_raw_result_clause(&[], &results, &bindings[1..], &namespace, budget),
            Err(FpAdapterError::Invalid(_))
        ));
    });
}

#[test]
fn all_authored_unchosen_roots_and_unused_bindings_are_still_checked() {
    original_owner(|budget, _end| {
        budget.admit(FIXTURE, FIXTURE).unwrap();
        let constant = Expr::bitvec_const(0u8, 32);
        let (output, target) = raw("out", 32);
        let results = [FpRawResultRelation {
            operation: FpRawOperation::Copy(&constant),
            output: &output,
        }];
        let namespace = ChcProblem::new();
        let binding = FpExprInputBinding {
            source: &output,
            target: &target,
        };
        let unsupported =
            Expr::func_app_with_sort("not_an_fp_primitive", vec![], crate::Sort::bool());
        let roots = [Expr::ite(Expr::true_(), Expr::true_(), unsupported)];
        assert!(matches!(
            lower_fp_raw_result_clause(&roots, &results, &[binding], &namespace, budget),
            Err(FpAdapterError::Unsupported(_))
        ));
        let omitted = Expr::var("omitted_bool", crate::Sort::bool());
        assert!(matches!(
            lower_fp_raw_result_clause(&[omitted], &results, &[binding], &namespace, budget),
            Err(FpAdapterError::Invalid(_))
        ));
        let invalid = Expr::bitvec_const(0u8, 32);
        let unused = FpExprInputBinding {
            source: &invalid,
            target: &target,
        };
        assert!(matches!(
            lower_fp_raw_result_clause(&[], &results, &[binding, unused], &namespace, budget),
            Err(FpAdapterError::Invalid(_))
        ));
    });
}

#[test]
fn old_extension_refusals_and_ieee_rem_are_not_silently_reinterpreted() {
    original_owner(|budget, _end| {
        budget.admit(FIXTURE, FIXTURE).unwrap();
        let sort = crate::Sort::fp(8, 24);
        let zero = Expr::fp_plus_zero(&sort);
        let extension = zero.clone().fp_to_ieee_bv().eq(Expr::bitvec_const(0u8, 32));
        let namespace = ChcProblem::new();
        assert!(matches!(
            lower_fp_expr_clause(&[extension], &[], &namespace, budget),
            Err(FpAdapterError::Unsupported(_))
        ));
        // Raw-operation arithmetic has no IEEE remainder case or generic computed Expr field.
        assert_ne!(
            RustFpArithmetic::TruncatingRemainder,
            RustFpArithmetic::Divide
        );
        let roots = [zero.clone().fp_rem(zero).fp_is_nan()];
        {
            let (body, source) = lower_fp_expr_clause(&roots, &[], &namespace, budget)
                .unwrap()
                .into_body(ClauseBody::empty())
                .unwrap()
                .into_parts()
                .unwrap();
            assert!(source.raw_results().is_empty());
            drop(body);
        }
        budget.charge(0).unwrap();
    });
}
