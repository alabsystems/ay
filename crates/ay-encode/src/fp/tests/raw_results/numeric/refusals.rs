// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
use super::*;

fn refusal(
    operation: FpRawOperation<'_>,
    output: &Expr,
    roots: &[Expr],
    bindings: &[FpExprInputBinding<'_>],
    budget: &mut WorkBudget<'_>,
) -> FpAdapterError {
    let results = [FpRawResultRelation { operation, output }];
    let namespace = ChcProblem::new();
    lower_fp_raw_result_clause(roots, &results, bindings, &namespace, budget)
        .err()
        .expect("must refuse before returning DATA")
}

#[test]
fn integer_widths_compounds_nested_extracts_and_non_word_outputs_refuse() {
    original_owner(|budget, _end| {
        budget.admit(FIXTURE, FIXTURE).unwrap();
        let (out, vo) = raw("bad_cast_out", 32);
        let bindings = [FpExprInputBinding {
            source: &out,
            target: &vo,
        }];
        let base = Expr::bitvec_const(0u8, 32);
        let nested = base.clone().extract(15, 0).extract(7, 0);
        let compound = base.clone().bvadd(base.clone());
        for input in [
            Expr::bitvec_const(0u8, 7),
            Expr::bitvec_const(0u8, 65),
            nested,
            compound,
        ] {
            for kind in [Kind::Signed, Kind::Unsigned] {
                assert!(matches!(
                    refusal(kind.operation(&input), &out, &[], &bindings, budget),
                    FpAdapterError::Unsupported(_)
                ));
            }
        }
        let value = Expr::bitvec_const(1u8, 8);
        let bad_output = Expr::bitvec_const(0u8, 32);
        assert!(matches!(
            refusal(
                Kind::Signed.operation(&value),
                &bad_output,
                &[],
                &bindings,
                budget
            ),
            FpAdapterError::Invalid(_)
        ));
        let (wrong, vw) = raw("bad_width", 16);
        let wrong_binding = [FpExprInputBinding {
            source: &wrong,
            target: &vw,
        }];
        assert!(matches!(
            refusal(
                Kind::Unsigned.operation(&value),
                &wrong,
                &[],
                &wrong_binding,
                budget
            ),
            FpAdapterError::Unsupported(_)
        ));
    });
}

#[test]
fn omitted_original_base_and_fresh_slice_binding_never_authorize_input_bits() {
    original_owner(|budget, _end| {
        budget.admit(FIXTURE, FIXTURE).unwrap();
        let (base, vb) = raw("original_integer_base", 64);
        let slice = base.clone().extract(7, 0);
        let (out, vo) = raw("original_integer_out", 32);
        let output_only = [FpExprInputBinding {
            source: &out,
            target: &vo,
        }];
        assert!(matches!(
            refusal(
                Kind::Signed.operation(&slice),
                &out,
                &[],
                &output_only,
                budget
            ),
            FpAdapterError::Invalid(_)
        ));
        let alias = ChcVar::new("slice_alias", ChcSort::BitVec(8));
        let projected = [
            FpExprInputBinding {
                source: &slice,
                target: &alias,
            },
            FpExprInputBinding {
                source: &out,
                target: &vo,
            },
        ];
        assert!(matches!(
            refusal(
                Kind::Unsigned.operation(&slice),
                &out,
                &[],
                &projected,
                budget
            ),
            FpAdapterError::Invalid(_)
        ));
        let replacement = Expr::var("original_integer_base", crate::Sort::bitvec(64));
        let swapped = [
            FpExprInputBinding {
                source: &replacement,
                target: &vb,
            },
            FpExprInputBinding {
                source: &out,
                target: &vo,
            },
        ];
        assert!(matches!(
            refusal(
                Kind::Unsigned.operation(&slice),
                &out,
                &[],
                &swapped,
                budget
            ),
            FpAdapterError::Invalid(_)
        ));
    });
}

#[test]
fn duplicate_self_and_forward_extract_descriptors_compare_original_base_identity() {
    original_owner(|budget, _end| {
        budget.admit(FIXTURE, FIXTURE).unwrap();
        let input = Expr::bitvec_const(1u8, 8);
        let (a, va) = raw("integer_ssa_a", 32);
        let (b, vb) = raw("integer_ssa_b", 32);
        let self_slice = a.clone().extract(7, 0);
        let forward_slice = b.clone().extract(7, 0);
        let good = FpRawResultRelation {
            operation: Kind::Unsigned.operation(&input),
            output: &a,
        };
        let duplicate = [good, good];
        let self_ref = [FpRawResultRelation {
            operation: Kind::Signed.operation(&self_slice),
            output: &a,
        }];
        let forward = [
            FpRawResultRelation {
                operation: Kind::Signed.operation(&forward_slice),
                output: &a,
            },
            FpRawResultRelation {
                operation: Kind::Unsigned.operation(&input),
                output: &b,
            },
        ];
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
        let namespace = ChcProblem::new();
        for results in [&duplicate[..], &self_ref[..], &forward[..]] {
            assert!(matches!(
                lower_fp_raw_result_clause(&[], results, &bindings, &namespace, budget),
                Err(FpAdapterError::Invalid(_))
            ));
        }
    });
}

#[test]
fn unchosen_hidden_source_and_computed_ieee_extension_still_refuse() {
    original_owner(|budget, _end| {
        budget.admit(FIXTURE, FIXTURE).unwrap();
        let input = Expr::bitvec_const(1u8, 8);
        let (out, vo) = raw("hidden_cast_out", 32);
        let bindings = [FpExprInputBinding {
            source: &out,
            target: &vo,
        }];
        let bad = Expr::func_app_with_sort("to_fp", vec![], crate::Sort::bool());
        let ieee = Expr::fp_plus_zero(&crate::Sort::fp(8, 24)).fp_to_ieee_bv();
        let extension = ieee.clone().eq(ieee);
        for root in [
            Expr::ite(Expr::true_(), Expr::true_(), bad),
            Expr::ite(Expr::false_(), extension, Expr::true_()),
        ] {
            assert!(matches!(
                refusal(
                    Kind::Unsigned.operation(&input),
                    &out,
                    &[root],
                    &bindings,
                    budget
                ),
                FpAdapterError::Unsupported(_)
            ));
        }
    });
}

#[test]
fn malformed_binding_sorts_and_named_integer_shapes_never_reach_native_encoding() {
    original_owner(|budget, _end| {
        budget.admit(FIXTURE, FIXTURE).unwrap();
        let (out, vo) = raw("malformed_cast_out", 32);
        let (input, _) = raw("malformed_integer_in", 8);
        let wrong = ChcVar::new("malformed_integer_in", ChcSort::BitVec(16));
        let bindings = [
            FpExprInputBinding {
                source: &input,
                target: &wrong,
            },
            FpExprInputBinding {
                source: &out,
                target: &vo,
            },
        ];
        assert!(matches!(
            refusal(Kind::Signed.operation(&input), &out, &[], &bindings, budget),
            FpAdapterError::Invalid(_)
        ));
        let named = Expr::func_app_with_sort("integer_source", vec![], crate::Sort::bitvec(8));
        assert!(matches!(
            refusal(
                Kind::Unsigned.operation(&named),
                &out,
                &[],
                &bindings[1..],
                budget
            ),
            FpAdapterError::Unsupported(_)
        ));
        let constant = Expr::bitvec_const(1u8, 8);
        let malformed_root = [Expr::bitvec_const(1u8, 8)];
        assert!(matches!(
            refusal(
                Kind::Signed.operation(&constant),
                &out,
                &malformed_root,
                &bindings[1..],
                budget
            ),
            FpAdapterError::Invalid(_)
        ));
    });
}
