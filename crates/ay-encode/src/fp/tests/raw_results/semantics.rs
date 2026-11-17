// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
use super::*;

#[test]
fn non_nan_words_are_unique_including_signed_zero_infinity_and_truncating_rem() {
    original_owner(|budget, end| {
        for width in [32, 64] {
            let (sign, infinity, _, one) = layout(width);
            let (two, three, residual) = if width == 32 {
                (0x40000000, 0x40400000, 0xa8800000)
            } else {
                (0x4000000000000000, 0x4008000000000000, 0xb970000000000000)
            };
            use RustFpArithmetic::*;
            budget.admit(FIXTURE, FIXTURE).unwrap();
            let rows = [
                (Add, vec![one, two], three),
                (Subtract, vec![three, two], one),
                (Multiply, vec![sign, one], sign),
                (Divide, vec![one, 0], infinity),
                (TruncatingRemainder, vec![three, two], one),
                (SquareRoot, vec![sign], sign),
                (Add, vec![sign, sign], sign),
                (Add, vec![sign, 0], 0),
            ];
            for (operation, inputs, correct) in rows {
                result_bits(
                    width,
                    operation,
                    &inputs,
                    RustNanPolicy::NoExtra,
                    correct,
                    true,
                    budget,
                    end,
                );
                arithmetic(
                    width,
                    operation,
                    &inputs,
                    RustNanPolicy::NoExtra,
                    |target| negate(pin(target, correct, width)),
                    false,
                    budget,
                    end,
                );
            }
            let inputs = if width == 32 {
                [0x3f800001, 0x3f7ffffe, 0xbf800000]
            } else {
                [0x3ff0000000000001, 0x3feffffffffffffe, 0xbff0000000000000]
            };
            // (1+2^-p)*(1-2^-p)-1 = -2^(-2p), not separately rounded zero.
            result_bits(
                width,
                FusedMultiplyAdd,
                &inputs,
                RustNanPolicy::NoExtra,
                residual,
                true,
                budget,
                end,
            );
            arithmetic(
                width,
                FusedMultiplyAdd,
                &inputs,
                RustNanPolicy::NoExtra,
                |target| negate(pin(target, residual, width)),
                false,
                budget,
                end,
            );
        }
    });
}

#[test]
fn copy_negate_and_abs_preserve_signaling_quietness_and_payload_exactly() {
    original_owner(|budget, end| {
        for width in [32, 64] {
            let (sign, infinity, quiet, _) = layout(width);
            let source_word = infinity | 0x123;
            for operation in 0..3 {
                for wrong in [false, true] {
                    budget.admit(FIXTURE, FIXTURE).unwrap();
                    let source = Expr::bitvec_const(source_word | sign, width);
                    let (output, target) = raw("bitwise_out", width);
                    let raw_op = match operation {
                        0 => FpRawOperation::Copy(&source),
                        1 => FpRawOperation::Negate(&source),
                        _ => FpRawOperation::AbsoluteValue(&source),
                    };
                    let results = [FpRawResultRelation {
                        operation: raw_op,
                        output: &output,
                    }];
                    let bindings = [FpExprInputBinding {
                        source: &output,
                        target: &target,
                    }];
                    let problem = ChcProblem::new();
                    let expected = if operation == 0 {
                        source_word | sign
                    } else {
                        source_word
                    };
                    let condition = if wrong {
                        negate(pin(&target, expected, width))
                    } else {
                        pin(&target, expected, width)
                    };
                    let body = {
                        let (body, _source) =
                            lower_fp_raw_result_clause(&[], &results, &bindings, &problem, budget)
                                .unwrap()
                                .into_body(ClauseBody::constraint(condition))
                                .unwrap()
                                .into_parts()
                                .unwrap();
                        body
                    };
                    native(body, !wrong, budget, end);
                }
            }
            // Quieting is not an allowed shortcut for the bitwise copy path.
            budget.admit(FIXTURE, FIXTURE).unwrap();
            assert_ne!(source_word, source_word | quiet);
        }
    });
}

#[test]
fn independent_executions_can_differ_but_repeated_reads_keep_one_ssa_word() {
    original_owner(|budget, end| {
        for width in [32, 64] {
            for independent in [true, false] {
                budget.admit(FIXTURE, FIXTURE).unwrap();
                let (sign, infinity, quiet, _) = layout(width);
                let zero = Expr::bitvec_const(0u8, width);
                let inputs = [&zero, &zero];
                let (a, va) = raw("execution_a", width);
                let (b, vb) = raw("execution_b", width);
                let operation = FpRawOperation::Arithmetic {
                    operation: RustFpArithmetic::Divide,
                    inputs: &inputs,
                    nan_policy: RustNanPolicy::NoExtra,
                };
                let both = [
                    FpRawResultRelation {
                        operation,
                        output: &a,
                    },
                    FpRawResultRelation {
                        operation,
                        output: &b,
                    },
                ];
                let both_bindings = [
                    FpExprInputBinding {
                        source: &a,
                        target: &va,
                    },
                    FpExprInputBinding {
                        source: &b,
                        target: &vb,
                    },
                ];
                let results = if independent {
                    both.as_slice()
                } else {
                    &both[..1]
                };
                let bindings = if independent {
                    both_bindings.as_slice()
                } else {
                    &both_bindings[..1]
                };
                let word = if independent { &vb } else { &va };
                let condition = conjunction(vec![
                    pin(&va, infinity | quiet, width),
                    pin(word, infinity | quiet | sign, width),
                ]);
                let problem = ChcProblem::new();
                let body = {
                    let (body, source) =
                        lower_fp_raw_result_clause(&[], results, bindings, &problem, budget)
                            .unwrap()
                            .into_body(ClauseBody::constraint(condition))
                            .unwrap()
                            .into_parts()
                            .unwrap();
                    assert_eq!(source.raw_results().len(), if independent { 2 } else { 1 });
                    body
                };
                native(body, independent, budget, end);
            }
        }
    });
}

#[test]
fn fused_nan_propagation_uses_the_third_original_input_not_an_intermediate() {
    original_owner(|budget, end| {
        for width in [32, 64] {
            let (sign, infinity, quiet, one) = layout(width);
            let s = infinity | 0x123;
            for bits in [s, s | sign, s | quiet, infinity | quiet] {
                result_bits(
                    width,
                    RustFpArithmetic::FusedMultiplyAdd,
                    &[one, one, s],
                    RustNanPolicy::NoExtra,
                    bits,
                    true,
                    budget,
                    end,
                );
            }
            result_bits(
                width,
                RustFpArithmetic::FusedMultiplyAdd,
                &[one, one, s],
                RustNanPolicy::NoExtra,
                infinity | quiet | 0x456,
                false,
                budget,
                end,
            );
        }
    });
}
