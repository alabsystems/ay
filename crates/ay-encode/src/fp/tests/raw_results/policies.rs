// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
use super::*;

#[test]
fn noextra_generated_nan_has_only_preferred_payload_and_either_sign() {
    original_owner(|budget, end| {
        for width in [32, 64] {
            let (sign, infinity, quiet, _) = layout(width);
            for (bits, ok) in [
                (infinity | quiet, true),
                (infinity | quiet | sign, true),
                (infinity | quiet | 0x456, false),
                (infinity | 0x123, false),
                (infinity, false),
            ] {
                result_bits(
                    width,
                    RustFpArithmetic::Divide,
                    &[0, 0],
                    RustNanPolicy::NoExtra,
                    bits,
                    ok,
                    budget,
                    end,
                );
            }
        }
    });
}

#[test]
fn signaling_input_can_propagate_unchanged_or_quieted_but_not_altered_signaling() {
    original_owner(|budget, end| {
        for width in [32, 64] {
            let (sign, infinity, quiet, one) = layout(width);
            let signaling = infinity | 0x123;
            for bits in [
                signaling,
                signaling | sign,
                signaling | quiet,
                signaling | quiet | sign,
                infinity | quiet,
            ] {
                result_bits(
                    width,
                    RustFpArithmetic::Multiply,
                    &[signaling, one],
                    RustNanPolicy::NoExtra,
                    bits,
                    true,
                    budget,
                    end,
                );
            }
            for policy in [
                RustNanPolicy::NoExtra,
                RustNanPolicy::AllQuietPayloads,
                RustNanPolicy::AllOnesQuietPayload,
                RustNanPolicy::WasmConditional,
            ] {
                result_bits(
                    width,
                    RustFpArithmetic::Multiply,
                    &[signaling, one],
                    policy,
                    infinity | 0x124,
                    false,
                    budget,
                    end,
                );
            }
        }
    });
}

#[test]
fn quiet_input_cannot_create_signaling_or_unrelated_noextra_payloads() {
    original_owner(|budget, end| {
        for width in [32, 64] {
            let (sign, infinity, quiet, one) = layout(width);
            let q = infinity | quiet | 0x123;
            for bits in [q, q | sign, infinity | quiet, infinity | quiet | sign] {
                result_bits(
                    width,
                    RustFpArithmetic::Add,
                    &[q, one],
                    RustNanPolicy::NoExtra,
                    bits,
                    true,
                    budget,
                    end,
                );
            }
            for bits in [infinity | 0x123, infinity | quiet | 0x456] {
                result_bits(
                    width,
                    RustFpArithmetic::Add,
                    &[q, one],
                    RustNanPolicy::NoExtra,
                    bits,
                    false,
                    budget,
                    end,
                );
            }
        }
    });
}

#[test]
fn allquiet_extras_accept_arbitrary_quiet_payload_but_not_new_signaling() {
    original_owner(|budget, end| {
        for width in [32, 64] {
            let (sign, infinity, quiet, _) = layout(width);
            for bits in [
                infinity | quiet | 0x456,
                infinity | quiet | sign | 0x789,
                infinity | (quiet * 2 - 1),
            ] {
                result_bits(
                    width,
                    RustFpArithmetic::Divide,
                    &[0, 0],
                    RustNanPolicy::AllQuietPayloads,
                    bits,
                    true,
                    budget,
                    end,
                );
            }
            result_bits(
                width,
                RustFpArithmetic::Divide,
                &[0, 0],
                RustNanPolicy::AllQuietPayloads,
                infinity | 0x123,
                false,
                budget,
                end,
            );
        }
    });
}

#[test]
fn allones_policy_adds_only_the_allone_quiet_payload() {
    original_owner(|budget, end| {
        for width in [32, 64] {
            let (sign, infinity, quiet, _) = layout(width);
            for bits in [
                infinity | quiet,
                infinity | (quiet * 2 - 1),
                infinity | sign | (quiet * 2 - 1),
            ] {
                result_bits(
                    width,
                    RustFpArithmetic::Divide,
                    &[0, 0],
                    RustNanPolicy::AllOnesQuietPayload,
                    bits,
                    true,
                    budget,
                    end,
                );
            }
            result_bits(
                width,
                RustFpArithmetic::Divide,
                &[0, 0],
                RustNanPolicy::AllOnesQuietPayload,
                infinity | quiet | 0x456,
                false,
                budget,
                end,
            );
        }
    });
}

#[test]
fn wasm_extras_require_an_original_nonpreferred_nan_input() {
    original_owner(|budget, end| {
        for width in [32, 64] {
            let (_, infinity, quiet, one) = layout(width);
            let preferred = infinity | quiet;
            budget.admit(FIXTURE, FIXTURE).unwrap();
            for (inputs, extra) in [
                (vec![0, 0], false),
                (vec![preferred, one], false),
                (vec![preferred | 0x123, one], true),
                (vec![infinity | 0x123, one], true),
            ] {
                let operation = if inputs[0] == 0 {
                    RustFpArithmetic::Divide
                } else {
                    RustFpArithmetic::Add
                };
                result_bits(
                    width,
                    operation,
                    &inputs,
                    RustNanPolicy::WasmConditional,
                    infinity | quiet | 0x456,
                    extra,
                    budget,
                    end,
                );
                result_bits(
                    width,
                    operation,
                    &inputs,
                    RustNanPolicy::WasmConditional,
                    infinity | 0x456,
                    false,
                    budget,
                    end,
                );
            }
        }
    });
}

#[test]
fn entire_forbidden_payload_regions_are_unsat_without_sampling_output_bits() {
    original_owner(|budget, end| {
        for width in [32, 64] {
            let (_, infinity, quiet, one) = layout(width);
            arithmetic(
                width,
                RustFpArithmetic::Divide,
                &[0, 0],
                RustNanPolicy::NoExtra,
                |v| negate(mantissa(v, width, quiet)),
                false,
                budget,
                end,
            );
            arithmetic(
                width,
                RustFpArithmetic::Divide,
                &[0, 0],
                RustNanPolicy::AllOnesQuietPayload,
                |v| {
                    conjunction(vec![
                        negate(mantissa(v, width, quiet)),
                        negate(mantissa(v, width, quiet * 2 - 1)),
                    ])
                },
                false,
                budget,
                end,
            );
            arithmetic(
                width,
                RustFpArithmetic::Add,
                &[infinity | quiet | 0x123, one],
                RustNanPolicy::AllQuietPayloads,
                |v| {
                    let bit = if width == 32 { 22 } else { 51 };
                    ChcExpr::Op(
                        ChcOp::Eq,
                        vec![
                            Arc::new(ChcExpr::Op(
                                ChcOp::BvExtract(bit, bit),
                                vec![Arc::new(ChcExpr::Var(v.clone()))],
                            )),
                            Arc::new(ChcExpr::BitVec(0, 1)),
                        ],
                    )
                },
                false,
                budget,
                end,
            );
        }
    });
}
