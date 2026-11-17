// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
use super::*;

#[test]
fn signed_eight_bit_complete_outputs_are_unique_in_both_formats() {
    original_owner(|budget, end| {
        for (width, words) in [
            (32, [0x3f800000, 0x42fe0000, 0xc3000000, 0xbf800000]),
            (
                64,
                [
                    0x3ff0000000000000,
                    0x405fc00000000000,
                    0xc060000000000000,
                    0xbff0000000000000,
                ],
            ),
        ] {
            for (bits, expected) in [1, 127, 128, 255].into_iter().zip(words) {
                word_case(Kind::Signed, 8, bits, width, expected, budget, end);
            }
        }
    });
}

#[test]
fn integer_zero_is_positive_zero_not_negative_zero_nan_or_infinity() {
    original_owner(|budget, end| {
        for width in [32, 64] {
            for kind in [Kind::Signed, Kind::Unsigned] {
                word_case(kind, 8, 0, width, 0, budget, end);
            }
        }
    });
}

#[test]
fn signed_sixty_four_limits_round_to_finite_complete_words() {
    original_owner(|budget, end| {
        for (width, negative, positive) in [
            (32, 0xdf000000, 0x5f000000),
            (64, 0xc3e0000000000000, 0x43e0000000000000),
        ] {
            word_case(Kind::Signed, 64, 1 << 63, width, negative, budget, end);
            word_case(
                Kind::Signed,
                64,
                (1 << 63) - 1,
                width,
                positive,
                budget,
                end,
            );
        }
    });
}

#[test]
fn unsigned_maxima_keep_the_original_integer_not_an_ieee_input_word() {
    original_owner(|budget, end| {
        for (width, small, large) in [
            (32, 0x437f0000, 0x5f800000),
            (64, 0x406fe00000000000, 0x43f0000000000000),
        ] {
            word_case(Kind::Unsigned, 8, 255, width, small, budget, end);
            word_case(Kind::Unsigned, 64, u64::MAX, width, large, budget, end);
        }
    });
}

#[test]
fn rne_halfway_even_and_odd_neighbors_have_unique_complete_words() {
    original_owner(|budget, end| {
        for (width, base, even, odd) in [
            (32, 1u64 << 24, 0x4b800000, 0x4b800002),
            (64, 1u64 << 53, 0x4340000000000000, 0x4340000000000002),
        ] {
            word_case(Kind::Unsigned, 64, base + 1, width, even, budget, end);
            word_case(Kind::Unsigned, 64, base + 3, width, odd, budget, end);
        }
    });
}

#[test]
fn negative_rne_ties_keep_sign_and_even_rounding_not_unsigned_interpretation() {
    original_owner(|budget, end| {
        for (width, base, even, odd) in [
            (32, 1u64 << 24, 0xcb800000, 0xcb800002),
            (64, 1u64 << 53, 0xc340000000000000, 0xc340000000000002),
        ] {
            word_case(
                Kind::Signed,
                64,
                0u64.wrapping_sub(base + 1),
                width,
                even,
                budget,
                end,
            );
            word_case(
                Kind::Signed,
                64,
                0u64.wrapping_sub(base + 3),
                width,
                odd,
                budget,
                end,
            );
        }
    });
}

#[test]
fn direct_extract_uses_every_original_base_bit_and_preserves_the_descriptor() {
    original_owner(|budget, end| {
        for (base_width, out_width, kind, expected) in [
            (32, 32, Kind::Signed, 0xbf800000),
            (64, 64, Kind::Unsigned, 0x406fe00000000000),
        ] {
            for correct in [true, false] {
                budget.admit(FIXTURE, FIXTURE).unwrap();
                let (base, vb) = raw("extract_integer", base_width);
                let slice = base.clone().try_extract(7, 0).unwrap();
                let (out, vo) = raw("extract_output", out_width);
                let results = [FpRawResultRelation {
                    operation: kind.operation(&slice),
                    output: &out,
                }];
                let bindings = [
                    FpExprInputBinding {
                        source: &base,
                        target: &vb,
                    },
                    FpExprInputBinding {
                        source: &out,
                        target: &vo,
                    },
                ];
                let problem = ChcProblem::new();
                let output_pin = pin(&vo, expected, out_width);
                let constraint = conjunction(vec![
                    pin(&vb, 0x1234ff, base_width),
                    if correct {
                        output_pin
                    } else {
                        negate(output_pin)
                    },
                ]);
                let body = {
                    let (body, source) =
                        lower_fp_raw_result_clause(&[], &results, &bindings, &problem, budget)
                            .unwrap()
                            .into_body(ClauseBody::constraint(constraint))
                            .unwrap()
                            .into_parts()
                            .unwrap();
                    assert!(std::ptr::eq(source.bindings()[0].source, &raw const base));
                    let retained = match source.raw_results()[0].operation {
                        FpRawOperation::SignedIntegerToFpRne(input)
                        | FpRawOperation::UnsignedIntegerToFpRne(input) => input,
                        _ => panic!(),
                    };
                    assert!(std::ptr::eq(retained, &raw const slice));
                    body
                };
                native(body, correct, budget, end);
                drop(slice);
                drop(base);
                drop(out);
                budget.charge(0).unwrap();
            }
        }
    });
}

#[test]
fn repeated_observations_and_distinct_executions_cannot_change_the_unique_word() {
    original_owner(|budget, end| {
        for width in [32, 64] {
            budget.admit(FIXTURE, FIXTURE).unwrap();
            let input = Expr::bitvec_const(255u8, 8);
            let (a, va) = raw("cast_ssa_a", width);
            let (b, vb) = raw("cast_ssa_b", width);
            let results = [
                FpRawResultRelation {
                    operation: Kind::Unsigned.operation(&input),
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
            let repeated = a.clone().try_eq(a.clone()).unwrap();
            let roots = [repeated.clone(), repeated];
            let problem = ChcProblem::new();
            let different = ChcExpr::Op(
                ChcOp::Not,
                vec![Arc::new(ChcExpr::Op(
                    ChcOp::Eq,
                    vec![
                        Arc::new(ChcExpr::Var(va.clone())),
                        Arc::new(ChcExpr::Var(vb.clone())),
                    ],
                ))],
            );
            let body = {
                let (body, source) =
                    lower_fp_raw_result_clause(&roots, &results, &bindings, &problem, budget)
                        .unwrap()
                        .into_body(ClauseBody::constraint(different))
                        .unwrap()
                        .into_parts()
                        .unwrap();
                assert!(std::ptr::eq(source.roots(), roots.as_slice()));
                body
            };
            native(body, false, budget, end);
        }
    });
}
