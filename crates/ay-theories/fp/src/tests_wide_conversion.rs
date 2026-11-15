// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Exact integer-range bounds, independent of the host's u64 width.

use super::*;
use crate::tests_support::{extract_lit, solve_fp_clauses, solve_fp_result};
use ay_core::{Sort, Symbol};
use ay_sat::SatResult;
use num_bigint::BigInt;
use std::cell::Cell;

type Input = (bool, u64, BigInt);

fn pow2(bit: usize) -> BigInt {
    BigInt::from(1u8) << bit
}

fn power(sign: bool, exponent: usize) -> Input {
    (sign, 16_383 + exponent as u64, BigInt::from(0u8))
}

/// 2^width - 1 is exact in binary128 for these 64/65-bit endpoints.
fn maximum(width: usize) -> Input {
    assert!(width <= 113);
    (
        false,
        16_383 + width as u64 - 1,
        pow2(112) - pow2(113 - width),
    )
}

/// 2^width - 1/2: distinguish range admission AFTER rounding.
fn upper_half(width: usize) -> Input {
    assert!(width < 113);
    (
        false,
        16_383 + width as u64 - 1,
        pow2(112) - pow2(112 - width),
    )
}

fn pin(solver: &mut FpSolver<'_>, fp: &FpDecomposed, input: &Input) {
    let (sign, exponent, fraction) = input;
    solver.add_clause(CnfClause::unit(if *sign { fp.sign } else { -fp.sign }));
    for (i, &bit) in fp.exponent.iter().enumerate() {
        solver.add_clause(CnfClause::unit(if (exponent >> i) & 1 == 1 {
            bit
        } else {
            -bit
        }));
    }
    for (i, &bit) in fp.significand.iter().enumerate() {
        solver.add_clause(CnfClause::unit(if fraction.bit(i as u64) {
            bit
        } else {
            -bit
        }));
    }
}

fn conversion(
    input: Input,
    width: usize,
    signed: bool,
    rm: RoundingMode,
    check: impl FnOnce(&mut FpSolver<'_>, &[CnfLit]),
) {
    let mut terms = TermStore::new();
    let term = terms.mk_var("wide_input", Sort::FloatingPoint(15, 113));
    let mut solver = FpSolver::new(&terms);
    let fp = solver.get_fp(term);
    pin(&mut solver, &fp, &input);
    let bits = solver.bitblast_to_bv(term, rm, width, signed);
    assert_eq!(bits.len(), width);
    assert!(!solver.has_encoding_gap());
    check(&mut solver, &bits);
}

fn word(integer: BigInt, width: usize) -> BigInt {
    if integer < BigInt::from(0u8) {
        pow2(width) + integer
    } else {
        integer
    }
}

/// Require a SAT circuit AND rule out EVERY different result bit pattern.
fn defined(input: Input, width: usize, signed: bool, rm: RoundingMode, integer: BigInt) {
    let expected = word(integer, width);
    assert!(expected >= BigInt::from(0u8) && expected < pow2(width));
    conversion(input, width, signed, rm, |solver, bits| {
        let model = solve_fp_clauses(solver);
        for (i, &bit) in bits.iter().enumerate() {
            assert_eq!(extract_lit(&model, bit), expected.bit(i as u64));
        }
        // This oracle does not use the newly added constant-vector helper.
        let differs = bits
            .iter()
            .enumerate()
            .map(|(i, &bit)| if expected.bit(i as u64) { -bit } else { bit })
            .collect();
        solver.add_clause(CnfClause::new(differs));
        assert!(matches!(solve_fp_result(solver), SatResult::Unsat(_)));
    });
}

/// An unspecified result can take two different words in separate models.
fn unspecified(input: Input, width: usize, signed: bool, rm: RoundingMode) {
    for expected in [BigInt::from(0u8), pow2(width) - BigInt::from(1u8)] {
        conversion(input.clone(), width, signed, rm, |solver, bits| {
            for (i, &bit) in bits.iter().enumerate() {
                solver.add_clause(CnfClause::unit(if expected.bit(i as u64) {
                    bit
                } else {
                    -bit
                }));
            }
            let model = solve_fp_clauses(solver);
            for (i, &bit) in bits.iter().enumerate() {
                assert_eq!(extract_lit(&model, bit), expected.bit(i as u64));
            }
        });
    }
}

#[test]
fn unsigned_64_uses_the_full_target_range() {
    defined(maximum(64), 64, false, RoundingMode::RNE, pow2(64) - 1u8);
}

#[test]
fn unsigned_65_does_not_truncate_the_bound_at_u64_max() {
    defined(maximum(65), 65, false, RoundingMode::RNE, pow2(65) - 1u8);
    defined(power(false, 64), 65, false, RoundingMode::RTZ, pow2(64));
}

#[test]
fn unsigned_128_keeps_high_target_bits_defined() {
    defined(power(false, 80), 128, false, RoundingMode::RNE, pow2(80));
    // Largest binary128 below 2^128: 2^128 - 2^15.
    let input = (false, 16_383 + 127, pow2(112) - 1u8);
    defined(input, 128, false, RoundingMode::RTZ, pow2(128) - pow2(15));
}

#[test]
fn signed_64_keeps_both_twos_complement_endpoints() {
    defined(maximum(63), 64, true, RoundingMode::RNE, pow2(63) - 1u8);
    defined(power(true, 63), 64, true, RoundingMode::RTZ, -pow2(63));
}

#[test]
fn signed_65_keeps_both_twos_complement_endpoints() {
    defined(maximum(64), 65, true, RoundingMode::RNE, pow2(64) - 1u8);
    defined(power(true, 64), 65, true, RoundingMode::RTZ, -pow2(64));
}

#[test]
fn signed_128_keeps_high_magnitudes_and_the_negative_minimum() {
    defined(power(false, 80), 128, true, RoundingMode::RNE, pow2(80));
    defined(power(true, 80), 128, true, RoundingMode::RTZ, -pow2(80));
    defined(power(true, 127), 128, true, RoundingMode::RNE, -pow2(127));
    let below_upper = (false, 16_383 + 126, pow2(112) - 1u8);
    defined(
        below_upper,
        128,
        true,
        RoundingMode::RTZ,
        pow2(127) - pow2(14),
    );
}

#[test]
fn all_five_rounding_modes_remain_exact_for_wide_unsigned_targets() {
    for width in [64, 65, 128] {
        for (rm, integer) in [
            (RoundingMode::RNE, 2),
            (RoundingMode::RNA, 2),
            (RoundingMode::RTP, 2),
            (RoundingMode::RTN, 1),
            (RoundingMode::RTZ, 1),
        ] {
            defined((false, 16_383, pow2(111)), width, false, rm, integer.into());
        }
    }
}

#[test]
fn all_five_rounding_modes_remain_exact_for_wide_signed_targets() {
    for width in [64, 65, 128] {
        for (rm, integer) in [
            (RoundingMode::RNE, -2),
            (RoundingMode::RNA, -2),
            (RoundingMode::RTP, -1),
            (RoundingMode::RTN, -2),
            (RoundingMode::RTZ, -1),
        ] {
            defined((true, 16_383, pow2(111)), width, true, rm, integer.into());
        }
    }
}

#[test]
fn ties_to_even_and_ties_away_are_not_confused() {
    for width in [64, 65, 128] {
        let two_and_half = (false, 16_384, pow2(110));
        defined(
            two_and_half.clone(),
            width,
            false,
            RoundingMode::RNE,
            2.into(),
        );
        defined(two_and_half, width, false, RoundingMode::RNA, 3.into());
    }
}

#[test]
fn unsigned_rounding_near_the_upper_boundary_remains_partial() {
    for width in [64, 65] {
        for rm in [RoundingMode::RTZ, RoundingMode::RTN] {
            defined(upper_half(width), width, false, rm, pow2(width) - 1u8);
        }
        for rm in [RoundingMode::RNE, RoundingMode::RNA, RoundingMode::RTP] {
            unspecified(upper_half(width), width, false, rm);
        }
    }
}

#[test]
fn signed_rounding_near_the_upper_boundary_remains_partial() {
    for width in [64, 65] {
        for rm in [RoundingMode::RTZ, RoundingMode::RTN] {
            defined(
                upper_half(width - 1),
                width,
                true,
                rm,
                pow2(width - 1) - 1u8,
            );
        }
        for rm in [RoundingMode::RNE, RoundingMode::RNA, RoundingMode::RTP] {
            unspecified(upper_half(width - 1), width, true, rm);
        }
    }
}

#[test]
fn out_of_range_finite_inputs_do_not_get_a_fixed_wide_result() {
    for width in [64, 65, 128] {
        unspecified(power(false, width), width, false, RoundingMode::RTZ);
        unspecified(power(false, width - 1), width, true, RoundingMode::RTZ);
        unspecified(power(true, width), width, true, RoundingMode::RTZ);
    }
}

#[test]
fn nan_and_infinity_remain_unspecified_at_all_three_target_widths() {
    for width in [64, 65, 128] {
        for signed in [false, true] {
            for input in [
                (false, 32_767, BigInt::from(1u8)),
                (false, 32_767, BigInt::from(0u8)),
                (true, 32_767, BigInt::from(0u8)),
            ] {
                unspecified(input, width, signed, RoundingMode::RNE);
            }
        }
    }
}

#[test]
fn abstract_nan_congruence_survives_wide_conversion_bounds() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("nan_a", Sort::FloatingPoint(15, 113));
    let y = terms.mk_var("nan_b", Sort::FloatingPoint(15, 113));
    let mut solver = FpSolver::new(&terms);
    let fx = solver.get_fp(x);
    let fy = solver.get_fp(y);
    pin(&mut solver, &fx, &(false, 32_767, BigInt::from(1u8)));
    pin(&mut solver, &fy, &(true, 32_767, pow2(111)));
    let a = solver.bitblast_to_bv(x, RoundingMode::RNE, 128, true);
    let b = solver.bitblast_to_bv(y, RoundingMode::RNE, 128, true);
    assert!(!solver.has_encoding_gap());
    solve_fp_clauses(&solver);
    solver.add_clause(CnfClause::unit(-a[0]));
    solver.add_clause(CnfClause::unit(b[0]));
    assert!(matches!(solve_fp_result(&solver), SatResult::Unsat(_)));
}

#[test]
fn both_zero_signs_convert_to_the_unique_zero_word() {
    for width in [64, 65, 128] {
        for signed in [false, true] {
            for negative in [false, true] {
                defined(
                    (negative, 0, 0.into()),
                    width,
                    signed,
                    RoundingMode::RNE,
                    0.into(),
                );
            }
        }
    }
}

#[test]
fn wide_conversion_refusal_cannot_reset_the_original_construction_owner() {
    let mut terms = TermStore::new();
    let input = terms.mk_var("x", Sort::FloatingPoint(15, 113));
    let rm = terms.mk_var("RTZ", Sort::Uninterpreted("RoundingMode".to_string()));
    let value = terms.mk_app(
        Symbol::indexed("fp.to_sbv", vec![128]),
        [rm, input],
        Sort::bitvec(128),
    );
    let zero = terms.mk_bitvec(0.into(), 128);
    let predicate = terms.mk_app(Symbol::named("="), [value, zero], Sort::Bool);
    let enabled = Cell::new(true);
    let calls = Cell::new(0);
    let mut stop = |p: FpBuildProgress| {
        calls.set(calls.get() + 1);
        enabled.get() && p.stage == FpBuildStage::Operation && p.clauses > 0
    };
    let mut attempt = FpConstruction::new(FpSolver::new(&terms), &mut stop).unwrap();
    assert!(matches!(
        attempt.try_bitblast_bv_predicate(predicate),
        Err(FpBuildError::Interrupted)
    ));
    let stopped = calls.get();
    enabled.set(false);
    assert!(matches!(
        attempt.try_bitblast_bv_predicate(predicate),
        Err(FpBuildError::Interrupted)
    ));
    assert!(matches!(attempt.finish(), Err(FpBuildError::Interrupted)));
    assert_eq!(calls.get(), stopped);
}
