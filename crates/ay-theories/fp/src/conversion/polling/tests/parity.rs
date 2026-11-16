// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

fn compare(
    signed: bool,
    precision: FpPrecision,
    width: u32,
    mode: Option<RoundingMode>,
    end: Instant,
    enclosing: &Option<ay_core::resource::CheckStop>,
) {
    assert!(!stopped(end, enclosing));
    let (terms, rm_term, word, result) = fixture(signed, precision, width, mode);
    let mut legacy = FpSolver::new(&terms);
    let rm = uninterrupted(|control| legacy.rounding_operand_with_control(rm_term, control));
    let expected = uninterrupted(|control| {
        if signed {
            legacy.oracle_signed(word, rm, precision, control)
        } else {
            legacy.oracle_unsigned(word, rm, precision, control)
        }
    });
    legacy.term_to_fp.insert(result, expected.clone());
    assert!(!stopped(end, enclosing));
    let mut stop = |_| stopped(end, enclosing);
    let mut attempt = FpConstruction::new(FpSolver::new(&terms), &mut stop).unwrap();
    let actual = attempt.try_get_fp(result).unwrap();
    let built = attempt.finish().unwrap();
    assert_fp(&actual, &expected);
    assert_eq!(built.clauses.as_slice(), legacy.clauses());
    assert_eq!(built.cache.next_var, legacy.next_var);
    assert_eq!(built.cache.cached_true, legacy.cached_true);
    assert_eq!(built.cache.cached_false, legacy.cached_false);
    assert_eq!(built.cache.bv_term_bits, legacy.bv_term_bits);
    assert_eq!(built.cache.rm_terms, legacy.rm_terms);
    assert_eq!(built.cache.term_to_fp.len(), legacy.term_to_fp.len());
    assert_fp(
        &built.cache.term_to_fp[&result],
        &legacy.term_to_fp[&result],
    );
    assert_eq!(built.pending_condition_links.len(), 0);
    assert_eq!(built.cache.to_bv_unspec_sites.len(), 0);
    assert_eq!(built.cache.ieee_nan_encodings.len(), 0);
    assert!(!built.has_encoding_gap);
    drop(built);
    drop(legacy);
    assert!(!stopped(end, enclosing));
}

#[test]
fn both_integer_signs_widths_and_all_literal_modes_keep_exact_legacy_cnf() {
    let (end, enclosing) = frame();
    for precision in [FpPrecision::Float32, FpPrecision::Float64] {
        for width in [8, 16, 32, 64] {
            for signed in [false, true] {
                for mode in crate::RM_ORDER {
                    compare(signed, precision, width, Some(mode), end, &enclosing);
                }
            }
        }
    }
}

#[test]
fn symbolic_rounding_keeps_exact_legacy_cache_and_gate_order() {
    let (end, enclosing) = frame();
    for signed in [false, true] {
        compare(signed, FpPrecision::Float64, 64, None, end, &enclosing);
    }
}

#[test]
fn repeated_numeric_roots_reuse_one_owned_input_and_result_cache() {
    let (end, enclosing) = frame();
    let (terms, _, word, result) = fixture(true, FpPrecision::Float64, 64, Some(RoundingMode::RNE));
    let calls = Cell::new(0);
    let mut stop = |_| {
        calls.set(calls.get() + 1);
        stopped(end, &enclosing)
    };
    let mut attempt = FpConstruction::new(FpSolver::new(&terms), &mut stop).unwrap();
    let first = attempt.try_get_fp(result).unwrap();
    let before = calls.get();
    let second = attempt.try_get_fp(result).unwrap();
    assert!(calls.get() > before);
    assert_fp(&first, &second);
    let built = attempt.finish().unwrap();
    assert_eq!(built.cache.bv_term_bits.len(), 1);
    assert_eq!(built.cache.bv_term_bits[&word].len(), 64);
    assert_eq!(built.cache.term_to_fp.len(), 1);
    drop(built);
    assert!(!stopped(end, &enclosing));
}
