// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::tests_support::{extract_fp, make_concrete_f16, solve_fp_clauses};
use super::*;
use ay_core::CnfClause;
use ay_sat::SatResult;

#[test]
fn test_fp16_add_tie_rne_rounds_to_even() {
    let terms = TermStore::new();
    let mut solver = FpSolver::new(&terms);
    let a = make_concrete_f16(&mut solver, false, 15, 0);
    let b = make_concrete_f16(&mut solver, false, 4, 0);
    let result = solver.make_add(&a, &b, RoundingMode::RNE);
    let model = solve_fp_clauses(&solver);
    let (sign, exp, sig) = extract_fp(&model, &result);
    assert!(!sign);
    assert_eq!(exp, 15);
    assert_eq!(sig, 0);
}

#[test]
fn test_fp16_add_tie_rna_rounds_away() {
    let terms = TermStore::new();
    let mut solver = FpSolver::new(&terms);
    let a = make_concrete_f16(&mut solver, false, 15, 0);
    let b = make_concrete_f16(&mut solver, false, 4, 0);
    let result = solver.make_add(&a, &b, RoundingMode::RNA);
    let model = solve_fp_clauses(&solver);
    let (sign, exp, sig) = extract_fp(&model, &result);
    assert!(!sign);
    assert_eq!(exp, 15);
    assert_eq!(sig, 1);
}

#[test]
fn test_fp16_add_tie_rtp_rounds_up() {
    let terms = TermStore::new();
    let mut solver = FpSolver::new(&terms);
    let a = make_concrete_f16(&mut solver, false, 15, 0);
    let b = make_concrete_f16(&mut solver, false, 4, 0);
    let result = solver.make_add(&a, &b, RoundingMode::RTP);
    let model = solve_fp_clauses(&solver);
    let (sign, exp, sig) = extract_fp(&model, &result);
    assert!(!sign);
    assert_eq!(exp, 15);
    assert_eq!(sig, 1);
}

#[test]
fn test_fp16_add_tie_rtn_truncates_positive() {
    let terms = TermStore::new();
    let mut solver = FpSolver::new(&terms);
    let a = make_concrete_f16(&mut solver, false, 15, 0);
    let b = make_concrete_f16(&mut solver, false, 4, 0);
    let result = solver.make_add(&a, &b, RoundingMode::RTN);
    let model = solve_fp_clauses(&solver);
    let (sign, exp, sig) = extract_fp(&model, &result);
    assert!(!sign);
    assert_eq!(exp, 15);
    assert_eq!(sig, 0);
}

#[test]
fn test_fp16_add_tie_rtz_truncates() {
    let terms = TermStore::new();
    let mut solver = FpSolver::new(&terms);
    let a = make_concrete_f16(&mut solver, false, 15, 0);
    let b = make_concrete_f16(&mut solver, false, 4, 0);
    let result = solver.make_add(&a, &b, RoundingMode::RTZ);
    let model = solve_fp_clauses(&solver);
    let (sign, exp, sig) = extract_fp(&model, &result);
    assert!(!sign);
    assert_eq!(exp, 15);
    assert_eq!(sig, 0);
}

#[test]
fn test_fp16_add_symbolic_commutative_rne() {
    let terms = TermStore::new();
    let mut solver = FpSolver::new(&terms);
    let a = solver.fresh_decomposed(FpPrecision::Float16);
    let b = solver.fresh_decomposed(FpPrecision::Float16);
    let ab = solver.make_add(&a, &b, RoundingMode::RNE);
    let ba = solver.make_add(&b, &a, RoundingMode::RNE);

    let sign_eq = solver.make_xnor(ab.sign, ba.sign);
    let exp_eq = solver.make_bits_equal(&ab.exponent, &ba.exponent);
    let sig_eq = solver.make_bits_equal(&ab.significand, &ba.significand);
    let exp_sig_eq = solver.make_and(exp_eq, sig_eq);
    let eq = solver.make_and(sign_eq, exp_sig_eq);
    solver.add_clause(CnfClause::unit(-eq));

    match tests_support::solve_fp_result(&solver) {
        SatResult::Sat(model) => {
            panic!(
                "symbolic FP16 add should be commutative under RNE; \
                 found model a={:?} b={:?} ab={:?} ba={:?}",
                extract_fp(&model, &a),
                extract_fp(&model, &b),
                extract_fp(&model, &ab),
                extract_fp(&model, &ba)
            );
        }
        SatResult::Unsat(_) => {}
        SatResult::Unknown => panic!("symbolic FP16 add commutativity should not be unknown"),
        #[allow(unreachable_patterns)]
        other => panic!("unexpected SAT result: {other:?}"),
    }
}

#[test]
fn test_fp16_add_neg_tie_rne() {
    let terms = TermStore::new();
    let mut solver = FpSolver::new(&terms);
    let a = make_concrete_f16(&mut solver, true, 15, 0);
    let b = make_concrete_f16(&mut solver, true, 4, 0);
    let result = solver.make_add(&a, &b, RoundingMode::RNE);
    let model = solve_fp_clauses(&solver);
    let (sign, exp, sig) = extract_fp(&model, &result);
    assert!(sign);
    assert_eq!(exp, 15);
    assert_eq!(sig, 0);
}

#[test]
fn test_fp16_add_neg_tie_rna() {
    let terms = TermStore::new();
    let mut solver = FpSolver::new(&terms);
    let a = make_concrete_f16(&mut solver, true, 15, 0);
    let b = make_concrete_f16(&mut solver, true, 4, 0);
    let result = solver.make_add(&a, &b, RoundingMode::RNA);
    let model = solve_fp_clauses(&solver);
    let (sign, exp, sig) = extract_fp(&model, &result);
    assert!(sign);
    assert_eq!(exp, 15);
    assert_eq!(sig, 1);
}

#[test]
fn test_fp16_add_neg_tie_rtp() {
    let terms = TermStore::new();
    let mut solver = FpSolver::new(&terms);
    let a = make_concrete_f16(&mut solver, true, 15, 0);
    let b = make_concrete_f16(&mut solver, true, 4, 0);
    let result = solver.make_add(&a, &b, RoundingMode::RTP);
    let model = solve_fp_clauses(&solver);
    let (sign, exp, sig) = extract_fp(&model, &result);
    assert!(sign);
    assert_eq!(exp, 15);
    assert_eq!(sig, 0);
}

#[test]
fn test_fp16_add_neg_tie_rtn() {
    let terms = TermStore::new();
    let mut solver = FpSolver::new(&terms);
    let a = make_concrete_f16(&mut solver, true, 15, 0);
    let b = make_concrete_f16(&mut solver, true, 4, 0);
    let result = solver.make_add(&a, &b, RoundingMode::RTN);
    let model = solve_fp_clauses(&solver);
    let (sign, exp, sig) = extract_fp(&model, &result);
    assert!(sign);
    assert_eq!(exp, 15);
    assert_eq!(sig, 1);
}

#[test]
fn test_fp16_add_neg_tie_rtz() {
    let terms = TermStore::new();
    let mut solver = FpSolver::new(&terms);
    let a = make_concrete_f16(&mut solver, true, 15, 0);
    let b = make_concrete_f16(&mut solver, true, 4, 0);
    let result = solver.make_add(&a, &b, RoundingMode::RTZ);
    let model = solve_fp_clauses(&solver);
    let (sign, exp, sig) = extract_fp(&model, &result);
    assert!(sign);
    assert_eq!(exp, 15);
    assert_eq!(sig, 0);
}

#[test]
fn test_fp16_div_pos_one_by_pos_inf_is_pos_zero() {
    let terms = TermStore::new();
    let mut solver = FpSolver::new(&terms);
    let one = make_concrete_f16(&mut solver, false, 15, 0);
    let pos_inf = make_concrete_f16(&mut solver, false, 0b11111, 0);
    let result = solver.make_div(&one, &pos_inf, RoundingMode::RNE);
    let model = solve_fp_clauses(&solver);
    let (sign, exp, sig) = extract_fp(&model, &result);
    assert!(!sign);
    assert_eq!(exp, 0);
    assert_eq!(sig, 0);
}

#[test]
fn test_fp16_div_neg_one_by_pos_inf_is_neg_zero() {
    let terms = TermStore::new();
    let mut solver = FpSolver::new(&terms);
    let neg_one = make_concrete_f16(&mut solver, true, 15, 0);
    let pos_inf = make_concrete_f16(&mut solver, false, 0b11111, 0);
    let result = solver.make_div(&neg_one, &pos_inf, RoundingMode::RNE);
    let model = solve_fp_clauses(&solver);
    let (sign, exp, sig) = extract_fp(&model, &result);
    assert!(sign);
    assert_eq!(exp, 0);
    assert_eq!(sig, 0);
}

#[test]
fn test_fp16_add_above_halfway_rne() {
    let terms = TermStore::new();
    let mut solver = FpSolver::new(&terms);
    let a = make_concrete_f16(&mut solver, false, 15, 0);
    let b = make_concrete_f16(&mut solver, false, 4, 0b1000000000);
    let result = solver.make_add(&a, &b, RoundingMode::RNE);
    let model = solve_fp_clauses(&solver);
    let (sign, exp, sig) = extract_fp(&model, &result);
    assert!(!sign);
    assert_eq!(exp, 15);
    assert_eq!(sig, 1);
}

#[test]
fn test_fp16_add_above_halfway_rtz() {
    let terms = TermStore::new();
    let mut solver = FpSolver::new(&terms);
    let a = make_concrete_f16(&mut solver, false, 15, 0);
    let b = make_concrete_f16(&mut solver, false, 4, 0b1000000000);
    let result = solver.make_add(&a, &b, RoundingMode::RTZ);
    let model = solve_fp_clauses(&solver);
    let (sign, exp, sig) = extract_fp(&model, &result);
    assert!(!sign);
    assert_eq!(exp, 15);
    assert_eq!(sig, 0);
}

#[test]
fn test_fp16_add_above_halfway_rtn() {
    let terms = TermStore::new();
    let mut solver = FpSolver::new(&terms);
    let a = make_concrete_f16(&mut solver, false, 15, 0);
    let b = make_concrete_f16(&mut solver, false, 4, 0b1000000000);
    let result = solver.make_add(&a, &b, RoundingMode::RTN);
    let model = solve_fp_clauses(&solver);
    let (sign, exp, sig) = extract_fp(&model, &result);
    assert!(!sign);
    assert_eq!(exp, 15);
    assert_eq!(sig, 0);
}

#[test]
fn test_fp16_mul_exact_all_modes_agree() {
    let terms = TermStore::new();
    let expected_sig = 272u64;

    for rm in [
        RoundingMode::RNE,
        RoundingMode::RNA,
        RoundingMode::RTP,
        RoundingMode::RTN,
        RoundingMode::RTZ,
    ] {
        let mut solver = FpSolver::new(&terms);
        let a = make_concrete_f16(&mut solver, false, 15, 128);
        let b = make_concrete_f16(&mut solver, false, 15, 128);
        let result = solver.make_mul(&a, &b, rm);
        let model = solve_fp_clauses(&solver);
        let (sign, exp, sig) = extract_fp(&model, &result);
        assert!(!sign);
        assert_eq!(exp, 15);
        assert_eq!(sig, expected_sig);
    }
}

#[test]
fn test_fp16_add_pos_zero_neg_zero_rne() {
    let terms = TermStore::new();
    let mut solver = FpSolver::new(&terms);
    let a = make_concrete_f16(&mut solver, false, 0, 0);
    let b = make_concrete_f16(&mut solver, true, 0, 0);
    let result = solver.make_add(&a, &b, RoundingMode::RNE);
    let model = solve_fp_clauses(&solver);
    let (sign, exp, sig) = extract_fp(&model, &result);
    assert_eq!(exp, 0);
    assert_eq!(sig, 0);
    assert!(!sign);
}

#[test]
fn test_fp16_add_pos_zero_neg_zero_rtn() {
    let terms = TermStore::new();
    let mut solver = FpSolver::new(&terms);
    let a = make_concrete_f16(&mut solver, false, 0, 0);
    let b = make_concrete_f16(&mut solver, true, 0, 0);
    let result = solver.make_add(&a, &b, RoundingMode::RTN);
    let model = solve_fp_clauses(&solver);
    let (sign, exp, sig) = extract_fp(&model, &result);
    assert_eq!(exp, 0);
    assert_eq!(sig, 0);
    assert!(sign);
}

#[test]
fn test_fp16_min_pos_zero_neg_zero_can_be_pos_zero() {
    let terms = TermStore::new();
    let mut solver = FpSolver::new(&terms);
    let pos_zero = make_concrete_f16(&mut solver, false, 0, 0);
    let neg_zero = make_concrete_f16(&mut solver, true, 0, 0);
    let result = solver.make_min(&pos_zero, &neg_zero);
    solver.add_clause(CnfClause::unit(-result.sign));
    let model = solve_fp_clauses(&solver);
    let (sign, exp, sig) = extract_fp(&model, &result);
    assert!(!sign);
    assert_eq!(exp, 0);
    assert_eq!(sig, 0);
}

#[test]
fn test_fp16_min_pos_zero_neg_zero_can_be_neg_zero() {
    let terms = TermStore::new();
    let mut solver = FpSolver::new(&terms);
    let pos_zero = make_concrete_f16(&mut solver, false, 0, 0);
    let neg_zero = make_concrete_f16(&mut solver, true, 0, 0);
    let result = solver.make_min(&pos_zero, &neg_zero);
    solver.add_clause(CnfClause::unit(result.sign));
    let model = solve_fp_clauses(&solver);
    let (sign, exp, sig) = extract_fp(&model, &result);
    assert!(sign);
    assert_eq!(exp, 0);
    assert_eq!(sig, 0);
}

#[test]
fn test_fp16_max_neg_zero_pos_zero_can_be_pos_zero() {
    let terms = TermStore::new();
    let mut solver = FpSolver::new(&terms);
    let neg_zero = make_concrete_f16(&mut solver, true, 0, 0);
    let pos_zero = make_concrete_f16(&mut solver, false, 0, 0);
    let result = solver.make_max(&neg_zero, &pos_zero);
    solver.add_clause(CnfClause::unit(-result.sign));
    let model = solve_fp_clauses(&solver);
    let (sign, exp, sig) = extract_fp(&model, &result);
    assert!(!sign);
    assert_eq!(exp, 0);
    assert_eq!(sig, 0);
}

#[test]
fn test_fp16_max_neg_zero_pos_zero_can_be_neg_zero() {
    let terms = TermStore::new();
    let mut solver = FpSolver::new(&terms);
    let neg_zero = make_concrete_f16(&mut solver, true, 0, 0);
    let pos_zero = make_concrete_f16(&mut solver, false, 0, 0);
    let result = solver.make_max(&neg_zero, &pos_zero);
    solver.add_clause(CnfClause::unit(result.sign));
    let model = solve_fp_clauses(&solver);
    let (sign, exp, sig) = extract_fp(&model, &result);
    assert!(sign);
    assert_eq!(exp, 0);
    assert_eq!(sig, 0);
}

#[test]
fn test_fp16_fma_rtn_neg_zero_times_pos_zero_plus_pos_zero_is_neg_zero() {
    let terms = TermStore::new();
    let mut solver = FpSolver::new(&terms);
    let neg_zero = make_concrete_f16(&mut solver, true, 0, 0);
    let pos_zero = make_concrete_f16(&mut solver, false, 0, 0);
    let result = solver.make_fma(&neg_zero, &pos_zero, &pos_zero, RoundingMode::RTN);
    let model = solve_fp_clauses(&solver);
    let (sign, exp, sig) = extract_fp(&model, &result);
    assert!(sign);
    assert_eq!(exp, 0);
    assert_eq!(sig, 0);
}

#[test]
fn test_fp16_fma_rtn_pos_zero_times_pos_zero_plus_neg_zero_is_neg_zero() {
    let terms = TermStore::new();
    let mut solver = FpSolver::new(&terms);
    let pos_zero = make_concrete_f16(&mut solver, false, 0, 0);
    let neg_zero = make_concrete_f16(&mut solver, true, 0, 0);
    let result = solver.make_fma(&pos_zero, &pos_zero, &neg_zero, RoundingMode::RTN);
    let model = solve_fp_clauses(&solver);
    let (sign, exp, sig) = extract_fp(&model, &result);
    assert!(sign);
    assert_eq!(exp, 0);
    assert_eq!(sig, 0);
}

// IEEE 754-2019 §6.3: fma(1, 1, -1) = exact 0 via cancellation. The sign is +0
// for every rounding mode except RTN. Regression for wrong -0 sign (the general
// path derived the sign from the larger-magnitude addend).
#[test]
fn test_fp16_fma_exact_cancel_sign_positive_zero_non_rtn() {
    for rm in [
        RoundingMode::RNE,
        RoundingMode::RNA,
        RoundingMode::RTP,
        RoundingMode::RTZ,
    ] {
        let terms = TermStore::new();
        let mut solver = FpSolver::new(&terms);
        // 1.0, 1.0, -1.0
        let one = make_concrete_f16(&mut solver, false, 0b01111, 0);
        let neg_one = make_concrete_f16(&mut solver, true, 0b01111, 0);
        let result = solver.make_fma(&one, &one, &neg_one, rm);
        let model = solve_fp_clauses(&solver);
        let (sign, exp, sig) = extract_fp(&model, &result);
        assert!(
            !sign,
            "fma cancel under {rm:?} must give +0, got sign={sign}"
        );
        assert_eq!(exp, 0, "{rm:?}");
        assert_eq!(sig, 0, "{rm:?}");
    }
}

#[test]
fn test_fp16_fma_exact_cancel_sign_negative_zero_rtn() {
    let terms = TermStore::new();
    let mut solver = FpSolver::new(&terms);
    let one = make_concrete_f16(&mut solver, false, 0b01111, 0);
    let neg_one = make_concrete_f16(&mut solver, true, 0b01111, 0);
    let result = solver.make_fma(&one, &one, &neg_one, RoundingMode::RTN);
    let model = solve_fp_clauses(&solver);
    let (sign, exp, sig) = extract_fp(&model, &result);
    assert!(sign, "fma cancel under RTN must give -0");
    assert_eq!(exp, 0);
    assert_eq!(sig, 0);
}

#[test]
fn test_fp16_add_pos_zero_neg_nan_is_canonical_nan() {
    let terms = TermStore::new();
    let mut solver = FpSolver::new(&terms);
    let pos_zero = make_concrete_f16(&mut solver, false, 0, 0);
    let neg_nan = make_concrete_f16(&mut solver, true, 0b11111, 0b1000000000);
    let result = solver.make_add(&pos_zero, &neg_nan, RoundingMode::RNE);
    let is_nan = solver.is_nan(&result);
    solver.add_clause(CnfClause::unit(is_nan));
    let model = solve_fp_clauses(&solver);
    let (sign, exp, sig) = extract_fp(&model, &result);
    assert!(!sign, "canonical NaN should clear the sign bit");
    assert_eq!(exp, 0b11111);
    assert_eq!(sig, 0b1000000000);
}

// fp.rem with a SUBNORMAL divisor: the shifted dividend `a_sig << 3 << exp_diff`
// must not overflow the dividend bitvector. A subnormal `y` drives `exp_diff` to
// its maximum (`2^eb + sb - 4`); the old dividend width truncated the shift and
// produced a wrong-signed/wrong-magnitude remainder (rank6_qf_fp_false_SAT).
//
// All expected values below are the IEEE-754 remainder confirmed by z3 (and cvc5
// with --fp-exp) get-value.

#[test]
fn test_fp16_rem_subnormal_divisor_positive_result() {
    // x = (fp #b1 #b11110 #b1111100110) (negative normal, |x| = 64704)
    // y = (fp #b1 #b00000 #b1001101111) (negative subnormal)
    // IEEE rem = (fp #b0 #b00000 #b0100000111)  (positive subnormal, +263 * 2^-24)
    let terms = TermStore::new();
    let mut solver = FpSolver::new(&terms);
    let x = make_concrete_f16(&mut solver, true, 0b11110, 0b1111100110);
    let y = make_concrete_f16(&mut solver, true, 0b00000, 0b1001101111);
    let result = solver.make_rem(&x, &y);
    let model = solve_fp_clauses(&solver);
    let (sign, exp, sig) = extract_fp(&model, &result);
    assert!(!sign, "rem must be positive (z3 == cvc5)");
    assert_eq!(exp, 0b00000);
    assert_eq!(sig, 0b0100000111);
}

#[test]
fn test_fp16_rem_subnormal_divisor_negative_result() {
    // x = (fp #b1 #b11110 #b1011111101) (negative normal)
    // y = (fp #b1 #b00000 #b0000101010) (negative subnormal)
    // IEEE rem = (fp #b1 #b00000 #b0000000010)  (negative subnormal, -2 * 2^-24)
    // Guards against the fix over-correcting every subnormal-divisor rem to positive.
    let terms = TermStore::new();
    let mut solver = FpSolver::new(&terms);
    let x = make_concrete_f16(&mut solver, true, 0b11110, 0b1011111101);
    let y = make_concrete_f16(&mut solver, true, 0b00000, 0b0000101010);
    let result = solver.make_rem(&x, &y);
    let model = solve_fp_clauses(&solver);
    let (sign, exp, sig) = extract_fp(&model, &result);
    assert!(sign, "rem must be negative (z3 == cvc5)");
    assert_eq!(exp, 0b00000);
    assert_eq!(sig, 0b0000000010);
}
