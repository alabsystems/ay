// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::FpEncodingCache;

pub(super) fn assert_fp(actual: &FpDecomposed, expected: &FpDecomposed) {
    assert_eq!(actual.sign, expected.sign);
    assert_eq!(actual.exponent, expected.exponent);
    assert_eq!(actual.significand, expected.significand);
    assert_eq!(actual.precision, expected.precision);
}

pub(super) fn assert_cache(actual: &FpEncodingCache, expected: &FpEncodingCache) {
    let FpEncodingCache {
        term_to_fp,
        bv_term_bits,
        next_var,
        cached_false,
        cached_true,
        bool_input_lits,
        to_bv_unspec_sites,
        ieee_nan_encodings,
        rm_terms,
    } = actual;
    assert_eq!(term_to_fp.len(), expected.term_to_fp.len());
    for (term, fp) in term_to_fp {
        assert_fp(fp, &expected.term_to_fp[term]);
    }
    assert_eq!(bv_term_bits, &expected.bv_term_bits);
    assert_eq!(*next_var, expected.next_var);
    assert_eq!(*cached_false, expected.cached_false);
    assert_eq!(*cached_true, expected.cached_true);
    assert_eq!(bool_input_lits, &expected.bool_input_lits);
    assert_eq!(ieee_nan_encodings, &expected.ieee_nan_encodings);
    assert_eq!(rm_terms, &expected.rm_terms);
    assert_eq!(to_bv_unspec_sites.len(), expected.to_bv_unspec_sites.len());
    for (site, expected) in to_bv_unspec_sites.iter().zip(&expected.to_bv_unspec_sites) {
        assert_fp(&site.input, &expected.input);
        assert_eq!(site.unspec, expected.unspec);
        assert_eq!(site.is_signed, expected.is_signed);
    }
}

#[test]
fn fresh_native_attempt_matches_complete_uninterrupted_legacy_encoding() {
    let terms = TermStore::new();
    let precision = FpPrecision::Float16;
    // First reject an actual partially built attempt; the next owner starts
    // with a new solver, not a reset token on the rejected transaction.
    interrupt_after_two_progressing_rows(precision, FpBuildStage::DivideRow);
    let (mut legacy, old_x, old_y) = symbolic(&terms, precision);
    let old_div = legacy.make_div(&old_x, &old_y, RoundingMode::RTP);
    let old_rem = legacy.make_rem(&old_x, &old_y);
    let expected_cache = legacy.export_cache();

    let (solver, x, y) = symbolic(&terms, precision);
    let trace = RefCell::new(Vec::new());
    let mut stop = |progress| {
        trace.borrow_mut().push(progress);
        false
    };
    let mut transaction = FpConstruction::new(solver, &mut stop).unwrap();
    let div = transaction.try_make_div(&x, &y, RoundingMode::RTP).unwrap();
    let rem = transaction.try_make_rem(&x, &y).unwrap();
    let built = transaction.finish().unwrap();
    assert_fp(&div, &old_div);
    assert_fp(&rem, &old_rem);
    assert_eq!(built.clauses.as_slice(), legacy.clauses());
    assert_eq!(
        built.pending_condition_links,
        legacy.pending_condition_links
    );
    assert_eq!(built.has_encoding_gap, legacy.has_encoding_gap());
    assert_cache(&built.cache, &expected_cache);
    assert_monotone(&trace.borrow());
    assert_eq!(trace.borrow().last().unwrap().stage, FpBuildStage::Finalize);
    for stage in [FpBuildStage::DivideRow, FpBuildStage::RemainderExponent] {
        assert!(trace.borrow().iter().any(|p| p.stage == stage));
    }
    assert_eq!(trace.borrow().last().unwrap().clauses, built.clauses.len());
    assert_eq!(
        trace.borrow().last().unwrap().variables,
        built.cache.next_var - 1
    );
}

#[test]
fn completed_native_division_and_ieee_remainder_keep_existing_value_semantics() {
    use crate::tests_support::{extract_fp, make_concrete_f16};
    use ay_sat::{Literal, SatResult, Solver};

    // 3/2 is exactly 1.5. IEEE remainder uses the nearest EVEN quotient 2,
    // hence +3 rem +2 = -1 (not Rust's truncating remainder +1).
    for negative in [false, true] {
        let terms = TermStore::new();
        let mut solver = FpSolver::new(&terms);
        let x = make_concrete_f16(&mut solver, negative, 16, 512);
        let y = make_concrete_f16(&mut solver, false, 16, 0);
        let mut stop = |_| false;
        let mut transaction = FpConstruction::new(solver, &mut stop).unwrap();
        let div = transaction.try_make_div(&x, &y, RoundingMode::RNE).unwrap();
        let rem = transaction.try_make_rem(&x, &y).unwrap();
        let built = transaction.finish().unwrap();
        assert!(!built.has_encoding_gap);
        let mut sat = Solver::new((built.cache.next_var - 1) as usize);
        for clause in &built.clauses {
            sat.add_clause(
                clause
                    .literals()
                    .iter()
                    .map(|&l| Literal::from_dimacs(l))
                    .collect(),
            );
        }
        let SatResult::Sat(model) = sat.solve().into_inner() else {
            panic!("completed concrete FP encoding must have a model");
        };
        assert_eq!(extract_fp(&model, &div), (negative, 15, 512));
        assert_eq!(extract_fp(&model, &rem), (!negative, 15, 0));
    }
}
