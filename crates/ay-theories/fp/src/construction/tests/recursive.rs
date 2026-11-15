// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use ay_core::{Sort, Symbol, TermId};
use num_bigint::BigInt;

fn division(terms: &mut TermStore) -> (TermId, TermId, TermId) {
    let sort = Sort::FloatingPoint(5, 11);
    let x = terms.mk_var("x", sort.clone());
    let y = terms.mk_var("y", sort.clone());
    let rm = terms.mk_var("RNE", Sort::Uninterpreted("RoundingMode".to_string()));
    let div = terms.mk_app(Symbol::named("fp.div"), [rm, x, y], sort);
    (div, rm, x)
}

fn nested_ite(terms: &mut TermStore) -> TermId {
    let (div, _, _) = division(terms);
    let condition = terms.mk_app(Symbol::named("fp.isZero"), [div], Sort::Bool);
    let left = terms.mk_var("left", Sort::bitvec(16));
    let right = terms.mk_var("right", Sort::bitvec(16));
    let bits = terms.mk_ite_raw(condition, left, right);
    terms.mk_app(
        Symbol::indexed("to_fp", vec![5, 11]),
        [bits],
        Sort::FloatingPoint(5, 11),
    )
}

fn assert_division_stop(terms: &TermStore, root: TermId) {
    let rows = Cell::new(0);
    let terms_seen = Cell::new(0);
    let calls = Cell::new(0);
    let mut stop = |progress: FpBuildProgress| {
        calls.set(calls.get() + 1);
        if progress.stage == FpBuildStage::Term {
            terms_seen.set(terms_seen.get() + 1);
        }
        if progress.stage == FpBuildStage::DivideRow {
            rows.set(rows.get() + 1);
            if rows.get() == 4 {
                assert!(progress.clauses > 0);
                return true;
            }
        }
        false
    };
    let mut attempt = FpConstruction::new(FpSolver::new(terms), &mut stop).unwrap();
    assert!(matches!(
        attempt.try_get_fp(root),
        Err(FpBuildError::Interrupted)
    ));
    assert_eq!(rows.get(), 4);
    assert!(terms_seen.get() > 2);
    let stopped_calls = calls.get();
    assert!(matches!(
        attempt.try_has_encoding_gap(),
        Err(FpBuildError::Interrupted)
    ));
    assert!(matches!(attempt.finish(), Err(FpBuildError::Interrupted)));
    assert_eq!(calls.get(), stopped_calls);
}

#[test]
fn cancellation_crosses_fp_conversion_bv_ite_and_boolean_predicate_recursion() {
    let mut terms = TermStore::new();
    let root = nested_ite(&mut terms);
    assert_division_stop(&terms, root);
}

#[test]
fn optimized_division_and_fma_do_not_drop_control_for_recursive_operands() {
    let mut terms = TermStore::new();
    let (div, rm, x) = division(&mut terms);
    let bits = terms.mk_bitvec(BigInt::from(0x4000), 16); // f16 +2.0
    let two = terms.mk_app(
        Symbol::indexed("to_fp", vec![5, 11]),
        [bits],
        Sort::FloatingPoint(5, 11),
    );
    let scaled = terms.mk_app(
        Symbol::named("fp.div"),
        [rm, div, two],
        Sort::FloatingPoint(5, 11),
    );
    let zero = terms.mk_app(Symbol::named("+zero"), [], Sort::FloatingPoint(5, 11));
    let fma = terms.mk_app(
        Symbol::named("fp.fma"),
        [rm, zero, div, x],
        Sort::FloatingPoint(5, 11),
    );
    for root in [scaled, fma] {
        assert_division_stop(&terms, root);
    }
}

#[test]
fn recursive_term_encoding_preserves_legacy_cnf_and_complete_cache() {
    let mut terms = TermStore::new();
    let root = nested_ite(&mut terms);
    let mut legacy = FpSolver::new(&terms);
    let expected = legacy.get_fp(root);
    let expected_cache = legacy.export_cache();
    let mut allow = |_| false;
    let mut attempt = FpConstruction::new(FpSolver::new(&terms), &mut allow).unwrap();
    let actual = attempt.try_get_fp(root).unwrap();
    let built = attempt.finish().unwrap();
    parity::assert_fp(&actual, &expected);
    parity::assert_cache(&built.cache, &expected_cache);
    assert_eq!(built.clauses.as_slice(), legacy.clauses());
    assert_eq!(built.has_encoding_gap, legacy.has_encoding_gap());
    assert_eq!(
        built.pending_condition_links,
        legacy.pending_condition_links
    );
}

#[test]
fn a_cached_term_still_checks_the_live_stop_before_copying_or_admitting() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::FloatingPoint(5, 11));
    let enabled = Cell::new(false);
    let mut stop =
        |progress: FpBuildProgress| enabled.get() && progress.stage == FpBuildStage::Term;
    let mut attempt = FpConstruction::new(FpSolver::new(&terms), &mut stop).unwrap();
    attempt.try_get_fp(x).unwrap();
    enabled.set(true);
    assert!(matches!(
        attempt.try_get_fp(x),
        Err(FpBuildError::Interrupted)
    ));
    assert!(matches!(attempt.finish(), Err(FpBuildError::Interrupted)));
}

#[test]
fn semantic_gap_snapshots_preserve_the_base_and_later_gap_distinction() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Bool);
    let opaque = terms.mk_app(Symbol::named("opaque"), [x], Sort::Bool);
    let mut allow = |_| false;
    let mut attempt = FpConstruction::new(FpSolver::new(&terms), &mut allow).unwrap();
    let base_gap = attempt.try_has_encoding_gap().unwrap();
    attempt.try_encode_bool_condition(opaque).unwrap();
    let later_gap = attempt.try_has_encoding_gap().unwrap();
    assert!(!base_gap);
    assert!(later_gap);
    assert!(attempt.finish().unwrap().has_encoding_gap);
}

#[test]
fn unsupported_bv_predicate_and_interruption_remain_distinct_results() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::bitvec(8));
    let opaque = terms.mk_app(Symbol::named("opaque"), [x], Sort::Bool);
    let mut allow = |_| false;
    let mut attempt = FpConstruction::new(FpSolver::new(&terms), &mut allow).unwrap();
    assert_eq!(attempt.try_bitblast_bv_predicate(opaque).unwrap(), None);
    assert!(attempt.finish().is_ok());

    let mut stop = |p: FpBuildProgress| p.stage == FpBuildStage::Term;
    let mut attempt = FpConstruction::new(FpSolver::new(&terms), &mut stop).unwrap();
    assert!(matches!(
        attempt.try_bitblast_bv_predicate(opaque),
        Err(FpBuildError::Interrupted)
    ));
    assert!(matches!(attempt.finish(), Err(FpBuildError::Interrupted)));
}
