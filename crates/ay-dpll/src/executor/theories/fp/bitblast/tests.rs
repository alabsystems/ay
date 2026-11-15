// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use std::cell::Cell;

use ay_core::{Symbol, TermStore};
use ay_fp::{FpBuildError, FpBuildProgress, FpBuildStage, FpConstruction};

use super::*;

fn verdict(result: FpPredicateResult) -> (u8, i32) {
    match result {
        FpPredicateResult::Bitblasted(lit) => (0, lit),
        FpPredicateResult::NotFpPredicate => (1, 0),
        FpPredicateResult::Unsupported => (2, 0),
    }
}

#[test]
fn owning_predicate_dispatch_matches_all_legacy_classifications_and_clauses() {
    let mut terms = TermStore::new();
    let fp_sort = Sort::FloatingPoint(5, 11);
    let x = terms.mk_var("x", fp_sort.clone());
    let y = terms.mk_var("y", fp_sort.clone());
    let a = terms.mk_var("a", Sort::bitvec(8));
    let b = terms.mk_var("b", Sort::bitvec(8));
    let c = terms.mk_var("c", Sort::bitvec(8));
    let plain = terms.mk_var("plain", Sort::Bool);
    let mut cases = Vec::new();
    for name in ["fp.eq", "fp.lt", "fp.leq", "fp.gt", "fp.geq", "="] {
        cases.push((terms.mk_app(Symbol::named(name), [x, y], Sort::Bool), 0));
    }
    for name in [
        "fp.isNaN",
        "fp.isInfinite",
        "fp.isZero",
        "fp.isNormal",
        "fp.isSubnormal",
        "fp.isPositive",
        "fp.isNegative",
    ] {
        cases.push((terms.mk_app(Symbol::named(name), [x], Sort::Bool), 0));
    }
    for name in [
        "=", "distinct", "bvult", "bvule", "bvugt", "bvuge", "bvslt", "bvsle", "bvsgt", "bvsge",
    ] {
        cases.push((terms.mk_app(Symbol::named(name), [a, b], Sort::Bool), 0));
    }
    cases.push((
        terms.mk_app(Symbol::named("distinct"), [a, b, c], Sort::Bool),
        2,
    ));
    cases.push((
        terms.mk_app(Symbol::named("fp.unknown"), [x], Sort::Bool),
        2,
    ));
    cases.push((terms.mk_app(Symbol::named("fp.lt"), [x], Sort::Bool), 2));
    cases.push((terms.mk_app(Symbol::named("opaque"), [x], Sort::Bool), 1));
    cases.push((terms.mk_app(Symbol::named("fp.add"), [x], fp_sort), 1));
    cases.push((plain, 1));
    for (term, expected_kind) in cases {
        let mut legacy = FpSolver::new(&terms);
        let expected = verdict(backend::infallible(dispatch::dispatch(
            &terms,
            &mut legacy,
            term,
        )));
        assert_eq!(expected.0, expected_kind);
        let mut allow = |_| false;
        let mut owner = FpConstruction::new(FpSolver::new(&terms), &mut allow).unwrap();
        let actual = verdict(bitblast_fp_predicate_controlled(&terms, &mut owner, term).unwrap());
        let built = owner.finish().unwrap();
        assert_eq!(actual, expected);
        assert_eq!(built.clauses.as_slice(), legacy.clauses());
        assert_eq!(built.cache.next_var - 1, legacy.num_vars());
        assert_eq!(built.has_encoding_gap, legacy.has_encoding_gap());
    }
}

#[test]
fn real_nested_division_cancellation_is_not_an_unsupported_predicate() {
    let mut terms = TermStore::new();
    let sort = Sort::FloatingPoint(5, 11);
    let x = terms.mk_var("x", sort.clone());
    let y = terms.mk_var("y", sort.clone());
    let rm = terms.mk_var("RNE", Sort::Uninterpreted("RoundingMode".to_string()));
    let div = terms.mk_app(Symbol::named("fp.div"), [rm, x, y], sort);
    let predicate = terms.mk_app(Symbol::named("fp.lt"), [div, y], Sort::Bool);
    let rows = Cell::new(0);
    let calls = Cell::new(0);
    let mut stop = |p: FpBuildProgress| {
        calls.set(calls.get() + 1);
        if p.stage == FpBuildStage::DivideRow {
            rows.set(rows.get() + 1);
            if rows.get() == 4 {
                assert!(p.clauses > 0);
                return true;
            }
        }
        false
    };
    let mut owner = FpConstruction::new(FpSolver::new(&terms), &mut stop).unwrap();
    assert!(matches!(
        bitblast_fp_predicate_controlled(&terms, &mut owner, predicate),
        Err(FpBuildError::Interrupted)
    ));
    assert_eq!(rows.get(), 4);
    let stopped = calls.get();
    assert!(matches!(owner.finish(), Err(FpBuildError::Interrupted)));
    assert_eq!(calls.get(), stopped);
}

#[test]
fn skipped_and_unsupported_predicates_still_observe_the_same_sticky_owner() {
    let mut terms = TermStore::new();
    let plain = terms.mk_var("plain", Sort::Bool);
    let unknown = terms.mk_app(Symbol::named("fp.unknown"), [plain], Sort::Bool);
    for term in [plain, unknown] {
        let enabled = Cell::new(false);
        let mut stop = |_| enabled.get();
        let mut owner = FpConstruction::new(FpSolver::new(&terms), &mut stop).unwrap();
        enabled.set(true);
        assert!(matches!(
            bitblast_fp_predicate_controlled(&terms, &mut owner, term),
            Err(FpBuildError::Interrupted)
        ));
        enabled.set(false);
        assert!(matches!(owner.finish(), Err(FpBuildError::Interrupted)));
    }
}
