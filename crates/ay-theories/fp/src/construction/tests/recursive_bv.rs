// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use ay_core::{Sort, Symbol, TermId};
use num_bigint::BigInt;

struct BvFixture {
    terms: TermStore,
    predicate: TermId,
    converted: TermId,
}

impl BvFixture {
    fn new(operator: &str) -> Self {
        let mut terms = TermStore::new();
        let left = terms.mk_var("left", Sort::bitvec(8));
        let right = terms.mk_var("right", Sort::bitvec(8));
        let value = terms.mk_app(Symbol::named(operator), [left, right], Sort::bitvec(8));
        let zero = terms.mk_bitvec(BigInt::from(0), 8);
        let predicate = terms.mk_app(Symbol::named("="), [value, zero], Sort::Bool);
        let rm = terms.mk_var("RNE", Sort::Uninterpreted("RoundingMode".to_string()));
        let converted = terms.mk_app(
            Symbol::indexed("to_fp", vec![5, 11]),
            [rm, value],
            Sort::FloatingPoint(5, 11),
        );
        Self {
            terms,
            predicate,
            converted,
        }
    }
}

#[derive(Clone, Copy)]
enum Entry {
    Predicate,
    Conversion,
}

fn enter(
    attempt: &mut FpConstruction<'_, '_>,
    fixture: &BvFixture,
    entry: Entry,
) -> Result<(), FpBuildError> {
    match entry {
        Entry::Predicate => {
            let result = attempt.try_bitblast_bv_predicate(fixture.predicate)?;
            assert!(result.is_some(), "supported BV predicate must not decline");
        }
        Entry::Conversion => {
            attempt.try_get_fp(fixture.converted)?;
        }
    }
    Ok(())
}

fn stop_inside_rows(operator: &str, stage: FpBuildStage, entry: Entry) {
    let fixture = BvFixture::new(operator);
    let rows = Cell::new(0);
    let enabled = Cell::new(true);
    let trace = RefCell::new(Vec::new());
    let first = Cell::new(None::<(u32, usize)>);
    let mut stop = |p: FpBuildProgress| {
        trace.borrow_mut().push(p);
        if p.stage == stage {
            rows.set(rows.get() + 1);
            if rows.get() == 1 {
                first.set(Some((p.variables, p.clauses)));
            }
            if rows.get() == 4 {
                let (variables, clauses) = first.get().unwrap();
                assert!(p.variables > variables && p.clauses > clauses);
                return enabled.get();
            }
        }
        false
    };
    let mut attempt = FpConstruction::new(FpSolver::new(&fixture.terms), &mut stop).unwrap();
    assert!(matches!(
        enter(&mut attempt, &fixture, entry),
        Err(FpBuildError::Interrupted)
    ));
    assert_eq!(rows.get(), 4); // Entry plus three row starts: two completed rows.
    assert_monotone(&trace.borrow());
    assert!(
        trace
            .borrow()
            .iter()
            .filter(|p| p.stage == FpBuildStage::Term)
            .count()
            > 2
    );
    let calls = trace.borrow().len();
    enabled.set(false);
    assert!(matches!(
        enter(&mut attempt, &fixture, entry),
        Err(FpBuildError::Interrupted)
    ));
    assert!(matches!(
        attempt.try_has_encoding_gap(),
        Err(FpBuildError::Interrupted)
    ));
    assert!(matches!(attempt.finish(), Err(FpBuildError::Interrupted)));
    assert_eq!(trace.borrow().len(), calls);
}

#[test]
fn all_bv_division_families_cancel_inside_conversion_and_predicate_recursion() {
    for operator in ["bvudiv", "bvurem", "bvsdiv", "bvsrem", "bvsmod"] {
        for entry in [Entry::Predicate, Entry::Conversion] {
            stop_inside_rows(operator, FpBuildStage::DivideRow, entry);
        }
    }
}

#[test]
fn bv_multiplication_cancels_inside_conversion_and_predicate_recursion() {
    for entry in [Entry::Predicate, Entry::Conversion] {
        stop_inside_rows("bvmul", FpBuildStage::MultiplyRow, entry);
    }
}

#[test]
fn allowed_recursive_bv_encodings_preserve_every_clause_and_cached_decomposition() {
    for operator in ["bvudiv", "bvurem", "bvsdiv", "bvsrem", "bvsmod", "bvmul"] {
        let fixture = BvFixture::new(operator);
        let mut legacy = FpSolver::new(&fixture.terms);
        let expected_predicate = legacy.bitblast_bv_predicate(fixture.predicate).unwrap();
        let expected_fp = legacy.get_fp(fixture.converted);
        let expected_cache = legacy.export_cache();
        assert!(!legacy.has_encoding_gap());
        let trace = RefCell::new(Vec::new());
        let mut allow = |p| {
            trace.borrow_mut().push(p);
            false
        };
        let mut attempt = FpConstruction::new(FpSolver::new(&fixture.terms), &mut allow).unwrap();
        assert_eq!(
            attempt
                .try_bitblast_bv_predicate(fixture.predicate)
                .unwrap(),
            Some(expected_predicate)
        );
        let actual = attempt.try_get_fp(fixture.converted).unwrap();
        assert!(!attempt.try_has_encoding_gap().unwrap());
        let built = attempt.finish().unwrap();
        parity::assert_fp(&actual, &expected_fp);
        parity::assert_cache(&built.cache, &expected_cache);
        assert_eq!(built.clauses.as_slice(), legacy.clauses());
        assert_eq!(
            built.pending_condition_links,
            legacy.pending_condition_links
        );
        assert!(!built.has_encoding_gap);
        assert_monotone(&trace.borrow());
        let stage = if operator == "bvmul" {
            FpBuildStage::MultiplyRow
        } else {
            FpBuildStage::DivideRow
        };
        assert!(trace.borrow().iter().any(|p| p.stage == stage));
    }
}

#[derive(Clone, Copy)]
enum Conversion {
    Signed,
    Ieee,
}

fn conversion_fixture(conversion: Conversion) -> (TermStore, TermId, TermId, TermId) {
    let mut terms = TermStore::new();
    let first = terms.mk_var("first", Sort::FloatingPoint(5, 11));
    let second = terms.mk_var("second", Sort::FloatingPoint(5, 11));
    let (value, width) = match conversion {
        Conversion::Signed => {
            let rm = terms.mk_var("RTZ", Sort::Uninterpreted("RoundingMode".to_string()));
            (
                terms.mk_app(
                    Symbol::indexed("fp.to_sbv", vec![8]),
                    [rm, second],
                    Sort::bitvec(8),
                ),
                8,
            )
        }
        Conversion::Ieee => (
            terms.mk_app(Symbol::named("fp.to_ieee_bv"), [second], Sort::bitvec(16)),
            16,
        ),
    };
    let zero = terms.mk_bitvec(BigInt::from(0), width);
    let predicate = terms.mk_app(Symbol::named("="), [value, zero], Sort::Bool);
    (terms, first, second, predicate)
}

fn prepared_conversion(terms: &TermStore, first: TermId, conversion: Conversion) -> FpSolver<'_> {
    let mut solver = FpSolver::new(terms);
    match conversion {
        Conversion::Signed => {
            solver.bitblast_to_bv(first, RoundingMode::RTZ, 8, true);
            assert_eq!(solver.to_bv_unspec_sites.len(), 1);
        }
        Conversion::Ieee => {
            solver.bitblast_to_ieee_bv(first);
            assert_eq!(solver.ieee_nan_encodings.len(), 1);
        }
    }
    assert!(!solver.has_encoding_gap());
    solver
}

#[test]
fn later_conversion_site_refusal_cannot_become_unsupported_or_publish_prior_cache() {
    for conversion in [Conversion::Signed, Conversion::Ieee] {
        let (terms, first, _, predicate) = conversion_fixture(conversion);
        let solver = prepared_conversion(&terms, first, conversion);
        let initial_clauses = solver.clauses().len();
        let initial_variables = solver.num_vars();
        let enabled = Cell::new(false);
        let calls = Cell::new(0);
        let mut stop = |p: FpBuildProgress| {
            calls.set(calls.get() + 1);
            // The second FP leaf alone creates no clauses. This stops only
            // after the actual second conversion emits gates, at a term/cache
            // boundary, with a complete first-site cache already owned.
            enabled.get()
                && p.stage == FpBuildStage::Term
                && p.clauses > initial_clauses
                && p.variables > initial_variables
        };
        let mut attempt = FpConstruction::new(solver, &mut stop).unwrap();
        assert!(!attempt.try_has_encoding_gap().unwrap());
        enabled.set(true);
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
        assert!(matches!(
            attempt.try_has_encoding_gap(),
            Err(FpBuildError::Interrupted)
        ));
        assert!(matches!(attempt.finish(), Err(FpBuildError::Interrupted)));
        assert_eq!(calls.get(), stopped);

        let mut legacy = prepared_conversion(&terms, first, conversion);
        let expected = legacy.bitblast_bv_predicate(predicate).unwrap();
        let expected_cache = legacy.export_cache();
        let mut allow = |_| false;
        let mut fresh =
            FpConstruction::new(prepared_conversion(&terms, first, conversion), &mut allow)
                .unwrap();
        assert_eq!(
            fresh.try_bitblast_bv_predicate(predicate).unwrap(),
            Some(expected)
        );
        assert!(!fresh.try_has_encoding_gap().unwrap());
        let built = fresh.finish().unwrap();
        parity::assert_cache(&built.cache, &expected_cache);
        assert_eq!(built.clauses.as_slice(), legacy.clauses());
        assert!(!built.has_encoding_gap);
        match conversion {
            Conversion::Signed => assert_eq!(built.cache.to_bv_unspec_sites.len(), 2),
            Conversion::Ieee => assert_eq!(built.cache.ieee_nan_encodings.len(), 1),
        }
    }
}
