// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::RM_ORDER;
use ay_core::{Sort, Symbol, TermId};
use std::time::{Duration, Instant};

#[path = "sqrt/reference.rs"]
mod reference;
#[path = "sqrt/semantics.rs"]
mod semantics;
#[path = "sqrt/support.rs"]
mod support;

fn root(terms: &mut TermStore, eb: u32, sb: u32, mode: RoundingMode) -> (TermId, TermId) {
    let sort = Sort::FloatingPoint(eb, sb);
    let x = terms.mk_var("original-free-sqrt-input", sort.clone());
    let rm = terms.mk_app(
        Symbol::named(mode.name()),
        [],
        Sort::Uninterpreted("RoundingMode".into()),
    );
    (terms.mk_app(Symbol::named("fp.sqrt"), [rm, x], sort), x)
}

#[test]
fn native_free_input_sqrt_operation_refusal_is_sticky_after_real_frontier_growth() {
    let end = Instant::now() + Duration::from_secs(20);
    for (eb, sb) in [(5, 11), (8, 24), (2, 6)] {
        let mut terms = TermStore::new();
        let (sqrt, _) = root(&mut terms, eb, sb, RoundingMode::RNE);
        let trace = RefCell::new(Vec::new());
        let raw = Cell::new(false);
        let operations = Cell::new(0);
        let mut stop = |p: FpBuildProgress| {
            trace.borrow_mut().push(p);
            if p.stage == FpBuildStage::Operation {
                operations.set(operations.get() + 1);
                if operations.get() == 16 {
                    raw.set(true);
                }
            }
            raw.get() || Instant::now() >= end
        };
        let mut attempt = FpConstruction::new(FpSolver::new(&terms), &mut stop).unwrap();
        assert!(matches!(
            attempt.try_get_fp(sqrt),
            Err(FpBuildError::Interrupted)
        ));
        assert_eq!(operations.get(), 16);
        let history = trace.borrow();
        assert_monotone(&history);
        let ops: Vec<_> = history
            .iter()
            .filter(|p| p.stage == FpBuildStage::Operation)
            .collect();
        assert!(ops[15].variables > ops[12].variables);
        assert!(ops[15].clauses > ops[12].clauses);
        assert!(
            history
                .iter()
                .filter(|p| p.stage == FpBuildStage::Term)
                .count()
                > 2
        );
        let calls = history.len();
        drop(ops);
        drop(history);
        raw.set(false);
        assert!(matches!(
            attempt.try_get_fp(sqrt),
            Err(FpBuildError::Interrupted)
        ));
        assert!(matches!(
            attempt.try_has_encoding_gap(),
            Err(FpBuildError::Interrupted)
        ));
        assert!(matches!(attempt.finish(), Err(FpBuildError::Interrupted)));
        assert_eq!(trace.borrow().len(), calls);
    }
}

#[test]
fn native_sqrt_final_publication_is_vetoed_before_and_after_solver_only_drop() {
    let end = Instant::now() + Duration::from_secs(20);
    for veto in [1, 2] {
        let mut terms = TermStore::new();
        let (sqrt, _) = root(&mut terms, 5, 11, RoundingMode::RTZ);
        let finals = Cell::new(0);
        let mut stop = |p: FpBuildProgress| {
            if p.stage == FpBuildStage::Finalize {
                finals.set(finals.get() + 1);
            }
            finals.get() == veto || Instant::now() >= end
        };
        let mut attempt = FpConstruction::new(FpSolver::new(&terms), &mut stop).unwrap();
        attempt.try_get_fp(sqrt).unwrap();
        assert!(matches!(attempt.finish(), Err(FpBuildError::Interrupted)));
        assert_eq!(finals.get(), veto);
    }
}

#[test]
fn native_sqrt_operation_exit_refuses_after_last_row_before_cache_publication() {
    let end = Instant::now() + Duration::from_secs(20);
    let mut terms = TermStore::new();
    let (sqrt, _) = root(&mut terms, 5, 11, RoundingMode::RNE);
    let seen = Cell::new(0);
    let last = Cell::new(0);
    let mut allow = |p: FpBuildProgress| {
        if p.stage == FpBuildStage::Operation {
            seen.set(seen.get() + 1);
            last.set(seen.get());
        }
        Instant::now() >= end
    };
    let mut healthy = FpConstruction::new(FpSolver::new(&terms), &mut allow).unwrap();
    healthy.try_get_fp(sqrt).unwrap();
    healthy.finish().unwrap();
    let exit = last.get();
    let calls = Cell::new(0);
    let operations = Cell::new(0);
    let raw = Cell::new(true);
    let mut stop = |p: FpBuildProgress| {
        calls.set(calls.get() + 1);
        if p.stage == FpBuildStage::Operation {
            operations.set(operations.get() + 1);
        }
        (raw.get() && operations.get() == exit) || Instant::now() >= end
    };
    let mut refused = FpConstruction::new(FpSolver::new(&terms), &mut stop).unwrap();
    assert!(matches!(
        refused.try_get_fp(sqrt),
        Err(FpBuildError::Interrupted)
    ));
    assert_eq!(operations.get(), exit);
    raw.set(false);
    let prior = calls.get();
    assert!(matches!(refused.finish(), Err(FpBuildError::Interrupted)));
    assert_eq!(calls.get(), prior);
}

#[test]
fn native_sqrt_callback_unwind_during_advanced_operations_forbids_recovery() {
    let end = Instant::now() + Duration::from_secs(20);
    let mut terms = TermStore::new();
    let (sqrt, _) = root(&mut terms, 5, 11, RoundingMode::RNA);
    let calls = Cell::new(0);
    let operations = Cell::new(0);
    let panic_enabled = Cell::new(true);
    let mut stop = |p: FpBuildProgress| {
        calls.set(calls.get() + 1);
        if p.stage == FpBuildStage::Operation {
            operations.set(operations.get() + 1);
            if operations.get() == 16 && panic_enabled.get() {
                assert!(p.clauses > 0);
                panic!("original sqrt callback after advanced circuit operations");
            }
        }
        Instant::now() >= end
    };
    let mut attempt = FpConstruction::new(FpSolver::new(&terms), &mut stop).unwrap();
    assert!(catch_unwind(AssertUnwindSafe(|| attempt.try_get_fp(sqrt))).is_err());
    panic_enabled.set(false);
    let prior = calls.get();
    assert!(matches!(
        attempt.try_get_fp(sqrt),
        Err(FpBuildError::Interrupted)
    ));
    assert!(matches!(attempt.finish(), Err(FpBuildError::Interrupted)));
    assert_eq!(calls.get(), prior);
}

#[test]
fn healthy_native_sqrt_matches_frozen_original_gate_order_and_complete_cache() {
    let end = Instant::now() + Duration::from_secs(20);
    for (eb, sb) in [(5, 11), (2, 3), (3, 8)] {
        for mode in RM_ORDER {
            let mut terms = TermStore::new();
            let (sqrt, x_term) = root(&mut terms, eb, sb, mode);
            let mut old = FpSolver::new(&terms);
            let x = old.get_fp(x_term);
            let expected = old.legacy_make_sqrt(&x, mode);
            // This is the exact old caller's cache insertion, not a second
            // native solve, and gate inputs use the same initial namespace.
            old.term_to_fp.insert(sqrt, expected.clone());
            let expected_cache = old.export_cache();
            let mut stop = |_| Instant::now() >= end;
            let mut attempt = FpConstruction::new(FpSolver::new(&terms), &mut stop).unwrap();
            let actual = attempt.try_get_fp(sqrt).unwrap();
            let built = attempt.finish().unwrap();
            parity::assert_fp(&actual, &expected);
            parity::assert_cache(&built.cache, &expected_cache);
            assert_eq!(built.clauses.as_slice(), old.clauses());
            assert_eq!(built.pending_condition_links, old.pending_condition_links);
            assert_eq!(built.has_encoding_gap, old.has_encoding_gap());
            drop((built, old, expected_cache));
            assert!(Instant::now() < end);
        }
    }
}

#[test]
fn observed_sqrt_refusal_requires_an_explicit_fresh_owning_attempt_for_recovery() {
    let end = Instant::now() + Duration::from_secs(20);
    let mut terms = TermStore::new();
    let (sqrt, _) = root(&mut terms, 5, 11, RoundingMode::RTP);
    let enabled = Cell::new(true);
    let operations = Cell::new(0);
    let mut stop = |p: FpBuildProgress| {
        if p.stage == FpBuildStage::Operation {
            operations.set(operations.get() + 1);
        }
        (enabled.get() && operations.get() == 16) || Instant::now() >= end
    };
    let mut old = FpConstruction::new(FpSolver::new(&terms), &mut stop).unwrap();
    assert!(matches!(
        old.try_get_fp(sqrt),
        Err(FpBuildError::Interrupted)
    ));
    enabled.set(false);
    assert!(matches!(old.finish(), Err(FpBuildError::Interrupted)));
    let mut fresh = FpConstruction::new(FpSolver::new(&terms), &mut stop).unwrap();
    fresh.try_get_fp(sqrt).unwrap();
    let built = fresh.finish().unwrap();
    assert!(!built.has_encoding_gap);
    assert_ne!(built.clauses.len(), 0);
}
