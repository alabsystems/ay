// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use crate::{FpBuildError, FpBuildStage, FpConstruction, FpSolver};
use ay_core::{Sort, Symbol, TermStore};
use std::cell::Cell;
use std::time::{Duration, Instant};

#[test]
fn reserved_truncating_dispatch_validates_arity_and_sorts_before_child_access() {
    let mut terms = TermStore::new();
    let sort = Sort::FloatingPoint(8, 24);
    let x = terms.mk_var("x", sort.clone());
    let b = terms.mk_var("b", Sort::Bool);
    let missing = terms.mk_app(Symbol::named("__ay_fp_truncating_rem"), [x], sort.clone());
    let wrong = terms.mk_app(Symbol::named("__ay_fp_truncating_rem"), [x, b], sort);
    let end = Instant::now() + Duration::from_secs(20);
    for root in [missing, wrong] {
        let mut stop = |_| Instant::now() >= end;
        let mut attempt = FpConstruction::new(FpSolver::new(&terms), &mut stop).unwrap();
        attempt.try_get_fp(root).unwrap();
        assert!(attempt.finish().unwrap().has_encoding_gap);
    }
}

#[test]
fn reserved_truncating_dispatch_keeps_the_original_recursive_row_refusal() {
    let mut terms = TermStore::new();
    let sort = Sort::FloatingPoint(11, 53);
    let x = terms.mk_var("x", sort.clone());
    let y = terms.mk_var("y", sort.clone());
    let root = terms.mk_app(Symbol::named("__ay_fp_truncating_rem"), [x, y], sort);
    let end = Instant::now() + Duration::from_secs(20);
    let rows = Cell::new(0);
    let raw = Cell::new(false);
    let mut stop = |p: crate::FpBuildProgress| {
        if p.stage == FpBuildStage::MultiplyRow {
            rows.set(rows.get() + 1);
            if rows.get() == 3 {
                assert!(p.clauses > 0);
                raw.set(true);
            }
        }
        raw.get() || Instant::now() >= end
    };
    let mut attempt = FpConstruction::new(FpSolver::new(&terms), &mut stop).unwrap();
    assert!(matches!(
        attempt.try_get_fp(root),
        Err(FpBuildError::Interrupted)
    ));
    assert_eq!(rows.get(), 3);
    raw.set(false);
    assert!(matches!(
        attempt.try_get_fp(root),
        Err(FpBuildError::Interrupted)
    ));
    assert!(matches!(attempt.finish(), Err(FpBuildError::Interrupted)));
}
