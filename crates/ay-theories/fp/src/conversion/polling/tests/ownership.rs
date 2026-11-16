// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use std::panic::{catch_unwind, AssertUnwindSafe};

#[derive(Debug, PartialEq)]
struct Refusal;
struct Deny;
impl BuildControl for Deny {
    type Error = Refusal;
    fn checkpoint(&mut self, _: FpBuildProgress) -> Result<(), Refusal> {
        Err(Refusal)
    }
}

struct AfterGrowth<'a> {
    end: Instant,
    enclosing: &'a Option<ay_core::resource::CheckStop>,
    frontier: u32,
    advances: usize,
}
impl BuildControl for AfterGrowth<'_> {
    type Error = Refusal;
    fn checkpoint(&mut self, progress: FpBuildProgress) -> Result<(), Refusal> {
        if progress.variables > self.frontier {
            self.frontier = progress.variables;
            self.advances += 1;
        }
        if stopped(self.end, self.enclosing) || self.advances >= 2 {
            Err(Refusal)
        } else {
            Ok(())
        }
    }
}

#[test]
fn both_barrel_directions_refuse_after_real_owned_stages() {
    let (end, enclosing) = frame();
    for left in [false, true] {
        let terms = TermStore::new();
        let mut solver = FpSolver::new(&terms);
        let word: Vec<_> = (0..64).map(|_| solver.fresh_var()).collect();
        let amount: Vec<_> = (0..64).map(|_| solver.fresh_var()).collect();
        solver.const_false();
        let mut control = AfterGrowth {
            end,
            enclosing: &enclosing,
            frontier: solver.num_vars(),
            advances: 0,
        };
        let result = if left {
            solver.bv_shl_with_control(&word, &amount, &mut control)
        } else {
            solver.conversion_lshr_with_control(&word, &amount, &mut control)
        };
        assert_eq!(result, Err(Refusal));
        assert_eq!(control.advances, 2);
        assert!(solver.num_vars() > 128);
        assert_ne!(solver.clauses().len(), 0);
    }
}

#[test]
fn typed_row_refusal_precedes_any_helper_allocation() {
    let terms = TermStore::new();
    let mut solver = FpSolver::new(&terms);
    for operation in 0..3 {
        let mut control = Deny;
        let result = match operation {
            0 => solver.conversion_lz_with_control(&[], 13, &mut control),
            1 => solver.bv_shl_with_control(&[], &[], &mut control),
            _ => solver.conversion_lshr_with_control(&[], &[], &mut control),
        };
        assert_eq!(result, Err(Refusal));
        assert_eq!(solver.num_vars(), 0);
        assert_eq!(solver.clauses().len(), 0);
    }
}

#[test]
fn conversion_row_refusal_remains_sticky_after_external_reset() {
    let (end, enclosing) = frame();
    for signed in [false, true] {
        let (terms, _, _, result) =
            fixture(signed, FpPrecision::Float64, 64, Some(RoundingMode::RNE));
        let last = Cell::new(0);
        let advances = Cell::new(0);
        let calls = Cell::new(0);
        let enabled = Cell::new(true);
        let mut stop = |p: FpBuildProgress| {
            calls.set(calls.get() + 1);
            if p.stage == FpBuildStage::Operation && p.variables > last.get() {
                advances.set(advances.get() + 1);
                last.set(p.variables);
            }
            stopped(end, &enclosing) || (enabled.get() && advances.get() >= 3)
        };
        let mut attempt = FpConstruction::new(FpSolver::new(&terms), &mut stop).unwrap();
        assert!(matches!(
            attempt.try_get_fp(result),
            Err(FpBuildError::Interrupted)
        ));
        assert_eq!(advances.get(), 3);
        let before = calls.get();
        enabled.set(false);
        assert!(matches!(
            attempt.try_get_fp(result),
            Err(FpBuildError::Interrupted)
        ));
        assert!(matches!(attempt.finish(), Err(FpBuildError::Interrupted)));
        assert_eq!(calls.get(), before);
    }
}

#[test]
fn conversion_callback_panic_cannot_publish_or_retry() {
    let (end, enclosing) = frame();
    let (terms, _, _, result) = fixture(true, FpPrecision::Float64, 64, Some(RoundingMode::RNE));
    let armed = Cell::new(true);
    let mut stop = |p: FpBuildProgress| {
        assert!(
            !(armed.get() && p.stage == FpBuildStage::Operation && p.variables > 64),
            "original callback"
        );
        stopped(end, &enclosing)
    };
    let mut attempt = FpConstruction::new(FpSolver::new(&terms), &mut stop).unwrap();
    assert!(catch_unwind(AssertUnwindSafe(|| attempt.try_get_fp(result))).is_err());
    armed.set(false);
    assert!(matches!(
        attempt.try_get_fp(result),
        Err(FpBuildError::Interrupted)
    ));
    assert!(matches!(attempt.finish(), Err(FpBuildError::Interrupted)));
}

#[test]
fn final_owner_veto_withholds_complete_numeric_data() {
    let (end, enclosing) = frame();
    let (terms, _, _, result) = fixture(false, FpPrecision::Float64, 64, Some(RoundingMode::RNE));
    let enabled = Cell::new(false);
    let mut stop = |p: FpBuildProgress| {
        stopped(end, &enclosing) || (enabled.get() && p.stage == FpBuildStage::Finalize)
    };
    let mut attempt = FpConstruction::new(FpSolver::new(&terms), &mut stop).unwrap();
    attempt.try_get_fp(result).unwrap();
    enabled.set(true);
    assert!(matches!(attempt.finish(), Err(FpBuildError::Interrupted)));
}
