// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn native_fma_multiplier_rows_refuse_after_two_real_advances_and_reset_stays_sticky() {
    let end = Instant::now() + Duration::from_secs(20);
    for (eb, sb) in [(5, 11), (8, 24), (11, 53)] {
        let mut terms = TermStore::new();
        let (fma, _) = root(&mut terms, eb, sb, RoundingMode::RNE);
        let history = RefCell::new(Vec::new());
        let prior = Cell::new(None::<(u32, usize)>);
        let advances = Cell::new(0);
        let enabled = Cell::new(true);
        let mut stop = |p: FpBuildProgress| {
            history.borrow_mut().push(p);
            if p.stage == FpBuildStage::MultiplyRow {
                if let Some((vars, rows)) = prior.get() {
                    if p.variables > vars && p.clauses > rows {
                        advances.set(advances.get() + 1);
                    }
                }
                prior.set(Some((p.variables, p.clauses)));
            }
            (enabled.get() && advances.get() == 2) || Instant::now() >= end
        };
        let mut attempt = FpConstruction::new(FpSolver::new(&terms), &mut stop).unwrap();
        assert!(matches!(
            attempt.try_get_fp(fma),
            Err(FpBuildError::Interrupted)
        ));
        assert_eq!(advances.get(), 2);
        assert_eq!(
            history.borrow().last().unwrap().stage,
            FpBuildStage::MultiplyRow
        );
        assert_monotone(&history.borrow());
        let calls = history.borrow().len();
        enabled.set(false);
        assert!(matches!(
            attempt.try_get_fp(fma),
            Err(FpBuildError::Interrupted)
        ));
        assert!(matches!(
            attempt.try_has_encoding_gap(),
            Err(FpBuildError::Interrupted)
        ));
        assert!(matches!(attempt.finish(), Err(FpBuildError::Interrupted)));
        assert_eq!(history.borrow().len(), calls);
    }
}

#[test]
fn native_fma_callback_unwind_after_real_multiplier_rows_forbids_publication() {
    let end = Instant::now() + Duration::from_secs(20);
    let mut terms = TermStore::new();
    let (fma, _) = root(&mut terms, 5, 11, RoundingMode::RNA);
    let rows = Cell::new(0);
    let calls = Cell::new(0);
    let enabled = Cell::new(true);
    let mut stop = |p: FpBuildProgress| {
        calls.set(calls.get() + 1);
        if p.stage == FpBuildStage::MultiplyRow {
            rows.set(rows.get() + 1);
            if enabled.get() && rows.get() == 4 {
                assert!(p.variables > 33 && p.clauses > 0);
                panic!("original FMA callback after multiplier frontier growth");
            }
        }
        Instant::now() >= end
    };
    let mut attempt = FpConstruction::new(FpSolver::new(&terms), &mut stop).unwrap();
    assert!(catch_unwind(AssertUnwindSafe(|| attempt.try_get_fp(fma))).is_err());
    assert_eq!(rows.get(), 4);
    enabled.set(false);
    let before = calls.get();
    assert!(matches!(
        attempt.try_get_fp(fma),
        Err(FpBuildError::Interrupted)
    ));
    assert!(matches!(attempt.finish(), Err(FpBuildError::Interrupted)));
    assert_eq!(calls.get(), before);
}

#[test]
fn native_fma_every_post_multiplier_phase_exit_and_final_outer_admission_can_refuse() {
    let end = Instant::now() + Duration::from_secs(20);
    for veto in 1..=10 {
        let mut terms = TermStore::new();
        let (fma, _) = root(&mut terms, 5, 11, RoundingMode::RTZ);
        let rows = Cell::new(0);
        let exits = Cell::new(0);
        let calls = Cell::new(0);
        let enabled = Cell::new(true);
        let mut stop = |p: FpBuildProgress| {
            calls.set(calls.get() + 1);
            if p.stage == FpBuildStage::MultiplyRow {
                rows.set(rows.get() + 1);
            }
            if rows.get() == 24 && p.stage == FpBuildStage::Operation {
                exits.set(exits.get() + 1);
            }
            (enabled.get() && exits.get() == veto) || Instant::now() >= end
        };
        let mut attempt = FpConstruction::new(FpSolver::new(&terms), &mut stop).unwrap();
        assert!(matches!(
            attempt.try_get_fp(fma),
            Err(FpBuildError::Interrupted)
        ));
        assert_eq!(rows.get(), 24); // entry + 22 original product rows + exit
        assert_eq!(exits.get(), veto);
        enabled.set(false);
        let before = calls.get();
        assert!(matches!(attempt.finish(), Err(FpBuildError::Interrupted)));
        assert_eq!(calls.get(), before);
    }
}

#[test]
fn native_fma_final_publication_refuses_before_and_after_solver_only_drop() {
    let end = Instant::now() + Duration::from_secs(20);
    for veto in [1, 2] {
        let mut terms = TermStore::new();
        let (fma, _) = root(&mut terms, 5, 11, RoundingMode::RTP);
        let finals = Cell::new(0);
        let mut stop = |p: FpBuildProgress| {
            if p.stage == FpBuildStage::Finalize {
                finals.set(finals.get() + 1);
            }
            finals.get() == veto || Instant::now() >= end
        };
        let mut attempt = FpConstruction::new(FpSolver::new(&terms), &mut stop).unwrap();
        attempt.try_get_fp(fma).unwrap();
        assert!(matches!(attempt.finish(), Err(FpBuildError::Interrupted)));
        assert_eq!(finals.get(), veto);
    }
}

#[test]
fn zero_factor_fma_recursive_division_retains_original_stop_and_never_falls_back() {
    let end = Instant::now() + Duration::from_secs(20);
    let mut terms = TermStore::new();
    let fma = zero_root(&mut terms, true);
    let divide = Cell::new(0);
    let multiply = Cell::new(0);
    let enabled = Cell::new(true);
    let calls = Cell::new(0);
    let mut stop = |p: FpBuildProgress| {
        calls.set(calls.get() + 1);
        if p.stage == FpBuildStage::DivideRow {
            divide.set(divide.get() + 1);
        }
        if p.stage == FpBuildStage::MultiplyRow {
            multiply.set(multiply.get() + 1);
        }
        (enabled.get() && divide.get() == 4) || Instant::now() >= end
    };
    let mut attempt = FpConstruction::new(FpSolver::new(&terms), &mut stop).unwrap();
    assert!(matches!(
        attempt.try_get_fp(fma),
        Err(FpBuildError::Interrupted)
    ));
    assert_eq!(divide.get(), 4);
    assert_eq!(multiply.get(), 0);
    enabled.set(false);
    let before = calls.get();
    assert!(matches!(
        attempt.try_get_fp(fma),
        Err(FpBuildError::Interrupted)
    ));
    assert!(matches!(attempt.finish(), Err(FpBuildError::Interrupted)));
    assert_eq!(calls.get(), before);
}

#[test]
fn zero_factor_fma_post_add_exit_refuses_without_reviving_the_same_owner() {
    let end = Instant::now() + Duration::from_secs(20);
    let mut terms = TermStore::new();
    let fma = zero_root(&mut terms, false);
    let operations = Cell::new(0);
    let mut allow = |p: FpBuildProgress| {
        if p.stage == FpBuildStage::Operation {
            operations.set(operations.get() + 1);
        }
        Instant::now() >= end
    };
    let mut healthy = FpConstruction::new(FpSolver::new(&terms), &mut allow).unwrap();
    healthy.try_get_fp(fma).unwrap();
    healthy.finish().unwrap();
    let last = operations.get();
    assert!(last >= 7);
    for veto in [last - 2, last - 1, last] {
        let seen = Cell::new(0);
        let calls = Cell::new(0);
        let enabled = Cell::new(true);
        let mut stop = |p: FpBuildProgress| {
            calls.set(calls.get() + 1);
            if p.stage == FpBuildStage::Operation {
                seen.set(seen.get() + 1);
            }
            (enabled.get() && seen.get() == veto) || Instant::now() >= end
        };
        let mut attempt = FpConstruction::new(FpSolver::new(&terms), &mut stop).unwrap();
        assert!(matches!(
            attempt.try_get_fp(fma),
            Err(FpBuildError::Interrupted)
        ));
        assert_eq!(seen.get(), veto);
        enabled.set(false);
        let before = calls.get();
        assert!(matches!(attempt.finish(), Err(FpBuildError::Interrupted)));
        assert_eq!(calls.get(), before);
    }
}

#[test]
fn fma_refusal_requires_explicit_fresh_attempt_and_does_not_cancel_healthy_new_owner() {
    let end = Instant::now() + Duration::from_secs(20);
    let mut terms = TermStore::new();
    let (fma, _) = root(&mut terms, 5, 11, RoundingMode::RTN);
    let enabled = Cell::new(true);
    let mut stop = |p: FpBuildProgress| {
        (enabled.get() && p.stage == FpBuildStage::MultiplyRow) || Instant::now() >= end
    };
    let mut old = FpConstruction::new(FpSolver::new(&terms), &mut stop).unwrap();
    assert!(matches!(
        old.try_get_fp(fma),
        Err(FpBuildError::Interrupted)
    ));
    enabled.set(false);
    assert!(matches!(old.finish(), Err(FpBuildError::Interrupted)));
    let mut fresh = FpConstruction::new(FpSolver::new(&terms), &mut stop).unwrap();
    fresh.try_get_fp(fma).unwrap();
    let built = fresh.finish().unwrap();
    assert!(!built.has_encoding_gap);
    assert_ne!(built.clauses.len(), 0);
}
