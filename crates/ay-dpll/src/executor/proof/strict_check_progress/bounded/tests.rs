// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::api::proofs::EnvelopeStop;
use ay_core::resource::enter_check_stop;
use std::sync::{
    atomic::{AtomicBool, AtomicUsize, Ordering},
    Arc,
};

#[test]
fn specialized_local_counts_are_exact_cumulative_and_irreversible() {
    let executor = Executor::new();
    assert_eq!(
        check_bounded_with_executor_progress(&executor, 10, 8, |offer| {
            assert!(offer(6, 5));
            assert!(offer(4, 3));
            Ok(7)
        }),
        Ok(7)
    );
    for extra in [(1, 0), (0, 1)] {
        let result = check_bounded_with_executor_progress(&executor, 10, 8, |offer| {
            assert!(offer(10, 8));
            assert!(!offer(extra.0, extra.1));
            assert!(!offer(0, 0), "no smaller offer revives a refused walk");
            Ok(7)
        });
        assert_eq!(result, Err(ProofCheckError::ResourceLimit));
        assert!(executor.certification_stop.get().is_none());
    }
    assert_eq!(
        check_bounded_with_executor_progress(&executor, usize::MAX, usize::MAX, |offer| {
            assert!(offer(usize::MAX, usize::MAX));
            assert!(!offer(1, 0));
            Ok(7)
        }),
        Err(ProofCheckError::ResourceLimit)
    );
}

#[test]
fn specialized_walk_neither_repolls_after_completion_nor_accepts_swallowed_stop() {
    let executor = Executor::new();
    let flag = Arc::new(AtomicBool::new(false));
    let observed = flag.clone();
    let calls = Arc::new(AtomicUsize::new(0));
    let counted = calls.clone();
    let _owner = enter_check_stop(Arc::new(move || {
        counted.fetch_add(1, Ordering::SeqCst);
        observed.load(Ordering::SeqCst)
    }));
    assert_eq!(
        check_bounded_with_executor_progress(&executor, 1, 1, |offer| {
            assert!(offer(1, 1));
            flag.store(true, Ordering::SeqCst);
            Ok(7)
        }),
        Ok(7)
    );
    assert_eq!(calls.load(Ordering::SeqCst), 2);
    assert!(executor.certification_stop.get().is_none());
    flag.store(false, Ordering::SeqCst);
    let result = check_bounded_with_executor_progress(&executor, 1, 1, |offer| {
        flag.store(true, Ordering::SeqCst);
        assert!(!offer(0, 0));
        flag.store(false, Ordering::SeqCst);
        assert!(!offer(0, 0));
        Ok(7)
    });
    assert_eq!(result, Err(ProofCheckError::Cancelled));
    assert_eq!(
        executor.certification_stop.get(),
        Some(EnvelopeStop::Caller)
    );
}

#[test]
fn specialized_walk_preserves_genuine_checker_rejections() {
    let executor = Executor::new();
    let result = check_bounded_with_executor_progress::<()>(&executor, 0, 0, |offer| {
        assert!(!offer(1, 0));
        Err(ProofCheckError::NoClauseProducingSteps)
    });
    assert_eq!(result, Err(ProofCheckError::NoClauseProducingSteps));
}
