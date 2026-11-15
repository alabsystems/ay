// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use std::sync::atomic::{AtomicBool, Ordering};
use std::time::Duration;

#[test]
fn every_inverse_poll_including_final_cleanup_can_stop_without_publication() {
    let (formula, keep) = sharing::alternatives(2);
    super::super::resources::assert_poll_boundaries(&formula, &keep);
}

#[test]
fn inverse_walks_nodes_and_storage_share_the_exact_cumulative_allowances() {
    let (formula, keep) = sharing::alternatives(2);
    super::super::resources::assert_numeric_boundaries(&formula, &keep);
    for limits in [
        Limits {
            branches: 1,
            ..Limits::default()
        },
        Limits {
            depth: 1,
            ..Limits::default()
        },
    ] {
        assert!(matches!(
            run(&formula, &keep, &mut Scope::new(limits, &|| true)),
            Projection::Stopped
        ));
    }
    assert!(matches!(
        run(
            &formula,
            &keep,
            &mut Scope::new(
                Limits {
                    branches: 2,
                    ..Limits::default()
                },
                &|| true,
            )
        ),
        Projection::Closed(_)
    ));
}

#[test]
fn inverse_still_observes_ambient_deadline_cancellation_and_memory_refusal() {
    let (formula, keep) = fixture(4, Form::SubRight, Orientation::Reverse);
    {
        let _deadline = crate::smt::ScopedSmtDeadline::install(Duration::ZERO);
        assert!(matches!(project(&formula, &keep), Projection::Stopped));
    }
    let cancelled = crate::CancellationToken::new();
    cancelled.cancel();
    {
        let _lane = crate::smt::ScopedLaneCancellation::install(cancelled, None);
        assert!(matches!(project(&formula, &keep), Projection::Stopped));
    }
    {
        let interrupt = Arc::new(AtomicBool::new(true));
        let _lane = crate::smt::ScopedLaneCancellation::install(
            crate::CancellationToken::new(),
            Some(interrupt.clone()),
        );
        assert!(matches!(project(&formula, &keep), Projection::Stopped));
        interrupt.store(false, Ordering::Relaxed);
        assert!(matches!(project(&formula, &keep), Projection::Closed(_)));
    }
    let _memory = crate::smt::SmtContext::scoped_thread_term_memory_budget(Some(0));
    assert!(matches!(project(&formula, &keep), Projection::Stopped));
}
