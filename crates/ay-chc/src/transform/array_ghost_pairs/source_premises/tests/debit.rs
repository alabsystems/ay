// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
#![allow(clippy::unwrap_used)]

use super::*;
use std::time::Duration;

fn control(token: &CancellationToken) -> SourceControl<'_> {
    SourceControl::new(Instant::now() + Duration::from_secs(60), token)
}

#[test]
fn independent_work_and_bytes_accept_the_exact_limits_without_a_node_multiplier() {
    let token = CancellationToken::new();
    let exact = control(&token);
    assert!(exact.debit(MAX_INSTANCE_NODES, MAX_COPY_BYTES).is_some());
    assert_eq!(exact.remaining.get(), 0);
    assert_eq!(exact.bytes_left.get(), 0);
    assert!(exact.debit(0, 0).is_some());
    assert!(exact.poll().is_some());
    assert!(exact.debit(1, 0).is_none());
    assert!(exact.debit(0, 0).is_none());
}

#[test]
fn either_one_short_counter_refuses_atomically_and_never_refunds_or_restarts() {
    let token = CancellationToken::new();
    for (work, bytes) in [(3, 0), (1, 4), (usize::MAX, 0), (0, usize::MAX)] {
        let stopped = control(&token);
        stopped
            .debit(MAX_INSTANCE_NODES - 2, MAX_COPY_BYTES - 3)
            .unwrap();
        assert!(stopped.debit(work, bytes).is_none());
        assert_eq!(stopped.remaining.get(), 2);
        assert_eq!(stopped.bytes_left.get(), 3);
        assert!(stopped.debit(2, 3).is_none());
        assert!(stopped.poll().is_none());
    }
    let fresh = control(&token);
    fresh
        .debit(MAX_INSTANCE_NODES - 2, MAX_COPY_BYTES - 3)
        .unwrap();
    assert!(fresh.debit(2, 3).is_some());
}

#[test]
fn legacy_nodes_still_charge_sixty_four_bytes_and_bytes_only_preserve_work() {
    let token = CancellationToken::new();
    let live = control(&token);
    live.charge(3).unwrap();
    live.bytes(17).unwrap();
    assert_eq!(live.remaining.get(), MAX_INSTANCE_NODES - 3);
    assert_eq!(live.bytes_left.get(), MAX_COPY_BYTES - 3 * 64 - 17);
    let before = (live.remaining.get(), live.bytes_left.get());
    assert!(live.charge(usize::MAX).is_none());
    assert_eq!((live.remaining.get(), live.bytes_left.get()), before);
    assert!(live.bytes(0).is_none());
    let exact = control(&token);
    exact.bytes(MAX_COPY_BYTES - 64).unwrap();
    exact.charge(1).unwrap();
    assert!(exact.poll().is_some());
    assert!(exact.charge(1).is_none());
}

#[test]
fn deadline_and_observed_cancellation_are_terminal_even_for_zero_debits() {
    let token = CancellationToken::new();
    let expired = SourceControl::new(Instant::now(), &token);
    assert!(expired.debit(0, 0).is_none());
    let stopped = control(&token);
    token.cancel();
    assert!(stopped.debit(0, 0).is_none());
    token.reset();
    assert!(stopped.debit(0, 0).is_none());
    assert!(stopped.charge(0).is_none());
    assert!(control(&token).debit(0, 0).is_some());
    assert!(!token.is_cancelled());
}
