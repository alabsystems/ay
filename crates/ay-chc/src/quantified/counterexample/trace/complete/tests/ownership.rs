// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn complete_original_source_owner_zero_work_refuses_without_refund_or_rearm() {
    let token = CancellationToken::new();
    let source = data_source();
    let rendered = render(&source, &token);
    let registry = registry(&source, &control(&token)).unwrap();
    let bindings = bindings(&rendered, &range());
    let owner = control(&token);
    owner.debit(8_000_000, 0).unwrap();
    assert!(pins::render(&rendered, &bindings, &[], &source, &registry, &owner).is_none());
    assert!(owner.debit(0, 0).is_none());
    assert!(pins::render(&rendered, &bindings, &[], &source, &registry, &owner).is_none());
    assert!(pins::render(
        &rendered,
        &bindings,
        &[],
        &source,
        &registry,
        &control(&token)
    )
    .is_some());
}

#[test]
fn complete_whole_batch_has_one_topology_reservation_not_one_per_array() {
    let token = CancellationToken::new();
    let source = data_source();
    let rendered = render(&source, &token);
    let bindings = bindings(&rendered, &range());
    let owner = control(&token);
    // Leave enough for one prepaid 1M DATA reservation and bounded formatting,
    // but not a second per-duplicate snapshot reservation.
    owner.debit(8_000_000 - 1_200_000, 0).unwrap();
    assert!(snapshots::build(&rendered.original, &bindings, &source, &owner).is_some());
    assert!(owner.debit(200_000, 0).is_none());
    assert!(owner.poll().is_none());
}

#[test]
fn complete_cancelled_and_expired_owners_cannot_publish_or_rearm() {
    let token = CancellationToken::new();
    let source = data_source();
    let rendered = render(&source, &token);
    let registry = registry(&source, &control(&token)).unwrap();
    let bindings = bindings(&rendered, &range());
    let expired = SourceControl::new(Instant::now(), &token);
    assert!(pins::render(&rendered, &bindings, &[], &source, &registry, &expired).is_none());
    assert!(expired.debit(0, 0).is_none());
    let owner = control(&token);
    token.cancel();
    assert!(pins::render(&rendered, &bindings, &[], &source, &registry, &owner).is_none());
    assert!(owner.poll().is_none());
}
