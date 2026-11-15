// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn canonical_source_arc_is_prepaid_once_before_allocation() {
    let token = CancellationToken::new();
    let source = "complete canonical source";
    let bytes = source.len() + 64;
    let exact = Control::with_limits(&token, 0, bytes);
    assert_eq!(retain_source(source, &exact).unwrap().as_ref(), source);
    let short = Control::with_limits(&token, 0, bytes - 1);
    assert!(retain_source(source, &short).is_err());
    assert!(short.poll().is_err());
}

#[test]
fn association_debits_the_existing_parent_and_cannot_reset_its_copy_allowance() {
    let source = duplicates(false);
    let obligation = rows(&source).remove(0);
    let token = CancellationToken::new();
    let measured = Control::new(deadline(), &token);
    authenticate(&obligation, &source, &measured).unwrap();
    let bytes = measured.bytes_used();
    assert!(bytes > 1_000 && bytes < 1024 * 1024);
    let exact = SourceControl::new(deadline(), &token);
    exact.bytes(64 * 1024 * 1024 - bytes).unwrap();
    assert!(obligation
        .authenticate_aggregate(&source, deadline(), &token, &exact)
        .is_some());
    assert!(exact.poll().is_some());
    assert!(obligation
        .authenticate_aggregate(&source, deadline(), &token, &exact)
        .is_none());
    assert!(exact.poll().is_none());
    let short = SourceControl::new(deadline(), &token);
    short.bytes(64 * 1024 * 1024 - bytes + 1).unwrap();
    assert!(obligation
        .authenticate_aggregate(&source, deadline(), &token, &short)
        .is_none());
    assert!(short.poll().is_none());
    assert!(accepts(&obligation, &source));
}

#[test]
fn every_association_checkpoint_including_post_cleanup_refuses_without_publication() {
    let source = duplicates(false);
    let obligation = rows(&source).remove(0);
    let token = CancellationToken::new();
    let measured = Control::new(deadline(), &token);
    authenticate(&obligation, &source, &measured).unwrap();
    let calls = measured.calls.get();
    assert!(calls > 20 && calls < 2_000);
    for stop in 1..=calls {
        let control = Control::new(deadline(), &token);
        control.stop_at.set(Some(stop));
        assert!(
            authenticate(&obligation, &source, &control).is_err(),
            "{stop}"
        );
        control.stop_at.set(None);
        assert!(authenticate(&obligation, &source, &control).is_err());
    }
}

#[test]
fn expired_parents_and_observed_cancel_reset_cannot_be_bypassed() {
    let source = duplicates(false);
    let obligation = rows(&source).remove(0);
    let token = CancellationToken::new();
    let expired = SourceControl::new(Instant::now(), &token);
    assert!(obligation
        .authenticate_aggregate(&source, deadline(), &token, &expired)
        .is_none());
    let parent = SourceControl::new(deadline(), &token);
    assert!(obligation
        .authenticate_aggregate(&source, Instant::now(), &token, &parent)
        .is_none());
    let stopped = SourceControl::new(deadline(), &token);
    token.cancel();
    assert!(obligation
        .authenticate_aggregate(&source, deadline(), &token, &stopped)
        .is_none());
    token.reset();
    assert!(obligation
        .authenticate_aggregate(&source, deadline(), &token, &stopped)
        .is_none());
    assert!(accepts(&obligation, &source));
}

#[test]
fn missing_plan_error_stops_the_shared_parent_even_after_identity_is_repaired() {
    let source = duplicates(false);
    let mut obligation = rows(&source).remove(0);
    let token = CancellationToken::new();
    let parent = SourceControl::new(deadline(), &token);
    let original = obligation.id.query_clause_index;
    obligation.id.query_clause_index = usize::MAX;
    assert!(obligation
        .authenticate_aggregate(&source, deadline(), &token, &parent)
        .is_none());
    assert!(parent.poll().is_none());
    obligation.id.query_clause_index = original;
    assert!(obligation
        .authenticate_aggregate(&source, deadline(), &token, &parent)
        .is_none());
    assert!(accepts(&obligation, &source));
}
