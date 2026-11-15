// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]

use super::*;

#[test]
fn cancelled_or_expired_attempt_cannot_build_rewrite_or_replay() {
    let source = fixture(true, "i");
    let model = interpretation(&source);
    let token = CancellationToken::new();
    token.cancel();
    let control = SourceControl::new(deadline(), &token);
    assert!(rewrite_source(&source, &model.spec, &control).is_none());
    token.reset();
    assert!(control.poll().is_none());
    let expired = SourceControl::new(Instant::now(), &token);
    assert!(replay::prepare(&source, &model, 0, &expired, None).is_none());
    let fresh = SourceControl::new(deadline(), &token);
    assert!(rewrite_source(&source, &model.spec, &fresh).is_some());
}

#[test]
fn instance_copy_budget_refusal_is_sticky_and_does_not_publish_a_prefix() {
    let token = CancellationToken::new();
    let control = SourceControl::new(deadline(), &token);
    assert!(control.bytes(usize::MAX).is_none());
    assert!(control.poll().is_none());
    let source = fixture(true, "i");
    assert!(source_premises::instances(
        &source.premises()[0],
        &[ChcExpr::BitVec(40, 64)],
        &control
    )
    .is_none());
    let fresh = SourceControl::new(deadline(), &token);
    assert_eq!(
        source_premises::instances(&source.premises()[0], &[ChcExpr::BitVec(40, 64)], &fresh)
            .unwrap()
            .len(),
        1
    );
}

#[test]
fn large_symbol_serialization_is_refused_before_legacy_formatter() {
    let token = CancellationToken::new();
    let control = SourceControl::new(deadline(), &token);
    let expr = ChcExpr::var(ChcVar::new(
        "x".repeat(MAX_REPLAY_BYTES / 4 + 1),
        ChcSort::Bool,
    ));
    assert!(source_premises::preflight(&expr, &control, &mut 0).is_none());
}

#[test]
fn inherited_memory_limit_cannot_be_widened_by_certificate_limit() {
    assert_eq!(tighter_memory(Some(1), Some(64 * 1024 * 1024)), Some(1));
    assert_eq!(tighter_memory(Some(1), None), Some(1));
    assert_eq!(tighter_memory(None, Some(10)), Some(10));
    let source = fixture(true, "i");
    let certificate = GhostSourceCertificate {
        source: Arc::from(source.source_smtlib()),
        interpretation: interpretation(&source),
        records: None,
    };
    let _memory = SmtContext::scoped_thread_term_memory_budget(Some(1));
    assert!(!certificate.recheck(&source, deadline(), &CancellationToken::new()));
}
