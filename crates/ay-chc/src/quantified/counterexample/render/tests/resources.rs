// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn cancellation_and_deadline_refuse_without_reviving_the_same_attempt() {
    let source = scoped_source();
    let token = CancellationToken::new();
    let attempt = control(&token);
    token.cancel();
    assert!(render(&source, &[0, 1], &attempt).is_err());
    token.reset();
    assert!(render(&source, &[0, 1], &attempt).is_err());
    assert!(attempt.poll().is_none());
    assert_eq!(
        render(&source, &[0, 1], &control(&token)).unwrap(),
        output(&source, &[0, 1])
    );
    let expired = SourceControl::new(Instant::now(), &token);
    assert!(render(&source, &[0, 1], &expired).is_err());
    assert!(expired.poll().is_none());
}

#[test]
fn shared_copy_exhaustion_is_terminal_and_fresh_rendering_retries() {
    let source = scoped_source();
    let token = CancellationToken::new();
    let attempt = control(&token);
    assert_eq!(attempt.bytes(64 * 1024 * 1024), Some(()));
    assert!(render(&source, &[0, 1], &attempt).is_err());
    assert!(attempt.bytes(0).is_none());
    assert!(render(&source, &[0, 1], &attempt).is_err());
    assert_eq!(
        render(&source, &[0, 1], &control(&token)).unwrap(),
        output(&source, &[0, 1])
    );
}

#[test]
fn output_cap_checks_before_copy_and_formatter_preflight_counts_shared_occurrences() {
    let token = CancellationToken::new();
    let attempt = control(&token);
    let text = "x".repeat(MAX_OUTPUT_BYTES);
    let mut out = Output::new(&attempt);
    out.push(&text).unwrap();
    assert!(out.push("x").is_err());
    assert_eq!(out.finish(), text);
    let fresh = control(&token);
    let mut out = Output::new(&fresh);
    let above = "x".repeat(MAX_OUTPUT_BYTES + 1);
    assert!(out.push(&above).is_err());
    assert!(out.finish().is_empty());

    // A tiny retained DAG may have exponential tree-printing cost. The
    // independent occurrence preflight refuses before invoking that printer.
    let mut expression = Arc::new(ChcExpr::Bool(true));
    for _ in 0..20 {
        expression = Arc::new(ChcExpr::Op(
            ChcOp::And,
            vec![expression.clone(), expression],
        ));
    }
    assert!(census::expression_cost(&expression, &control(&token)).is_err());
    assert!(census::expression_cost(&ChcExpr::Bool(true), &control(&token)).is_ok());
}
