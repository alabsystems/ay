// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

// The original accepted-proof fixture from crate::tests, not a new proof rule.
const SAFE_CHC: &str = r#"
(set-logic HORN)
(declare-fun Inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (Inv x))))
(assert (forall ((x Int) (xp Int)) (=> (and (Inv x) (= xp (+ x 1))) (Inv xp))))
(assert (forall ((x Int)) (=> (and (Inv x) (= x (- 1))) false)))
(check-sat)
"#;

fn fixture() -> ChcProblem {
    ay_chc::ChcParser::parse(SAFE_CHC).expect("original accepted-proof fixture parses")
}

fn config() -> EncodeConfig {
    EncodeConfig::new()
        .with_proof_mode(ProofMode::Strict)
        .with_timeout(Duration::from_secs(30))
}

fn assert_refused_bound(run: &ProofRun, source: &str) {
    assert!(run.result().is_unknown());
    assert!(!run.accepted_as_proof());
    let certificate = run.certificate();
    assert!(!certificate.accepted_as_proof());
    assert!(!certificate.metadata().accepted_as_proof());
    assert!(!certificate.consumer_evidence().accepted_for_consumer());
    assert_eq!(certificate.normalized_input_sha256(), source);
}

#[test]
fn precancelled_parent_returns_only_source_bound_unknown_evidence() {
    let problem = fixture();
    let source = crate::normalized_chc_input_sha256(&problem);
    let parent = CancellationToken::new();
    parent.cancel();
    let run = solve_with_proof_with_cancellation(problem, &config(), &parent)
        .expect("caller cancellation is non-accepted evidence, not an internal error");
    assert_refused_bound(&run, &source);
    assert!(parent.is_cancelled(), "the entry never clears the caller");
}

#[test]
fn observed_attempt_cancellation_survives_raw_parent_and_attempt_reset() {
    let parent = CancellationToken::new();
    let attempt = parent.sticky_child();
    parent.cancel();
    assert!(attempt.is_cancelled(), "observe the original refusal");
    parent.reset();
    attempt.reset();
    assert!(!parent.is_cancelled());
    assert!(attempt.is_cancelled());
    let problem = fixture();
    let source = crate::normalized_chc_input_sha256(&problem);
    let run = solve_with_proof_with_cancellation(problem, &config(), &attempt)
        .expect("latched refusal returns a non-accepted proof run");
    assert_refused_bound(&run, &source);
    assert!(
        attempt.is_cancelled(),
        "the private child inherits the latch"
    );
    assert!(!parent.is_cancelled(), "no upward cancellation write");
}

#[test]
fn explicit_fresh_solve_recovers_without_reviving_the_refused_attempt() {
    let parent = CancellationToken::new();
    let attempt = parent.sticky_child();
    parent.cancel();
    assert!(attempt.is_cancelled());
    parent.reset();
    let problem = fixture();
    let source = crate::normalized_chc_input_sha256(&problem);
    let refused = solve_with_proof_with_cancellation(problem, &config(), &attempt)
        .expect("the old attempt remains refused");
    assert_refused_bound(&refused, &source);

    let accepted = solve_with_proof_with_cancellation(fixture(), &config(), &parent)
        .expect("an explicit fresh solve validates the same original source");
    assert!(accepted.result().is_safe());
    assert!(accepted.accepted_as_proof());
    assert!(accepted.certificate().accepted_as_proof());
    assert_eq!(accepted.certificate().normalized_input_sha256(), source);
    assert_refused_bound(&refused, &source);
    assert!(attempt.is_cancelled());
    assert!(!parent.is_cancelled());
}

#[test]
fn healthy_entry_preserves_existing_accepted_proof_and_certificate_behavior() {
    let parent = CancellationToken::new();
    let configured = config();
    let original = solve_with_proof(fixture(), &configured)
        .expect("the unchanged entry accepts the original proof fixture");
    let linked = solve_with_proof_with_cancellation(fixture(), &configured, &parent)
        .expect("the linked entry uses that same production proof engine");
    assert!(original.result().is_safe() && linked.result().is_safe());
    assert!(original.accepted_as_proof() && linked.accepted_as_proof());
    let original_certificate = original.certificate();
    let linked_certificate = linked.certificate();
    assert!(original_certificate.accepted_as_proof() && linked_certificate.accepted_as_proof());
    assert_eq!(
        original_certificate.normalized_input_sha256(),
        linked_certificate.normalized_input_sha256()
    );
    assert_eq!(
        original_certificate.proof_status(),
        linked_certificate.proof_status()
    );
    assert_eq!(original_certificate.result(), linked_certificate.result());
    assert!(!parent.is_cancelled());
}
