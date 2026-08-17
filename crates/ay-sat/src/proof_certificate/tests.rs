// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::literal::Variable;

fn make_test_steps() -> Vec<LratStep> {
    let v0 = Variable(0);
    let v1 = Variable(1);
    vec![
        LratStep {
            clause_id: 4,
            literals: vec![Literal::positive(v0), Literal::negative(v1)],
            hints: vec![1i64, 2],
        },
        LratStep {
            clause_id: 5,
            literals: vec![Literal::negative(v0)],
            hints: vec![3i64, 4],
        },
        LratStep {
            clause_id: 6,
            literals: vec![],
            hints: vec![4i64, 5],
        },
    ]
}

#[test]
fn test_proof_certificate_is_deferred_before_materialization() {
    let cert = ProofCertificate::from_backward_result(make_test_steps(), true);
    assert!(
        cert.is_deferred(),
        "certificate should be deferred before materialization"
    );
}

#[test]
fn test_proof_certificate_not_deferred_after_materialization() {
    let cert = ProofCertificate::from_backward_result(make_test_steps(), true);
    let _ = cert.materialize();
    assert!(
        !cert.is_deferred(),
        "certificate should not be deferred after materialization"
    );
}

#[test]
fn test_proof_certificate_materialize_returns_steps() {
    let cert = ProofCertificate::from_backward_result(make_test_steps(), true);
    let steps = cert.materialize();
    assert_eq!(steps.len(), 3);
    assert_eq!(steps[0].clause_id, 4);
    assert_eq!(steps[0].hints, vec![1i64, 2]);
    assert_eq!(steps[1].clause_id, 5);
    assert_eq!(steps[2].clause_id, 6);
    assert!(
        steps[2].literals.is_empty(),
        "last step should be empty clause"
    );
}

#[test]
fn test_proof_certificate_materialize_is_idempotent() {
    let cert = ProofCertificate::from_backward_result(make_test_steps(), true);
    let steps1 = cert.materialize();
    let steps2 = cert.materialize();
    assert_eq!(steps1.len(), steps2.len());
    // Same pointer -- OnceCell caching
    assert!(std::ptr::eq(steps1, steps2));
}

#[test]
fn test_proof_certificate_step_count() {
    let cert = ProofCertificate::from_backward_result(make_test_steps(), true);
    assert_eq!(cert.step_count(), 3);
    // After step_count, no longer deferred
    assert!(!cert.is_deferred());
}

#[test]
fn test_proof_certificate_write_lrat_produces_output() {
    let cert = ProofCertificate::from_backward_result(make_test_steps(), true);
    let mut buf = Vec::new();
    cert.write_lrat(&mut buf)
        .expect("write_lrat should succeed");
    let output = String::from_utf8(buf).expect("should be valid UTF-8");
    assert!(!output.is_empty(), "LRAT output should not be empty");
    // Each line ends with "0\n" (the hint terminator)
    let lines: Vec<&str> = output.lines().collect();
    assert_eq!(lines.len(), 3, "should have 3 proof steps");
    // First line should start with clause_id 4
    assert!(
        lines[0].starts_with("4 "),
        "first line should start with clause ID 4, got: {}",
        lines[0]
    );
    // Last line should be for the empty clause (clause_id 6, no literals)
    assert!(
        lines[2].starts_with("6 0 "),
        "last line should start with '6 0 ' (empty clause), got: {}",
        lines[2]
    );
}

#[test]
fn test_proof_certificate_write_drat_produces_output() {
    let cert = ProofCertificate::from_backward_result(make_test_steps(), true);
    let mut buf = Vec::new();
    cert.write_drat(&mut buf)
        .expect("write_drat should succeed");
    let output = String::from_utf8(buf).expect("should be valid UTF-8");
    assert!(!output.is_empty(), "DRAT output should not be empty");
    let lines: Vec<&str> = output.lines().collect();
    assert_eq!(lines.len(), 3, "should have 3 proof steps");
    // DRAT has no clause IDs or hints -- just literals terminated by 0
    // Last line should be "0" (empty clause, no literals)
    assert_eq!(
        lines[2].trim(),
        "0",
        "last line should be '0' (empty clause), got: {}",
        lines[2]
    );
}

#[test]
fn test_proof_certificate_empty() {
    let cert = ProofCertificate::empty();
    assert!(cert.is_deferred());
    assert!(!cert.is_complete());
    assert_eq!(cert.step_count(), 0);
    assert!(!cert.is_deferred()); // step_count materialized it
}

#[test]
fn test_proof_certificate_from_lrat_text_materializes_additions() {
    let lrat = b"3 1 0 1 0\n4 0 3 -2 0\n5 d 3 0\n";
    let cert = ProofCertificate::from_lrat_text(lrat, true).expect("valid LRAT text");
    let steps = cert.materialize();

    assert_eq!(steps.len(), 2);
    assert_eq!(steps[0].clause_id, 3);
    assert_eq!(steps[0].dimacs_literals(), vec![1]);
    assert_eq!(steps[0].hints, vec![1]);
    assert_eq!(steps[1].clause_id, 4);
    assert!(steps[1].literals.is_empty());
    assert_eq!(steps[1].hints, vec![3, -2]);
    assert!(cert.is_complete());
}

#[test]
fn test_proof_certificate_from_lrat_text_rejects_missing_terminator() {
    let err = ProofCertificate::from_lrat_text(b"3 1 0 1\n", true)
        .expect_err("missing final 0 must fail");
    assert_eq!(err.kind(), io::ErrorKind::InvalidData);
}

#[test]
fn test_proof_certificate_is_complete() {
    let complete = ProofCertificate::from_backward_result(make_test_steps(), true);
    assert!(complete.is_complete());

    let incomplete = ProofCertificate::from_backward_result(make_test_steps(), false);
    assert!(!incomplete.is_complete());
}

#[test]
fn test_proof_certificate_debug_format() {
    let cert = ProofCertificate::from_backward_result(make_test_steps(), true);
    let debug_str = format!("{cert:?}");
    assert!(
        debug_str.contains("materialized: false"),
        "debug should show unmaterialized state"
    );
    let _ = cert.materialize();
    let debug_str = format!("{cert:?}");
    assert!(
        debug_str.contains("materialized: true"),
        "debug should show materialized state"
    );
}

#[test]
fn test_proof_step_from_lrat_step() {
    let v0 = Variable(0);
    let lrat_step = LratStep {
        clause_id: 42,
        literals: vec![Literal::positive(v0)],
        hints: vec![10i64, 20],
    };
    let proof_step = ProofStep::from(lrat_step);
    assert_eq!(proof_step.clause_id, 42);
    assert_eq!(proof_step.literals.len(), 1);
    assert_eq!(proof_step.hints, vec![10i64, 20]);
}

#[test]
fn test_minimal_core_extracts_original_clause_ids() {
    let cert = ProofCertificate::from_backward_result(make_test_steps(), true);
    let core = cert.minimal_core();
    assert_eq!(
        core,
        vec![1, 2, 3],
        "minimal core should contain original clause IDs 1, 2, 3"
    );
}

#[test]
fn test_minimal_core_empty_proof() {
    let cert = ProofCertificate::empty();
    let core = cert.minimal_core();
    assert!(core.is_empty(), "empty proof should yield empty core");
}

#[test]
fn test_minimal_core_single_step_no_hints() {
    let steps = vec![LratStep {
        clause_id: 1,
        literals: vec![],
        hints: vec![],
    }];
    let cert = ProofCertificate::from_backward_result(steps, true);
    let core = cert.minimal_core();
    assert!(
        core.is_empty(),
        "proof step with no hints should yield empty core"
    );
}

#[test]
fn test_minimal_core_all_original() {
    let steps = vec![LratStep {
        clause_id: 10,
        literals: vec![],
        hints: vec![1i64, 2, 3],
    }];
    let cert = ProofCertificate::from_backward_result(steps, true);
    let core = cert.minimal_core();
    assert_eq!(
        core,
        vec![1, 2, 3],
        "all hints should be original clause IDs"
    );
}

#[test]
fn test_minimal_core_dedup_and_sort() {
    let steps = vec![
        LratStep {
            clause_id: 10,
            literals: vec![Literal::positive(Variable(0))],
            hints: vec![3i64, 1, 2, 1, 3],
        },
        LratStep {
            clause_id: 11,
            literals: vec![],
            hints: vec![10i64, 2],
        },
    ];
    let cert = ProofCertificate::from_backward_result(steps, true);
    let core = cert.minimal_core();
    assert_eq!(core, vec![1, 2, 3], "core should be sorted and deduped");
}

// ── Streaming UNSAT core tests (#8250) ──────────────────────────────

#[test]
fn test_streaming_core_not_present_by_default() {
    let cert = ProofCertificate::from_backward_result(make_test_steps(), true);
    assert!(
        !cert.has_streaming_core(),
        "default certificate should not have streaming core"
    );
}

#[test]
fn test_streaming_core_overrides_dag_walk() {
    let mut cert = ProofCertificate::from_backward_result(make_test_steps(), true);
    // DAG walk would produce [1, 2, 3], but streaming core overrides.
    cert.set_streaming_core(vec![1, 3]);
    assert!(cert.has_streaming_core());
    let core = cert.minimal_core();
    assert_eq!(
        core,
        vec![1, 3],
        "streaming core should override DAG walk result"
    );
}

#[test]
fn test_streaming_core_returns_without_materializing() {
    let mut cert = ProofCertificate::from_backward_result(make_test_steps(), true);
    cert.set_streaming_core(vec![2, 5]);
    assert!(
        cert.is_deferred(),
        "proof should still be deferred before minimal_core"
    );
    let core = cert.minimal_core();
    assert_eq!(core, vec![2, 5]);
    // Streaming core path does NOT materialize the proof
    assert!(
        cert.is_deferred(),
        "streaming core should not trigger materialization"
    );
}

#[test]
fn test_streaming_core_empty_certificate() {
    let mut cert = ProofCertificate::empty();
    assert!(!cert.has_streaming_core());
    cert.set_streaming_core(vec![1]);
    assert!(cert.has_streaming_core());
    assert_eq!(cert.minimal_core(), vec![1]);
}

#[test]
fn test_streaming_core_debug_includes_size() {
    let mut cert = ProofCertificate::from_backward_result(make_test_steps(), true);
    cert.set_streaming_core(vec![1, 2, 3]);
    let debug_str = format!("{cert:?}");
    assert!(
        debug_str.contains("streaming_core: Some(3)"),
        "debug should show streaming core size, got: {debug_str}"
    );
}

#[test]
fn test_streaming_core_clone_preserves() {
    let mut cert = ProofCertificate::from_backward_result(make_test_steps(), true);
    cert.set_streaming_core(vec![1, 2]);
    let cloned = cert.clone();
    assert!(cloned.has_streaming_core());
    assert_eq!(cloned.minimal_core(), vec![1, 2]);
}
