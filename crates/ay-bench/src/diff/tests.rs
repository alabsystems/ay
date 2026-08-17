// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

fn row(commit: &str, eval: &str, bench: &str, result: &str, ms: i64, ok: i32) -> ResultRow {
    ResultRow {
        commit_hash: commit.to_string(),
        eval_name: eval.to_string(),
        benchmark_path: bench.to_string(),
        result: result.to_string(),
        runtime_ms: ms,
        memory_mb: 0,
        verifier_ok: ok,
        timestamp: "2026-04-18T00:00:00Z".to_string(),
        resource_envelope: Some(
            "oom-guard-v1:jobs=1;memlimit_mb=1024;nbcore=1;headroom_mb=16000".to_string(),
        ),
        benchmark_content_hash: Some("fh128:test".to_string()),
        artifact_output_dir: None,
        proof_path: None,
        proof_format: None,
        proof_exists: None,
        proof_bytes: None,
        proof_hash: None,
        proof_validation: None,
        family: None,
        clause_width_max: None,
        clause_width_mean: None,
        xor_density: None,
        cardinality_density: None,
        modularity: None,
        feature_extract_ms: None,
    }
}

#[test]
fn test_classify_solved() {
    assert_eq!(classify("sat", 1), Verdict::Solved);
    assert_eq!(classify("UNSAT", 1), Verdict::Solved);
    // -1 (unknown check) is treated as Solved since the solver reported a verdict.
    assert_eq!(classify("sat", -1), Verdict::Solved);
}

#[test]
fn test_classify_wrong() {
    assert_eq!(classify("sat", 0), Verdict::WrongAnswer);
    assert_eq!(classify("unsat", 0), Verdict::WrongAnswer);
}

#[test]
fn test_classify_unsolved() {
    assert_eq!(classify("unknown", 1), Verdict::Unsolved);
    assert_eq!(classify("timeout", 1), Verdict::Unsolved);
    assert_eq!(classify("error", 0), Verdict::Unsolved);
}

#[test]
fn test_diff_regression_solved_to_unsolved() {
    let base = vec![row("A", "e", "b.smt2", "sat", 100, 1)];
    let head = vec![row("B", "e", "b.smt2", "unknown", 30_000, 1)];
    let rep = compute_diff("A", &base, "B", &head, DiffOptions::default());
    assert_eq!(rep.regressions.len(), 1);
    assert!(rep.has_regressions());
    assert_eq!(rep.improvements.len(), 0);
    assert_eq!(rep.slowdowns.len(), 0);
}

#[test]
fn test_diff_resource_mismatch_is_explicitly_non_comparable() {
    let base = vec![row("A", "e", "b.smt2", "sat", 100, 1)];
    let mut head = row("B", "e", "b.smt2", "unknown", 30_000, 1);
    head.resource_envelope =
        Some("oom-guard-v1:jobs=1;memlimit_mb=2048;nbcore=1;headroom_mb=16000".to_string());
    let rep = compute_diff("A", &base, "B", &[head], DiffOptions::default());
    assert_eq!(rep.non_comparable.len(), 1);
    assert!(rep.has_non_comparable());
    assert!(rep.regressions.is_empty());
    assert!(rep.improvements.is_empty());
    assert!(rep.slowdowns.is_empty());
}

#[test]
fn test_diff_content_mismatch_is_explicitly_non_comparable() {
    let base = vec![row("A", "e", "b.smt2", "sat", 100, 1)];
    let mut head = row("B", "e", "b.smt2", "sat", 90, 1);
    head.benchmark_content_hash = Some("fh128:changed".to_string());
    let rep = compute_diff("A", &base, "B", &[head], DiffOptions::default());
    assert_eq!(rep.non_comparable.len(), 1);
    assert_eq!(rep.non_comparable[0].reason, "benchmark content differs");
    assert!(rep.speedups.is_empty());
}

#[test]
fn test_diff_regression_correct_to_wrong() {
    let base = vec![row("A", "e", "b.smt2", "sat", 100, 1)];
    let head = vec![row("B", "e", "b.smt2", "sat", 100, 0)]; // now wrong
    let rep = compute_diff("A", &base, "B", &head, DiffOptions::default());
    assert_eq!(rep.regressions.len(), 1);
    assert!(rep.has_regressions());
}

#[test]
fn test_diff_improvement_unsolved_to_solved() {
    let base = vec![row("A", "e", "b.smt2", "timeout", 30_000, 1)];
    let head = vec![row("B", "e", "b.smt2", "sat", 500, 1)];
    let rep = compute_diff("A", &base, "B", &head, DiffOptions::default());
    assert_eq!(rep.improvements.len(), 1);
    assert_eq!(rep.regressions.len(), 0);
    assert!(!rep.has_regressions());
}

#[test]
fn test_diff_improvement_wrong_to_correct() {
    let base = vec![row("A", "e", "b.smt2", "sat", 100, 0)];
    let head = vec![row("B", "e", "b.smt2", "unsat", 100, 1)];
    let rep = compute_diff("A", &base, "B", &head, DiffOptions::default());
    assert_eq!(rep.improvements.len(), 1);
    assert_eq!(rep.regressions.len(), 0);
}

#[test]
fn test_diff_slowdown_above_threshold() {
    let base = vec![row("A", "e", "b.smt2", "sat", 1000, 1)];
    let head = vec![row("B", "e", "b.smt2", "sat", 1500, 1)]; // +50%
    let rep = compute_diff("A", &base, "B", &head, DiffOptions::default());
    assert_eq!(rep.slowdowns.len(), 1);
    assert!(rep.slowdowns[0].runtime_delta_pct.unwrap() > 20.0);
    assert!(!rep.has_regressions());
}

#[test]
fn test_diff_slowdown_below_threshold_ignored() {
    let base = vec![row("A", "e", "b.smt2", "sat", 1000, 1)];
    let head = vec![row("B", "e", "b.smt2", "sat", 1100, 1)]; // +10%, under 20% threshold
    let rep = compute_diff("A", &base, "B", &head, DiffOptions::default());
    assert_eq!(rep.slowdowns.len(), 0);
    assert_eq!(rep.unchanged_count, 1);
}

#[test]
fn test_diff_speedup_detected() {
    let base = vec![row("A", "e", "b.smt2", "sat", 1000, 1)];
    let head = vec![row("B", "e", "b.smt2", "sat", 400, 1)]; // -60%
    let rep = compute_diff("A", &base, "B", &head, DiffOptions::default());
    assert_eq!(rep.speedups.len(), 1);
    assert!(rep.speedups[0].runtime_delta_pct.unwrap() < -20.0);
}

#[test]
fn test_diff_added_removed() {
    let base = vec![row("A", "e", "only_base.smt2", "sat", 10, 1)];
    let head = vec![row("B", "e", "only_head.smt2", "sat", 10, 1)];
    let rep = compute_diff("A", &base, "B", &head, DiffOptions::default());
    assert_eq!(rep.added.len(), 1);
    assert_eq!(rep.removed.len(), 1);
    assert_eq!(rep.regressions.len(), 0);
}

#[test]
fn test_diff_eval_filter_respected_in_keys() {
    // compute_diff itself doesn't filter — the caller does. Test that
    // filtering the input rows works as expected.
    let base = vec![
        row("A", "e1", "a.smt2", "sat", 10, 1),
        row("A", "e2", "a.smt2", "sat", 10, 1),
    ];
    let head = vec![
        row("B", "e1", "a.smt2", "unknown", 100, 1),
        row("B", "e2", "a.smt2", "sat", 10, 1),
    ];
    let rep = compute_diff("A", &base, "B", &head, DiffOptions::default());
    assert_eq!(rep.regressions.len(), 1);
    assert_eq!(rep.regressions[0].eval_name, "e1");
}

#[test]
fn test_diff_wrong_persists_still_flagged() {
    let base = vec![row("A", "e", "b.smt2", "sat", 100, 0)];
    let head = vec![row("B", "e", "b.smt2", "sat", 100, 0)];
    let rep = compute_diff("A", &base, "B", &head, DiffOptions::default());
    // WrongAnswer on both sides — flagged as regression so it stays visible.
    assert_eq!(rep.regressions.len(), 1);
}

#[test]
fn test_diff_unsolved_to_wrong_is_regression() {
    let base = vec![row("A", "e", "b.smt2", "timeout", 30_000, 1)];
    let head = vec![row("B", "e", "b.smt2", "sat", 100, 0)]; // wrong now
    let rep = compute_diff("A", &base, "B", &head, DiffOptions::default());
    assert_eq!(rep.regressions.len(), 1);
}

#[test]
fn test_diff_zero_base_runtime_no_delta() {
    // Runtime of 0 should not produce a slowdown entry (avoid div/0).
    let base = vec![row("A", "e", "b.smt2", "sat", 0, 1)];
    let head = vec![row("B", "e", "b.smt2", "sat", 500, 1)];
    let rep = compute_diff("A", &base, "B", &head, DiffOptions::default());
    assert_eq!(rep.slowdowns.len(), 0);
    // Falls through to unchanged bucket because delta is None.
    assert_eq!(rep.unchanged_count, 1);
}

#[test]
fn test_render_table_includes_regressions_header_when_empty() {
    let rep = compute_diff(
        "A",
        &[row("A", "e", "b.smt2", "sat", 100, 1)],
        "B",
        &[row("B", "e", "b.smt2", "sat", 110, 1)],
        DiffOptions::default(),
    );
    let out = render_table(&rep);
    assert!(out.contains("Regressions"));
    assert!(out.contains("(none)"));
}

#[test]
fn test_render_json_roundtrips() {
    let rep = compute_diff(
        "aaaaaaaaaaaa",
        &[row("aaaaaaaaaaaa", "e", "b.smt2", "sat", 100, 1)],
        "bbbbbbbbbbbb",
        &[row("bbbbbbbbbbbb", "e", "b.smt2", "unknown", 30_000, 1)],
        DiffOptions::default(),
    );
    let j = render_json(&rep).expect("render_json");
    assert!(j.contains("regressions"));
    assert!(j.contains("\"base_commit\""));
}

#[test]
fn test_diff_from_store_end_to_end() {
    let mut store = ResultsStore::open_in_memory().expect("open");
    store
        .upsert_rows(&[row("A", "e", "b.smt2", "sat", 100, 1)])
        .expect("insert A");
    store
        .upsert_rows(&[row("B", "e", "b.smt2", "unknown", 30_000, 1)])
        .expect("insert B");
    let rep = diff_from_store(&store, "A", "B", None, DiffOptions::default()).expect("diff");
    assert_eq!(rep.regressions.len(), 1);
}

// -------------------------------------------------------------
// Timeout / solved reclassification matrix
//
// `classify()` already collapses `timeout` into `Verdict::Unsolved`,
// so the existing Solved/Unsolved transitions drive this logic. These
// tests lock the behaviour down explicitly so a future refactor that
// accidentally promotes `timeout` to its own verdict doesn't silently
// miss regressions / improvements.
// -------------------------------------------------------------

#[test]
fn test_diff_solved_to_timeout_is_regression() {
    let base = vec![row("A", "e", "b.smt2", "sat", 500, 1)];
    let head = vec![row("B", "e", "b.smt2", "timeout", 30_000, 1)];
    let rep = compute_diff("A", &base, "B", &head, DiffOptions::default());
    assert_eq!(
        rep.regressions.len(),
        1,
        "solved→timeout must be a regression"
    );
    assert!(rep.has_regressions());
    assert_eq!(rep.improvements.len(), 0);
    assert_eq!(rep.slowdowns.len(), 0);
    // Verdict on head side is Unsolved (timeout collapses into Unsolved).
    assert_eq!(rep.regressions[0].head_verdict, Some(Verdict::Unsolved));
}

#[test]
fn test_diff_timeout_to_solved_is_improvement() {
    let base = vec![row("A", "e", "b.smt2", "timeout", 30_000, 1)];
    let head = vec![row("B", "e", "b.smt2", "unsat", 250, 1)];
    let rep = compute_diff("A", &base, "B", &head, DiffOptions::default());
    assert_eq!(
        rep.improvements.len(),
        1,
        "timeout→solved must be an improvement"
    );
    assert_eq!(rep.regressions.len(), 0);
    assert!(!rep.has_regressions());
}

#[test]
fn test_diff_timeout_to_timeout_is_unchanged() {
    let base = vec![row("A", "e", "b.smt2", "timeout", 30_000, 1)];
    let head = vec![row("B", "e", "b.smt2", "timeout", 30_000, 1)];
    let rep = compute_diff("A", &base, "B", &head, DiffOptions::default());
    // Both sides unsolved with same runtime → falls into unchanged bucket,
    // NOT regressions.
    assert_eq!(rep.regressions.len(), 0);
    assert_eq!(rep.improvements.len(), 0);
    assert_eq!(rep.slowdowns.len(), 0);
    assert_eq!(rep.unchanged_count, 1);
}

#[test]
fn test_diff_timeout_to_wrong_answer_is_regression() {
    // Even though both sides are "not a correct solve", going from
    // timeout (honest unknown) to sat-with-verifier-disagreement is a
    // NEW bug and must be flagged.
    let base = vec![row("A", "e", "b.smt2", "timeout", 30_000, 1)];
    let head = vec![row("B", "e", "b.smt2", "sat", 100, 0)];
    let rep = compute_diff("A", &base, "B", &head, DiffOptions::default());
    assert_eq!(rep.regressions.len(), 1);
}

#[test]
fn test_diff_from_store_eval_filter() {
    let mut store = ResultsStore::open_in_memory().expect("open");
    store
        .upsert_rows(&[
            row("A", "e1", "b.smt2", "sat", 100, 1),
            row("A", "e2", "b.smt2", "sat", 100, 1),
        ])
        .expect("insert A");
    store
        .upsert_rows(&[
            row("B", "e1", "b.smt2", "unknown", 30_000, 1),
            row("B", "e2", "b.smt2", "sat", 100, 1),
        ])
        .expect("insert B");
    let rep_e1 =
        diff_from_store(&store, "A", "B", Some("e1"), DiffOptions::default()).expect("diff");
    assert_eq!(rep_e1.regressions.len(), 1);
    let rep_e2 =
        diff_from_store(&store, "A", "B", Some("e2"), DiffOptions::default()).expect("diff");
    assert_eq!(rep_e2.regressions.len(), 0);
}
