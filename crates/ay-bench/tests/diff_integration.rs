// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// Integration test: synthesize two runs at different (fake) commit hashes,
// persist them via the real `ResultsStore`, and verify that `compute_diff`
// produces the expected regression / improvement / slowdown classification.

use ay_bench::db::{ResultRow, ResultsStore};
use ay_bench::diff::{self, DiffOptions};
use tempfile::TempDir;

fn make_row(
    commit: &str,
    eval: &str,
    bench: &str,
    result: &str,
    runtime_ms: i64,
    verifier_ok: i32,
) -> ResultRow {
    ResultRow {
        commit_hash: commit.to_string(),
        eval_name: eval.to_string(),
        benchmark_path: bench.to_string(),
        result: result.to_string(),
        runtime_ms,
        memory_mb: 0,
        verifier_ok,
        timestamp: "2026-04-18T12:00:00Z".to_string(),
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
fn two_fake_commits_roundtrip_through_sqlite_and_diff() {
    let tmp = TempDir::new().expect("tempdir");
    let db_path = tmp.path().join(".ay-bench").join("results.sqlite");

    // Populate the store with two synthesized runs.
    {
        let mut store = ResultsStore::open(&db_path).expect("open store");
        let base = "a".repeat(40);
        let head = "b".repeat(40);
        let rows = vec![
            // Regression: solved -> unsolved.
            make_row(&base, "eval-sat", "bench1.cnf", "sat", 500, 1),
            make_row(&head, "eval-sat", "bench1.cnf", "unknown", 30_000, -1),
            // Improvement: unsolved -> solved.
            make_row(&base, "eval-sat", "bench2.cnf", "timeout", 30_000, -1),
            make_row(&head, "eval-sat", "bench2.cnf", "unsat", 400, 1),
            // Slowdown: same verdict, +60%.
            make_row(&base, "eval-sat", "bench3.cnf", "sat", 1_000, 1),
            make_row(&head, "eval-sat", "bench3.cnf", "sat", 1_600, 1),
            // Unchanged (stable runtime).
            make_row(&base, "eval-sat", "bench4.cnf", "sat", 1_000, 1),
            make_row(&head, "eval-sat", "bench4.cnf", "sat", 1_050, 1),
            // Wrong-answer regression: correct -> wrong.
            make_row(&base, "eval-sat", "bench5.cnf", "sat", 100, 1),
            make_row(&head, "eval-sat", "bench5.cnf", "sat", 100, 0),
            // Filtered out by eval scope (different eval).
            make_row(&base, "eval-other", "bench6.smt2", "sat", 100, 1),
            make_row(&head, "eval-other", "bench6.smt2", "unknown", 30_000, -1),
        ];
        store.upsert_rows(&rows).expect("upsert");
    }

    // Reopen (verify data survives across handles).
    let store = ResultsStore::open(&db_path).expect("reopen store");
    let base = "a".repeat(40);
    let head = "b".repeat(40);

    // Diff scoped to `eval-sat` only.
    let rep = diff::diff_from_store(
        &store,
        &base,
        &head,
        Some("eval-sat"),
        DiffOptions::default(),
    )
    .expect("diff");

    assert_eq!(
        rep.regressions.len(),
        2,
        "expected 2 regressions (solved->unsolved, correct->wrong)"
    );
    assert_eq!(rep.improvements.len(), 1);
    assert_eq!(rep.slowdowns.len(), 1);
    assert_eq!(rep.unchanged_count, 1);

    // Ensure the other-eval rows were filtered out.
    for r in &rep.regressions {
        assert_eq!(r.eval_name, "eval-sat");
    }

    // Diff without filter — should include the `eval-other` regression too.
    let rep_all = diff::diff_from_store(&store, &base, &head, None, DiffOptions::default())
        .expect("diff all");
    assert_eq!(rep_all.regressions.len(), 3);

    // has_regressions() wired correctly.
    assert!(rep.has_regressions());

    // Rendering smoke-tests — should always include the Regressions header.
    let table = diff::render_table(&rep);
    assert!(table.contains("Regressions"));
    assert!(table.contains("bench1.cnf"));
    let json = diff::render_json(&rep).expect("render_json");
    assert!(json.contains("\"regressions\""));
}

#[test]
fn empty_store_diff_returns_no_regressions() {
    let tmp = TempDir::new().expect("tempdir");
    let db_path = tmp.path().join(".ay-bench").join("results.sqlite");
    let store = ResultsStore::open(&db_path).expect("open");

    let rep = diff::diff_from_store(&store, "deadbeef", "cafebabe", None, DiffOptions::default())
        .expect("diff");

    assert_eq!(rep.regressions.len(), 0);
    assert_eq!(rep.improvements.len(), 0);
    assert!(!rep.has_regressions());
}
