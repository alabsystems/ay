// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// Acceptance-criteria tests for #8723.
//
// These complement `diff_integration.rs` by pinning the exact wire-level
// behaviours that a pre-commit hook or CI pipeline depends on:
//
//   1. `ay-bench run` appends rows keyed by commit hash (verified via the
//      public `db::ResultsStore` upsert roundtrip — the same code path the
//      `runner` module uses after each eval completes).
//   2. `ay bench diff` reports regressions / improvements / slowdowns
//      correctly in both human- and machine-readable formats.
//   3. `ay bench diff` signals regressions via `has_regressions()` so the
//      CLI can map to a non-zero exit code for commit hooks / CI.
//   4. A tmpdir sqlite can be written and diffed without touching any
//      repo-relative state.

use ay_bench::db::{ResultRow, ResultsStore};
use ay_bench::diff::{self, DiffOptions};
use tempfile::TempDir;

const BASE_SHA: &str = "0000000000000000000000000000000000000000";
const HEAD_SHA: &str = "1111111111111111111111111111111111111111";
const EVAL: &str = "test-diff-8723";

fn row(commit: &str, bench: &str, result: &str, runtime_ms: i64, verifier_ok: i32) -> ResultRow {
    ResultRow {
        commit_hash: commit.to_string(),
        eval_name: EVAL.to_string(),
        benchmark_path: bench.to_string(),
        result: result.to_string(),
        runtime_ms,
        memory_mb: 0,
        verifier_ok,
        timestamp: "2026-04-19T00:00:00Z".to_string(),
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

fn seeded_store(tmp: &TempDir) -> ResultsStore {
    let db_path = tmp.path().join(".ay-bench").join("results.sqlite");
    let mut store = ResultsStore::open(&db_path).expect("open");
    let rows = vec![
        // solved -> unsolved regression
        row(BASE_SHA, "b1.cnf", "sat", 500, 1),
        row(HEAD_SHA, "b1.cnf", "unknown", 30_000, -1),
        // unsolved -> solved improvement
        row(BASE_SHA, "b2.cnf", "timeout", 30_000, -1),
        row(HEAD_SHA, "b2.cnf", "unsat", 400, 1),
        // 60% slowdown (same verdict)
        row(BASE_SHA, "b3.cnf", "sat", 1_000, 1),
        row(HEAD_SHA, "b3.cnf", "sat", 1_600, 1),
        // 50% speedup (same verdict)
        row(BASE_SHA, "b4.cnf", "sat", 2_000, 1),
        row(HEAD_SHA, "b4.cnf", "sat", 1_000, 1),
        // stable
        row(BASE_SHA, "b5.cnf", "sat", 1_000, 1),
        row(HEAD_SHA, "b5.cnf", "sat", 1_050, 1),
        // correct -> wrong (soundness regression)
        row(BASE_SHA, "b6.cnf", "sat", 100, 1),
        row(HEAD_SHA, "b6.cnf", "sat", 100, 0),
    ];
    store.upsert_rows(&rows).expect("upsert");
    store
}

#[test]
fn diff_classifies_every_transition_type() {
    let tmp = TempDir::new().expect("tempdir");
    let store = seeded_store(&tmp);
    let rep = diff::diff_from_store(
        &store,
        BASE_SHA,
        HEAD_SHA,
        Some(EVAL),
        DiffOptions::default(),
    )
    .expect("diff");

    // 2 regressions (solved->unsolved + correct->wrong).
    assert_eq!(rep.regressions.len(), 2, "regressions");
    // 1 improvement (timeout->unsat).
    assert_eq!(rep.improvements.len(), 1, "improvements");
    // 1 slowdown above the 20% default threshold (60% delta).
    assert_eq!(rep.slowdowns.len(), 1, "slowdowns");
    // 1 speedup at 50% (>20% threshold).
    assert_eq!(rep.speedups.len(), 1, "speedups");
    // 1 unchanged (5% delta, below threshold).
    assert_eq!(rep.unchanged_count, 1, "unchanged");
}

#[test]
fn has_regressions_signals_ci_exit_code() {
    // Store with zero rows on both sides: no regressions => exit 0.
    let tmp = TempDir::new().expect("tempdir");
    let db_path = tmp.path().join(".ay-bench").join("results.sqlite");
    let store = ResultsStore::open(&db_path).expect("open");
    let rep_empty = diff::diff_from_store(&store, BASE_SHA, HEAD_SHA, None, DiffOptions::default())
        .expect("diff");
    assert!(!rep_empty.has_regressions(), "empty store must not block");

    // Seeded store with at least one regression => exit 1.
    let tmp = TempDir::new().expect("tempdir");
    let store = seeded_store(&tmp);
    let rep = diff::diff_from_store(
        &store,
        BASE_SHA,
        HEAD_SHA,
        Some(EVAL),
        DiffOptions::default(),
    )
    .expect("diff");
    assert!(rep.has_regressions(), "seeded regressions must block");
}

#[test]
fn slowdown_threshold_is_configurable() {
    let tmp = TempDir::new().expect("tempdir");
    let store = seeded_store(&tmp);

    // 100% threshold: 60% slowdown and 50% speedup both drop below.
    let opts = DiffOptions {
        slowdown_threshold_pct: 100.0,
    };
    let rep = diff::diff_from_store(&store, BASE_SHA, HEAD_SHA, Some(EVAL), opts).expect("diff");
    assert_eq!(
        rep.slowdowns.len(),
        0,
        "100% threshold filters 60% slowdown"
    );
    assert_eq!(rep.speedups.len(), 0, "100% threshold filters 50% speedup");

    // 10% threshold: the 5% stable row also becomes a slowdown? No — 5% < 10%.
    let opts = DiffOptions {
        slowdown_threshold_pct: 10.0,
    };
    let rep = diff::diff_from_store(&store, BASE_SHA, HEAD_SHA, Some(EVAL), opts).expect("diff");
    assert_eq!(rep.slowdowns.len(), 1, "60% still above 10%");
    assert_eq!(rep.speedups.len(), 1, "50% speedup still above 10%");
}

#[test]
fn json_output_is_machine_readable() {
    let tmp = TempDir::new().expect("tempdir");
    let store = seeded_store(&tmp);
    let rep = diff::diff_from_store(
        &store,
        BASE_SHA,
        HEAD_SHA,
        Some(EVAL),
        DiffOptions::default(),
    )
    .expect("diff");

    let json = diff::render_json(&rep).expect("render_json");
    // Exact schema keys consumed by CI tooling.
    assert!(json.contains("\"base_commit\""));
    assert!(json.contains("\"head_commit\""));
    assert!(json.contains("\"regressions\""));
    assert!(json.contains("\"improvements\""));
    assert!(json.contains("\"slowdowns\""));
    assert!(json.contains("\"speedups\""));
    assert!(json.contains("\"slowdown_threshold_pct\""));
    // Regression body carries enough context for a PR comment.
    assert!(json.contains("b1.cnf"));

    // Round-trip through serde_json to confirm validity.
    let parsed: serde_json::Value =
        serde_json::from_str(&json).expect("json must be valid for CI consumers");
    assert!(parsed
        .get("regressions")
        .and_then(|v| v.as_array())
        .is_some());
}

#[test]
fn table_output_always_shows_regressions_section() {
    let tmp = TempDir::new().expect("tempdir");
    let store = seeded_store(&tmp);
    let rep = diff::diff_from_store(
        &store,
        BASE_SHA,
        HEAD_SHA,
        Some(EVAL),
        DiffOptions::default(),
    )
    .expect("diff");

    let table = diff::render_table(&rep);
    assert!(table.contains("Regressions"));
    // Per-row formatting includes the eval scope so multi-eval runs stay
    // unambiguous in a single report.
    assert!(table.contains("[test-diff-8723]"));
    assert!(table.contains("b1.cnf"));
}

#[test]
fn markdown_output_is_pr_comment_ready() {
    let tmp = TempDir::new().expect("tempdir");
    let store = seeded_store(&tmp);
    let rep = diff::diff_from_store(
        &store,
        BASE_SHA,
        HEAD_SHA,
        Some(EVAL),
        DiffOptions::default(),
    )
    .expect("diff");

    let md = diff::render_markdown(&rep);
    // Headers suitable for a GitHub PR comment.
    assert!(md.contains("## ay-bench diff"));
    assert!(md.contains("### Regressions"));
    // Markdown tables render cleanly in GitHub.
    assert!(md.contains("| Eval | Benchmark |"));
}

#[test]
fn eval_filter_scopes_the_diff() {
    // Two eval scopes in the same store.
    let tmp = TempDir::new().expect("tempdir");
    let db_path = tmp.path().join(".ay-bench").join("results.sqlite");
    let mut store = ResultsStore::open(&db_path).expect("open");

    let other_eval = ResultRow {
        eval_name: "other-eval".to_string(),
        ..row(HEAD_SHA, "x.cnf", "unknown", 30_000, -1)
    };
    let other_eval_base = ResultRow {
        eval_name: "other-eval".to_string(),
        ..row(BASE_SHA, "x.cnf", "sat", 100, 1)
    };
    store
        .upsert_rows(&[other_eval_base, other_eval])
        .expect("seed");

    // Seeded eval rows for EVAL.
    let seeded = seeded_store(&tmp); // reopens same db_path
    drop(seeded);

    let store = ResultsStore::open(&db_path).expect("reopen");

    // With filter: only EVAL rows counted.
    let rep = diff::diff_from_store(
        &store,
        BASE_SHA,
        HEAD_SHA,
        Some(EVAL),
        DiffOptions::default(),
    )
    .expect("diff filtered");
    assert_eq!(rep.regressions.len(), 2);

    // Without filter: also includes the `other-eval` regression.
    let rep_all = diff::diff_from_store(&store, BASE_SHA, HEAD_SHA, None, DiffOptions::default())
        .expect("diff all");
    assert_eq!(rep_all.regressions.len(), 3);
}
