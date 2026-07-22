// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Integration tests for `ay bench cross-verify` (issue #8711, Phase 3).
//!
//! Exercises `classify_answers`, `build_report`, `cmd_cross_verify`, and
//! `render_cross_table` against an in-memory baseline store.

use std::collections::BTreeMap;
use std::path::PathBuf;

use ay_bench::cross_verify::{
    build_report, classify_answers, cmd_cross_verify, render_cross_table, CrossClass, CrossEntry,
    CrossReport, CrossVerifyArgs,
};
use ay_bench::harvest::{BaselineRow, BaselineStore};

fn sample(corpus: &str, bench: &str, solver: &str, answer: &str) -> BaselineRow {
    BaselineRow {
        corpus: corpus.to_string(),
        benchmark_path: bench.to_string(),
        content_hash: "fh128:deadbeef".to_string(),
        solver: solver.to_string(),
        solver_version: "v1".to_string(),
        answer: answer.to_string(),
        expected: "unknown".to_string(),
        wall_ms: 10,
        exit_code: Some(0),
        timeout_s: 30.0,
        stdout_head: String::new(),
        stderr_head: String::new(),
        harvested_at: "unix:1".to_string(),
        resource_requested_jobs: 1,
        resource_jobs: 1,
        resource_memlimit_mb: 1024,
        resource_nbcore: 1,
        resource_headroom_mb: 16000,
        resource_enforcement: "test".to_string(),
    }
}

// ---------- classify_answers ----------

#[test]
fn classify_all_agree_sat() {
    let answers = [Some("sat"), Some("sat"), Some("sat")];
    assert_eq!(classify_answers(&answers), CrossClass::Agree);
}

#[test]
fn classify_all_agree_unsat_mixed_case() {
    let answers = [Some("UNSAT"), Some("unsat")];
    assert_eq!(classify_answers(&answers), CrossClass::Agree);
}

#[test]
fn classify_dispute() {
    let answers = [Some("sat"), Some("unsat")];
    assert_eq!(classify_answers(&answers), CrossClass::Dispute);
}

#[test]
fn classify_dispute_three_solvers_majority() {
    // Two agree, one disagrees — still a dispute (any definite/definite
    // disagreement is a ref_wrong signal).
    let answers = [Some("sat"), Some("sat"), Some("unsat")];
    assert_eq!(classify_answers(&answers), CrossClass::Dispute);
}

#[test]
fn classify_partial_timeout() {
    let answers = [Some("sat"), Some("timeout")];
    assert_eq!(classify_answers(&answers), CrossClass::Partial);
}

#[test]
fn classify_partial_unknown() {
    let answers = [Some("unsat"), Some("unknown")];
    assert_eq!(classify_answers(&answers), CrossClass::Partial);
}

#[test]
fn classify_partial_all_unknown() {
    let answers = [Some("unknown"), Some("timeout")];
    assert_eq!(classify_answers(&answers), CrossClass::Partial);
}

#[test]
fn classify_missing_solver_row() {
    let answers = [Some("sat"), None];
    assert_eq!(classify_answers(&answers), CrossClass::Missing);
}

// ---------- build_report (in-memory store) ----------

#[test]
fn build_report_agree_and_dispute() {
    // Seed: 2 benchmarks, one agrees (both solvers unsat), one disputes
    // (z3 sat vs golem unsat). This mirrors the minimal "one agree, one
    // dispute" integration case called out in issue #8711 Phase 3.
    let mut store = BaselineStore::open_in_memory().expect("open");
    let rows = vec![
        sample("c1", "agree.smt2", "z3", "unsat"),
        sample("c1", "agree.smt2", "golem", "unsat"),
        sample("c1", "dispute.smt2", "z3", "sat"),
        sample("c1", "dispute.smt2", "golem", "unsat"),
    ];
    store.upsert_rows(&rows).expect("upsert");

    let report =
        build_report(&store, "c1", &["z3".to_string(), "golem".to_string()]).expect("report");

    assert_eq!(report.total, 2);
    assert_eq!(report.agree, 1);
    assert_eq!(report.dispute, 1);
    assert_eq!(report.partial, 0);
    assert_eq!(report.missing, 0);
    assert!(report.has_disputes());

    let dispute = report
        .entries
        .iter()
        .find(|e| e.classification == "dispute")
        .expect("has dispute entry");
    assert_eq!(dispute.benchmark_path, "dispute.smt2");
    assert_eq!(
        dispute.answers.get("z3").and_then(Option::as_deref),
        Some("sat")
    );
    assert_eq!(
        dispute.answers.get("golem").and_then(Option::as_deref),
        Some("unsat")
    );
}

#[test]
fn build_report_partial_and_missing() {
    let mut store = BaselineStore::open_in_memory().expect("open");
    let rows = vec![
        // partial: z3 unknown, golem unsat
        sample("c1", "a.smt2", "z3", "unknown"),
        sample("c1", "a.smt2", "golem", "unsat"),
        // missing: only z3 has a row
        sample("c1", "b.smt2", "z3", "sat"),
    ];
    store.upsert_rows(&rows).expect("upsert");

    let report =
        build_report(&store, "c1", &["z3".to_string(), "golem".to_string()]).expect("report");

    assert_eq!(report.total, 2);
    assert_eq!(report.partial, 1);
    assert_eq!(report.missing, 1);
    assert_eq!(report.dispute, 0);
    assert!(!report.has_disputes());
}

#[test]
fn build_report_rejects_unknown_corpus() {
    let store = BaselineStore::open_in_memory().expect("open");
    let err = build_report(
        &store,
        "does-not-exist",
        &["z3".to_string(), "golem".to_string()],
    )
    .expect_err("empty corpus should error");
    let msg = format!("{err}");
    assert!(msg.contains("does-not-exist"), "msg={msg}");
}

#[test]
fn build_report_handles_partial_solver_coverage() {
    let mut store = BaselineStore::open_in_memory().expect("open");
    store
        .upsert_rows(&[sample("c1", "a.smt2", "z3", "sat")])
        .expect("upsert");
    // cvc5 has no rows at all for c1 — but z3 does. The report should
    // classify this as Missing (not bail).
    let report =
        build_report(&store, "c1", &["z3".to_string(), "cvc5".to_string()]).expect("report");
    assert_eq!(report.total, 1);
    assert_eq!(report.missing, 1);
}

#[test]
fn build_report_bails_when_no_solver_matches() {
    let mut store = BaselineStore::open_in_memory().expect("open");
    store
        .upsert_rows(&[sample("c1", "a.smt2", "z3", "sat")])
        .expect("upsert");
    let err = build_report(&store, "c1", &["cvc5".to_string(), "bitwuzla".to_string()])
        .expect_err("no matching solvers");
    let msg = format!("{err}");
    assert!(msg.contains("no rows matching"), "msg={msg}");
}

// ---------- cmd_cross_verify (args validation) ----------

#[test]
fn cmd_cross_verify_rejects_single_solver() {
    let args = CrossVerifyArgs {
        corpus: "c1".into(),
        solvers: vec!["z3".into()],
        baseline_store: Some(PathBuf::from("/tmp/does-not-exist.sqlite")),
        json: false,
    };
    let err = cmd_cross_verify(args).expect_err("needs >=2");
    assert!(format!("{err}").contains("at least 2"), "err={err}");
}

#[test]
fn cmd_cross_verify_dedup_solver_list() {
    let args = CrossVerifyArgs {
        corpus: "c1".into(),
        solvers: vec!["z3".into(), "z3".into()],
        baseline_store: Some(PathBuf::from("/tmp/also-does-not-exist.sqlite")),
        json: false,
    };
    // After dedup, only one distinct solver remains — should error.
    let err = cmd_cross_verify(args).expect_err("needs >=2 distinct");
    assert!(format!("{err}").contains("distinct"), "err={err}");
}

// ---------- render_cross_table ----------

#[test]
fn render_cross_table_no_disputes() {
    let report = CrossReport {
        corpus: "c1".into(),
        solvers: vec!["z3".into(), "golem".into()],
        total: 2,
        agree: 2,
        dispute: 0,
        partial: 0,
        missing: 0,
        entries: vec![],
    };
    let text = render_cross_table(&report);
    assert!(text.contains("corpus: c1"));
    assert!(text.contains("solvers: z3, golem"));
    assert!(text.contains("total benchmarks: 2"));
    assert!(text.contains("=== DISPUTES ==="));
    assert!(text.contains("(none)"));
}

#[test]
fn render_cross_table_with_disputes() {
    let mut answers = BTreeMap::new();
    answers.insert("z3".to_string(), Some("sat".to_string()));
    answers.insert("golem".to_string(), Some("unsat".to_string()));
    let report = CrossReport {
        corpus: "c1".into(),
        solvers: vec!["z3".into(), "golem".into()],
        total: 1,
        agree: 0,
        dispute: 1,
        partial: 0,
        missing: 0,
        entries: vec![CrossEntry {
            benchmark_path: "d.smt2".into(),
            answers,
            classification: "dispute".into(),
        }],
    };
    let text = render_cross_table(&report);
    assert!(text.contains("disputes (ref-vs-ref disagreement): 1"));
    assert!(text.contains("d.smt2"));
    assert!(text.contains("z3=sat"));
    assert!(text.contains("golem=unsat"));
}
