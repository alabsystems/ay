// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use std::collections::BTreeMap;
use std::path::PathBuf;
use std::time::Duration;

use ay_bench::ResourcePlan;

use super::super::{BenchConfig, BenchOutcome, Category, DivStats, FileRecord, OutcomeKind};
use super::render_report;
use crate::diff::Verdict;

fn outcome(kind: OutcomeKind, wall_ms: u64) -> BenchOutcome {
    BenchOutcome {
        kind,
        wall: Duration::from_millis(wall_ms),
        peak_rss: None,
    }
}

fn record(
    file: PathBuf,
    category: Category,
    ay: BenchOutcome,
    z3: BenchOutcome,
    ratio: Option<f64>,
) -> FileRecord {
    FileRecord {
        division: "synthetic/QF_TEST".to_string(),
        file,
        ay,
        z3,
        category,
        ratio,
    }
}

fn synthetic_records() -> Vec<FileRecord> {
    let sat = || outcome(OutcomeKind::Verdicts(vec![Verdict::Sat]), 1);
    let mut records = vec![
        record(
            PathBuf::from("crash.smt2"),
            Category::CrashAy,
            outcome(OutcomeKind::Crash("signal 6".to_string()), 1),
            sat(),
            None,
        ),
        record(
            PathBuf::from("timeout.smt2"),
            Category::TimeoutAy,
            outcome(OutcomeKind::Timeout, 20_000),
            sat(),
            None,
        ),
        record(
            PathBuf::from("memout.smt2"),
            Category::MemoutAy,
            outcome(OutcomeKind::MemoryLimit, 50),
            sat(),
            None,
        ),
        record(
            PathBuf::from("unknown.smt2"),
            Category::AyUnknownZ3Decided,
            outcome(OutcomeKind::Verdicts(vec![Verdict::Unknown]), 1),
            sat(),
            None,
        ),
        record(
            PathBuf::from("no-verdict.smt2"),
            Category::Other,
            outcome(OutcomeKind::Verdicts(Vec::new()), 1),
            sat(),
            None,
        ),
    ];
    records.extend((0_u32..21).map(|index| {
        let ratio = f64::from(index) + 3.0;
        record(
            PathBuf::from(format!("slow-{index:02}.smt2")),
            Category::AgreeSat,
            outcome(
                OutcomeKind::Verdicts(vec![Verdict::Sat]),
                u64::from(index + 3) * 10,
            ),
            outcome(OutcomeKind::Verdicts(vec![Verdict::Sat]), 10),
            Some(ratio),
        )
    }));
    records
}

fn synthetic_report() -> String {
    let records = synthetic_records();
    let mut division = DivStats::default();
    let mut totals = DivStats::default();
    for record in &records {
        division.add(record);
        totals.add(record);
    }
    let divisions = BTreeMap::from([("synthetic/QF_TEST".to_string(), division)]);
    let cfg = BenchConfig {
        ay: PathBuf::from("renderer-test-missing-ay"),
        z3: PathBuf::from("renderer-test-missing-z3"),
        roots: vec![PathBuf::from("benchmarks/smtlib-sample")],
        timeout_secs: 20,
        jobs: 8,
        json_stdout: false,
        json_out: PathBuf::from("unused.json"),
        report_out: PathBuf::from("unused.md"),
    };
    let resource_plan = ResourcePlan {
        requested_jobs: 8,
        jobs: 3,
        memlimit_mb_per_child: 2048,
        nbcore_per_child: 2,
        headroom_mb: 16_384,
        planner: "scripts/_oom_guard.py".to_string(),
    };
    let resource_evidence = serde_json::json!({
        "hard_timeout_secs": 22.0,
        "external_ffi": { "execution_envelope": "test-envelope" },
    });
    render_report(
        &cfg,
        &records,
        &divisions,
        &totals,
        Some("AY test version"),
        Some("z3 test version"),
        Duration::from_millis(1234),
        &resource_plan,
        &resource_evidence,
    )
}

fn assert_in_order(text: &str, expected: &[&str]) {
    let mut remainder = text;
    for needle in expected {
        let position = remainder
            .find(needle)
            .unwrap_or_else(|| panic!("missing ordered report fragment: {needle}"));
        remainder = &remainder[position + needle.len()..];
    }
}

#[test]
fn report_preserves_section_order_and_z3_truncation() {
    let report = synthetic_report();
    assert_in_order(
        &report,
        &[
            "# AY vs z3 — differential benchmark report",
            "## Reproduce",
            "## Soundness: sat-vs-unsat disagreements",
            "## Per-division results",
            "## Where z3 wins",
            "## Where AY wins",
            "## Methodology",
        ],
    );
    assert_in_order(
        &report,
        &[
            "### AY crashes (1)",
            "### AY timed out where z3 decided (1 files)",
            "### AY exceeded its memory envelope where z3 decided (1 files)",
            "### AY answered `unknown` where z3 decided (1 files)",
            "### AY produced no verdict where z3 decided (1 files)",
            "### z3 more than 2x faster (decided-by-both; 21 files, top 20 by ratio)",
        ],
    );
    let z3_section = report
        .split_once("## Where z3 wins")
        .and_then(|(_, tail)| tail.split_once("## Where AY wins"))
        .map(|(section, _)| section)
        .expect("ordered z3-win section");
    assert_eq!(z3_section.matches("| `slow-").count(), 20);
    assert!(z3_section.contains("| `slow-01.smt2` |"));
    assert!(!z3_section.contains("slow-00.smt2"));
    assert!(report.contains("SCOPE: these numbers describe exactly those roots and"));
    assert!(report.contains("| exact execution envelope | `test-envelope` |"));
    assert!(report.contains("**DISAGREE = 0** across 26 files."));
}
