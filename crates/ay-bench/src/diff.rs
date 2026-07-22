// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Compute and render the diff between two commits stored in the bench results DB.
//!
//! The diff classifies every (eval, benchmark) pair into one of four buckets:
//!
//! * **Regression**: was solved + verified, now unsolved OR wrong answer
//!   (solved → unsolved, correct → wrong). ALWAYS shown.
//! * **Improvement**: was unsolved, now solved.
//! * **Slowdown**: same verdict both sides, but runtime grew by more than the
//!   threshold (default 20%).
//! * **Speedup**: same verdict, runtime dropped by more than the threshold.
//!
//! Benchmarks that exist on only one side (newly added / removed) are surfaced
//! under `added` / `removed` but do not count as regressions.
//!
//! Exit code: `has_regressions()` returns `true` iff the Regressions section is
//! non-empty. The CLI maps that to a non-zero exit status so commit hooks / CI
//! can fail fast.

use crate::db::{ResultRow, ResultsStore};
use crate::error::Result;
use serde::Serialize;
use std::collections::{BTreeMap, BTreeSet};

// ===================================================================
// Result classification
// ===================================================================

/// The three verdict classes we collapse results into.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub enum Verdict {
    Solved,
    WrongAnswer,
    Unsolved,
}

/// Collapse a `(result, verifier_ok)` pair into a `Verdict`.
///
/// Rules:
/// * `sat` / `unsat` with `verifier_ok == 0` → `WrongAnswer` (diverged from reference)
/// * `sat` / `unsat` with `verifier_ok != 0` → `Solved` (including -1 "unchecked",
///   because the default mode does not compare against a reference; we trust
///   the solver until proven otherwise).
/// * everything else (`unknown`, `timeout`, `error`, ...) → `Unsolved`.
#[must_use]
pub fn classify(result: &str, verifier_ok: i32) -> Verdict {
    let r = result.trim().to_ascii_lowercase();
    let is_verdict = r == "sat" || r == "unsat";
    if is_verdict {
        if verifier_ok == 0 {
            Verdict::WrongAnswer
        } else {
            Verdict::Solved
        }
    } else {
        Verdict::Unsolved
    }
}

// ===================================================================
// Diff entries
// ===================================================================

#[derive(Debug, Clone, Serialize)]
pub struct DiffEntry {
    pub eval_name: String,
    pub benchmark_path: String,
    pub base_result: Option<String>,
    pub head_result: Option<String>,
    pub base_runtime_ms: Option<i64>,
    pub head_runtime_ms: Option<i64>,
    pub base_verdict: Option<Verdict>,
    pub head_verdict: Option<Verdict>,
    /// Percent change `(head - base) / base * 100`, only set for slowdowns/speedups.
    pub runtime_delta_pct: Option<f64>,
}

/// A row present on both sides whose admitted execution envelopes differ (or
/// whose legacy row has no envelope provenance). Such a row must never enter
/// correctness or runtime-delta classification.
#[derive(Debug, Clone, Serialize)]
pub struct NonComparableEntry {
    pub eval_name: String,
    pub benchmark_path: String,
    pub reason: String,
    pub base_resource_envelope: Option<String>,
    pub head_resource_envelope: Option<String>,
    pub base_content_hash: Option<String>,
    pub head_content_hash: Option<String>,
}

#[derive(Debug, Clone, Serialize)]
pub struct DiffReport {
    pub base_commit: String,
    pub head_commit: String,
    pub slowdown_threshold_pct: f64,
    pub regressions: Vec<DiffEntry>,
    pub improvements: Vec<DiffEntry>,
    pub slowdowns: Vec<DiffEntry>,
    pub speedups: Vec<DiffEntry>,
    pub added: Vec<DiffEntry>,
    pub removed: Vec<DiffEntry>,
    pub non_comparable: Vec<NonComparableEntry>,
    /// Benchmarks with unchanged verdict and runtime within threshold.
    pub unchanged_count: usize,
}

impl DiffReport {
    #[must_use]
    pub fn has_regressions(&self) -> bool {
        !self.regressions.is_empty()
    }

    #[must_use]
    pub fn has_non_comparable(&self) -> bool {
        !self.non_comparable.is_empty()
    }

    #[must_use]
    pub fn total_base(&self) -> usize {
        self.regressions.len()
            + self.improvements.len()
            + self.slowdowns.len()
            + self.speedups.len()
            + self.removed.len()
            + self.non_comparable.len()
            + self.unchanged_count
    }
}

// ===================================================================
// Diff computation
// ===================================================================

/// Inputs to the diff computation. Threshold is a percentage (20.0 = 20%).
#[derive(Debug, Clone, Copy)]
pub struct DiffOptions {
    pub slowdown_threshold_pct: f64,
}

impl Default for DiffOptions {
    fn default() -> Self {
        Self {
            slowdown_threshold_pct: 20.0,
        }
    }
}

/// Compute a `DiffReport` from two sets of rows.
///
/// Rows are keyed by `(eval_name, benchmark_path)`. Both sides must already be
/// scoped to their respective commits; this function does no DB lookups.
#[must_use]
pub fn compute_diff(
    base_commit: &str,
    base_rows: &[ResultRow],
    head_commit: &str,
    head_rows: &[ResultRow],
    opts: DiffOptions,
) -> DiffReport {
    type Key = (String, String);
    let index = |rows: &[ResultRow]| -> BTreeMap<Key, ResultRow> {
        rows.iter()
            .map(|r| ((r.eval_name.clone(), r.benchmark_path.clone()), r.clone()))
            .collect()
    };

    let base_map = index(base_rows);
    let head_map = index(head_rows);

    let keys: BTreeSet<Key> = base_map.keys().chain(head_map.keys()).cloned().collect();
    let keys: Vec<Key> = keys.into_iter().collect();

    let mut regressions = Vec::new();
    let mut improvements = Vec::new();
    let mut slowdowns = Vec::new();
    let mut speedups = Vec::new();
    let mut added = Vec::new();
    let mut removed = Vec::new();
    let mut non_comparable = Vec::new();
    let mut unchanged_count = 0usize;

    for (eval, bench) in keys {
        let base = base_map.get(&(eval.clone(), bench.clone()));
        let head = head_map.get(&(eval.clone(), bench.clone()));

        match (base, head) {
            (None, None) => {}
            (Some(b), None) => {
                removed.push(DiffEntry {
                    eval_name: eval,
                    benchmark_path: bench,
                    base_result: Some(b.result.clone()),
                    head_result: None,
                    base_runtime_ms: Some(b.runtime_ms),
                    head_runtime_ms: None,
                    base_verdict: Some(classify(&b.result, b.verifier_ok)),
                    head_verdict: None,
                    runtime_delta_pct: None,
                });
            }
            (None, Some(h)) => {
                added.push(DiffEntry {
                    eval_name: eval,
                    benchmark_path: bench,
                    base_result: None,
                    head_result: Some(h.result.clone()),
                    base_runtime_ms: None,
                    head_runtime_ms: Some(h.runtime_ms),
                    base_verdict: None,
                    head_verdict: Some(classify(&h.result, h.verifier_ok)),
                    runtime_delta_pct: None,
                });
            }
            (Some(b), Some(h)) => {
                let resources_match = matches!(
                    (&b.resource_envelope, &h.resource_envelope),
                    (Some(base), Some(head)) if base == head
                );
                let content_matches = matches!(
                    (&b.benchmark_content_hash, &h.benchmark_content_hash),
                    (Some(base), Some(head)) if base == head
                );
                if !resources_match || !content_matches {
                    let reason = match (resources_match, content_matches) {
                        (false, false) => "resource envelope and benchmark content differ",
                        (false, true) => "resource envelope differs",
                        (true, false) => "benchmark content differs",
                        (true, true) => unreachable!(),
                    };
                    non_comparable.push(NonComparableEntry {
                        eval_name: eval,
                        benchmark_path: bench,
                        reason: reason.to_string(),
                        base_resource_envelope: b.resource_envelope.clone(),
                        head_resource_envelope: h.resource_envelope.clone(),
                        base_content_hash: b.benchmark_content_hash.clone(),
                        head_content_hash: h.benchmark_content_hash.clone(),
                    });
                    continue;
                }
                let bv = classify(&b.result, b.verifier_ok);
                let hv = classify(&h.result, h.verifier_ok);

                let entry = |delta: Option<f64>| DiffEntry {
                    eval_name: eval.clone(),
                    benchmark_path: bench.clone(),
                    base_result: Some(b.result.clone()),
                    head_result: Some(h.result.clone()),
                    base_runtime_ms: Some(b.runtime_ms),
                    head_runtime_ms: Some(h.runtime_ms),
                    base_verdict: Some(bv),
                    head_verdict: Some(hv),
                    runtime_delta_pct: delta,
                };

                match (bv, hv) {
                    // Regression: was Solved, now Unsolved or WrongAnswer.
                    (Verdict::Solved, Verdict::Unsolved)
                    | (Verdict::Solved, Verdict::WrongAnswer) => {
                        regressions.push(entry(None));
                    }
                    // Regression: was WrongAnswer, now still WrongAnswer on a
                    // different verdict OR became Unsolved — we classify as
                    // regression iff a previously *correct* result is gone.
                    // WrongAnswer → Unsolved: silent improvement (no longer
                    // wrong), we surface it as `improvement`.
                    (Verdict::WrongAnswer, Verdict::Unsolved) => {
                        improvements.push(entry(None));
                    }
                    // Improvement: unsolved → solved, or unsolved → wrong-answer.
                    // The latter is technically a new bug, so flag it as a
                    // regression instead.
                    (Verdict::Unsolved, Verdict::Solved) => {
                        improvements.push(entry(None));
                    }
                    (Verdict::Unsolved, Verdict::WrongAnswer) => {
                        regressions.push(entry(None));
                    }
                    // WrongAnswer on both sides — keep surfaced as regression
                    // so the user still sees it. It's not new but also not
                    // fixed.
                    (Verdict::WrongAnswer, Verdict::WrongAnswer) => {
                        regressions.push(entry(None));
                    }
                    // WrongAnswer → Solved: improvement (correctness fixed).
                    (Verdict::WrongAnswer, Verdict::Solved) => {
                        improvements.push(entry(None));
                    }
                    // Same verdict on both sides — check runtime delta.
                    (a, b_same) if a == b_same => {
                        let delta = runtime_delta_pct(b.runtime_ms, h.runtime_ms);
                        match delta {
                            Some(d) if d > opts.slowdown_threshold_pct => {
                                slowdowns.push(entry(Some(d)));
                            }
                            Some(d) if d < -opts.slowdown_threshold_pct => {
                                speedups.push(entry(Some(d)));
                            }
                            _ => {
                                unchanged_count += 1;
                            }
                        }
                    }
                    _ => {
                        // Exhaustive; above matches cover all combinations.
                        unchanged_count += 1;
                    }
                }
            }
        }
    }

    DiffReport {
        base_commit: base_commit.to_string(),
        head_commit: head_commit.to_string(),
        slowdown_threshold_pct: opts.slowdown_threshold_pct,
        regressions,
        improvements,
        slowdowns,
        speedups,
        added,
        removed,
        non_comparable,
        unchanged_count,
    }
}

/// Compute `(head - base) / base * 100`. Returns `None` if `base` is zero or
/// negative (avoids division-by-zero and nonsensical deltas).
fn runtime_delta_pct(base_ms: i64, head_ms: i64) -> Option<f64> {
    if base_ms <= 0 {
        return None;
    }
    let base = base_ms as f64;
    let head = head_ms as f64;
    Some((head - base) / base * 100.0)
}

/// Convenience wrapper: load rows for two commits and compute the diff.
pub fn diff_from_store(
    store: &ResultsStore,
    base_commit: &str,
    head_commit: &str,
    eval_filter: Option<&str>,
    opts: DiffOptions,
) -> Result<DiffReport> {
    let base_rows = store.rows_for_commit(base_commit, eval_filter)?;
    let head_rows = store.rows_for_commit(head_commit, eval_filter)?;
    Ok(compute_diff(
        base_commit,
        &base_rows,
        head_commit,
        &head_rows,
        opts,
    ))
}

// ===================================================================
// Rendering
// ===================================================================

/// Human-readable table rendering of a `DiffReport` to stdout-friendly string.
#[must_use]
pub fn render_table(report: &DiffReport) -> String {
    let mut s = String::new();
    let short = |h: &str| {
        if h.len() >= 12 {
            h[..12].to_string()
        } else {
            h.to_string()
        }
    };
    s.push_str(&format!(
        "diff {} -> {} (slowdown threshold {:.0}%)\n",
        short(&report.base_commit),
        short(&report.head_commit),
        report.slowdown_threshold_pct,
    ));
    s.push_str(&format!(
        "  regressions={} improvements={} slowdowns={} speedups={} added={} removed={} non_comparable={} unchanged={}\n",
        report.regressions.len(),
        report.improvements.len(),
        report.slowdowns.len(),
        report.speedups.len(),
        report.added.len(),
        report.removed.len(),
        report.non_comparable.len(),
        report.unchanged_count,
    ));

    if !report.non_comparable.is_empty() {
        s.push_str("\n== Non-comparable evidence ==\n");
        for entry in &report.non_comparable {
            s.push_str(&format!(
                "  [{}] {} : {} (resources {} -> {}; content {} -> {})\n",
                entry.eval_name,
                entry.benchmark_path,
                entry.reason,
                entry
                    .base_resource_envelope
                    .as_deref()
                    .unwrap_or("<missing>"),
                entry
                    .head_resource_envelope
                    .as_deref()
                    .unwrap_or("<missing>"),
                entry.base_content_hash.as_deref().unwrap_or("<missing>"),
                entry.head_content_hash.as_deref().unwrap_or("<missing>"),
            ));
        }
    }

    // Regressions always shown, even if empty.
    s.push_str("\n== Regressions (solved/correct -> unsolved/wrong) ==\n");
    if report.regressions.is_empty() {
        s.push_str("  (none)\n");
    } else {
        for e in &report.regressions {
            s.push_str(&format!(
                "  [{}] {} : {} -> {}\n",
                e.eval_name,
                e.benchmark_path,
                e.base_result.as_deref().unwrap_or("-"),
                e.head_result.as_deref().unwrap_or("-"),
            ));
        }
    }

    if !report.improvements.is_empty() {
        s.push_str("\n== Improvements (unsolved/wrong -> solved) ==\n");
        for e in &report.improvements {
            s.push_str(&format!(
                "  [{}] {} : {} -> {}\n",
                e.eval_name,
                e.benchmark_path,
                e.base_result.as_deref().unwrap_or("-"),
                e.head_result.as_deref().unwrap_or("-"),
            ));
        }
    }

    if !report.slowdowns.is_empty() {
        s.push_str(&format!(
            "\n== Slowdowns (>{:.0}% runtime) ==\n",
            report.slowdown_threshold_pct
        ));
        for e in &report.slowdowns {
            s.push_str(&format!(
                "  [{}] {} : {}ms -> {}ms ({:+.1}%)\n",
                e.eval_name,
                e.benchmark_path,
                e.base_runtime_ms.unwrap_or(0),
                e.head_runtime_ms.unwrap_or(0),
                e.runtime_delta_pct.unwrap_or(0.0),
            ));
        }
    }

    if !report.speedups.is_empty() {
        s.push_str(&format!(
            "\n== Speedups (<-{:.0}% runtime) ==\n",
            report.slowdown_threshold_pct
        ));
        for e in &report.speedups {
            s.push_str(&format!(
                "  [{}] {} : {}ms -> {}ms ({:+.1}%)\n",
                e.eval_name,
                e.benchmark_path,
                e.base_runtime_ms.unwrap_or(0),
                e.head_runtime_ms.unwrap_or(0),
                e.runtime_delta_pct.unwrap_or(0.0),
            ));
        }
    }

    s
}

/// JSON rendering (pretty-printed).
pub fn render_json(report: &DiffReport) -> Result<String> {
    Ok(serde_json::to_string_pretty(report)?)
}

pub use crate::diff_markdown::render_markdown;

// ===================================================================
// Tests
// ===================================================================

#[cfg(test)]
mod tests {
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
}
