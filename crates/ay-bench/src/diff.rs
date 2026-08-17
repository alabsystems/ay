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
                if let Some(reason) = match (resources_match, content_matches) {
                    (false, false) => Some("resource envelope and benchmark content differ"),
                    (false, true) => Some("resource envelope differs"),
                    (true, false) => Some("benchmark content differs"),
                    (true, true) => None,
                } {
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
mod tests;
