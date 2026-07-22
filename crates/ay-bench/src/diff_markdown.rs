// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! GitHub-flavored-markdown rendering for [`crate::diff::DiffReport`].
//!
//! Kept in a dedicated module so `diff.rs` stays focused on classification /
//! computation and remains under the 500-line cap. The format is intentionally
//! stable — external tooling (PR bots, dashboards) can parse the emitted
//! tables without reaching into the binary JSON form.
//!
//! Sections emitted (always, in this order):
//!   1. Title + base→head commit short-hashes.
//!   2. Single-line summary bullet of counters.
//!   3. `Regressions` table (always — `_none_` placeholder when empty).
//!   4. `Improvements` table.
//!   5. `Slowdowns` table (heading includes the threshold percentage).
//!
//! Speedups / added / removed / unchanged rows are summarised in the header
//! counters only; surfacing them as dedicated tables would clutter a PR
//! comment with noise. Consumers who need the full data should use the JSON
//! format.

use crate::diff::{DiffEntry, DiffReport};

/// Render a `DiffReport` as GitHub-flavored Markdown.
#[must_use]
pub fn render_markdown(report: &DiffReport) -> String {
    let mut s = String::new();
    write_header(&mut s, report);
    write_non_comparable_table(&mut s, report);
    write_verdict_table(&mut s, "### Regressions", &report.regressions);
    write_verdict_table(&mut s, "### Improvements", &report.improvements);
    write_slowdown_table(&mut s, report);
    s
}

fn write_header(s: &mut String, report: &DiffReport) {
    s.push_str(&format!(
        "## ay-bench diff: `{}` \u{2192} `{}`\n\n",
        short_hash(&report.base_commit),
        short_hash(&report.head_commit),
    ));
    s.push_str(&format!(
        "slowdown threshold: **{:.0}%** \u{00b7} regressions: **{}** \u{00b7} improvements: **{}** \u{00b7} slowdowns: **{}** \u{00b7} speedups: **{}** \u{00b7} added: **{}** \u{00b7} removed: **{}** \u{00b7} non-comparable: **{}** \u{00b7} unchanged: **{}**\n\n",
        report.slowdown_threshold_pct,
        report.regressions.len(),
        report.improvements.len(),
        report.slowdowns.len(),
        report.speedups.len(),
        report.added.len(),
        report.removed.len(),
        report.non_comparable.len(),
        report.unchanged_count,
    ));
}

fn write_non_comparable_table(s: &mut String, report: &DiffReport) {
    if report.non_comparable.is_empty() {
        return;
    }
    s.push_str("### Non-comparable evidence\n\n");
    s.push_str("| Eval | Benchmark | Reason | Base envelope | Head envelope | Base content | Head content |\n");
    s.push_str("|------|-----------|--------|---------------|---------------|--------------|--------------|\n");
    for entry in &report.non_comparable {
        s.push_str(&format!(
            "| `{}` | `{}` | {} | `{}` | `{}` | `{}` | `{}` |\n",
            md_escape(&entry.eval_name),
            md_escape(&entry.benchmark_path),
            md_escape(&entry.reason),
            md_escape(
                entry
                    .base_resource_envelope
                    .as_deref()
                    .unwrap_or("<missing>")
            ),
            md_escape(
                entry
                    .head_resource_envelope
                    .as_deref()
                    .unwrap_or("<missing>")
            ),
            md_escape(entry.base_content_hash.as_deref().unwrap_or("<missing>")),
            md_escape(entry.head_content_hash.as_deref().unwrap_or("<missing>")),
        ));
    }
    s.push('\n');
}

fn write_verdict_table(s: &mut String, heading: &str, entries: &[DiffEntry]) {
    s.push_str(heading);
    s.push_str("\n\n");
    if entries.is_empty() {
        s.push_str("_none_\n\n");
        return;
    }
    s.push_str("| Eval | Benchmark | Base | Head |\n");
    s.push_str("|------|-----------|------|------|\n");
    for e in entries {
        s.push_str(&format!(
            "| `{}` | `{}` | `{}` | `{}` |\n",
            md_escape(&e.eval_name),
            md_escape(&e.benchmark_path),
            md_escape(e.base_result.as_deref().unwrap_or("-")),
            md_escape(e.head_result.as_deref().unwrap_or("-")),
        ));
    }
    s.push('\n');
}

fn write_slowdown_table(s: &mut String, report: &DiffReport) {
    s.push_str(&format!(
        "### Slowdowns (>{:.0}% runtime)\n\n",
        report.slowdown_threshold_pct,
    ));
    if report.slowdowns.is_empty() {
        s.push_str("_none_\n\n");
        return;
    }
    s.push_str("| Eval | Benchmark | Base (ms) | Head (ms) | \u{0394} |\n");
    s.push_str("|------|-----------|-----------|-----------|---|\n");
    for e in &report.slowdowns {
        s.push_str(&format!(
            "| `{}` | `{}` | {} | {} | {:+.1}% |\n",
            md_escape(&e.eval_name),
            md_escape(&e.benchmark_path),
            e.base_runtime_ms.unwrap_or(0),
            e.head_runtime_ms.unwrap_or(0),
            e.runtime_delta_pct.unwrap_or(0.0),
        ));
    }
    s.push('\n');
}

fn short_hash(hash: &str) -> String {
    if hash.len() >= 12 {
        hash[..12].to_string()
    } else {
        hash.to_string()
    }
}

/// Escape the small set of characters that break Markdown table cells: the
/// column-delimiter `|` and embedded newlines.
fn md_escape(s: &str) -> String {
    s.replace('|', "\\|").replace('\n', " ")
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::db::ResultRow;
    use crate::diff::{compute_diff, DiffOptions};

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
    fn test_render_markdown_headers_and_summary() {
        let rep = compute_diff(
            "aaaaaaaaaaaa",
            &[row("aaaaaaaaaaaa", "e", "b.smt2", "sat", 100, 1)],
            "bbbbbbbbbbbb",
            &[row("bbbbbbbbbbbb", "e", "b.smt2", "sat", 110, 1)],
            DiffOptions::default(),
        );
        let md = render_markdown(&rep);
        assert!(md.contains("## ay-bench diff"));
        assert!(md.contains("### Regressions"));
        assert!(md.contains("### Improvements"));
        assert!(md.contains("### Slowdowns"));
        assert!(md.contains("_none_"), "empty sections should render _none_");
        // Short-hash truncation: 12 chars of the commit, no more.
        assert!(md.contains("`aaaaaaaaaaaa`"));
        assert!(md.contains("`bbbbbbbbbbbb`"));
    }

    #[test]
    fn test_render_markdown_regression_row_formatting() {
        let base = vec![row("A", "e", "b.smt2", "sat", 500, 1)];
        let head = vec![row("B", "e", "b.smt2", "timeout", 30_000, 1)];
        let rep = compute_diff("A", &base, "B", &head, DiffOptions::default());
        let md = render_markdown(&rep);
        assert!(md.contains("| Eval | Benchmark | Base | Head |"));
        assert!(md.contains("`b.smt2`"));
        assert!(md.contains("`sat`"));
        assert!(md.contains("`timeout`"));
        // Regressions section must not say `_none_` when we have rows.
        assert!(!md.contains("### Regressions\n\n_none_"));
    }

    #[test]
    fn test_render_markdown_slowdown_delta_column() {
        let base = vec![row("A", "e", "b.smt2", "sat", 1000, 1)];
        let head = vec![row("B", "e", "b.smt2", "sat", 1500, 1)]; // +50%
        let rep = compute_diff("A", &base, "B", &head, DiffOptions::default());
        let md = render_markdown(&rep);
        assert!(md.contains("Slowdowns"));
        assert!(md.contains("+50.0%"));
        assert!(md.contains("1000"));
        assert!(md.contains("1500"));
    }

    #[test]
    fn test_render_markdown_escapes_pipes() {
        let base = vec![row("A", "e|pipe", "b|b.smt2", "sat", 100, 1)];
        let head = vec![row("B", "e|pipe", "b|b.smt2", "timeout", 30_000, 1)];
        let rep = compute_diff("A", &base, "B", &head, DiffOptions::default());
        let md = render_markdown(&rep);
        assert!(md.contains("e\\|pipe"));
        assert!(md.contains("b\\|b.smt2"));
    }

    #[test]
    fn test_md_escape_newlines_collapsed() {
        assert_eq!(md_escape("a\nb"), "a b");
        assert_eq!(md_escape("a|b"), "a\\|b");
        assert_eq!(md_escape("plain"), "plain");
    }

    #[test]
    fn test_short_hash_truncates_long_and_preserves_short() {
        assert_eq!(short_hash("abcdef1234567890"), "abcdef123456");
        assert_eq!(short_hash("short"), "short");
        // Exactly 12 chars: preserved verbatim.
        assert_eq!(short_hash("abcdef123456"), "abcdef123456");
    }
}
