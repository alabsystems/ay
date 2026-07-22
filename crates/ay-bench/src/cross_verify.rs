// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Cross-solver verification — given a corpus + 2-3 reference solvers in the
//! baseline store, flag benchmarks where the solvers disagree with *each
//! other* on a definite (`sat`/`unsat`) answer.
//!
//! Part of issue #8711 Phase 3 (universal differential suite, cross-solver
//! majority voting / `ref_wrong` rule). Phases 1-2 wired up single-solver
//! harvest (`ay bench harvest`) and AY-vs-reference verification
//! (`ay bench verify`). Phase 3 closes the loop: if two or more reference
//! solvers disagree on the same input, at least one of them is wrong, and
//! any downstream baseline that trusts the wrong one is poisoned.
//!
//! This module is a pure SQL query + aggregation on top of the baseline
//! store populated by `crate::harvest::cmd_harvest`. No solver is invoked.
//!
//! ## Classification
//!
//! For each benchmark in the corpus:
//!
//! | Class      | Meaning                                                      |
//! |------------|--------------------------------------------------------------|
//! | `agree`    | All requested solvers returned the same definite answer.     |
//! | `dispute`  | Two solvers returned different definite answers.             |
//! | `partial`  | At least one solver returned `unknown`/`timeout`/`error`.    |
//! | `missing`  | One of the requested solvers has no row for this benchmark.  |
//! | `non_comparable` | Input identity is missing, legacy, or differs.         |
//!
//! A `dispute` is the Phase 3 `ref_wrong` signal — the caller (CLI layer)
//! is responsible for mapping it to a non-zero exit code. Resource
//! comparability is reported independently: a same-input `sat`/`unsat`
//! contradiction remains a dispute even when its performance envelopes differ.

use serde::Serialize;
use std::collections::BTreeMap;
use std::path::PathBuf;

use crate::error::{BenchError, Result, WithContext};
use crate::harvest::{BaselineRow, BaselineStore, BaselineStorePath};

/// Arguments for `ay bench cross-verify`.
#[derive(Debug, Clone)]
pub struct CrossVerifyArgs {
    /// Corpus name in the baseline store (e.g. `qfuf-neq`).
    pub corpus: String,
    /// Reference solver short names to cross-check (e.g. `["z3", "golem"]`).
    /// Must contain at least two entries.
    pub solvers: Vec<String>,
    /// Override baseline store path. `None` uses the default.
    pub baseline_store: Option<PathBuf>,
    /// Emit the report as JSON instead of a table.
    pub json: bool,
}

/// Classification of one benchmark's cross-solver agreement.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[serde(rename_all = "lowercase")]
pub enum CrossClass {
    /// Every requested solver returned the same definite answer.
    Agree,
    /// Two or more solvers returned different definite answers.
    Dispute,
    /// At least one solver returned a non-definite answer
    /// (`unknown`/`timeout`/`error`).
    Partial,
    /// One of the requested solvers has no row for this benchmark in the
    /// baseline store.
    Missing,
    /// Every solver has a row, but they were not run on identical benchmark
    /// bytes under the same enforced resource envelope.
    NonComparable,
}

impl CrossClass {
    #[must_use]
    pub fn as_str(self) -> &'static str {
        match self {
            Self::Agree => "agree",
            Self::Dispute => "dispute",
            Self::Partial => "partial",
            Self::Missing => "missing",
            Self::NonComparable => "non_comparable",
        }
    }
}

/// One entry in a cross-verify report.
#[derive(Debug, Clone, Serialize)]
pub struct CrossEntry {
    /// Path of the benchmark (relative to wherever the harvester found it).
    pub benchmark_path: String,
    /// Per-solver answer keyed by solver short name. `None` if the solver
    /// has no baseline row for this benchmark.
    pub answers: BTreeMap<String, Option<String>>,
    /// Classification bucket.
    pub classification: String,
    /// Whether input identity and effective enforced resource limits match.
    pub comparable: bool,
    /// Why otherwise-present rows cannot be compared, if applicable. This is
    /// orthogonal to logical classification when input bytes are identical.
    pub non_comparable_reason: Option<String>,
}

/// Aggregate report from `cmd_cross_verify`.
#[derive(Debug, Clone, Serialize)]
pub struct CrossReport {
    pub corpus: String,
    pub solvers: Vec<String>,
    pub total: usize,
    pub agree: usize,
    pub dispute: usize,
    pub partial: usize,
    pub missing: usize,
    pub non_comparable: usize,
    pub entries: Vec<CrossEntry>,
}

impl CrossReport {
    /// `true` iff any benchmark classified as a cross-solver dispute.
    #[must_use]
    pub fn has_disputes(&self) -> bool {
        self.dispute > 0
    }

    /// Cross-solver disagreement, missing requested evidence, and
    /// non-comparable evidence are all fail-closed outcomes for the CLI gate.
    /// Partial (`unknown`/timeout) rows remain visible but are not, by
    /// themselves, a soundness failure.
    #[must_use]
    pub fn has_failures(&self) -> bool {
        self.has_disputes() || self.missing > 0 || self.non_comparable > 0
    }
}

/// Classify the per-solver answers for a single benchmark.
///
/// `answers` is indexed in the same order as the requested solver list; each
/// entry is `None` if the baseline has no row for that `(benchmark, solver)`
/// pair, or `Some(answer)` otherwise. Case-insensitive `sat` / `unsat` are
/// treated as definite; anything else (`unknown`, `timeout`, `error`, empty)
/// is non-definite.
#[must_use]
pub fn classify_answers(answers: &[Option<&str>]) -> CrossClass {
    if answers.is_empty() {
        return CrossClass::Partial;
    }
    // Any solver missing a row -> Missing.
    if answers.iter().any(Option::is_none) {
        return CrossClass::Missing;
    }
    // Any non-definite -> Partial (a dispute requires two definite answers
    // that disagree, so it takes precedence iff everyone is definite).
    let definite: Vec<&str> = answers
        .iter()
        .filter_map(|a| {
            a.and_then(|v| {
                let l = v.trim().to_ascii_lowercase();
                if l == "sat" || l == "unsat" {
                    Some(v.trim())
                } else {
                    None
                }
            })
        })
        .collect();
    if definite.len() != answers.len() {
        return CrossClass::Partial;
    }
    // All definite — check agreement.
    let first = definite[0].to_ascii_lowercase();
    if definite
        .iter()
        .all(|a| a.eq_ignore_ascii_case(first.as_str()))
    {
        CrossClass::Agree
    } else {
        CrossClass::Dispute
    }
}

/// Run the cross-verify subcommand.
///
/// The caller (CLI layer) is responsible for printing `render_cross_table`
/// (or the JSON form) and mapping `report.has_failures()` to a non-zero exit
/// code.
pub fn cmd_cross_verify(args: CrossVerifyArgs) -> Result<CrossReport> {
    if args.solvers.len() < 2 {
        return Err(BenchError::InvalidArgs {
            reason: format!(
                "cross-verify requires at least 2 solvers, got {}",
                args.solvers.len()
            ),
        });
    }
    // Normalize solver list (dedupe while preserving first occurrence).
    let mut seen = std::collections::BTreeSet::new();
    let solvers: Vec<String> = args
        .solvers
        .iter()
        .filter_map(|s| {
            let t = s.trim().to_string();
            if t.is_empty() {
                None
            } else if seen.insert(t.clone()) {
                Some(t)
            } else {
                None
            }
        })
        .collect();
    if solvers.len() < 2 {
        return Err(BenchError::InvalidArgs {
            reason:
                "cross-verify requires at least 2 distinct non-empty solver names (after dedup)"
                    .to_string(),
        });
    }

    let root = crate::runner::repo_root_public();
    let store_path = args
        .baseline_store
        .clone()
        .unwrap_or_else(|| BaselineStorePath::default_at(&root).as_path().to_path_buf());
    if !store_path.exists() {
        return Err(BenchError::msg(format!(
            "no baseline store at {} — run `ay bench harvest` first",
            store_path.display()
        )));
    }

    let store = BaselineStore::open(&store_path)
        .with_bench_context(|| format!("opening baseline store {}", store_path.display()))?;
    build_report(&store, &args.corpus, &solvers)
}

/// Build a cross-verify report from an already-open baseline store.
///
/// Pulled out of `cmd_cross_verify` so integration tests can seed an
/// in-memory store and exercise the classification pipeline without
/// touching the filesystem.
pub fn build_report(
    store: &BaselineStore,
    corpus: &str,
    solvers: &[String],
) -> Result<CrossReport> {
    let distinct = solvers
        .iter()
        .map(|solver| solver.trim())
        .filter(|solver| !solver.is_empty())
        .collect::<std::collections::BTreeSet<_>>();
    if distinct.len() < 2 || distinct.len() != solvers.len() {
        return Err(BenchError::InvalidArgs {
            reason: "cross-verify requires at least 2 distinct non-empty solver names".to_string(),
        });
    }
    let rows = store
        .rows_for_corpus(corpus)
        .with_bench_context(|| format!("fetching baselines for corpus '{corpus}'"))?;
    if rows.is_empty() {
        return Err(BenchError::msg(format!(
            "no baseline rows for corpus '{corpus}'"
        )));
    }
    // The harvest publication validator is intentionally not used here:
    // migrated or incomplete rows must remain visible as non-comparable
    // evidence instead of aborting the entire report.
    // Index: benchmark_path -> solver_name -> row.
    let mut by_bench: BTreeMap<String, BTreeMap<String, &BaselineRow>> = BTreeMap::new();
    for row in &rows {
        if !solvers.iter().any(|s| s == &row.solver) {
            continue;
        }
        by_bench
            .entry(row.benchmark_path.clone())
            .or_default()
            .insert(row.solver.clone(), row);
    }
    if by_bench.is_empty() {
        return Err(BenchError::msg(format!(
            "corpus '{corpus}' has no rows matching any of the requested solvers {solvers:?}"
        )));
    }

    let mut entries = Vec::with_capacity(by_bench.len());
    let mut counts = CrossCounts::default();

    for (bench_path, solver_rows) in by_bench {
        // Build per-solver answer slice in the order callers requested.
        let answers_vec: Vec<Option<&str>> = solvers
            .iter()
            .map(|s| solver_rows.get(s).map(|r| r.answer.as_str()))
            .collect();
        let comparison = if answers_vec.iter().all(Option::is_some) {
            comparison_status(solvers, &solver_rows)
        } else {
            ComparisonStatus::missing()
        };
        // A logical contradiction only has meaning when every answer concerns
        // exactly the same bytes. Once content identity is established, retain
        // that classification even if timing/throughput evidence is not
        // comparable because the resource envelopes differ.
        let class = if comparison.content_identity_proven {
            classify_answers(&answers_vec)
        } else if answers_vec.iter().any(Option::is_none) {
            CrossClass::Missing
        } else {
            CrossClass::NonComparable
        };
        counts.add(class);
        if comparison.reason.is_some() {
            counts.non_comparable += 1;
        }

        let mut answers = BTreeMap::new();
        for s in solvers {
            answers.insert(s.clone(), solver_rows.get(s).map(|r| r.answer.clone()));
        }
        entries.push(CrossEntry {
            benchmark_path: bench_path,
            answers,
            classification: class.as_str().to_string(),
            comparable: comparison.content_identity_proven && comparison.reason.is_none(),
            non_comparable_reason: comparison.reason,
        });
    }

    Ok(CrossReport {
        corpus: corpus.to_string(),
        solvers: solvers.to_vec(),
        total: entries.len(),
        agree: counts.agree,
        dispute: counts.dispute,
        partial: counts.partial,
        missing: counts.missing,
        non_comparable: counts.non_comparable,
        entries,
    })
}

struct ComparisonStatus {
    content_identity_proven: bool,
    reason: Option<String>,
}

impl ComparisonStatus {
    fn missing() -> Self {
        Self {
            content_identity_proven: false,
            // Missing evidence has its own aggregate/classification and is
            // deliberately not double-counted as `non_comparable`.
            reason: None,
        }
    }
}

fn comparison_status(
    solvers: &[String],
    rows: &BTreeMap<String, &BaselineRow>,
) -> ComparisonStatus {
    let selected: Vec<(&str, &BaselineRow)> = solvers
        .iter()
        .filter_map(|solver| rows.get(solver).map(|row| (solver.as_str(), *row)))
        .collect();

    let content_hashes: Vec<(&str, &str)> = selected
        .iter()
        .map(|(solver, row)| (*solver, row.content_hash.trim()))
        .collect();
    if content_hashes.iter().any(|(_, hash)| hash.is_empty()) {
        return ComparisonStatus {
            content_identity_proven: false,
            reason: Some("one or more benchmark content hashes are missing".to_string()),
        };
    }
    let unsupported: Vec<String> = content_hashes
        .iter()
        .filter(|(_, hash)| !is_stable_sha256(hash))
        .map(|(solver, hash)| format!("{solver}={hash}"))
        .collect();
    if !unsupported.is_empty() {
        return ComparisonStatus {
            content_identity_proven: false,
            reason: Some(format!(
                "legacy or unsupported content hash; re-harvest with sha256: {}",
                unsupported.join(", ")
            )),
        };
    }
    if let Some((_, first)) = content_hashes.first() {
        if content_hashes
            .iter()
            .any(|(_, hash)| !hash.eq_ignore_ascii_case(first))
        {
            return ComparisonStatus {
                content_identity_proven: false,
                reason: Some(format!(
                    "benchmark content differs: {}",
                    content_hashes
                        .iter()
                        .map(|(solver, hash)| format!("{solver}={hash}"))
                        .collect::<Vec<_>>()
                        .join(", ")
                )),
            };
        }
    }

    let envelopes: Vec<(&str, Result<String, &'static str>)> = selected
        .iter()
        .map(|(solver, row)| (*solver, execution_envelope(row)))
        .collect();
    let invalid: Vec<String> = envelopes
        .iter()
        .filter_map(|(solver, envelope)| {
            envelope
                .as_ref()
                .err()
                .map(|reason| format!("{solver}={reason}"))
        })
        .collect();
    if !invalid.is_empty() {
        return ComparisonStatus {
            content_identity_proven: true,
            reason: Some(format!(
                "one or more resource envelopes are missing or unenforced: {}",
                invalid.join(", ")
            )),
        };
    }
    let first = envelopes.first().and_then(|(_, value)| value.as_ref().ok());
    if envelopes
        .iter()
        .any(|(_, envelope)| envelope.as_ref().ok() != first)
    {
        return ComparisonStatus {
            content_identity_proven: true,
            reason: Some(format!(
                "resource envelopes differ: {}",
                envelopes
                    .iter()
                    .map(|(solver, envelope)| format!(
                        "{solver}={}",
                        envelope
                            .as_ref()
                            .cloned()
                            .unwrap_or_else(|_| "<invalid>".to_string())
                    ))
                    .collect::<Vec<_>>()
                    .join(", ")
            )),
        };
    }
    ComparisonStatus {
        content_identity_proven: true,
        reason: None,
    }
}

fn is_stable_sha256(hash: &str) -> bool {
    let Some(digest) = hash.trim().strip_prefix("sha256:") else {
        return false;
    };
    digest.len() == 64 && digest.bytes().all(|byte| byte.is_ascii_hexdigit())
}

fn execution_envelope(row: &BaselineRow) -> Result<String, &'static str> {
    if row.solver_path.trim().is_empty()
        || row.solver_size_bytes <= 0
        || !is_stable_sha256(&row.solver_sha256)
    {
        return Err("missing stable solver binary provenance");
    }
    if row.resource_jobs <= 0
        || row.resource_memlimit_mb <= 0
        || row.resource_nbcore <= 0
        || row.resource_headroom_mb < 0
    {
        return Err("invalid numeric limits");
    }
    let plan = crate::resource::ResourcePlan {
        requested_jobs: usize::try_from(row.resource_requested_jobs)
            .map_err(|_| "invalid numeric limits")?,
        jobs: usize::try_from(row.resource_jobs).map_err(|_| "invalid numeric limits")?,
        memlimit_mb_per_child: usize::try_from(row.resource_memlimit_mb)
            .map_err(|_| "invalid numeric limits")?,
        nbcore_per_child: usize::try_from(row.resource_nbcore)
            .map_err(|_| "invalid numeric limits")?,
        headroom_mb: usize::try_from(row.resource_headroom_mb)
            .map_err(|_| "invalid numeric limits")?,
        planner: "persisted-baseline".to_string(),
    };
    crate::resource::effective_execution_envelope(&plan, &row.resource_enforcement, row.timeout_s)
        .map_err(|_| "no recognized complete enforced execution envelope")
}

#[derive(Default)]
struct CrossCounts {
    agree: usize,
    dispute: usize,
    partial: usize,
    missing: usize,
    non_comparable: usize,
}

impl CrossCounts {
    fn add(&mut self, class: CrossClass) {
        match class {
            CrossClass::Agree => self.agree += 1,
            CrossClass::Dispute => self.dispute += 1,
            CrossClass::Partial => self.partial += 1,
            CrossClass::Missing => self.missing += 1,
            CrossClass::NonComparable => {}
        }
    }
}

/// Render a cross-verify report as a human-readable table.
#[must_use]
pub fn render_cross_table(report: &CrossReport) -> String {
    let mut s = String::new();
    s.push_str(&format!("corpus: {}\n", report.corpus));
    s.push_str(&format!("solvers: {}\n", report.solvers.join(", ")));
    s.push_str(&format!("total benchmarks: {}\n", report.total));
    s.push_str(&format!("  agree (all definite): {}\n", report.agree));
    s.push_str(&format!("  partial (some unknown): {}\n", report.partial));
    s.push_str(&format!(
        "  disputes (ref-vs-ref disagreement): {}\n",
        report.dispute
    ));
    if report.missing > 0 {
        s.push_str(&format!(
            "  missing (solver has no row for benchmark): {}\n",
            report.missing
        ));
    }
    if report.non_comparable > 0 {
        s.push_str(&format!(
            "  non-comparable (input/resources differ): {}\n",
            report.non_comparable
        ));
    }

    for entry in report
        .entries
        .iter()
        .filter(|entry| entry.non_comparable_reason.is_some())
    {
        s.push_str(&format!(
            "  NON-COMPARABLE {} : {}\n",
            entry.benchmark_path,
            entry
                .non_comparable_reason
                .as_deref()
                .unwrap_or("unknown reason")
        ));
    }

    let disputes: Vec<&CrossEntry> = report
        .entries
        .iter()
        .filter(|e| e.classification == "dispute")
        .collect();
    s.push_str("\n=== DISPUTES ===\n");
    if disputes.is_empty() {
        s.push_str("(none)\n");
    } else {
        for e in disputes {
            let answers: Vec<String> = report
                .solvers
                .iter()
                .map(|solver| {
                    let a = e
                        .answers
                        .get(solver)
                        .and_then(Option::as_deref)
                        .unwrap_or("?");
                    format!("{solver}={a}")
                })
                .collect();
            s.push_str(&format!("  {} : {}\n", e.benchmark_path, answers.join(" ")));
        }
    }
    s
}

// Tests live in `crates/ay-bench/tests/cross_verify_integration.rs` so this
// module stays under the 500-line cap. The integration tests exercise the
// public API (`classify_answers`, `build_report`, `cmd_cross_verify`,
// `render_cross_table`) against an in-memory baseline store.
