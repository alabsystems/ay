// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! In-process differential oracle — ay replayed as a LIBRARY against an
//! authoritative external verdict.
//!
//! This crate is the neutral home for AY's in-process differential oracle. The
//! existing `diff`/`bench` subcommands drive AY through the Z3 C ABI
//! (`libay_ffi` dlopen); this module contributes the complementary lane —
//! driving ay **in-process** via [`ay_frontend::parse`] +
//! [`ay_dpll::Executor::execute`] (no dylib build needed), with a wall-time
//! deadline, [`std::panic::catch_unwind`], and a structured
//! [`UnknownReason::code`]-keyed completeness histogram.
//!
//! **Polarity.** The verdict supplied to [`classify_script_with_deadline`] is
//! authoritative
//! for the script *as written* — the same script ay replays — so no
//! re-inversion happens here. (Verus-emitted scripts assert the *negation* of
//! each VC: a *verified* goal is `unsat`, a *failing* goal is `sat`. Inverting
//! would manufacture phantom soundness alarms.)
//!
//! **Soundness is the point.** When ay *decides* the opposite of the
//! authoritative verdict the script lands in the hard
//! [`DiffBucket::UnsoundDisagree`] bucket: a critical soundness finding, never
//! a mere completeness gap. ay returning `Unknown` where the oracle decided is
//! incompleteness ([`DiffBucket::AyIncomplete`], reason-coded). A
//! timeout/deadline is completeness too ([`DiffBucket::Timeout`]) and is
//! explicitly excluded from genuine ay-gap counts.
//!
//! The `classify` subcommand feeds this classifier hermetically from each
//! file's own `(set-info :status sat|unsat)` ground truth — no Z3 required.

use std::path::PathBuf;
use std::time::{Duration, Instant};

use ay_dpll::UnknownReason;
use serde::{Deserialize, Serialize};

use crate::diff;

/// Authoritative SMT verdict for a script *as written*.
///
/// The ground truth this oracle compares ay against: Z3's verdict for
/// harvested corpora, or the file's declared `(set-info :status …)` in
/// hermetic mode. The same three-valued normalization is applied to ay's own
/// result so the two can be compared directly.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub(crate) enum SolverVerdict {
    /// The script is unsatisfiable (e.g. a verified Verus-style goal).
    Unsat,
    /// The script is satisfiable (e.g. a failing goal / counterexample).
    Sat,
    /// The solver could not decide (incompleteness, not a verdict).
    Unknown,
}

impl SolverVerdict {
    /// True when the verdict is a definite decision (`Sat` or `Unsat`).
    #[must_use]
    pub(crate) fn is_decided(self) -> bool {
        matches!(self, Self::Sat | Self::Unsat)
    }

    /// True when `self` and `other` are both decided but opposite — the
    /// soundness tripwire.
    #[must_use]
    pub(crate) fn is_opposite_decision(self, other: Self) -> bool {
        matches!(
            (self, other),
            (Self::Unsat, Self::Sat) | (Self::Sat, Self::Unsat)
        )
    }
}

/// The differential classification for a single replayed script.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub(crate) enum DiffBucket {
    /// ay reached the same definite verdict as the oracle (the healthy case).
    Agree,
    /// ay returned `Unknown` where the oracle decided — an ay completeness gap.
    /// The structured reason code rides alongside in [`Classification::ay_reason`].
    AyIncomplete,
    /// ay decided the *opposite* of the oracle — a CRITICAL soundness finding.
    UnsoundDisagree,
    /// ay hit the wall-time deadline (or reported a timeout) — completeness,
    /// explicitly excluded from genuine ay-gap counts.
    Timeout,
    /// The script failed to parse, ay errored, or ay panicked.
    ParseError,
}

impl DiffBucket {
    /// Stable snake_case machine code for evidence and routing consumers.
    #[must_use]
    pub(crate) fn code(self) -> &'static str {
        match self {
            Self::Agree => "agree",
            Self::AyIncomplete => "ay_incomplete",
            Self::UnsoundDisagree => "unsound_disagree",
            Self::Timeout => "timeout",
            Self::ParseError => "parse_error",
        }
    }

    /// True iff this bucket is a critical soundness finding (fail-closed).
    /// Production code gates on [`DifferentialReport::has_soundness_findings`];
    /// this per-bucket form is exercised by the tests.
    #[cfg(test)]
    #[must_use]
    pub(crate) fn is_soundness_finding(self) -> bool {
        matches!(self, Self::UnsoundDisagree)
    }
}

/// The outcome of replaying one script and classifying it against the oracle.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub(crate) struct Classification {
    /// The bucket the `(ay × oracle)` pair landed in.
    pub bucket: DiffBucket,
    /// The authoritative verdict supplied by the caller.
    pub z3_verdict: SolverVerdict,
    /// ay's normalized verdict (`None` when ay never produced a `check-sat`
    /// result, e.g. parse error, executor error, panic, or deadline).
    pub ay_verdict: Option<SolverVerdict>,
    /// ay's structured [`UnknownReason::code`] when ay returned `Unknown`.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub ay_reason: Option<String>,
    /// Human-readable detail for parse/executor/panic failures.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub detail: Option<String>,
}

impl Classification {
    /// True iff this is a critical soundness finding. Test-only convenience;
    /// production gates on [`DifferentialReport::has_soundness_findings`].
    #[cfg(test)]
    #[must_use]
    pub(crate) fn is_soundness_finding(&self) -> bool {
        self.bucket.is_soundness_finding()
    }
}

/// Default wall-time deadline for a single replay. A breach is `Timeout`
/// (completeness), never silently `Unknown` folded into the gap counts.
/// (Production paths take an explicit `--timeout`; the default is test-only.)
#[cfg(test)]
pub(crate) const DEFAULT_DEADLINE: Duration = Duration::from_secs(10);

/// Replays `smt_script` through ay and classifies it against the authoritative
/// `z3_verdict`, using [`DEFAULT_DEADLINE`]. Test-only convenience; production
/// goes through [`classify_script_with_deadline`].
#[cfg(test)]
#[must_use]
pub(crate) fn classify_script(smt_script: &str, z3_verdict: SolverVerdict) -> Classification {
    classify_script_with_deadline(smt_script, z3_verdict, DEFAULT_DEADLINE)
}

/// Replays `smt_script` through ay under an explicit wall-time `deadline` and
/// classifies it against the authoritative `z3_verdict`.
///
/// The whole ay run is wrapped in [`std::panic::catch_unwind`]; a panic is
/// reported as [`DiffBucket::ParseError`] (an ay defect to triage), never
/// allowed to masquerade as a verdict.
#[must_use]
pub(crate) fn classify_script_with_deadline(
    smt_script: &str,
    z3_verdict: SolverVerdict,
    deadline: Duration,
) -> Classification {
    let script = smt_script.to_string();
    let run = std::panic::catch_unwind(move || run_ay(&script, deadline));

    match run {
        Ok(outcome) => classify_outcome(outcome, z3_verdict),
        Err(payload) => Classification {
            bucket: DiffBucket::ParseError,
            z3_verdict,
            ay_verdict: None,
            ay_reason: None,
            detail: Some(format!("ay panicked: {}", panic_message(&payload))),
        },
    }
}

/// What an ay replay produced, before differential classification.
enum AyOutcome {
    /// ay produced a definite verdict or a reason-coded `Unknown`.
    Verdict {
        verdict: SolverVerdict,
        reason: Option<&'static str>,
    },
    /// The wall-time deadline elapsed before ay finished.
    Deadline,
    /// The script failed to parse, ay errored, or ay produced no `check-sat`.
    Error(String),
}

/// Drives `ay_frontend::parse` + `ay_dpll::Executor::execute` over the script,
/// surfacing the structured [`UnknownReason`] and honoring a wall-time
/// `deadline`.
fn run_ay(smt_script: &str, deadline: Duration) -> AyOutcome {
    let commands = match ay_frontend::parse(smt_script) {
        Ok(commands) => commands,
        Err(e) => return AyOutcome::Error(format!("parse error: {e:?}")),
    };

    let started = Instant::now();
    let mut executor = ay_dpll::Executor::new();
    let mut verdict: Option<SolverVerdict> = None;
    let mut reason: Option<&'static str> = None;

    for cmd in &commands {
        if started.elapsed() >= deadline {
            return AyOutcome::Deadline;
        }
        match executor.execute(cmd) {
            Ok(Some(output)) => {
                let trimmed = output.trim();
                match trimmed {
                    "unsat" => {
                        verdict = Some(SolverVerdict::Unsat);
                        reason = None;
                    }
                    "sat" => {
                        verdict = Some(SolverVerdict::Sat);
                        reason = None;
                    }
                    "unknown" => {
                        verdict = Some(SolverVerdict::Unknown);
                        reason = executor.unknown_reason().map(|r| r.code());
                    }
                    // Model output or other S-expression: ignore.
                    _ => {}
                }
            }
            Ok(None) => {}
            Err(e) => return AyOutcome::Error(format!("executor error: {e:?}")),
        }
    }

    // A deadline that elapsed during the final command still counts as Timeout.
    if started.elapsed() >= deadline && verdict.is_none() {
        return AyOutcome::Deadline;
    }

    match verdict {
        Some(verdict) => AyOutcome::Verdict { verdict, reason },
        None => AyOutcome::Error("no check-sat result received".to_string()),
    }
}

/// Applies the classification policy. Polarity is already baked into both
/// verdicts (the script is replayed verbatim and `z3_verdict` is for that same
/// script), so the comparison is direct — no inversion.
fn classify_outcome(outcome: AyOutcome, z3_verdict: SolverVerdict) -> Classification {
    match outcome {
        AyOutcome::Deadline => Classification {
            bucket: DiffBucket::Timeout,
            z3_verdict,
            ay_verdict: Some(SolverVerdict::Unknown),
            ay_reason: Some(UnknownReason::Timeout.code().to_string()),
            detail: None,
        },
        AyOutcome::Error(detail) => Classification {
            bucket: DiffBucket::ParseError,
            z3_verdict,
            ay_verdict: None,
            ay_reason: None,
            detail: Some(detail),
        },
        AyOutcome::Verdict { verdict, reason } => {
            // ay self-reported a timeout while still inside the deadline: treat
            // as completeness (excluded from gap counts), not as an ay gap.
            if matches!(verdict, SolverVerdict::Unknown)
                && reason == Some(UnknownReason::Timeout.code())
            {
                return Classification {
                    bucket: DiffBucket::Timeout,
                    z3_verdict,
                    ay_verdict: Some(verdict),
                    ay_reason: reason.map(str::to_string),
                    detail: None,
                };
            }

            let bucket = if z3_verdict.is_opposite_decision(verdict) {
                // CRITICAL: both decided, opposite. The soundness tripwire.
                DiffBucket::UnsoundDisagree
            } else if matches!(verdict, SolverVerdict::Unknown) && z3_verdict.is_decided() {
                // ay could not decide where the oracle did: a completeness gap.
                DiffBucket::AyIncomplete
            } else {
                // Same decision, or the oracle itself is Unknown (no ground
                // truth to contradict): not a finding.
                DiffBucket::Agree
            };

            Classification {
                bucket,
                z3_verdict,
                ay_verdict: Some(verdict),
                ay_reason: reason.map(str::to_string),
                detail: None,
            }
        }
    }
}

/// Best-effort extraction of a panic payload's message.
fn panic_message(payload: &Box<dyn std::any::Any + Send>) -> String {
    if let Some(s) = payload.downcast_ref::<&str>() {
        (*s).to_string()
    } else if let Some(s) = payload.downcast_ref::<String>() {
        s.clone()
    } else {
        "<non-string panic payload>".to_string()
    }
}

/// A counted aggregate over many [`Classification`]s.
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub(crate) struct DifferentialReport {
    /// Total scripts classified.
    pub total: usize,
    /// ay agreed with the oracle's decision.
    pub agree: usize,
    /// ay returned `Unknown` where the oracle decided (completeness gaps).
    pub ay_incomplete: usize,
    /// ay decided the opposite of the oracle — CRITICAL soundness findings.
    pub unsound_disagree: usize,
    /// Deadline / self-reported timeout (completeness, excluded from gaps).
    pub timeout: usize,
    /// Parse / executor / panic failures.
    pub parse_error: usize,
    /// Histogram of [`UnknownReason::code`] over the `ay_incomplete` bucket,
    /// the genuine ay-gap surface (timeouts are *not* counted here).
    pub ay_incomplete_reasons: std::collections::BTreeMap<String, usize>,
    /// Every soundness finding, retained verbatim for triage.
    pub soundness_findings: Vec<Classification>,
}

impl DifferentialReport {
    /// Folds a single [`Classification`] into the aggregate.
    pub(crate) fn record(&mut self, classification: &Classification) {
        self.total += 1;
        match classification.bucket {
            DiffBucket::Agree => self.agree += 1,
            DiffBucket::AyIncomplete => {
                self.ay_incomplete += 1;
                let code = classification
                    .ay_reason
                    .clone()
                    .unwrap_or_else(|| UnknownReason::Unknown.code().to_string());
                *self.ay_incomplete_reasons.entry(code).or_insert(0) += 1;
            }
            DiffBucket::UnsoundDisagree => {
                self.unsound_disagree += 1;
                self.soundness_findings.push(classification.clone());
            }
            DiffBucket::Timeout => self.timeout += 1,
            DiffBucket::ParseError => self.parse_error += 1,
        }
    }

    /// Builds a report from an iterator of classifications. Test-only
    /// convenience; production folds incrementally via [`Self::record`].
    #[cfg(test)]
    pub(crate) fn from_classifications<'a, I>(classifications: I) -> Self
    where
        I: IntoIterator<Item = &'a Classification>,
    {
        let mut report = Self::default();
        for classification in classifications {
            report.record(classification);
        }
        report
    }

    /// True iff any critical soundness finding was recorded — the non-zero
    /// gate exit.
    #[must_use]
    pub(crate) fn has_soundness_findings(&self) -> bool {
        self.unsound_disagree > 0
    }
}

/// One row of the per-file section of the `--json` output: the classified
/// file's path and the bucket it landed in.
#[derive(Debug, Serialize)]
pub(crate) struct FileBucket {
    /// The classified file's path, as displayed.
    pub file: String,
    /// The differential bucket the file landed in (snake_case code).
    pub bucket: DiffBucket,
}

/// Renders the `--json` output for a classify run. The schema is additive
/// over the original `{report, skipped_undeclared}` shape: `per_file` lists
/// every classified file with its bucket, in classification order.
fn render_classify_json(
    report: &DifferentialReport,
    skipped_undeclared: usize,
    per_file: &[FileBucket],
) -> String {
    #[derive(Serialize)]
    struct Out<'a> {
        report: &'a DifferentialReport,
        skipped_undeclared: usize,
        per_file: &'a [FileBucket],
    }
    serde_json::to_string_pretty(&Out {
        report,
        skipped_undeclared,
        per_file,
    })
    .expect("report serializes")
}

/// The `classify` subcommand: hermetic in-process differential run over a
/// corpus of `.smt2` files carrying their own `(set-info :status sat|unsat)`
/// ground truth. Files without a decided `:status` are skipped (counted).
/// Returns the process exit code: non-zero iff any UnsoundDisagree.
pub(crate) fn run_classify(paths: &[PathBuf], timeout_secs: u64, json: bool) -> i32 {
    let files = diff::collect_smt2(paths);
    if files.is_empty() {
        eprintln!("classify: no .smt2 files found under the given paths");
        return 2;
    }

    let deadline = Duration::from_secs(timeout_secs);
    let mut report = DifferentialReport::default();
    let mut skipped_undeclared = 0usize;
    let mut per_file: Vec<FileBucket> = Vec::new();

    for file in &files {
        let text = match std::fs::read_to_string(file) {
            Ok(t) => t,
            Err(e) => {
                eprintln!("classify: cannot read {}: {e}", file.display());
                skipped_undeclared += 1;
                continue;
            }
        };
        let declared = match diff::declared_status_of(&text) {
            Some(diff::Verdict::Sat) => SolverVerdict::Sat,
            Some(diff::Verdict::Unsat) => SolverVerdict::Unsat,
            _ => {
                skipped_undeclared += 1;
                continue;
            }
        };
        let c = classify_script_with_deadline(&text, declared, deadline);
        if !json {
            println!("{:<18} {}", c.bucket.code(), file.display());
        }
        per_file.push(FileBucket {
            file: file.display().to_string(),
            bucket: c.bucket,
        });
        report.record(&c);
    }

    if json {
        println!(
            "{}",
            render_classify_json(&report, skipped_undeclared, &per_file)
        );
    } else {
        println!(
            "\nclassify: {} total | {} agree | {} ay_incomplete | {} timeout | {} parse_error | {} skipped(no :status) | {} UNSOUND-DISAGREE",
            report.total,
            report.agree,
            report.ay_incomplete,
            report.timeout,
            report.parse_error,
            skipped_undeclared,
            report.unsound_disagree,
        );
        if !report.ay_incomplete_reasons.is_empty() {
            println!("ay_incomplete reasons: {:?}", report.ay_incomplete_reasons);
        }
        for finding in &report.soundness_findings {
            println!("SOUNDNESS FINDING: {finding:?}");
        }
    }

    if report.has_soundness_findings() {
        1
    } else {
        0
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// (a) Trivially UNSAT: `(assert false)`. The oracle says unsat; ay must
    /// agree.
    const SEED_UNSAT: &str = "(assert false)\n(check-sat)\n";

    /// (b) Trivially SAT: an unconstrained positive integer. The oracle says
    /// sat; ay must agree.
    const SEED_SAT: &str = "(declare-const x Int)\n(assert (> x 0))\n(check-sat)\n";

    /// (c) ay-known-Unknown: a triggerless quantified UFNIA assertion,
    /// `forall x. f(x*x) > x`. The oracle decides SAT (witness: `f(n) = |n|+1`,
    /// so `f(x^2) = x^2 + 1 > x` for every integer `x`), but ay's quantifier
    /// engine gives up (CEGQI incompleteness over the nonlinear body) and
    /// returns Unknown with a stable reason code.
    ///
    /// History: the original seed here was "factor the prime 1000003 into two
    /// factors > 1" (UNSAT), inherited from the deductive-checks extraction
    /// (7f477903). ay's nonlinear-integer fragment has since grown strong
    /// enough to decide it (interval branch-and-prune, 43034c4b lineage): it
    /// now answers `unsat` in milliseconds, landing in `Agree` — so that
    /// script no longer exercises the `AyIncomplete` bucket.
    const SEED_AY_UNKNOWN: &str = concat!(
        "(set-logic UFNIA)\n",
        "(declare-fun f (Int) Int)\n",
        "(assert (forall ((x Int)) (> (f (* x x)) x)))\n",
        "(check-sat)\n",
    );

    #[test]
    fn seed_unsat_agrees() {
        let c = classify_script(SEED_UNSAT, SolverVerdict::Unsat);
        assert_eq!(c.bucket, DiffBucket::Agree, "{c:?}");
        assert_eq!(c.ay_verdict, Some(SolverVerdict::Unsat), "{c:?}");
        assert!(!c.is_soundness_finding());
    }

    #[test]
    fn seed_sat_agrees() {
        let c = classify_script(SEED_SAT, SolverVerdict::Sat);
        assert_eq!(c.bucket, DiffBucket::Agree, "{c:?}");
        assert_eq!(c.ay_verdict, Some(SolverVerdict::Sat), "{c:?}");
        assert!(!c.is_soundness_finding());
    }

    #[test]
    fn seed_ay_unknown_is_incomplete() {
        // The authoritative verdict for the quantified-UF script is SAT.
        let c = classify_script(SEED_AY_UNKNOWN, SolverVerdict::Sat);
        assert_eq!(c.bucket, DiffBucket::AyIncomplete, "{c:?}");
        assert_eq!(c.ay_verdict, Some(SolverVerdict::Unknown), "{c:?}");
        // The reason must be carried through as a stable UnknownReason code.
        assert!(
            c.ay_reason.is_some(),
            "AyIncomplete must record an UnknownReason code: {c:?}"
        );
        assert!(!c.is_soundness_finding());
    }

    /// The soundness-detection tripwire: feed a DELIBERATELY-WRONG oracle
    /// verdict (SAT) for the trivially-UNSAT script. ay correctly decides
    /// UNSAT, so the classifier MUST fire `UnsoundDisagree` — proving the
    /// detector works.
    #[test]
    fn wrong_oracle_verdict_triggers_unsound_disagree() {
        let c = classify_script(SEED_UNSAT, SolverVerdict::Sat);
        assert_eq!(c.bucket, DiffBucket::UnsoundDisagree, "{c:?}");
        assert_eq!(c.ay_verdict, Some(SolverVerdict::Unsat), "{c:?}");
        assert!(
            c.is_soundness_finding(),
            "opposite decisions must be a soundness finding: {c:?}"
        );
    }

    /// Symmetric tripwire: a wrong UNSAT verdict against the trivially-SAT
    /// script must also fire.
    #[test]
    fn wrong_oracle_verdict_on_sat_triggers_unsound_disagree() {
        let c = classify_script(SEED_SAT, SolverVerdict::Unsat);
        assert_eq!(c.bucket, DiffBucket::UnsoundDisagree, "{c:?}");
        assert!(c.is_soundness_finding(), "{c:?}");
    }

    /// Polarity guard: a *verified* Verus-style goal is `unsat`. The runner
    /// must NOT re-invert — `(assert false)` (a trivially verified goal)
    /// against an `Unsat` verdict is Agree, never a manufactured
    /// disagreement.
    #[test]
    fn polarity_verified_goal_is_agree_not_disagree() {
        let c = classify_script(SEED_UNSAT, SolverVerdict::Unsat);
        assert_eq!(c.bucket, DiffBucket::Agree, "{c:?}");
    }

    /// A parse failure lands in `ParseError`, not in any verdict bucket.
    #[test]
    fn malformed_script_is_parse_error() {
        let c = classify_script("(this is not smt", SolverVerdict::Unsat);
        assert_eq!(c.bucket, DiffBucket::ParseError, "{c:?}");
        assert!(c.ay_verdict.is_none(), "{c:?}");
    }

    /// A zero deadline forces the Timeout bucket — completeness, NOT an ay
    /// gap, and NOT a soundness finding.
    #[test]
    fn deadline_breach_is_timeout() {
        let c = classify_script_with_deadline(
            SEED_AY_UNKNOWN,
            SolverVerdict::Sat,
            Duration::from_secs(0),
        );
        assert_eq!(c.bucket, DiffBucket::Timeout, "{c:?}");
        assert!(!c.is_soundness_finding());
    }

    /// The counted aggregate folds buckets correctly and only counts genuine
    /// ay gaps (AyIncomplete) in the reason histogram — not timeouts.
    #[test]
    fn report_aggregates_buckets() {
        let classifications = vec![
            classify_script(SEED_UNSAT, SolverVerdict::Unsat), // Agree
            classify_script(SEED_SAT, SolverVerdict::Sat),     // Agree
            classify_script(SEED_AY_UNKNOWN, SolverVerdict::Sat), // AyIncomplete
            classify_script(SEED_UNSAT, SolverVerdict::Sat),   // UnsoundDisagree
            classify_script_with_deadline(
                SEED_AY_UNKNOWN,
                SolverVerdict::Sat,
                Duration::from_secs(0),
            ), // Timeout
            classify_script("(bad", SolverVerdict::Unsat),     // ParseError
        ];
        let report = DifferentialReport::from_classifications(&classifications);

        assert_eq!(report.total, 6);
        assert_eq!(report.agree, 2);
        assert_eq!(report.ay_incomplete, 1);
        assert_eq!(report.unsound_disagree, 1);
        assert_eq!(report.timeout, 1);
        assert_eq!(report.parse_error, 1);
        assert!(report.has_soundness_findings());
        assert_eq!(report.soundness_findings.len(), 1);
        // The timeout did NOT pollute the genuine ay-gap reason histogram.
        let gap_total: usize = report.ay_incomplete_reasons.values().sum();
        assert_eq!(gap_total, 1);
        assert!(!report.ay_incomplete_reasons.contains_key("timeout"));
    }

    /// The `--json` output carries a per-file section alongside the original
    /// `{report, skipped_undeclared}` fields — an additive, backward-compatible
    /// schema extension (existing consumers keep their fields untouched).
    #[test]
    fn classify_json_includes_per_file_section() {
        let report = DifferentialReport::from_classifications(&[classify_script(
            SEED_UNSAT,
            SolverVerdict::Unsat,
        )]);
        let per_file = vec![FileBucket {
            file: "a.smt2".to_string(),
            bucket: DiffBucket::Agree,
        }];
        let json = render_classify_json(&report, 3, &per_file);
        let v: serde_json::Value = serde_json::from_str(&json).expect("valid JSON");
        assert_eq!(v["skipped_undeclared"], 3, "{json}");
        assert_eq!(v["report"]["total"], 1, "{json}");
        assert_eq!(v["per_file"][0]["file"], "a.smt2", "{json}");
        assert_eq!(v["per_file"][0]["bucket"], "agree", "{json}");
    }

    /// The report round-trips through serde.
    #[test]
    fn report_serializes() {
        let report = DifferentialReport::from_classifications(&[
            classify_script(SEED_UNSAT, SolverVerdict::Unsat),
            classify_script(SEED_UNSAT, SolverVerdict::Sat),
        ]);
        let json = serde_json::to_string(&report).expect("serialize");
        assert!(json.contains("\"unsound_disagree\":1"), "{json}");
        let back: DifferentialReport = serde_json::from_str(&json).expect("deserialize");
        assert_eq!(back.total, report.total);
        assert_eq!(back.unsound_disagree, report.unsound_disagree);
    }
}
