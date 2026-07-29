// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Fail-closed diagnostic gate for `--verify-firewall`.
//!
//! On UNSAT, this reconstructs the per-theory "firewall" Lean artifacts (the
//! same import-the-verified-`AySoundness`-theorem shape that
//! `--emit-firewall-lean` writes) and may kernel-check them with the *real* Lean
//! toolchain via `lake env lean <file>` run inside a private project whose Lake
//! metadata is embedded in the executable. The checker prepends the theorem base
//! embedded at AY build time instead of importing a mutable project `.olean`,
//! then requires
//! `#print axioms no_model` to report a subset of {propext, Classical.choice,
//! Quot.sound}.
//!
//! These artifacts are currently diagnostic only. Per-lemma emitters prove a
//! synthetic contradiction around one theory lemma, and the general emitter's
//! rendered `Assume` clauses carry no independently checked binding back to the
//! frontend assertions. Kernel acceptance therefore says that the rendered
//! local theorem is valid, not that the user's query is UNSAT.
//!
//! # Soundness contract
//!
//! `--verify-firewall` NARROWS what AY will report. Until an artifact includes a
//! checker-verifiable binding from its premises to the actual query, every
//! `unsat` is downgraded to a sound `unknown`, even when all diagnostic artifacts
//! kernel-check. Downgrading `unsat` → `unknown` is always sound (§0).
//!
//! # Diagnostic backend: today `lake env lean`
//!
//! Diagnostic checking currently shells out to the full Lean toolchain. A future
//! resident `clean olean verify-batch` backend could avoid per-file startup, but
//! changing kernels does not supply the missing query binding: neither backend
//! may certify AY's verdict until the artifact format proves that binding. Each
//! Unix child also inherits a hard `RLIMIT_AS`: the smaller of AY's configured
//! process-memory ceiling and a fixed 2 GiB diagnostic ceiling (2 GiB when AY's
//! in-process limit is disabled).

use std::collections::VecDeque;
use std::path::{Path, PathBuf};
use std::process::{Child, Command, Stdio};
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::mpsc;
use std::time::{Duration, Instant};

use ay_dpll::Executor;

/// Per-file kernel-check result.
pub(crate) struct LemmaCheck {
    /// 0-based firewall file index (`firewall_<i>.lean`).
    pub index: usize,
    /// Whether Lean's kernel accepted the diagnostic file. This is not query
    /// certification.
    pub passed: bool,
    /// Short human detail (`kernel-checked` on success, else the failure).
    pub detail: String,
}

/// Diagnostic outcome for an internal `unsat` result.
///
/// Current firewall artifacts cannot certify the query, so every outcome tells
/// the caller why it must report `unknown` and includes any per-file diagnostics
/// collected before that decision.
pub(crate) struct FirewallDiagnosticOutcome {
    /// Short SMT-LIB `:reason-unknown` payload.
    pub reason: String,
    /// Per-file diagnostic results collected before the gate stopped.
    pub results: Vec<LemmaCheck>,
}

/// Per-file Lean kernel-check timeout. The total diagnostic budget below is an
/// additional cap, so many artifacts cannot multiply this into an unbounded
/// post-solve delay.
const PER_FILE_TIMEOUT: Duration = Duration::from_secs(120);

/// Maximum wall-clock time spent in firewall emission/audit/checking when the
/// CLI deadline has more time remaining (or no deadline). The actual budget is
/// the smaller of this and the remaining CLI timeout.
const TOTAL_DIAGNOSTIC_TIMEOUT: Duration = Duration::from_secs(120);

/// Diagnostic artifacts are attacker/input-amplifiable through proof size. Cap
/// both their count and aggregate standalone Lean source before invoking Lean.
pub(crate) const MAX_DIAGNOSTIC_FILES: usize = 64;
pub(crate) const MAX_DIAGNOSTIC_SOURCE_BYTES: usize = 8 * 1024 * 1024;
const MAX_DIAGNOSTIC_PROOF_STEPS: usize = 200_000;
const MAX_DIAGNOSTIC_EMITTER_ITEMS: usize = 100_000;
const MAX_DIAGNOSTIC_ASSERTIONS: usize = 10_000;
const MAX_DIAGNOSTIC_TERMS: usize = 200_000;
const MAX_DIAGNOSTIC_TERM_BYTES: usize = 32 * 1024 * 1024;
const MAX_DIAGNOSTIC_DATATYPES: usize = 10_000;
const MAX_DIAGNOSTIC_DATATYPE_CONSTRUCTORS: usize = 100_000;
const MAX_DIAGNOSTIC_DATATYPE_BYTES: usize = 8 * 1024 * 1024;
// Lean 4.30 reserves a 1 GiB runtime stack before it processes `-s`; this is an
// address-space ceiling, not an RSS allowance. Worker stacks are pinned below.
const MAX_DIAGNOSTIC_CHILD_MEMORY_BYTES: u64 = 4 * 1024 * 1024 * 1024;
const DIAGNOSTIC_ONLY_REASON: &str = "(incomplete firewall-diagnostic-only-no-query-certificate)";

/// Besides one possible artifact per theory-lemma step, the current emitter can
/// append eleven parsed-assertion recognizers and one general artifact.
const NON_STEP_ARTIFACT_UPPER_BOUND: usize = 12;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum DiagnosticPreflightLimit {
    ProofSteps,
    EmitterItems,
    Assertions,
    Terms,
    TermBytes,
    DatatypeRegistry,
    PotentialFiles,
}

impl DiagnosticPreflightLimit {
    fn reason(self) -> &'static str {
        match self {
            Self::ProofSteps => "(incomplete firewall-diagnostic-proof-step-cap-exceeded)",
            Self::EmitterItems => "(incomplete firewall-diagnostic-proof-payload-cap-exceeded)",
            Self::Assertions => "(incomplete firewall-diagnostic-assertion-cap-exceeded)",
            Self::Terms => "(incomplete firewall-diagnostic-term-cap-exceeded)",
            Self::TermBytes => "(incomplete firewall-diagnostic-term-byte-cap-exceeded)",
            Self::DatatypeRegistry => {
                "(incomplete firewall-diagnostic-datatype-registry-cap-exceeded)"
            }
            Self::PotentialFiles => "(incomplete firewall-diagnostic-file-cap-exceeded)",
        }
    }
}

fn check_diagnostic_preflight(
    proof_steps: usize,
    emitter_items: usize,
    theory_lemmas: usize,
    assertions: usize,
    terms: usize,
    term_bytes: usize,
    datatypes: usize,
    datatype_constructors: usize,
    datatype_bytes: usize,
) -> Result<(), DiagnosticPreflightLimit> {
    check_diagnostic_o1_preflight(proof_steps, assertions, terms, term_bytes)?;
    if emitter_items > MAX_DIAGNOSTIC_EMITTER_ITEMS {
        return Err(DiagnosticPreflightLimit::EmitterItems);
    }
    if datatypes > MAX_DIAGNOSTIC_DATATYPES
        || datatype_constructors > MAX_DIAGNOSTIC_DATATYPE_CONSTRUCTORS
        || datatype_bytes > MAX_DIAGNOSTIC_DATATYPE_BYTES
    {
        return Err(DiagnosticPreflightLimit::DatatypeRegistry);
    }
    if theory_lemmas
        .checked_add(NON_STEP_ARTIFACT_UPPER_BOUND)
        .is_none_or(|files| files > MAX_DIAGNOSTIC_FILES)
    {
        return Err(DiagnosticPreflightLimit::PotentialFiles);
    }
    Ok(())
}

/// Limits whose values are already available in O(1). These must be checked
/// before walking proof payloads or datatype registries; otherwise an input
/// whose proof length is visibly over cap can still force a full traversal.
fn check_diagnostic_o1_preflight(
    proof_steps: usize,
    assertions: usize,
    terms: usize,
    term_bytes: usize,
) -> Result<(), DiagnosticPreflightLimit> {
    if proof_steps > MAX_DIAGNOSTIC_PROOF_STEPS {
        return Err(DiagnosticPreflightLimit::ProofSteps);
    }
    if assertions > MAX_DIAGNOSTIC_ASSERTIONS {
        return Err(DiagnosticPreflightLimit::Assertions);
    }
    if terms > MAX_DIAGNOSTIC_TERMS {
        return Err(DiagnosticPreflightLimit::Terms);
    }
    if term_bytes > MAX_DIAGNOSTIC_TERM_BYTES {
        return Err(DiagnosticPreflightLimit::TermBytes);
    }
    Ok(())
}

fn checked_diagnostic_source_total(current: usize, next: usize) -> Option<usize> {
    current
        .checked_add(next)
        .filter(|total| *total <= MAX_DIAGNOSTIC_SOURCE_BYTES)
}

// Embed the complete trusted source base needed by every runtime firewall. This
// prevents a same-named module in the current working directory (or a stale,
// replaced project `.olean`) from redefining the theorem the gate claims to
// check. FpThy, Datatype and NiaProduct are included because specialized
// emitters use their verified lemmas in addition to the common Firewall/Lrat
// base. NiaProduct carries the McCormick bilinear-product bridge that the
// nonlinear-integer emitter injects; like the others it is import-free, so it
// concatenates cleanly after the imports have been stripped.
//
// StringThy and RegexThy were MISSING here until the `str.in_re` length-
// invariant emitter landed, which meant every string-theory emitter (`str.len`
// over concat, `str.len = 0`, `str.at`, `str.indexof`, and now `str.in_re`)
// produced an artifact this gate rejected as "an untrusted Lean import" — the
// acceptance path had never once run for a string emitter. RegexThy is the only
// embedded module with an import of its own (`AySoundness.StringThy`); it is
// stripped below and the two are concatenated in dependency order.
const LRAT_SOURCE: &str = include_str!("../../../verification/lean/AySoundness/Lrat.lean");
const FIREWALL_SOURCE: &str = include_str!("../../../verification/lean/AySoundness/Firewall.lean");
const FP_SOURCE: &str = include_str!("../../../verification/lean/AySoundness/FpThy.lean");
const DATATYPE_SOURCE: &str = include_str!("../../../verification/lean/AySoundness/Datatype.lean");
const NIA_PRODUCT_SOURCE: &str =
    include_str!("../../../verification/lean/AySoundness/NiaProduct.lean");
const STRING_SOURCE: &str = include_str!("../../../verification/lean/AySoundness/StringThy.lean");
const REGEX_SOURCE: &str = include_str!("../../../verification/lean/AySoundness/RegexThy.lean");
/// The REAL-faithful ordered-field model abstraction the QF_UFLRA congruence
/// emitter quantifies over. Import-free (Lean core only), so it concatenates
/// cleanly like the other embedded theory modules.
const ORD_FIELD_SOURCE: &str = include_str!("../../../verification/lean/AySoundness/OrdField.lean");
const LAKEFILE_SOURCE: &str = include_str!("../../../verification/lean/lakefile.toml");
const LEAN_TOOLCHAIN_SOURCE: &str = include_str!("../../../verification/lean/lean-toolchain");

fn diagnostic_time_budget() -> Duration {
    let cli_timeout_ms = super::GLOBAL_TIMEOUT_MS.load(Ordering::SeqCst);
    if cli_timeout_ms == 0 {
        return TOTAL_DIAGNOSTIC_TIMEOUT;
    }
    let remaining = super::START_TIME.get().map_or_else(
        || Duration::from_millis(cli_timeout_ms),
        |start| Duration::from_millis(cli_timeout_ms).saturating_sub(start.elapsed()),
    );
    remaining.min(TOTAL_DIAGNOSTIC_TIMEOUT)
}

fn diagnostic_time_remaining(started: Instant, budget: Duration) -> Option<Duration> {
    budget
        .checked_sub(started.elapsed())
        .filter(|left| !left.is_zero())
}

fn diagnostic_child_memory_limit_from(configured: usize) -> u64 {
    if configured == 0 {
        return MAX_DIAGNOSTIC_CHILD_MEMORY_BYTES;
    }
    u64::try_from(configured)
        .unwrap_or(u64::MAX)
        .min(MAX_DIAGNOSTIC_CHILD_MEMORY_BYTES)
}

fn diagnostic_child_memory_limit() -> u64 {
    diagnostic_child_memory_limit_from(ay_sys::get_process_memory_limit())
}

fn diagnostic_only_outcome(results: Vec<LemmaCheck>) -> FirewallDiagnosticOutcome {
    FirewallDiagnosticOutcome {
        reason: DIAGNOSTIC_ONLY_REASON.to_string(),
        results,
    }
}

/// Run the fail-closed firewall gate for a fresh `unsat` result.
///
/// Current emitter results are diagnostic-only, so the caller must downgrade
/// every internal `unsat` to `unknown`. Diagnostic checking is bounded and
/// stops at the first rejection.
pub(crate) fn diagnose_firewall_for_unsat(executor: &Executor) -> FirewallDiagnosticOutcome {
    let Some(proof) = executor.last_proof() else {
        return FirewallDiagnosticOutcome {
            reason: "(incomplete firewall-no-proof)".to_string(),
            results: Vec::new(),
        };
    };

    let gate_started = Instant::now();
    let total_budget = diagnostic_time_budget();
    if total_budget.is_zero() {
        return FirewallDiagnosticOutcome {
            reason: "(incomplete firewall-total-deadline-exceeded)".to_string(),
            results: Vec::new(),
        };
    }

    // `lake` is a wrapper which may spawn `lean`. Safe process-group cleanup
    // requires observing the wrapper's exit without reaping it: the unreaped
    // leader keeps its PID/PGID reserved until every descendant has been
    // signalled. Reject platforms where `waitid(..., WNOWAIT)` is unavailable
    // instead of risking a kill against a reused process-group ID.
    if !UNREAPED_CHILD_WAIT_AVAILABLE {
        return FirewallDiagnosticOutcome {
            reason: "(incomplete firewall-diagnostic-process-containment-unavailable)".to_string(),
            results: Vec::new(),
        };
    }

    let context = executor.context();
    let assertions = context
        .assertions
        .len()
        .max(context.assertions_parsed().len());
    // Reject every O(1)-known cap before either bounded scan. In particular,
    // `proof.steps.len()` is already known and must gate the payload walk.
    if let Err(limit) = check_diagnostic_o1_preflight(
        proof.steps.len(),
        assertions,
        context.terms.len(),
        context.terms.instance_term_bytes(),
    ) {
        return FirewallDiagnosticOutcome {
            reason: limit.reason().to_string(),
            results: Vec::new(),
        };
    }

    // Bound the inputs the emitter walks before it allocates its Vec<String>.
    // Counting every theory lemma is deliberately conservative: unsupported
    // kinds may emit nothing, but accepting that over-cap proof would make this
    // guard depend on the emitter's current dispatch details. Check the shared
    // deadline during the scan so preflight cannot itself outrun the gate.
    let mut theory_lemmas = 0usize;
    let mut emitter_items = 0usize;
    for step in &proof.steps {
        if diagnostic_time_remaining(gate_started, total_budget).is_none() {
            return FirewallDiagnosticOutcome {
                reason: "(incomplete firewall-total-deadline-exceeded)".to_string(),
                results: Vec::new(),
            };
        }
        match step {
            ay_core::ProofStep::Assume(_) => {
                emitter_items = emitter_items.saturating_add(1);
            }
            ay_core::ProofStep::TheoryLemma { clause, .. } => {
                theory_lemmas = theory_lemmas.saturating_add(1);
                emitter_items = emitter_items.saturating_add(clause.len());
            }
            _ => {}
        }
        if emitter_items > MAX_DIAGNOSTIC_EMITTER_ITEMS {
            return FirewallDiagnosticOutcome {
                reason: DiagnosticPreflightLimit::EmitterItems.reason().to_string(),
                results: Vec::new(),
            };
        }
        if theory_lemmas
            .checked_add(NON_STEP_ARTIFACT_UPPER_BOUND)
            .is_none_or(|files| files > MAX_DIAGNOSTIC_FILES)
        {
            return FirewallDiagnosticOutcome {
                reason: DiagnosticPreflightLimit::PotentialFiles
                    .reason()
                    .to_string(),
                results: Vec::new(),
            };
        }
    }
    // Datatype declarations live in frontend registries rather than the term
    // arena. A query can declare many unused constructors, so term count/bytes
    // alone do not bound the registry clone performed by the emitter.
    let mut datatypes = 0usize;
    let mut datatype_constructors = 0usize;
    let mut datatype_bytes = 0usize;
    for (name, constructors) in context.datatype_iter() {
        if diagnostic_time_remaining(gate_started, total_budget).is_none() {
            return FirewallDiagnosticOutcome {
                reason: "(incomplete firewall-total-deadline-exceeded)".to_string(),
                results: Vec::new(),
            };
        }
        datatypes = datatypes.saturating_add(1);
        datatype_constructors = datatype_constructors.saturating_add(constructors.len());
        datatype_bytes = datatype_bytes.saturating_add(name.len());
        for constructor in constructors {
            if diagnostic_time_remaining(gate_started, total_budget).is_none() {
                return FirewallDiagnosticOutcome {
                    reason: "(incomplete firewall-total-deadline-exceeded)".to_string(),
                    results: Vec::new(),
                };
            }
            datatype_bytes = datatype_bytes.saturating_add(constructor.len());
            if datatype_bytes > MAX_DIAGNOSTIC_DATATYPE_BYTES {
                break;
            }
        }
        if datatypes > MAX_DIAGNOSTIC_DATATYPES
            || datatype_constructors > MAX_DIAGNOSTIC_DATATYPE_CONSTRUCTORS
            || datatype_bytes > MAX_DIAGNOSTIC_DATATYPE_BYTES
        {
            break;
        }
    }
    if let Err(limit) = check_diagnostic_preflight(
        proof.steps.len(),
        emitter_items,
        theory_lemmas,
        assertions,
        context.terms.len(),
        context.terms.instance_term_bytes(),
        datatypes,
        datatype_constructors,
        datatype_bytes,
    ) {
        return FirewallDiagnosticOutcome {
            reason: limit.reason().to_string(),
            results: Vec::new(),
        };
    }

    let Some(leans) = executor.emit_datatype_firewall_lean_bounded(
        proof,
        MAX_DIAGNOSTIC_FILES,
        MAX_DIAGNOSTIC_SOURCE_BYTES,
    ) else {
        return FirewallDiagnosticOutcome {
            reason: "(incomplete firewall-diagnostic-emission-cap-exceeded)".to_string(),
            results: Vec::new(),
        };
    };
    if leans.is_empty() {
        return FirewallDiagnosticOutcome {
            reason: "(incomplete firewall-not-emitted)".to_string(),
            results: Vec::new(),
        };
    }
    if leans.len() > MAX_DIAGNOSTIC_FILES {
        return FirewallDiagnosticOutcome {
            reason: "(incomplete firewall-diagnostic-file-cap-exceeded)".to_string(),
            results: Vec::new(),
        };
    }

    // Consume emitter strings into one bounded standalone batch. Each standalone
    // source is constructed exactly once; its exact length is audited before
    // allocation, and the emitter String is dropped as soon as it is converted.
    let mut source_bytes = 0usize;
    let mut standalones = Vec::with_capacity(leans.len());
    for (index, lean) in leans.into_iter().enumerate() {
        if diagnostic_time_remaining(gate_started, total_budget).is_none() {
            return FirewallDiagnosticOutcome {
                reason: "(incomplete firewall-total-deadline-exceeded)".to_string(),
                results: vec![LemmaCheck {
                    index,
                    passed: false,
                    detail: "total firewall diagnostic deadline exceeded".to_string(),
                }],
            };
        }
        let bytes = match standalone_firewall_source_len(&lean) {
            Ok(bytes) => bytes,
            Err(error) => {
                return FirewallDiagnosticOutcome {
                    reason: "(incomplete firewall-source-audit-failed)".to_string(),
                    results: vec![LemmaCheck {
                        index,
                        passed: false,
                        detail: format!("source audit error: {error}"),
                    }],
                };
            }
        };
        source_bytes = match checked_diagnostic_source_total(source_bytes, bytes) {
            Some(total) => total,
            _ => {
                return FirewallDiagnosticOutcome {
                    reason: "(incomplete firewall-diagnostic-source-cap-exceeded)".to_string(),
                    results: vec![LemmaCheck {
                        index,
                        passed: false,
                        detail: format!(
                            "aggregate standalone source exceeds {MAX_DIAGNOSTIC_SOURCE_BYTES} byte cap"
                        ),
                    }],
                };
            }
        };
        let standalone = match standalone_firewall_source(&lean) {
            Ok(source) => source,
            Err(error) => {
                return FirewallDiagnosticOutcome {
                    reason: "(incomplete firewall-source-audit-failed)".to_string(),
                    results: vec![LemmaCheck {
                        index,
                        passed: false,
                        detail: format!("source audit error: {error}"),
                    }],
                };
            }
        };
        debug_assert_eq!(standalone.len(), bytes);
        standalones.push(standalone);
    }

    let tmp = match FirewallTempDir::new() {
        Ok(dir) => dir,
        Err(e) => {
            return FirewallDiagnosticOutcome {
                reason: format!("(incomplete firewall-tmpdir-error \"{}\")", sanitize(&e)),
                results: Vec::new(),
            };
        }
    };
    if let Err(error) = initialize_lean_project(tmp.path()) {
        return FirewallDiagnosticOutcome {
            reason: format!(
                "(incomplete firewall-lean-project-error \"{}\")",
                sanitize(&error)
            ),
            results: Vec::new(),
        };
    }

    let mut results: Vec<LemmaCheck> = Vec::with_capacity(standalones.len());
    let mut stop_reason: Option<&'static str> = None;
    for (i, standalone) in standalones.iter().enumerate() {
        if diagnostic_time_remaining(gate_started, total_budget).is_none() {
            results.push(LemmaCheck {
                index: i,
                passed: false,
                detail: "total firewall diagnostic deadline exceeded".to_string(),
            });
            stop_reason = Some("(incomplete firewall-total-deadline-exceeded)");
            break;
        }
        let path = tmp.path().join(format!("firewall_{i}.lean"));
        if let Err(e) = std::fs::write(&path, standalone) {
            results.push(LemmaCheck {
                index: i,
                passed: false,
                detail: format!("write error: {e}"),
            });
            stop_reason = Some("(incomplete firewall-write-failed)");
            break;
        }
        let Some(remaining) = diagnostic_time_remaining(gate_started, total_budget) else {
            results.push(LemmaCheck {
                index: i,
                passed: false,
                detail: "total firewall diagnostic deadline exceeded".to_string(),
            });
            stop_reason = Some("(incomplete firewall-total-deadline-exceeded)");
            break;
        };
        let check = kernel_check_one(tmp.path(), &path, remaining.min(PER_FILE_TIMEOUT));
        if !check.passed {
            stop_reason = Some("(incomplete firewall-kernel-check-failed)");
        }
        results.push(check);
        if stop_reason.is_some() {
            break;
        }
    }

    if let Some(reason) = stop_reason {
        FirewallDiagnosticOutcome {
            reason: reason.to_string(),
            results,
        }
    } else {
        diagnostic_only_outcome(results)
    }
}

/// Emit the diagnostic per-artifact PASS/FAIL report and a coverage summary.
pub(crate) fn report(results: &[LemmaCheck]) {
    for r in results {
        let tag = if r.passed { "PASS" } else { "FAIL" };
        safe_eprintln!(
            "ay: firewall diagnostic #{} {} — {}",
            r.index,
            tag,
            r.detail
        );
    }
    let passed = results.iter().filter(|r| r.passed).count();
    if results.is_empty() {
        safe_eprintln!(
            "ay: firewall diagnostic incomplete — no query-bound certificate; reporting unknown"
        );
    } else {
        safe_eprintln!(
            "ay: firewall diagnostic complete — {}/{} artifact(s) kernel-checked; artifacts do not certify the query; reporting unknown",
            passed,
            results.len()
        );
    }
}

const AXIOM_AUDIT_SENTINEL: &str = "AY_FIREWALL_AXIOM_AUDIT_END";
const AXIOM_AUDIT_PREFIX: &str = "\n#print axioms no_model\n#eval IO.println \"";
const AXIOM_AUDIT_SUFFIX: &str = "\"\n";

struct StandaloneParts<'a> {
    body: &'a str,
    firewall: &'static str,
    /// `REGEX_SOURCE` with its `import AySoundness.StringThy` header stripped,
    /// so it concatenates after the embedded `STRING_SOURCE`.
    regex: &'static str,
    audit_at: usize,
}

/// The import allow-list, in the ORDER an emitted artifact must write it. The
/// strip below is an ordered `strip_prefix` walk, so an emitter whose header
/// lists these modules in a different relative order leaves a residual `import `
/// line and is rejected as untrusted. `AySoundness.NiaProduct` therefore sits
/// immediately AFTER `AySoundness.Firewall`, matching
/// `render_nia_product_lean`'s two-line header. Skipping entries is fine — the
/// walk only strips what is actually present — so the string emitters'
/// `Firewall`/`StringThy` pair, the regex emitter's
/// `Firewall`/`StringThy`/`RegexThy` triple, and the REAL-sorted ordered-field
/// emitter's `Firewall`/`OrdField` pair all pass.
///
/// Modules whose emitters are still REJECTED here (their sources are not
/// embedded, so accepting the import would let a working-directory module
/// redefine the lemma): `AySoundness.SeqThy`, `AySoundness.SetThy`,
/// `AySoundness.FpUnderflow`. Adding one means embedding its source below and
/// concatenating it in dependency order — not just listing it here.
const ALLOWED_EMITTED_IMPORTS: [&str; 7] = [
    "import AySoundness.Firewall\n",
    "import AySoundness.NiaProduct\n",
    "import AySoundness.FpThy\n",
    "import AySoundness.Datatype\n",
    "import AySoundness.StringThy\n",
    "import AySoundness.RegexThy\n",
    "import AySoundness.OrdField\n",
];

fn standalone_parts(emitted: &str) -> Result<StandaloneParts<'_>, String> {
    let mut body = emitted;
    for import in ALLOWED_EMITTED_IMPORTS {
        if let Some(rest) = body.strip_prefix(import) {
            body = rest;
        }
    }
    if body.trim_start().starts_with("import ") {
        return Err("emitter requested an untrusted Lean import".to_string());
    }

    let firewall = FIREWALL_SOURCE
        .strip_prefix("import AySoundness.Lrat\n")
        .ok_or_else(|| "embedded Firewall source has an unexpected import header".to_string())?;
    let regex = REGEX_SOURCE
        .strip_prefix("import AySoundness.StringThy\n")
        .ok_or_else(|| "embedded RegexThy source has an unexpected import header".to_string())?;
    let theorem = body
        .find("theorem no_model")
        .ok_or_else(|| "emitter produced no no_model theorem".to_string())?;
    let relative_end = body[theorem..]
        .find("\nend ")
        .ok_or_else(|| "emitter produced no namespace end after no_model".to_string())?;

    Ok(StandaloneParts {
        body,
        firewall,
        regex,
        audit_at: theorem + relative_end,
    })
}

fn standalone_firewall_source_len(emitted: &str) -> Result<usize, String> {
    let parts = standalone_parts(emitted)?;
    [
        LRAT_SOURCE.len(),
        1,
        parts.firewall.len(),
        1,
        FP_SOURCE.len(),
        1,
        DATATYPE_SOURCE.len(),
        1,
        NIA_PRODUCT_SOURCE.len(),
        1,
        STRING_SOURCE.len(),
        1,
        parts.regex.len(),
        1,
        ORD_FIELD_SOURCE.len(),
        1,
        parts.body.len(),
        AXIOM_AUDIT_PREFIX.len(),
        AXIOM_AUDIT_SENTINEL.len(),
        AXIOM_AUDIT_SUFFIX.len(),
    ]
    .into_iter()
    .try_fold(0usize, |total, bytes| total.checked_add(bytes))
    .ok_or_else(|| "standalone source size overflow".to_string())
}

/// Turn an emitter result into a self-contained Lean file whose trusted theorem
/// base is the source embedded in this AY binary. The runtime project is used
/// only to select the Lean toolchain; none of its AySoundness modules are
/// imported. The audit commands remain inside the emitter's namespace so
/// `no_model` resolves unambiguously.
fn standalone_firewall_source(emitted: &str) -> Result<String, String> {
    let parts = standalone_parts(emitted)?;
    let mut source = String::with_capacity(standalone_firewall_source_len(emitted)?);
    source.push_str(LRAT_SOURCE);
    source.push('\n');
    source.push_str(parts.firewall);
    source.push('\n');
    source.push_str(FP_SOURCE);
    source.push('\n');
    source.push_str(DATATYPE_SOURCE);
    source.push('\n');
    source.push_str(NIA_PRODUCT_SOURCE);
    source.push('\n');
    // Dependency order: RegexThy's stripped source refers to StringThy's `Str`
    // and `len`, so StringThy must precede it. OrdField is import-free and
    // independent of both, so it follows them.
    source.push_str(STRING_SOURCE);
    source.push('\n');
    source.push_str(parts.regex);
    source.push('\n');
    source.push_str(ORD_FIELD_SOURCE);
    source.push('\n');
    source.push_str(&parts.body[..parts.audit_at]);
    source.push_str(AXIOM_AUDIT_PREFIX);
    source.push_str(AXIOM_AUDIT_SENTINEL);
    source.push_str(AXIOM_AUDIT_SUFFIX);
    source.push_str(&parts.body[parts.audit_at..]);
    Ok(source)
}

/// Diagnostic-check a single firewall file with `lake env lean <file>` inside
/// the private embedded-metadata project. The external executable/toolchain is
/// diagnostic TCB only and cannot authorize an AY query verdict.
fn kernel_check_one(project: &Path, file: &Path, timeout: Duration) -> LemmaCheck {
    let index = firewall_index(file);
    let lake = lake_binary();
    let mut cmd = kernel_check_command(&lake, project, file);
    #[cfg(unix)]
    ay_sys::supervisor::configure_child_address_space_limit(
        &mut cmd,
        diagnostic_child_memory_limit(),
    );
    isolate_process_group(&mut cmd);

    let child = match cmd.spawn() {
        Ok(c) => c,
        Err(err) if err.kind() == std::io::ErrorKind::NotFound => {
            return LemmaCheck {
                index,
                passed: false,
                detail: format!("lake not found at '{}'", lake.display()),
            };
        }
        Err(err) => {
            return LemmaCheck {
                index,
                passed: false,
                detail: format!("failed to spawn lake: {err}"),
            };
        }
    };

    match wait_with_timeout(child, timeout) {
        WaitOutcome::Exited {
            code,
            stdout,
            stderr,
            rejection_seen,
        } => {
            let diag = format!("{stdout}\n{stderr}");
            let axiom_audit = if diag.matches(AXIOM_AUDIT_SENTINEL).count() == 1 {
                axiom_audit_result(&stdout)
                    .or_else(|_| axiom_audit_result(&stderr))
                    .or_else(|_| axiom_audit_result(&diag))
            } else {
                Err("missing or duplicate audit sentinel across Lean streams".to_string())
            };
            if code == 0
                && !rejection_seen
                && !stderr_indicates_rejection(&diag)
                && axiom_audit.is_ok()
            {
                LemmaCheck {
                    index,
                    passed: true,
                    detail: "kernel-checked; axiom audit passed".to_string(),
                }
            } else {
                let audit_detail = axiom_audit
                    .err()
                    .map(|error| format!("; axiom audit: {error}"))
                    .unwrap_or_default();
                LemmaCheck {
                    index,
                    passed: false,
                    detail: format!(
                        "lean rejected (exit {code}): {}{audit_detail}",
                        first_error_line(&diag)
                    ),
                }
            }
        }
        WaitOutcome::TimedOut => LemmaCheck {
            index,
            passed: false,
            detail: format!("lean exceeded {:.3}s timeout", timeout.as_secs_f64()),
        },
        WaitOutcome::Error(e) => LemmaCheck {
            index,
            passed: false,
            detail: format!("lean wait error: {e}"),
        },
    }
}

fn kernel_check_command(lake: &Path, project: &Path, file: &Path) -> Command {
    let mut cmd = Command::new(lake);
    cmd.current_dir(project)
        .arg("env")
        .arg("lean")
        // A single source file gains nothing from Lean's hardware-sized worker
        // pool. Lean's default 1 GiB worker stacks can exhaust the checker's
        // fixed address-space envelope before elaboration starts.
        .arg("-j1")
        .arg("-s8192")
        .arg(file)
        // Lean prints kernel/elaboration diagnostics to STDOUT; capture both
        // streams and treat an error marker on either as rejection (defensive
        // against a toolchain that reports an error but exits 0).
        .stdout(Stdio::piped())
        .stderr(Stdio::piped());
    cmd
}

enum WaitOutcome {
    Exited {
        code: i32,
        stdout: String,
        stderr: String,
        /// Rejection marker observed anywhere in either full stream, including
        /// bytes omitted from the bounded diagnostic text.
        rejection_seen: bool,
    },
    TimedOut,
    Error(String),
}

fn wait_with_timeout(mut child: Child, timeout: Duration) -> WaitOutcome {
    // Drain both pipes from process start. Waiting for the child to exit before
    // reading can deadlock once Lean fills an OS pipe; that used to turn a
    // quick rejection with verbose diagnostics into a false 120-second timeout.
    let stdout = child.stdout.take().map(BoundedCapture::start);
    let stderr = child.stderr.take().map(BoundedCapture::start);
    let start = Instant::now();
    let poll = Duration::from_millis(50);
    loop {
        match child_exited_unreaped(&child) {
            Ok(true) => {
                // A wrapper may exit while a descendant still owns the pipe
                // descriptors. The leader is deliberately still unreaped here,
                // so its PID/PGID cannot be reused while the complete dedicated
                // group is killed.
                let status = match terminate_process_group(&mut child, false) {
                    Ok(status) => status,
                    Err(error) => return WaitOutcome::Error(error),
                };
                let stdout = match finish_capture(stdout, "stdout") {
                    Ok(output) => output,
                    Err(error) => return WaitOutcome::Error(error),
                };
                let stderr = match finish_capture(stderr, "stderr") {
                    Ok(output) => output,
                    Err(error) => return WaitOutcome::Error(error),
                };
                return WaitOutcome::Exited {
                    code: status.code().unwrap_or(-1),
                    stdout: stdout.text,
                    stderr: stderr.text,
                    rejection_seen: stdout.rejection_seen || stderr.rejection_seen,
                };
            }
            Ok(false) => {
                if start.elapsed() >= timeout {
                    if let Err(error) = terminate_process_group(&mut child, true) {
                        return WaitOutcome::Error(error);
                    }
                    return WaitOutcome::TimedOut;
                }
                std::thread::sleep(poll);
            }
            Err(e) => {
                // An observation failure means we cannot prove that the group
                // leader still reserves this PGID. Do not issue a potentially
                // misdirected kill; the firewall verdict remains fail-closed.
                return WaitOutcome::Error(e);
            }
        }
    }
}

#[cfg(any(
    target_os = "android",
    target_os = "freebsd",
    target_os = "haiku",
    all(target_os = "linux", not(target_env = "uclibc")),
))]
const UNREAPED_CHILD_WAIT_AVAILABLE: bool = true;

#[cfg(not(any(
    target_os = "android",
    target_os = "freebsd",
    target_os = "haiku",
    all(target_os = "linux", not(target_env = "uclibc")),
)))]
const UNREAPED_CHILD_WAIT_AVAILABLE: bool = false;

#[cfg(any(
    target_os = "android",
    target_os = "freebsd",
    target_os = "haiku",
    all(target_os = "linux", not(target_env = "uclibc")),
))]
fn child_exited_unreaped(child: &Child) -> Result<bool, String> {
    use nix::sys::wait::{waitid, Id, WaitPidFlag, WaitStatus};
    use nix::unistd::Pid;

    let raw_pid = i32::try_from(child.id())
        .map_err(|_| "firewall child PID does not fit pid_t".to_string())?;
    let flags = WaitPidFlag::WEXITED | WaitPidFlag::WNOHANG | WaitPidFlag::WNOWAIT;
    match waitid(Id::Pid(Pid::from_raw(raw_pid)), flags) {
        Ok(WaitStatus::Exited(..) | WaitStatus::Signaled(..)) => Ok(true),
        Ok(WaitStatus::StillAlive) => Ok(false),
        Ok(status) => Err(format!(
            "unexpected unreaped firewall child status: {status:?}"
        )),
        Err(error) => Err(format!(
            "failed to observe firewall child without reaping it: {error}"
        )),
    }
}

#[cfg(not(any(
    target_os = "android",
    target_os = "freebsd",
    target_os = "haiku",
    all(target_os = "linux", not(target_env = "uclibc")),
)))]
fn child_exited_unreaped(_child: &Child) -> Result<bool, String> {
    Err("unreaped child observation is unavailable on this platform".to_string())
}

const CAPTURE_HEAD_BYTES: usize = 128 * 1024;
const CAPTURE_TAIL_BYTES: usize = 128 * 1024;
const CAPTURE_FINISH_TIMEOUT: Duration = Duration::from_secs(2);

struct BoundedCapture {
    receiver: mpsc::Receiver<Result<CapturedOutput, String>>,
}

struct CapturedOutput {
    text: String,
    rejection_seen: bool,
}

impl BoundedCapture {
    fn start<R>(mut reader: R) -> Self
    where
        R: std::io::Read + Send + 'static,
    {
        let (sender, receiver) = mpsc::channel();
        std::thread::spawn(move || {
            let mut head = Vec::new();
            let mut tail: VecDeque<Vec<u8>> = VecDeque::new();
            let mut tail_len = 0usize;
            let mut total_len = 0usize;
            let mut scan_suffix = Vec::new();
            let mut rejection_seen = false;
            let mut chunk = [0u8; 8192];
            loop {
                let read = match reader.read(&mut chunk) {
                    Ok(0) => break,
                    Ok(read) => read,
                    Err(error) if error.kind() == std::io::ErrorKind::Interrupted => continue,
                    Err(error) => {
                        let _ = sender.send(Err(error.to_string()));
                        return;
                    }
                };
                total_len = total_len.saturating_add(read);
                let mut scan = Vec::with_capacity(scan_suffix.len() + read);
                scan.extend_from_slice(&scan_suffix);
                scan.extend_from_slice(&chunk[..read]);
                rejection_seen |= rejection_bytes_present(&scan);
                let suffix_start = scan
                    .len()
                    .saturating_sub(MAX_REJECTION_PATTERN_BYTES.saturating_sub(1));
                scan_suffix.clear();
                scan_suffix.extend_from_slice(&scan[suffix_start..]);
                let head_read = read.min(CAPTURE_HEAD_BYTES.saturating_sub(head.len()));
                head.extend_from_slice(&chunk[..head_read]);
                if head_read < read {
                    let trailing = chunk[head_read..read].to_vec();
                    tail_len = tail_len.saturating_add(trailing.len());
                    tail.push_back(trailing);
                    while tail_len > CAPTURE_TAIL_BYTES {
                        let excess = tail_len - CAPTURE_TAIL_BYTES;
                        let Some(front) = tail.front_mut() else {
                            break;
                        };
                        let remove = excess.min(front.len());
                        front.drain(..remove);
                        tail_len -= remove;
                        if front.is_empty() {
                            tail.pop_front();
                        }
                    }
                }
            }

            if total_len > head.len().saturating_add(tail_len) {
                head.extend_from_slice(b"\n... diagnostics truncated ...\n");
            }
            for bytes in tail {
                head.extend_from_slice(&bytes);
            }
            let _ = sender.send(Ok(CapturedOutput {
                text: String::from_utf8_lossy(&head).into_owned(),
                rejection_seen,
            }));
        });
        Self { receiver }
    }

    fn finish(self) -> Result<CapturedOutput, String> {
        self.receiver
            .recv_timeout(CAPTURE_FINISH_TIMEOUT)
            .map_err(|error| format!("diagnostic capture did not finish: {error}"))?
    }
}

fn finish_capture(capture: Option<BoundedCapture>, stream: &str) -> Result<CapturedOutput, String> {
    capture
        .map(BoundedCapture::finish)
        .transpose()
        .map_err(|error| format!("failed to capture Lean {stream}: {error}"))?
        .map_or_else(
            || {
                Ok(CapturedOutput {
                    text: String::new(),
                    rejection_seen: false,
                })
            },
            Ok,
        )
}

#[cfg(unix)]
fn isolate_process_group(cmd: &mut Command) {
    use std::os::unix::process::CommandExt as _;
    cmd.process_group(0);
}

#[cfg(not(unix))]
fn isolate_process_group(_cmd: &mut Command) {}

#[cfg(any(
    target_os = "android",
    target_os = "freebsd",
    target_os = "haiku",
    all(target_os = "linux", not(target_env = "uclibc")),
))]
fn terminate_process_group(
    child: &mut Child,
    allow_term_grace: bool,
) -> Result<std::process::ExitStatus, String> {
    use nix::errno::Errno;
    use nix::sys::signal::{killpg, Signal};
    use nix::unistd::Pid;

    let raw_pid = i32::try_from(child.id())
        .map_err(|_| "firewall child PID does not fit pid_t".to_string())?;
    let pgid = Pid::from_raw(raw_pid);
    let signal_group = |signal| match killpg(pgid, signal) {
        Ok(()) | Err(Errno::ESRCH) => Ok(()),
        Err(error) => Err(format!(
            "failed to signal firewall process group {raw_pid}: {error}"
        )),
    };

    if allow_term_grace {
        signal_group(Signal::SIGTERM)?;
        // Keep the leader unreaped for the complete grace interval, so even a
        // wrapper that exits in response to SIGTERM continues to lease its
        // process-group identity until SIGKILL has covered all descendants.
        std::thread::sleep(Duration::from_millis(200));
    }
    signal_group(Signal::SIGKILL)?;

    // SIGKILL does not wake an uninterruptible task. Bound cleanup instead of
    // turning the firewall deadline into an unbounded `Child::wait`.
    let deadline = Instant::now() + Duration::from_secs(2);
    loop {
        if child_exited_unreaped(child)? {
            return child
                .wait()
                .map_err(|error| format!("failed to reap firewall child: {error}"));
        }
        if Instant::now() >= deadline {
            return Err("firewall child did not exit after process-group SIGKILL".to_string());
        }
        std::thread::sleep(Duration::from_millis(10));
    }
}

#[cfg(not(any(
    target_os = "android",
    target_os = "freebsd",
    target_os = "haiku",
    all(target_os = "linux", not(target_env = "uclibc")),
)))]
fn terminate_process_group(
    _child: &mut Child,
    _allow_term_grace: bool,
) -> Result<std::process::ExitStatus, String> {
    Err("firewall process-group containment is unavailable on this platform".to_string())
}

fn stderr_indicates_rejection(stderr: &str) -> bool {
    stderr.contains("error:")
        || stderr.contains("proof failed")
        || stderr.contains("declaration uses 'sorry'")
        || stderr.contains("declaration uses `sorry`")
}

const REJECTION_PATTERNS: [&[u8]; 4] = [
    b"error:",
    b"proof failed",
    b"declaration uses 'sorry'",
    b"declaration uses `sorry`",
];
const MAX_REJECTION_PATTERN_BYTES: usize = 24;

fn rejection_bytes_present(bytes: &[u8]) -> bool {
    REJECTION_PATTERNS.iter().any(|pattern| {
        bytes
            .windows(pattern.len())
            .any(|window| window == *pattern)
    })
}

const ALLOWED_AXIOMS: [&str; 3] = ["propext", "Classical.choice", "Quot.sound"];

fn axiom_audit_result(output: &str) -> Result<(), String> {
    if output.matches(AXIOM_AUDIT_SENTINEL).count() != 1 {
        return Err("missing or duplicate audit sentinel".to_string());
    }
    let sentinel = output
        .find(AXIOM_AUDIT_SENTINEL)
        .ok_or_else(|| "missing audit sentinel".to_string())?;
    let report = &output[..sentinel];
    let no_axioms_marker = "does not depend on any axioms";
    let marker = "depends on axioms:";
    let no_axioms = report.rfind(no_axioms_marker);
    let depends = report.rfind(marker);
    let start = match (no_axioms, depends) {
        (Some(no_axioms), Some(depends)) if no_axioms > depends => no_axioms,
        (Some(no_axioms), None) => no_axioms,
        (_, Some(depends)) => depends,
        (None, None) => return Err("missing #print axioms report".to_string()),
    };
    let line_start = report[..start].rfind('\n').map_or(0, |newline| newline + 1);
    if !report[line_start..start].contains("no_model") {
        return Err("axiom report is not for no_model".to_string());
    }
    if Some(start) == no_axioms {
        return Ok(());
    }

    let list = &report[start + marker.len()..];
    let open = list
        .find('[')
        .ok_or_else(|| "malformed axiom list (missing '[')".to_string())?;
    let close = list[open + 1..]
        .find(']')
        .map(|offset| open + 1 + offset)
        .ok_or_else(|| "malformed axiom list (missing ']')".to_string())?;
    let names = &list[open + 1..close];
    for name in names
        .split(',')
        .map(str::trim)
        .filter(|name| !name.is_empty())
    {
        if !ALLOWED_AXIOMS.contains(&name) {
            return Err(format!("forbidden axiom '{name}'"));
        }
    }
    Ok(())
}

fn first_error_line(stderr: &str) -> String {
    let line = stderr
        .lines()
        .find(|l| l.contains("error:"))
        .or_else(|| stderr.lines().find(|l| !l.trim().is_empty()))
        .unwrap_or("")
        .trim();
    let truncated: String = line.chars().take(160).collect();
    sanitize(&truncated)
}

fn sanitize(s: &str) -> String {
    s.replace('"', "'").replace('\n', " ")
}

fn firewall_index(file: &Path) -> usize {
    file.file_stem()
        .and_then(|s| s.to_str())
        .and_then(|s| s.strip_prefix("firewall_"))
        .and_then(|s| s.parse::<usize>().ok())
        .unwrap_or(0)
}

/// The diagnostic `lake` binary to drive. This external executable and the Lean
/// toolchain it selects are diagnostic TCB only: their output cannot authorize
/// an `unsat` result.
fn lake_binary() -> PathBuf {
    if let Some(home) = std::env::var_os("HOME") {
        let elan = PathBuf::from(home).join(".elan/bin/lake");
        if elan.exists() {
            return elan;
        }
    }
    PathBuf::from("lake")
}

/// Materialize only the Lake metadata needed to select the build-pinned Lean
/// toolchain. Both files are embedded in the executable, so a copied/installed
/// AY binary does not depend on the original `CARGO_MANIFEST_DIR` checkout and
/// never searches the caller's working directory for project configuration.
fn initialize_lean_project(project: &Path) -> Result<(), String> {
    std::fs::write(project.join("lakefile.toml"), LAKEFILE_SOURCE)
        .map_err(|error| format!("could not write embedded lakefile.toml: {error}"))?;
    std::fs::write(project.join("lean-toolchain"), LEAN_TOOLCHAIN_SOURCE)
        .map_err(|error| format!("could not write embedded lean-toolchain: {error}"))?;
    Ok(())
}

static TEMP_DIR_COUNTER: AtomicU64 = AtomicU64::new(0);

struct FirewallTempDir {
    path: PathBuf,
}

impl FirewallTempDir {
    fn new() -> Result<Self, String> {
        let base = std::env::temp_dir();
        let nonce = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map(|duration| duration.as_nanos())
            .unwrap_or(0);
        for _ in 0..32 {
            let sequence = TEMP_DIR_COUNTER.fetch_add(1, Ordering::Relaxed);
            let path = base.join(format!(
                "ay-firewall-{}-{nonce}-{sequence}",
                std::process::id()
            ));
            let mut builder = std::fs::DirBuilder::new();
            #[cfg(unix)]
            {
                use std::os::unix::fs::DirBuilderExt as _;
                builder.mode(0o700);
            }
            match builder.create(&path) {
                Ok(()) => return Ok(Self { path }),
                Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => continue,
                Err(error) => return Err(error.to_string()),
            }
        }
        Err("could not allocate a unique firewall temporary directory".to_string())
    }

    fn path(&self) -> &Path {
        &self.path
    }
}

impl Drop for FirewallTempDir {
    fn drop(&mut self) {
        // Cleanup is best effort and cannot widen a solver verdict.
        let _ = std::fs::remove_dir_all(&self.path);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn firewall_index_parses_filename() {
        assert_eq!(firewall_index(Path::new("/x/firewall_0.lean")), 0);
        assert_eq!(firewall_index(Path::new("/x/firewall_7.lean")), 7);
        assert_eq!(firewall_index(Path::new("/x/other.lean")), 0);
    }

    #[test]
    fn stderr_rejection_detection() {
        assert!(stderr_indicates_rejection("foo error: bad\n"));
        assert!(stderr_indicates_rejection("declaration uses 'sorry'"));
        assert!(!stderr_indicates_rejection("warning: unused variable\n"));
        assert!(!stderr_indicates_rejection(""));
    }

    #[test]
    fn sanitize_strips_quotes_and_newlines() {
        assert_eq!(sanitize("a\"b\nc"), "a'b c");
    }

    #[test]
    fn lean_project_is_materialized_from_embedded_metadata() {
        let temp = FirewallTempDir::new().expect("temporary firewall directory");
        initialize_lean_project(temp.path()).expect("embedded Lake project");
        assert_eq!(
            std::fs::read_to_string(temp.path().join("lakefile.toml")).expect("lakefile"),
            LAKEFILE_SOURCE
        );
        assert_eq!(
            std::fs::read_to_string(temp.path().join("lean-toolchain")).expect("toolchain"),
            LEAN_TOOLCHAIN_SOURCE
        );
    }

    #[test]
    fn kernel_checker_uses_one_lean_worker() {
        let command = kernel_check_command(
            Path::new("lake"),
            Path::new("/tmp/project"),
            Path::new("/tmp/firewall.lean"),
        );
        let args = command
            .get_args()
            .map(|arg| arg.to_string_lossy().into_owned())
            .collect::<Vec<_>>();
        assert_eq!(args, ["env", "lean", "-j1", "-s8192", "/tmp/firewall.lean"]);
        assert_eq!(command.get_current_dir(), Some(Path::new("/tmp/project")));
    }

    #[test]
    fn standalone_source_embeds_trusted_base_and_axiom_audit() {
        let emitted = "import AySoundness.Firewall\n\
                       import AySoundness.FpThy\n\
                       namespace Example\n\
                       theorem no_model : True := by trivial\n\
                       end Example\n";
        let source = standalone_firewall_source(emitted).expect("standalone source");
        assert_eq!(
            source.len(),
            standalone_firewall_source_len(emitted).expect("standalone source length")
        );
        assert!(!source.lines().any(|line| line.starts_with("import ")));
        assert!(source.contains("theorem lratCheck_sound"));
        assert!(source.contains("theorem firewall_combined_unsat"));
        assert!(source.contains("namespace AySoundness.FpThy"));
        let audit = source
            .find("#print axioms no_model")
            .expect("axiom audit command");
        let end = source.rfind("end Example").expect("namespace end");
        assert!(audit < end);
        assert!(source.contains(AXIOM_AUDIT_SENTINEL));
    }

    /// The verbatim body of a real `--emit-firewall-lean` artifact from the
    /// nonlinear-integer product emitter (`benchmarks/smt/QF_NIA/`
    /// `sign_consistency.smt2`), doc comment elided. It is a FIXTURE, not a
    /// golden output: the point is that this exact byte shape — two allow-listed
    /// imports in the emitter's order, and a `AySoundness.NiaProduct` corner
    /// lemma applied inside the proof — survives the standalone embedding and is
    /// accepted by the Lean kernel with no project `.olean` in sight.
    const NIA_PRODUCT_ARTIFACT: &str = r#"import AySoundness.Firewall
import AySoundness.NiaProduct
set_option linter.unusedSimpArgs false

namespace AySoundness.Emitted.NiaProd_77b5a9d756ebabfd
open AySoundness

abbrev Val := Nat → Int

def atomVal (m : Val) (n : Nat) : Bool :=
  match n with
  | 1 => decide ((m 0) > (0 : Int))
  | 2 => decide ((m 1) > (0 : Int))
  | 3 => decide (((m 0) * (m 1)) < (0 : Int))
  | _ => false

def original : List (Cid × Clause) := [(1, [1]), (2, [2]), (3, [3])]
def lemmas   : List (Cid × Clause) := [(4, [-1, -2, -3])]
def proof    : List (Cid × Clause × List Int) := [(5, [], [1, 2, 3, 4])]

theorem lemma_valid (m : Val) : clauseSat (atomVal m) [-1, -2, -3] = true := by
  simp only [clauseSat, litSat, atomVal, List.any_cons, List.any_nil,
    Int.reduceGT, Int.reduceNeg, Int.reduceToNat, reduceIte, Bool.or_false,
    Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not]
  exact
    if h1 : (m 0) > (0 : Int) then
  if h2 : (m 1) > (0 : Int) then
  if h3 : ((m 0) * (m 1)) < (0 : Int) then (show False by have hb0 := AySoundness.NiaProduct.mul_lb_ll (x := (m 0)) (y := (m 1)) (a := (1 : Int)) (c := (1 : Int)) (by omega) (by omega); omega).elim else Or.inr (Or.inr (h3))
else Or.inr (Or.inl h2)
else Or.inl h1

theorem lemmas_valid :
    ∀ cl ∈ clauses lemmas, ∀ m : Val, clauseSat (atomVal m) cl = true := by
  intro cl hcl m
  simp only [clauses, lemmas, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hcl
  subst hcl
  exact lemma_valid m

theorem no_model : ∀ m : Val, ¬ Sat (atomVal m) (clauses original) :=
  firewall_combined_unsat (original := original) (lemmas := lemmas) (proof := proof)
    atomVal (by decide) (by decide) lemmas_valid (by decide)

end AySoundness.Emitted.NiaProd_77b5a9d756ebabfd
"#;

    /// The nonlinear-integer emitter imports `AySoundness.NiaProduct` on top of
    /// the common base, so the standalone build must EMBED that module's source
    /// too. Without the embedding the artifact would either lose its bridge
    /// lemma or fall back on a mutable project `.olean` — the exact substitution
    /// the embedding exists to prevent.
    #[test]
    fn standalone_source_embeds_the_nia_product_bridge() {
        let source = standalone_firewall_source(NIA_PRODUCT_ARTIFACT).expect("standalone source");
        assert_eq!(
            source.len(),
            standalone_firewall_source_len(NIA_PRODUCT_ARTIFACT).expect("standalone source length")
        );
        // Nothing is imported: every trusted module is inlined from this binary.
        assert!(!source.lines().any(|line| line.starts_with("import ")));
        assert!(source.contains("namespace AySoundness.NiaProduct"));
        assert!(source.contains("theorem mul_lb_ll"));
        assert!(source.contains("theorem firewall_combined_unsat"));
        // The bridge must be DEFINED before the emitted proof applies it.
        let bridge = source
            .find("theorem mul_lb_ll")
            .expect("bridge lemma in the embedded base");
        let use_site = source
            .find("AySoundness.NiaProduct.mul_lb_ll (x := (m 0))")
            .expect("bridge application in the emitted body");
        assert!(bridge < use_site);
        assert!(source.contains(AXIOM_AUDIT_SENTINEL));
        eprintln!("----STANDALONE-BEGIN----\n{source}\n----STANDALONE-END----");
    }

    /// O4: `standalone_parts` strips the allow-list with an ORDERED
    /// `strip_prefix` walk, so the emitter's header order is load-bearing. An
    /// artifact that lists `NiaProduct` BEFORE `Firewall` leaves a residual
    /// `import` line and must be rejected as untrusted rather than silently
    /// accepted — this pins the coupling that
    /// `lean_firewall::render_nia_product_lean` has to honour.
    #[test]
    fn standalone_source_rejects_allow_listed_imports_out_of_order() {
        let reordered = NIA_PRODUCT_ARTIFACT.replace(
            "import AySoundness.Firewall\nimport AySoundness.NiaProduct\n",
            "import AySoundness.NiaProduct\nimport AySoundness.Firewall\n",
        );
        assert!(standalone_firewall_source(&reordered).is_err());
        // Sanity: the allow-list itself is in the order emitters must write.
        assert_eq!(
            ALLOWED_EMITTED_IMPORTS[..2],
            [
                "import AySoundness.Firewall\n",
                "import AySoundness.NiaProduct\n"
            ]
        );
    }

    /// The verbatim body of a real `--emit-firewall-lean` artifact from the
    /// `str.in_re` length-invariant emitter, produced on
    /// `benchmarks/smtcomp/QF_SLIA/.../regex-011-unsat-fuzz-graft-reverse.smt2`
    /// (doc comment elided). Three allow-listed imports, and both a
    /// `AySoundness.StringThy` and a `AySoundness.RegexThy` name applied inside
    /// the proof.
    const STR_IN_RE_ARTIFACT: &str = r#"import AySoundness.Firewall
import AySoundness.StringThy
import AySoundness.RegexThy
namespace AySoundness.Emitted.StrInReLen_e14609b60131ee43
open AySoundness

abbrev Val := StringThy.Str

def re1 : RegexThy.Re :=
  (RegexThy.Re.cat (RegexThy.Re.star (RegexThy.Re.lit [58, 123, 39, 104, 65, 97])) (RegexThy.Re.star (RegexThy.Re.star (RegexThy.Re.lit [58, 123, 39, 104, 65, 97]))))

noncomputable def atomVal (m : Val) (n : Nat) : Bool :=
  match n with
  | 1 => decide (RegexThy.Mem re1 m)
  | 2 => decide (StringThy.len m = 4)
  | _ => false

def original : List (Cid × Clause) := [(1, [1]), (2, [2])]
def lemmas   : List (Cid × Clause) := [(3, [-1, -2])]
def proof    : List (Cid × Clause × List Int) := [(4, [], [1, 2, 3])]

theorem lemma_valid (m : Val) : clauseSat (atomVal m) [-1, -2] = true := by
  by_cases hm : RegexThy.Mem re1 m
  · have hpin : ¬ (StringThy.len m = 4) := fun h =>
      RegexThy.regex_len_mod_conflict (k := 6) (by decide) hm h (by decide)
    have ha : atomVal m 2 = false := by
      simp only [atomVal, decide_eq_false_iff_not]
      exact hpin
    simp [clauseSat, litSat, List.any_cons, List.any_nil, ha]
  · have ha : atomVal m 1 = false := by
      simp only [atomVal, decide_eq_false_iff_not]
      exact hm
    simp [clauseSat, litSat, List.any_cons, List.any_nil, ha]

theorem lemmas_valid :
    ∀ cl ∈ clauses lemmas, ∀ m : Val, clauseSat (atomVal m) cl = true := by
  intro cl hcl m
  simp only [clauses, lemmas, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hcl
  subst hcl
  exact lemma_valid m

theorem no_model : ∀ m : Val, ¬ Sat (atomVal m) (clauses original) :=
  firewall_combined_unsat (original := original) (lemmas := lemmas) (proof := proof)
    atomVal (by decide) (by decide) lemmas_valid (by decide)

end AySoundness.Emitted.StrInReLen_e14609b60131ee43
"#;

    /// REGRESSION (the acceptance path had never run for ANY string emitter):
    /// `AySoundness.StringThy` was absent from the allow-list AND from the
    /// embedded sources, so every `str.len`/`str.at`/`str.indexof`/`str.in_re`
    /// artifact was rejected with "emitter requested an untrusted Lean import"
    /// before a kernel ever saw it. Both halves matter — allow-listing an import
    /// whose source is not embedded would let a module in the working directory
    /// redefine the lemma the gate claims to check.
    #[test]
    fn standalone_source_embeds_the_string_and_regex_base() {
        let source = standalone_firewall_source(STR_IN_RE_ARTIFACT).expect("standalone source");
        assert_eq!(
            source.len(),
            standalone_firewall_source_len(STR_IN_RE_ARTIFACT).expect("standalone source length")
        );
        // Nothing is imported: every trusted module is inlined from this binary.
        assert!(!source.lines().any(|line| line.starts_with("import ")));
        assert!(source.contains("namespace AySoundness.StringThy"));
        assert!(source.contains("namespace AySoundness.RegexThy"));
        assert!(source.contains("theorem mem_len_dvd"));
        assert!(source.contains("theorem regex_len_mod_conflict"));
        // Dependency order: RegexThy's body mentions `StringThy.Str`.
        let string_thy = source
            .find("namespace AySoundness.StringThy")
            .expect("StringThy in the embedded base");
        let regex_thy = source
            .find("namespace AySoundness.RegexThy")
            .expect("RegexThy in the embedded base");
        let use_site = source
            .find("RegexThy.regex_len_mod_conflict (k := 6)")
            .expect("corollary application in the emitted body");
        assert!(string_thy < regex_thy);
        assert!(regex_thy < use_site);
        assert!(source.contains(AXIOM_AUDIT_SENTINEL));
        eprintln!("----STANDALONE-BEGIN----\n{source}\n----STANDALONE-END----");
    }

    /// The REAL-sorted ordered-field emitter writes
    /// `Firewall` then `OrdField`, so both must strip and the embedded
    /// `OrdField` source must land in the standalone file ahead of the body.
    #[test]
    fn standalone_source_embeds_ord_field_for_the_real_emitter() {
        let emitted = "import AySoundness.Firewall\n\
                       import AySoundness.OrdField\n\
                       namespace X\n\
                       theorem no_model (F : AySoundness.OrdField) : True := by trivial\n\
                       end X\n";
        let source = standalone_firewall_source(emitted).expect("standalone source");
        assert!(source.contains("structure OrdField where"));
        assert!(source.contains("theorem ordField_nonvacuous"));
        let ord_field = source
            .find("structure OrdField where")
            .expect("embedded OrdField");
        let body = source.find("namespace X").expect("emitted body");
        assert!(ord_field < body);
        // The embedded module must be import-free, or the concatenation breaks.
        assert!(!ORD_FIELD_SOURCE.contains("\nimport "));
        assert!(!ORD_FIELD_SOURCE.starts_with("import "));
    }

    #[test]
    fn standalone_source_rejects_unknown_import_or_missing_theorem() {
        assert!(standalone_firewall_source(
            "import Malicious\nnamespace X\ntheorem no_model : True := by trivial\nend X\n"
        )
        .is_err());
        assert!(standalone_firewall_source(
            "import AySoundness.Firewall\nnamespace X\ntheorem other : True := by trivial\nend X\n"
        )
        .is_err());
    }

    #[test]
    fn diagnostic_preflight_caps_emitter_inputs_before_allocation() {
        assert_eq!(
            check_diagnostic_preflight(
                MAX_DIAGNOSTIC_PROOF_STEPS,
                MAX_DIAGNOSTIC_EMITTER_ITEMS,
                MAX_DIAGNOSTIC_FILES - NON_STEP_ARTIFACT_UPPER_BOUND,
                MAX_DIAGNOSTIC_ASSERTIONS,
                MAX_DIAGNOSTIC_TERMS,
                MAX_DIAGNOSTIC_TERM_BYTES,
                MAX_DIAGNOSTIC_DATATYPES,
                MAX_DIAGNOSTIC_DATATYPE_CONSTRUCTORS,
                MAX_DIAGNOSTIC_DATATYPE_BYTES,
            ),
            Ok(())
        );
        assert_eq!(
            check_diagnostic_preflight(MAX_DIAGNOSTIC_PROOF_STEPS + 1, 0, 0, 0, 0, 0, 0, 0, 0),
            Err(DiagnosticPreflightLimit::ProofSteps)
        );
        assert_eq!(
            check_diagnostic_preflight(0, MAX_DIAGNOSTIC_EMITTER_ITEMS + 1, 0, 0, 0, 0, 0, 0, 0),
            Err(DiagnosticPreflightLimit::EmitterItems)
        );
        assert_eq!(
            check_diagnostic_preflight(0, 0, 0, MAX_DIAGNOSTIC_ASSERTIONS + 1, 0, 0, 0, 0, 0),
            Err(DiagnosticPreflightLimit::Assertions)
        );
        assert_eq!(
            check_diagnostic_preflight(0, 0, 0, 0, MAX_DIAGNOSTIC_TERMS + 1, 0, 0, 0, 0),
            Err(DiagnosticPreflightLimit::Terms)
        );
        assert_eq!(
            check_diagnostic_preflight(0, 0, 0, 0, 0, MAX_DIAGNOSTIC_TERM_BYTES + 1, 0, 0, 0),
            Err(DiagnosticPreflightLimit::TermBytes)
        );
        assert_eq!(
            check_diagnostic_preflight(0, 0, 0, 0, 0, 0, MAX_DIAGNOSTIC_DATATYPES + 1, 0, 0,),
            Err(DiagnosticPreflightLimit::DatatypeRegistry)
        );
        assert_eq!(
            check_diagnostic_preflight(
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                MAX_DIAGNOSTIC_DATATYPE_CONSTRUCTORS + 1,
                0,
            ),
            Err(DiagnosticPreflightLimit::DatatypeRegistry)
        );
        assert_eq!(
            check_diagnostic_preflight(0, 0, 0, 0, 0, 0, 0, 0, MAX_DIAGNOSTIC_DATATYPE_BYTES + 1,),
            Err(DiagnosticPreflightLimit::DatatypeRegistry)
        );
        assert_eq!(
            check_diagnostic_preflight(
                0,
                0,
                MAX_DIAGNOSTIC_FILES - NON_STEP_ARTIFACT_UPPER_BOUND + 1,
                0,
                0,
                0,
                0,
                0,
                0,
            ),
            Err(DiagnosticPreflightLimit::PotentialFiles)
        );
    }

    #[test]
    fn diagnostic_o1_preflight_rejects_before_scan_derived_work() {
        assert_eq!(
            check_diagnostic_o1_preflight(
                MAX_DIAGNOSTIC_PROOF_STEPS + 1,
                MAX_DIAGNOSTIC_ASSERTIONS + 1,
                MAX_DIAGNOSTIC_TERMS + 1,
                MAX_DIAGNOSTIC_TERM_BYTES + 1,
            ),
            Err(DiagnosticPreflightLimit::ProofSteps),
            "the already-known proof length must reject before any proof payload scan"
        );
        assert_eq!(
            check_diagnostic_o1_preflight(
                0,
                MAX_DIAGNOSTIC_ASSERTIONS + 1,
                MAX_DIAGNOSTIC_TERMS + 1,
                MAX_DIAGNOSTIC_TERM_BYTES + 1,
            ),
            Err(DiagnosticPreflightLimit::Assertions),
            "context counts must reject before datatype registry work"
        );
    }

    #[test]
    fn aggregate_standalone_source_cap_is_hard_and_overflow_safe() {
        assert_eq!(
            checked_diagnostic_source_total(0, MAX_DIAGNOSTIC_SOURCE_BYTES),
            Some(MAX_DIAGNOSTIC_SOURCE_BYTES)
        );
        assert_eq!(
            checked_diagnostic_source_total(MAX_DIAGNOSTIC_SOURCE_BYTES, 1),
            None
        );
        assert_eq!(checked_diagnostic_source_total(usize::MAX, 1), None);
    }

    #[test]
    fn diagnostic_child_memory_limit_never_exceeds_fixed_ceiling() {
        assert_eq!(MAX_DIAGNOSTIC_CHILD_MEMORY_BYTES, 4 * 1024 * 1024 * 1024);
        assert_eq!(
            diagnostic_child_memory_limit_from(0),
            MAX_DIAGNOSTIC_CHILD_MEMORY_BYTES
        );
        assert_eq!(
            diagnostic_child_memory_limit_from(64 * 1024 * 1024),
            64 * 1024 * 1024
        );
        assert_eq!(
            diagnostic_child_memory_limit_from(usize::MAX),
            MAX_DIAGNOSTIC_CHILD_MEMORY_BYTES
        );
    }

    #[test]
    fn kernel_accepted_diagnostics_cannot_certify_the_query() {
        let outcome = diagnostic_only_outcome(vec![LemmaCheck {
            index: 0,
            passed: true,
            detail: "kernel-checked; axiom audit passed".to_string(),
        }]);
        let FirewallDiagnosticOutcome { reason, results } = outcome;
        assert_eq!(reason, DIAGNOSTIC_ONLY_REASON);
        assert_eq!(results.len(), 1);
        assert!(results[0].passed);
    }

    #[test]
    fn axiom_audit_accepts_only_the_documented_kernel_axioms() {
        for report in [
            format!("'Example.no_model' does not depend on any axioms\n{AXIOM_AUDIT_SENTINEL}\n"),
            format!(
                "'Example.no_model' depends on axioms: [propext, Classical.choice, Quot.sound]\n\
                 {AXIOM_AUDIT_SENTINEL}\n"
            ),
        ] {
            axiom_audit_result(&report).expect("allowed axiom report");
        }

        let forbidden = format!(
            "'Example.no_model' depends on axioms: [propext, Bad.unsound]\n\
             {AXIOM_AUDIT_SENTINEL}\n"
        );
        assert!(axiom_audit_result(&forbidden)
            .expect_err("custom axiom must fail")
            .contains("Bad.unsound"));
        assert!(axiom_audit_result(AXIOM_AUDIT_SENTINEL).is_err());
        let duplicate = format!(
            "'Example.no_model' does not depend on any axioms\n{AXIOM_AUDIT_SENTINEL}\n{AXIOM_AUDIT_SENTINEL}\n"
        );
        assert!(axiom_audit_result(&duplicate).is_err());
        let unrelated =
            format!("'Example.other' does not depend on any axioms\n{AXIOM_AUDIT_SENTINEL}\n");
        assert!(axiom_audit_result(&unrelated).is_err());
    }

    #[test]
    fn firewall_temp_dir_is_unique_private_and_restricted_subseted_up() {
        let temp = FirewallTempDir::new().expect("temporary firewall directory");
        let path = temp.path().to_path_buf();
        std::fs::write(path.join("proof.lean"), "example : True := by trivial\n")
            .expect("write temporary proof");
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt as _;
            let mode = std::fs::metadata(&path)
                .expect("temporary directory metadata")
                .permissions()
                .mode();
            assert_eq!(mode & 0o777, 0o700);
        }
        drop(temp);
        assert!(!path.exists());
    }

    #[cfg(unix)]
    #[test]
    fn wait_with_timeout_drains_large_output_and_keeps_middle_rejection_signal() {
        if !UNREAPED_CHILD_WAIT_AVAILABLE {
            return;
        }
        let mut command = Command::new("sh");
        command
            .arg("-c")
            .arg(
                "dd if=/dev/zero bs=1048576 count=1 2>/dev/null; \
                 printf 'error: middle marker\\n'; \
                 dd if=/dev/zero bs=1048576 count=1 2>/dev/null",
            )
            .stdout(Stdio::piped())
            .stderr(Stdio::piped());
        isolate_process_group(&mut command);
        let child = command.spawn().expect("spawn verbose child");
        let started = Instant::now();
        let WaitOutcome::Exited {
            code,
            stdout,
            rejection_seen,
            ..
        } = wait_with_timeout(child, Duration::from_secs(5))
        else {
            panic!("verbose child should exit normally");
        };
        assert_eq!(code, 0);
        assert!(rejection_seen);
        assert!(!stdout.contains("error: middle marker"));
        assert!(started.elapsed() < Duration::from_secs(5));
        assert!(stdout.len() <= CAPTURE_HEAD_BYTES + CAPTURE_TAIL_BYTES + 64);
    }

    #[cfg(unix)]
    #[test]
    fn wait_with_timeout_terminates_stuck_checker() {
        if !UNREAPED_CHILD_WAIT_AVAILABLE {
            return;
        }
        let mut command = Command::new("sh");
        command
            .arg("-c")
            .arg("sleep 30")
            .stdout(Stdio::piped())
            .stderr(Stdio::piped());
        isolate_process_group(&mut command);
        let child = command.spawn().expect("spawn stuck child");
        let started = Instant::now();
        assert!(matches!(
            wait_with_timeout(child, Duration::from_millis(50)),
            WaitOutcome::TimedOut
        ));
        assert!(started.elapsed() < Duration::from_secs(2));
    }

    #[cfg(unix)]
    #[test]
    fn wait_with_timeout_kills_descendants_before_reaping_exited_group_leader() {
        if !UNREAPED_CHILD_WAIT_AVAILABLE {
            return;
        }
        let mut command = Command::new("sh");
        command
            .arg("-c")
            // The background process inherits both capture pipes. Merely
            // reaping the shell would leave capture blocked for 30 seconds.
            .arg("sleep 30 & exit 0")
            .stdout(Stdio::piped())
            .stderr(Stdio::piped());
        isolate_process_group(&mut command);
        let child = command.spawn().expect("spawn wrapper with descendant");
        let started = Instant::now();
        let WaitOutcome::Exited { code, .. } = wait_with_timeout(child, Duration::from_secs(5))
        else {
            panic!("exited wrapper and its descendants must be contained");
        };
        assert_eq!(code, 0, "cleanup must preserve the wrapper's true status");
        assert!(started.elapsed() < Duration::from_secs(2));
    }
}
