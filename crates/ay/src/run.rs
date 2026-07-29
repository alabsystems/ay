// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Execution mode implementations for the AY CLI.
//!
//! Contains the interactive (stdin), piped, and file-based execution
//! paths. Extracted from `main.rs` to keep each file under 500 lines.

use std::cell::RefCell;
use std::collections::HashMap;
use std::io::{self, BufRead, BufWriter, Read, Write};

use ay_core::{escape_string_contents, quote_symbol};
use ay_dpll::{Executor, UnknownReason};
use ay_frontend::{
    parse, sexp::parse_sexp, Command, CommandStream, CommandStreamItem, Constant, FormulaStats,
    Index, IntroKind, QualifiedIdentifier, SExpr, Sort, Term,
};
use sha2::{Digest as _, Sha256};

use super::firewall_verify;
use super::{
    chc_runner, dimacs, eprintln_smt_error, exit_if_timed_out, explain, explain_reason,
    is_timed_out,
    proof_artifact::{
        write_sealed_proof_artifact, DigestBytes, ProofArtifactProblem, ProofArtifactTheoryMetadata,
    },
    stats_output, ProofConfig, ProofFormat, EXPLAIN_ENABLED, EXPLAIN_FORMAT_JSON,
    EXPLICIT_VERIFY_PROOF_ENABLED, GLOBAL_TIMEOUT_MS, INTERRUPT_HANDLE, MINIMIZE_MODEL_ENABLED,
    PROGRESS_ENABLED, PROGRESS_JSON_PATH, SELF_CHECK_ENABLED, START_TIME, STRICT_PROOFS_ENABLED,
    VERIFY_FIREWALL_ENABLED, VERIFY_PROOF_ENABLED, Z3_MODEL_ENABLED, Z3_MODE_ENABLED,
};
use ay::solution_visualization::{render_solution_visualization, VisualizationFormat};

const SMT_FILE_THREAD_STACK_SIZE: usize = 64 * 1024 * 1024;

/// Adapt a proof config for the SMT-LIB execution path.
///
/// When default proof auto-verification synthesizes a temporary DRAT path, the
/// choice happens before the input format is known. SMT-LIB produces Alethe,
/// which AY cannot post-check with its DRAT/LRAT verifier. Such verify-only temp
/// configs are therefore dropped instead of enabling costly proof tracking,
/// writing Alethe, and deleting it without verification. An explicit
/// `--verify-proof` is rejected by the route gate before this adapter runs.
///
/// Returns `None` when `proof_config` is `None` or verify-only temporary.
/// Persistent default and explicit proof configs are returned unchanged; the
/// caller validates that their format is Alethe.
fn adapt_proof_config_for_smt(proof_config: Option<&ProofConfig>) -> Option<ProofConfig> {
    let src = proof_config?;
    if src.is_temp {
        return None;
    }
    Some(src.clone())
}

fn logic_from_commands(commands: &[Command]) -> Option<&str> {
    commands.iter().find_map(|command| {
        if let Command::SetLogic(logic) = command {
            Some(logic.as_str())
        } else {
            None
        }
    })
}

/// Remove a synthesized temp proof file after the SMT run completes.
/// No-op when the config is `None`, not marked `is_temp`, or the file is
/// already absent. Used to avoid leaving stray `/tmp/ay-verify-*.alethe`
/// files when `--verify-proof` auto-defaults on under debug builds with
/// no user-supplied `--proof` path (Finding A).
fn cleanup_temp_proof(proof_config: Option<&ProofConfig>) {
    if let Some(proof) = proof_config {
        if proof.is_temp {
            let _ = std::fs::remove_file(&proof.path);
        }
    }
}

/// Create an executor with global timeout interrupt wired in (#2971).
fn new_executor() -> Executor {
    let mut executor = Executor::new();
    if let Some(handle) = INTERRUPT_HANDLE.get() {
        executor.set_interrupt(handle.clone());
    }
    // #8749: Install a wall-clock deadline matching `--timeout` so theory
    // solvers that poll deadlines (IntSat probe, LIA cascade, LRA split loop,
    // …) bail out at the boundary instead of waiting for the watchdog's
    // two-second hard-exit grace period. The watchdog remains the ultimate
    // safety net — this deadline only accelerates cooperative shutdown.
    let ms = GLOBAL_TIMEOUT_MS.load(std::sync::atomic::Ordering::SeqCst);
    if ms > 0 {
        if let Some(start) = START_TIME.get() {
            // An adversarially large CLI timeout can exceed the monotonic
            // clock's representable range. The watchdog still owns the hard
            // timeout; omit only this cooperative deadline instead of
            // panicking before the solve starts.
            if let Some(deadline) = start.checked_add(std::time::Duration::from_millis(ms)) {
                executor.set_deadline(Some(deadline));
            }
        }
    }
    // Wire progress flag so SAT solvers inside the SMT pipeline emit
    // periodic status lines when --progress is set.
    if PROGRESS_ENABLED.load(std::sync::atomic::Ordering::Relaxed) {
        executor.set_progress_enabled(true);
    }
    // Wire JSONL progress file path (#8155 subtask 7b).
    if let Some(path) = PROGRESS_JSON_PATH.get() {
        executor.set_progress_json(Some(path.clone()));
    }
    // Wire aggressive model minimization (#8297).
    if MINIMIZE_MODEL_ENABLED.load(std::sync::atomic::Ordering::Relaxed) {
        executor.set_aggressive_model_minimize(true);
    }
    // Strict-proof mode forces internal Alethe proof generation regardless of
    // `--proof` so that the terminal-trust check has a proof to inspect (#8759).
    if strict_proofs_enabled() {
        executor.set_produce_proofs(true);
    }
    // Fail-closed self-check: AY must certify its own answers (model evaluation
    // for SAT, refutation proof for UNSAT) or degrade to a sound `unknown`.
    if self_check_enabled() {
        executor.set_self_check(true);
        // A refutation proof is required to certify UNSAT, so force proof
        // production on even without `--proof`.
        executor.set_produce_proofs(true);
    }
    // The firewall diagnostics are reconstructed from the refutation proof, so
    // proof production must be on even without `--proof`.
    if verify_firewall_enabled() {
        executor.set_produce_proofs(true);
    }
    executor
}

/// Deterministic RUP-replay step budget for the SYNTHESIZED-DEFAULT Alethe
/// certificate (#A2b). SMT-LIB only requires proofs on `:produce-proofs` /
/// `(get-proof)`; the by-default `<input>.alethe` is an ay extra, so it must
/// never trade a fast UNSAT verdict for minutes of proof materialization
/// (QF_UF PEQ: 1s unsat became a 30s-timeout `unknown`). On budget
/// exhaustion the run keeps its verdict and prints the existing
/// "c warning: no proof certificate emitted" degrade. Step count, not wall
/// time, so verdict/artifact behavior is deterministic. Explicit `--proof`,
/// `--strict-proofs`, `--self-check`, `--emit-firewall-lean`, and
/// `:produce-proofs` scripts are never budgeted.
const DEFAULT_PROOF_RECONSTRUCTION_STEP_BUDGET: u64 = 1_000_000;

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
struct ResultGateRequests {
    strict_proofs: bool,
    self_check: bool,
    verify_firewall: bool,
    emit_firewall_lean: bool,
    explicit_verify_proof: bool,
}

impl ResultGateRequests {
    fn current() -> Self {
        Self {
            strict_proofs: strict_proofs_enabled(),
            self_check: self_check_enabled(),
            verify_firewall: verify_firewall_enabled(),
            emit_firewall_lean: crate::FIREWALL_LEAN_DIR.get().is_some(),
            explicit_verify_proof: EXPLICIT_VERIFY_PROOF_ENABLED
                .load(std::sync::atomic::Ordering::SeqCst),
        }
    }

    fn any(self) -> bool {
        self.strict_proofs
            || self.self_check
            || self.verify_firewall
            || self.emit_firewall_lean
            || self.explicit_verify_proof
    }
}

fn should_budget_synthesized_proof(synthesized_default: bool, gates: ResultGateRequests) -> bool {
    synthesized_default && !gates.any()
}

fn may_use_ungated_solver_route(gates: ResultGateRequests) -> bool {
    !gates.any()
}

fn required_smt_unsat_publication(proof: Option<&ProofConfig>) -> bool {
    proof.is_some_and(|proof| {
        !proof.synthesized_default
            || proof.artifact_path.is_some()
            || strict_proofs_enabled()
            || crate::FIREWALL_LEAN_DIR.get().is_some()
    })
}

fn unsupported_explicit_proof_verification_error(
    explicit: bool,
    route: &str,
    certificate_kind: &str,
) -> Option<String> {
    explicit.then(|| {
        format!(
            "--verify-proof cannot verify {route} {certificate_kind} certificates; the built-in post-checker supports DIMACS DRAT/LRAT only"
        )
    })
}

pub(super) fn reject_explicit_proof_verification_for_route(route: &str, certificate_kind: &str) {
    let explicit = EXPLICIT_VERIFY_PROOF_ENABLED.load(std::sync::atomic::Ordering::SeqCst);
    if let Some(error) =
        unsupported_explicit_proof_verification_error(explicit, route, certificate_kind)
    {
        safe_eprintln!("Error: {error}");
        std::process::exit(1);
    }
}

fn unsupported_firewall_verification_error(enabled: bool, route: &str) -> Option<String> {
    enabled.then(|| {
        format!(
            "--verify-firewall supports only the SMT-LIB DPLL(T) route; it cannot run firewall diagnostics for {route} results"
        )
    })
}

pub(super) fn reject_firewall_verification_for_route(route: &str) {
    if let Some(error) = unsupported_firewall_verification_error(verify_firewall_enabled(), route) {
        safe_eprintln!("Error: {error}");
        std::process::exit(1);
    }
}

fn unsupported_firewall_emission_error(enabled: bool, route: &str) -> Option<String> {
    enabled.then(|| {
        format!(
            "--emit-firewall-lean supports only the SMT-LIB DPLL(T) route; it cannot emit firewall diagnostics for {route} results"
        )
    })
}

pub(super) fn reject_firewall_emission_for_route(route: &str) {
    if let Some(error) =
        unsupported_firewall_emission_error(crate::FIREWALL_LEAN_DIR.get().is_some(), route)
    {
        safe_eprintln!("Error: {error}");
        std::process::exit(1);
    }
}

/// Reject routes whose solver cannot produce the single-result SAT decision
/// trace format. The reservation is descriptor-invalidated before the route
/// can publish a verdict; pathname replacement is never unlinked.
fn reject_decision_trace_for_route(route: &str) {
    if ay_core::trace_config().decision_trace_path.is_none() {
        return;
    }
    if let Err(error) = invalidate_non_authoritative_decision_trace(&format!(
        "{route} does not use the SMT-LIB/DIMACS single-query decision-trace protocol"
    )) {
        safe_eprintln!("Error: {error}");
    }
    safe_eprintln!(
        "Error: --decision-trace is incompatible with {route}; decision traces support one SMT-LIB or DIMACS decision query"
    );
    std::process::exit(1);
}

/// Apply the best-effort reconstruction budget for a synthesized-default
/// proof config (never for an explicit proof or mandatory result gate).
fn apply_default_proof_budget(executor: &mut Executor, proof: &ProofConfig) {
    // Every mandatory result gate needs the complete proof reconstruction it
    // requested. In particular, `--verify-firewall` synthesizes its proof
    // config by default; treating that config as best-effort could stop proof
    // reconstruction before the requested diagnostics run.
    if should_budget_synthesized_proof(proof.synthesized_default, ResultGateRequests::current()) {
        executor
            .set_proof_reconstruction_step_budget(Some(DEFAULT_PROOF_RECONSTRUCTION_STEP_BUDGET));
    }
}

/// `true` when `--self-check` was set.
fn self_check_enabled() -> bool {
    SELF_CHECK_ENABLED.load(std::sync::atomic::Ordering::Relaxed)
}

/// `true` when `--strict-proofs` was set.
fn strict_proofs_enabled() -> bool {
    STRICT_PROOFS_ENABLED.load(std::sync::atomic::Ordering::Relaxed)
}

/// `true` when `--verify-firewall` was set.
fn verify_firewall_enabled() -> bool {
    VERIFY_FIREWALL_ENABLED.load(std::sync::atomic::Ordering::Relaxed)
}

/// Whether the assertion set seen by `check-sat` is the COMPLETE problem.
///
/// A command that contributes to the problem (an `assert`, a declaration, a
/// definition, a stack op, ...) but fails to parse or elaborate is reported as a
/// recoverable `(error ...)` and then DROPPED. Dropping a constraint can only
/// turn UNSAT into SAT, so once any such command is discarded the solver must
/// fail closed: a subsequent `check-sat` answers `unknown`, never a definitive
/// sat/unsat on the incomplete remainder. (#match-soundness, Part 1.)
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
enum ProblemCompleteness {
    /// Every problem-contributing command so far was processed in full.
    #[default]
    Complete,
    /// At least one problem-contributing command was discarded.
    Incomplete,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum PublicVerdict {
    Sat,
    Unsat,
    Unknown,
}

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
enum DecisionTracePublication {
    #[default]
    Pending,
    Settled(PublicVerdict),
    Invalidated,
}

#[derive(Default)]
enum SmtUnsatPublicationState {
    #[default]
    Unprepared,
    ReadyWithoutArtifacts,
    Prepared(Box<SmtUnsatPublicationTransaction>),
    Committed,
    Rejected,
}

#[derive(Clone, Debug)]
struct ScopedSymbolSort {
    sort: String,
    /// `None` denotes a declaration made while `:global-decls` was enabled.
    /// Otherwise the binding expires when the assertion stack is popped below
    /// this depth.
    scope_depth: Option<u32>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct SmtFileIdentity {
    #[cfg(unix)]
    device: u64,
    #[cfg(unix)]
    inode: u64,
    #[cfg(windows)]
    volume: Option<u32>,
    #[cfg(windows)]
    index: Option<u64>,
}

impl SmtFileIdentity {
    fn from_metadata(metadata: &std::fs::Metadata) -> Option<Self> {
        #[cfg(unix)]
        {
            use std::os::unix::fs::MetadataExt as _;
            Some(Self {
                device: metadata.dev(),
                inode: metadata.ino(),
            })
        }
        #[cfg(windows)]
        {
            use std::os::windows::fs::MetadataExt as _;
            Some(Self {
                volume: metadata.volume_serial_number(),
                index: metadata.file_index(),
            })
        }
        #[cfg(not(any(unix, windows)))]
        {
            let _ = metadata;
            None
        }
    }
}

#[derive(Clone, Debug)]
struct SmtProtectedPath {
    path: std::path::PathBuf,
    identity: Option<SmtFileIdentity>,
}

#[derive(Clone, Debug)]
struct SmtFileSource {
    path: std::path::PathBuf,
    identity: Option<SmtFileIdentity>,
}

impl SmtFileSource {
    fn from_open_file(path: &std::path::Path, file: &std::fs::File) -> io::Result<Self> {
        Ok(Self {
            // Preserve the physical parent selected for this invocation even if
            // an ancestor symlink is retargeted after the input descriptor opens.
            path: resolve_artifact_target(path)?,
            identity: SmtFileIdentity::from_metadata(&file.metadata()?),
        })
    }
}

#[derive(Default)]
struct SmtTranscriptState {
    print_success: bool,
    interactive_mode: bool,
    produce_assignments: bool,
    produce_proofs: bool,
    produce_unsat_assumptions: bool,
    global_decls: bool,
    auto_config: bool,
    model_v2: bool,
    model_compact: bool,
    pp_decimal: bool,
    pp_decimal_precision: String,
    pp_max_depth: String,
    pp_max_ribbon: String,
    pp_single_line: bool,
    pp_bv_literals: bool,
    regular_output_channel: String,
    diagnostic_output_channel: String,
    /// File-backed channels are opened once through an exclusive temporary
    /// inode and atomically published. Keeping the owned handles prevents later
    /// path replacement from redirecting transcript writes to a symlink,
    /// hardlink, FIFO, or device.
    regular_output_file: RefCell<Option<std::fs::File>>,
    diagnostic_output_file: RefCell<Option<std::fs::File>>,
    protected_paths: Vec<SmtProtectedPath>,
    protected_output_directories: Vec<std::path::PathBuf>,
    verbosity: String,
    rlimit_option: String,
    z3_compat_bool_options: HashMap<String, bool>,
    status: Option<String>,
    rlimit: u64,
    assertion_stack_depth: u32,
    executor_assertion_stack_depth: u32,
    /// Inferred sort for an unqualified nullary symbol. `None` means more than
    /// one active nullary overload has the same surface name, so using a sort
    /// here would be unsound.
    symbol_sorts: HashMap<String, Option<String>>,
    symbol_sort_bindings: HashMap<String, Vec<ScopedSymbolSort>>,
    current_source: Option<CommandSource>,
    current_command_ordinal: usize,
    processed_commands: usize,
    /// Decision traces contain exactly one terminal result. Track queries at
    /// the CLI boundary so a second `check-sat` is rejected before another
    /// solver can append an incompatible epoch to the same artifact.
    decision_queries_seen: usize,
    had_recoverable_error: bool,
    recoverable_error_count: usize,
    completeness: ProblemCompleteness,
    /// Verdict exposed at the CLI boundary. This intentionally remains
    /// separate from `Executor`'s raw result: mandatory result gates can reject
    /// an internal UNSAT and publish `unknown` instead.
    public_verdict: Option<PublicVerdict>,
    public_unknown_reason: Option<String>,
    /// Whether the current public verdict came directly from the executor.
    /// Synthesized fail-closed outcomes must not reuse raw solver artifacts.
    public_verdict_from_executor: bool,
    /// Publication state for the invocation-owned decision trace. A settled
    /// trace has already been authenticated against the public verdict before
    /// that verdict reached the regular output channel; an invalidated trace
    /// must never authorize a later verdict.
    decision_trace_publication: DecisionTracePublication,
    result_certification_rejected: bool,
    /// A required persistent proof/firewall transaction must commit before an
    /// executor-produced UNSAT becomes observable on the regular channel.
    defer_unsat_publication: bool,
    pending_unsat_output: Option<String>,
    /// Retained proof/artifact authority for a deferred UNSAT. The prepared
    /// transaction remains armed until the decision trace settles and every
    /// participant is revalidated immediately before the verdict is emitted.
    smt_unsat_publication: SmtUnsatPublicationState,
}

#[derive(Clone, Debug)]
struct CommandSource {
    line: usize,
    column: usize,
    text: String,
}

#[derive(Clone, Copy, Debug)]
struct SourcePosition {
    line: usize,
    column: usize,
}

impl SmtTranscriptState {
    fn new() -> Self {
        Self {
            print_success: false,
            interactive_mode: false,
            produce_assignments: false,
            produce_proofs: false,
            produce_unsat_assumptions: false,
            global_decls: false,
            auto_config: true,
            model_v2: false,
            model_compact: true,
            pp_decimal: false,
            pp_decimal_precision: "10".to_string(),
            pp_max_depth: "5".to_string(),
            pp_max_ribbon: "80".to_string(),
            pp_single_line: false,
            pp_bv_literals: true,
            regular_output_channel: "stdout".to_string(),
            diagnostic_output_channel: "stderr".to_string(),
            regular_output_file: RefCell::new(None),
            diagnostic_output_file: RefCell::new(None),
            protected_paths: Vec::new(),
            protected_output_directories: Vec::new(),
            verbosity: "0".to_string(),
            rlimit_option: "0".to_string(),
            z3_compat_bool_options: z3_compat_bool_option_defaults(),
            status: Some("unknown".to_string()),
            rlimit: 1,
            assertion_stack_depth: 0,
            executor_assertion_stack_depth: 0,
            symbol_sorts: HashMap::new(),
            symbol_sort_bindings: HashMap::new(),
            current_source: None,
            current_command_ordinal: 0,
            processed_commands: 0,
            decision_queries_seen: 0,
            had_recoverable_error: false,
            recoverable_error_count: 0,
            completeness: ProblemCompleteness::Complete,
            public_verdict: None,
            public_unknown_reason: None,
            public_verdict_from_executor: false,
            decision_trace_publication: DecisionTracePublication::Pending,
            result_certification_rejected: false,
            defer_unsat_publication: false,
            pending_unsat_output: None,
            smt_unsat_publication: SmtUnsatPublicationState::Unprepared,
        }
    }

    fn note_recoverable_error(&mut self) {
        self.had_recoverable_error = true;
        self.recoverable_error_count = self.recoverable_error_count.saturating_add(1);
    }

    /// Mark the problem as incomplete: a problem-contributing command was
    /// dropped, so a later `check-sat` must answer `unknown` (fail closed).
    fn mark_incomplete(&mut self) {
        self.completeness = ProblemCompleteness::Incomplete;
        // A dropped semantic mutation also revokes any result from an earlier
        // check immediately. EOF consumers must never publish that stale
        // proof/model merely because no later check-sat was issued.
        self.clear_public_result();
    }

    fn is_incomplete(&self) -> bool {
        self.completeness == ProblemCompleteness::Incomplete
    }

    fn clear_public_result(&mut self) {
        self.public_verdict = None;
        self.public_unknown_reason = None;
        self.public_verdict_from_executor = false;
        self.result_certification_rejected = false;
        self.pending_unsat_output = None;
        self.smt_unsat_publication = SmtUnsatPublicationState::Unprepared;
    }

    fn record_public_verdict(&mut self, verdict: PublicVerdict) {
        self.public_verdict = Some(verdict);
        self.public_unknown_reason = None;
        self.public_verdict_from_executor = true;
        self.result_certification_rejected = false;
        self.pending_unsat_output = None;
        self.smt_unsat_publication = SmtUnsatPublicationState::Unprepared;
    }

    fn record_executor_unknown(&mut self, reason: Option<String>) {
        self.public_verdict = Some(PublicVerdict::Unknown);
        self.public_unknown_reason = reason;
        self.public_verdict_from_executor = true;
        self.result_certification_rejected = false;
        self.pending_unsat_output = None;
        self.smt_unsat_publication = SmtUnsatPublicationState::Unprepared;
    }

    fn record_synthesized_unknown(&mut self, reason: impl Into<String>) {
        self.public_verdict = Some(PublicVerdict::Unknown);
        self.public_unknown_reason = Some(reason.into());
        self.public_verdict_from_executor = false;
        self.result_certification_rejected = false;
        self.pending_unsat_output = None;
        self.smt_unsat_publication = SmtUnsatPublicationState::Unprepared;
    }

    fn reject_result_certification(&mut self, reason: impl Into<String>) {
        self.record_synthesized_unknown(reason);
        self.result_certification_rejected = true;
    }

    fn public_unsat_artifacts_allowed(&self) -> bool {
        self.public_verdict == Some(PublicVerdict::Unsat)
            && self.public_verdict_from_executor
            && !self.result_certification_rejected
            && !self.had_recoverable_error
            && !self.is_incomplete()
    }

    fn protect_path(&mut self, path: &std::path::Path) -> io::Result<()> {
        let resolved = resolve_artifact_target(path)?;
        let identity = std::fs::metadata(path)
            .ok()
            .and_then(|metadata| SmtFileIdentity::from_metadata(&metadata));
        self.protect_resolved_path(resolved, identity);
        Ok(())
    }

    fn protect_file_source(&mut self, source: &SmtFileSource) {
        self.protect_resolved_path(source.path.clone(), source.identity);
    }

    fn protect_resolved_path(
        &mut self,
        path: std::path::PathBuf,
        identity: Option<SmtFileIdentity>,
    ) {
        if !self
            .protected_paths
            .iter()
            .any(|protected| protected.path == path && protected.identity == identity)
        {
            self.protected_paths
                .push(SmtProtectedPath { path, identity });
        }
    }

    fn protect_output_directory(&mut self, path: &std::path::Path) -> io::Result<()> {
        let path = super::comparable_output_path(path)?;
        if !self.protected_output_directories.contains(&path) {
            self.protected_output_directories.push(path);
        }
        Ok(())
    }

    fn output_channel_conflicts(&self, channel: &str, other_channel: &str) -> bool {
        if matches!(channel, "stdout" | "stderr") {
            return false;
        }
        let channel_path = std::path::Path::new(channel);
        let Ok(resolved) = resolve_artifact_target(channel_path) else {
            return false;
        };
        let identity = std::fs::metadata(channel_path)
            .ok()
            .and_then(|metadata| SmtFileIdentity::from_metadata(&metadata));
        for protected in &self.protected_paths {
            if identity.is_some() && identity == protected.identity {
                return true;
            }
            match super::certificate_paths_may_alias(&resolved, &protected.path) {
                Ok(true) | Err(_) => return true,
                Ok(false) => {}
            }
        }
        for directory in &self.protected_output_directories {
            match (
                super::certificate_path_is_within(&resolved, directory),
                super::certificate_path_is_within(directory, &resolved),
            ) {
                (Ok(false), Ok(false)) => {}
                _ => return true,
            }
        }
        if matches!(other_channel, "stdout" | "stderr") {
            return false;
        }
        let Ok(other) = resolve_artifact_target(std::path::Path::new(other_channel)) else {
            return true;
        };
        super::certificate_paths_may_alias(&resolved, &other).unwrap_or(true)
    }
}

fn seed_smt_transcript_protections(
    transcript: &mut SmtTranscriptState,
    source: Option<&SmtFileSource>,
    proof: Option<&ProofConfig>,
) -> io::Result<()> {
    if let Some(source) = source {
        transcript.protect_file_source(source);
    }
    if let Some(proof) = proof {
        transcript.protect_path(std::path::Path::new(&proof.path))?;
        if proof.synthesized_default && proof.format == ProofFormat::Drat {
            let status_path = dimacs::dimacs_proof_status_path(&proof.path);
            let status_lock_path = dimacs::dimacs_proof_status_lock_path(&status_path);
            transcript.protect_path(&status_path)?;
            transcript.protect_path(&status_lock_path)?;
        }
        if let Some(path) = proof.artifact_path.as_deref() {
            transcript.protect_path(std::path::Path::new(path))?;
        }
    }

    if let Some(path) = PROGRESS_JSON_PATH.get() {
        transcript.protect_path(std::path::Path::new(path))?;
    }
    if let Some(path) = super::LEAN_BINARY_PATH.get() {
        transcript.protect_path(path)?;
    }

    let trace = ay_core::trace_config();
    for path in [
        trace.diagnostic_path.as_deref(),
        trace.decision_trace_path.as_deref(),
        trace.replay_trace_path.as_deref(),
        trace.trace_file_path.as_deref(),
        trace.solution_file_path.as_deref(),
        trace.decision_log_path.as_deref(),
        trace.dump_bv_cnf_path.as_deref(),
        trace.bv_drat_path.as_deref(),
        trace.dump_encoding_path.as_deref(),
    ]
    .into_iter()
    .flatten()
    {
        transcript.protect_path(std::path::Path::new(path))?;
    }
    if let Some(path) = trace.kind_dump_dir.as_deref() {
        transcript.protect_output_directory(std::path::Path::new(path))?;
    }

    let misc = ay_core::misc_cli_flags();
    for path in [
        misc.dpll_diagnostic_file.as_deref(),
        misc.dpll_trace_file.as_deref(),
    ]
    .into_iter()
    .flatten()
    {
        transcript.protect_path(std::path::Path::new(path))?;
    }
    if misc.dpll_diagnostic_enabled {
        transcript.protect_path(
            &std::env::temp_dir().join(format!("ay_dpll_diagnostic_{}.jsonl", std::process::id())),
        )?;
    }

    if let Some(path) = crate::FIREWALL_LEAN_DIR.get() {
        transcript.protect_output_directory(path)?;
    }
    Ok(())
}

fn seed_smt_transcript_protections_or_exit(
    transcript: &mut SmtTranscriptState,
    source: Option<&SmtFileSource>,
    proof: Option<&ProofConfig>,
) {
    if let Err(error) = seed_smt_transcript_protections(transcript, source, proof) {
        safe_eprintln!("Error: cannot protect SMT-LIB input/artifact paths: {error}");
        std::process::exit(1);
    }
}

/// True when a top-level command that just FAILED TO PARSE (and was therefore
/// dropped) contributes to the satisfiability problem, so the session must be
/// tainted to `unknown`. `consumed` is the exact source slice the command stream
/// read for the failed item — for a cleanly-parsed-but-invalid command (e.g. an
/// `assert` whose body uses an unsupported construct) this is precisely that
/// command's text, so its leading keyword is a reliable signal. A malformed
/// S-expression (e.g. a stray `)`) does not start with `(<keyword>` and is left
/// untainted, preserving z3-style continued-execution for such structural slips.
fn parse_drop_contributes_to_problem(consumed: &str) -> bool {
    source_has_command_keyword(consumed, command_keyword_contributes_to_problem)
}

fn invalidate_export_after_malformed_decision(source: &str) {
    if ay_core::trace_config().dump_bv_cnf_path.is_none()
        || !source_has_command_keyword(source, |keyword| {
            matches!(keyword, "check-sat" | "check-sat-assuming")
        })
    {
        return;
    }
    if let Err(error) = Executor::invalidate_bv_cnf_export_for_rejected_check() {
        eprintln_smt_error(error.to_string());
    }
}

/// Extract the leading command keyword from a top-level command's raw source
/// text (a balanced `(...)` chunk). Returns the symbol immediately after the
/// opening paren, or `None` when the text is not a simple `(<keyword> ...)`.
fn skip_smt_trivia(mut source: &str) -> &str {
    loop {
        source = source.trim_start_matches(char::is_whitespace);
        let Some(comment) = source.strip_prefix(';') else {
            return source;
        };
        source = comment
            .find('\n')
            .map_or("", |newline| &comment[newline + 1..]);
    }
}

fn command_source_keyword(text: &str) -> Option<&str> {
    let body = skip_smt_trivia(text).strip_prefix('(')?;
    let body = skip_smt_trivia(body);
    let end = body
        .find(|c: char| c.is_whitespace() || c == '(' || c == ')')
        .unwrap_or(body.len());
    let keyword = &body[..end];
    (!keyword.is_empty()).then_some(keyword)
}

/// Inspect every list head in a possibly malformed command buffer. Looking at
/// nested heads as well is intentionally conservative: an earlier missing `)`
/// must not hide a later problem command by making it appear nested.
/// This scanner is deliberately smaller than the parser but honors the lexical
/// regions that can contain inert parentheses/semicolons: line comments,
/// doubled-quote strings, and `|quoted symbols|`. It therefore cannot miss a
/// later semantic command merely because an earlier harmless command caused
/// whole-buffer parsing to fail.
fn source_has_command_keyword(text: &str, predicate: impl Fn(&str) -> bool) -> bool {
    let bytes = text.as_bytes();
    let mut index = 0usize;
    let mut in_comment = false;
    let mut in_string = false;
    let mut in_quoted_symbol = false;

    while index < bytes.len() {
        let byte = bytes[index];
        if in_comment {
            if byte == b'\n' {
                in_comment = false;
            }
            index += 1;
            continue;
        }
        if in_string {
            if byte == b'"' {
                if bytes.get(index + 1) == Some(&b'"') {
                    index += 2;
                    continue;
                }
                in_string = false;
            }
            index += 1;
            continue;
        }
        if in_quoted_symbol {
            if byte == b'|' {
                in_quoted_symbol = false;
            }
            index += 1;
            continue;
        }

        match byte {
            b';' => in_comment = true,
            b'"' => in_string = true,
            b'|' => in_quoted_symbol = true,
            b'(' => {
                if command_source_keyword(&text[index..]).is_some_and(&predicate) {
                    return true;
                }
            }
            _ => {}
        }
        index += 1;
    }
    false
}

/// Command keywords whose failure to parse changes the satisfiability of the
/// problem: anything that asserts a constraint, declares/defines a symbol or
/// sort, or manipulates the assertion stack. Pure queries and options
/// (`get-*`, `set-*`, `echo`, ...) are deliberately excluded — discarding one
/// cannot flip a sat/unsat verdict, so the solver stays answerable (matching
/// z3's continued-execution).
fn command_keyword_contributes_to_problem(keyword: &str) -> bool {
    matches!(
        keyword,
        "assert"
            | "assert-soft"
            | "minimize"
            | "maximize"
            | "declare-const"
            | "declare-fun"
            | "declare-sort"
            | "define-sort"
            | "declare-datatype"
            | "declare-datatypes"
            | "define-fun"
            | "define-fun-rec"
            | "define-funs-rec"
            | "declare-rel"
            | "declare-var"
            | "rule"
            | "query"
            | "push"
            | "pop"
            | "reset"
            | "reset-assertions"
            | "set-logic"
            | "synth-fun"
            | "synth-inv"
            | "constraint"
            | "inv-constraint"
            // z3's `(include "file")` extension splices the file's commands
            // inline. AY does not implement it, so it fails to parse ("Unknown
            // command: include") and is DROPPED — silently discarding every
            // assertion/declaration the included file contributes. Treating it
            // as problem-contributing taints the session so a later check-sat
            // fails closed to `unknown` instead of answering `sat` on the
            // (constraint-stripped) remainder — a confirmed wrong-`sat` class
            // when the included file is unsatisfiable. (burndown item #3)
            | "include"
    )
}

/// Parsed-command analogue of [`command_keyword_contributes_to_problem`]: true
/// when discarding `cmd` after an ELABORATION failure could change a sat/unsat
/// verdict, so the session must be tainted to `unknown`.
fn command_mutates_problem(cmd: &Command) -> bool {
    matches!(
        cmd,
        Command::SetLogic(_)
            | Command::Assert(_)
            | Command::AssertSoft { .. }
            | Command::Maximize(_)
            | Command::Minimize(_)
            | Command::DeclareConst(..)
            | Command::DeclareFun(..)
            | Command::DeclareSort(..)
            | Command::DefineSort(..)
            | Command::DeclareDatatype(..)
            | Command::DeclareDatatypes(..)
            | Command::DefineFun(..)
            | Command::DefineFunRec(..)
            | Command::DefineFunsRec(..)
            | Command::DeclareRel(..)
            | Command::DeclareVar(..)
            | Command::Rule(..)
            | Command::Query(..)
            | Command::SynthFun(..)
            | Command::SynthInv(..)
            | Command::SygusConstraint(..)
            | Command::InvConstraint(..)
            | Command::Push(_)
            | Command::Pop(_)
            | Command::Reset
            | Command::ResetAssertions
    )
}

fn command_contributes_to_problem(cmd: &Command) -> bool {
    command_mutates_problem(cmd)
}

fn collect_command_sources(input: &str) -> Vec<CommandSource> {
    collect_command_sources_from_line(input, 1)
}

/// Like [`collect_command_sources`] but numbers the first line `line_base`
/// instead of 1. The streaming `-in` path parses one command chunk at a time and
/// clears the buffer between chunks, so it threads a running line count here to
/// keep error positions cumulative across the whole session — z3 reports the
/// true whole-input line number in `-in` mode, not a per-command reset.
fn collect_command_sources_from_line(input: &str, line_base: usize) -> Vec<CommandSource> {
    let mut sources = Vec::new();
    let mut line = line_base;
    let mut column = 1usize;
    let mut depth = 0usize;
    let mut start_idx = 0usize;
    let mut start_line = line_base;
    let mut start_column = 1usize;
    let mut in_comment = false;
    let mut in_string = false;
    let mut in_quoted_symbol = false;
    let mut chars = input.char_indices().peekable();

    while let Some((idx, ch)) = chars.next() {
        if in_comment {
            if ch == '\n' {
                in_comment = false;
                line += 1;
                column = 1;
            } else {
                column += 1;
            }
            continue;
        }

        if in_string {
            if ch == '"' {
                if let Some((_, '"')) = chars.peek().copied() {
                    let _ = chars.next();
                    column += 2;
                    continue;
                }
                in_string = false;
            }
            if ch == '\n' {
                line += 1;
                column = 1;
            } else {
                column += 1;
            }
            continue;
        }

        if in_quoted_symbol {
            if ch == '|' {
                in_quoted_symbol = false;
            }
            if ch == '\n' {
                line += 1;
                column = 1;
            } else {
                column += 1;
            }
            continue;
        }

        match ch {
            ';' => in_comment = true,
            '"' => in_string = true,
            '|' => in_quoted_symbol = true,
            '(' => {
                if depth == 0 {
                    start_idx = idx;
                    start_line = line;
                    start_column = column;
                }
                depth = depth.saturating_add(1);
            }
            ')' if depth > 0 => {
                depth -= 1;
                if depth == 0 {
                    let end = idx + ch.len_utf8();
                    sources.push(CommandSource {
                        line: start_line,
                        column: start_column,
                        text: input[start_idx..end].to_string(),
                    });
                }
            }
            _ => {}
        }

        if ch == '\n' {
            line += 1;
            column = 1;
        } else {
            column += 1;
        }
    }

    sources
}

fn set_current_command_source(
    state: &mut SmtTranscriptState,
    sources: &[CommandSource],
    index: usize,
) {
    state.current_source = sources.get(index).cloned();
    state.current_command_ordinal = state.processed_commands;
    state.processed_commands = state.processed_commands.saturating_add(1);
}

fn source_position_at(source: &CommandSource, byte_offset: usize) -> SourcePosition {
    let mut line = source.line;
    let mut column = source.column;
    let capped_offset = byte_offset.min(source.text.len());

    for (_, ch) in source
        .text
        .char_indices()
        .take_while(|(idx, _)| *idx < capped_offset)
    {
        if ch == '\n' {
            line += 1;
            column = 1;
        } else {
            column += 1;
        }
    }

    SourcePosition { line, column }
}

fn source_error(position: Option<SourcePosition>, message: &str) -> String {
    let message = if let Some(position) = position {
        format!(
            "line {} column {}: {message}",
            position.line, position.column
        )
    } else {
        message.to_string()
    };
    format!("(error \"{}\")", escape_string_contents(&message))
}

fn z3_parser_symbol_position(
    state: &SmtTranscriptState,
    mut position: SourcePosition,
) -> SourcePosition {
    if state.current_command_ordinal > 0 {
        position.column = position.column.saturating_sub(1);
    }
    position
}

fn z3_parser_application_position(
    state: &SmtTranscriptState,
    mut position: SourcePosition,
) -> SourcePosition {
    if state.current_command_ordinal == 0 {
        position.column = position.column.saturating_add(1);
    }
    position
}

fn write_transcript_line(channel: &str, owned_file: &RefCell<Option<std::fs::File>>, line: &str) {
    match channel {
        "stdout" => safe_println!("{line}"),
        "stderr" => safe_eprintln!("{line}"),
        path => {
            let mut file = owned_file.borrow_mut();
            match file.as_mut() {
                Some(file) => {
                    if let Err(err) = writeln!(file, "{line}") {
                        safe_eprintln!(
                            "warning: failed to write SMT-LIB transcript channel {path}: {err}"
                        );
                    }
                }
                None => safe_eprintln!(
                    "warning: SMT-LIB transcript channel {path} has no safe owned file handle"
                ),
            }
        }
    }
}

fn prepare_transcript_channel(channel: &str) -> io::Result<Option<std::fs::File>> {
    if matches!(channel, "stdout" | "stderr") {
        return Ok(None);
    }

    let target = std::path::Path::new(channel);
    let (resolved_target, temp_path, file) = create_artifact_temp_file(target)?;
    match publish_artifact_temp(&temp_path, &resolved_target) {
        Ok(()) => Ok(Some(file)),
        Err(error) => {
            drop(file);
            let _ = std::fs::remove_file(&temp_path);
            Err(error)
        }
    }
}

fn print_regular_line(state: &SmtTranscriptState, line: &str) {
    write_transcript_line(
        &state.regular_output_channel,
        &state.regular_output_file,
        line,
    );
}

fn print_diagnostic_line(state: &SmtTranscriptState, line: &str) {
    write_transcript_line(
        &state.diagnostic_output_channel,
        &state.diagnostic_output_file,
        line,
    );
}

fn z3_unsupported_query_position(state: &SmtTranscriptState) -> Option<SourcePosition> {
    let source = state.current_source.as_ref()?;
    let column = if state.current_command_ordinal == 0 {
        source.column
    } else {
        source.column.saturating_sub(1)
    };
    Some(SourcePosition {
        line: source.line,
        column,
    })
}

fn z3_unsupported_query_comment(state: &SmtTranscriptState, keyword: &str) -> String {
    if let Some(position) = z3_unsupported_query_position(state) {
        format!(
            "; {} line: {} position: {}",
            keyword_with_colon(keyword),
            position.line,
            position.column
        )
    } else {
        format!("; {} unsupported", keyword_with_colon(keyword))
    }
}

fn eprintln_z3_unsupported_query_comment(state: &SmtTranscriptState, keyword: &str) {
    print_diagnostic_line(state, &z3_unsupported_query_comment(state, keyword));
}

fn current_source_last_token_position(state: &SmtTranscriptState) -> Option<SourcePosition> {
    let source = state.current_source.as_ref()?;
    let close_idx = source.text.rfind(')')?;
    let token_idx = source.text[..close_idx]
        .char_indices()
        .rev()
        .find_map(|(idx, ch)| (!ch.is_whitespace()).then_some(idx))?;
    Some(source_position_at(source, token_idx))
}

fn invalid_status_position(state: &SmtTranscriptState) -> Option<SourcePosition> {
    let source = state.current_source.as_ref()?;
    let status_idx = source.text.find(":status")?;
    Some(source_position_at(source, status_idx + ":status".len()))
}

fn keyword_key(keyword: &str) -> &str {
    keyword.trim_start_matches(':')
}

fn is_global_decls_option(key: &str) -> bool {
    matches!(key, "global-declarations" | "global-decls")
}

fn keyword_with_colon(keyword: &str) -> String {
    if keyword.starts_with(':') {
        keyword.to_string()
    } else {
        format!(":{keyword}")
    }
}

fn sexpr_bool(value: &SExpr) -> Option<bool> {
    match value {
        SExpr::True => Some(true),
        SExpr::False => Some(false),
        SExpr::Symbol(symbol) if symbol == "true" => Some(true),
        SExpr::Symbol(symbol) if symbol == "false" => Some(false),
        _ => None,
    }
}

fn sexpr_string(value: &SExpr) -> Option<&str> {
    match value {
        SExpr::String(value) => Some(value),
        _ => None,
    }
}

fn sexpr_numeral(value: &SExpr) -> Option<&str> {
    match value {
        SExpr::Numeral(value) => Some(value),
        _ => None,
    }
}

fn sexpr_status(value: &SExpr) -> Option<&'static str> {
    match value {
        SExpr::Symbol(symbol) if symbol == "sat" => Some("sat"),
        SExpr::Symbol(symbol) if symbol == "unsat" => Some("unsat"),
        SExpr::Symbol(symbol) if symbol == "unknown" => Some("unknown"),
        _ => None,
    }
}

fn is_invalid_status_attribute(cmd: &Command) -> bool {
    matches!(
        cmd,
        Command::SetInfo(keyword, SExpr::Symbol(_))
            if keyword_key(keyword) == "status" && sexpr_status_value(cmd).is_none()
    )
}

fn sexpr_status_value(cmd: &Command) -> Option<&'static str> {
    let Command::SetInfo(_, value) = cmd else {
        return None;
    };
    sexpr_status(value)
}

fn maybe_handle_cli_transcript_command(state: &mut SmtTranscriptState, cmd: &Command) -> bool {
    if matches!(cmd, Command::GetUnsatAssumptions) && !state.produce_unsat_assumptions {
        print_regular_line(
            state,
            &source_error(
                current_source_last_token_position(state),
                "unsat assumptions construction is not enabled, use command (set-option :produce-unsat-assumptions true)",
            ),
        );
        state.note_recoverable_error();
        return true;
    }

    if matches!(cmd, Command::GetProof) && !state.produce_proofs {
        print_regular_line(
            state,
            &source_error(
                current_source_last_token_position(state),
                "proof construction is not enabled, use command (set-option :produce-proofs true)",
            ),
        );
        state.note_recoverable_error();
        return true;
    }

    if matches!(cmd, Command::GetAssertions) && !state.interactive_mode {
        print_regular_line(
            state,
            &source_error(
                current_source_last_token_position(state),
                "command is only available in interactive mode, use command (set-option :interactive-mode true)",
            ),
        );
        state.note_recoverable_error();
        return true;
    }

    if let Command::Pop(depth) = cmd {
        if *depth > state.assertion_stack_depth {
            print_regular_line(
                state,
                &source_error(
                    current_source_last_token_position(state),
                    "invalid pop command, argument is greater than the current stack depth",
                ),
            );
            state.note_recoverable_error();
            return true;
        }

        if *depth > state.executor_assertion_stack_depth {
            update_transcript_state_after_command(state, cmd);
            maybe_print_success(state);
            return true;
        }
    }

    if is_invalid_status_attribute(cmd) {
        print_regular_line(
            state,
            &source_error(
                invalid_status_position(state),
                "invalid ':status' attribute",
            ),
        );
        state.note_recoverable_error();
        return true;
    }

    if let Command::SetOption(keyword, value) = cmd {
        let key = keyword_key(keyword);
        if key == "auto-config" && sexpr_bool(value).is_some() {
            update_transcript_state_after_command(state, cmd);
            maybe_print_success(state);
            return true;
        }
        if key == "model.v2" && sexpr_bool(value).is_some() {
            update_transcript_state_after_command(state, cmd);
            maybe_print_success(state);
            return true;
        }
        if key == "model.compact" && sexpr_bool(value).is_some() {
            update_transcript_state_after_command(state, cmd);
            maybe_print_success(state);
            return true;
        }
        if key == "pp.decimal" && sexpr_bool(value).is_some() {
            update_transcript_state_after_command(state, cmd);
            maybe_print_success(state);
            return true;
        }
        if key == "pp.decimal-precision" && sexpr_numeral(value).is_some() {
            update_transcript_state_after_command(state, cmd);
            maybe_print_success(state);
            return true;
        }
        if key == "pp.max-depth" && sexpr_numeral(value).is_some() {
            update_transcript_state_after_command(state, cmd);
            maybe_print_success(state);
            return true;
        }
        if key == "pp.max-ribbon" && sexpr_numeral(value).is_some() {
            update_transcript_state_after_command(state, cmd);
            maybe_print_success(state);
            return true;
        }
        if key == "pp.single-line" && sexpr_bool(value).is_some() {
            update_transcript_state_after_command(state, cmd);
            maybe_print_success(state);
            return true;
        }
        if key == "pp.bv-literals" && sexpr_bool(value).is_some() {
            update_transcript_state_after_command(state, cmd);
            maybe_print_success(state);
            return true;
        }
        if matches!(key, "regular-output-channel" | "diagnostic-output-channel") {
            let Some(channel) = sexpr_string(value) else {
                return false;
            };
            let other_channel = if key == "regular-output-channel" {
                state.diagnostic_output_channel.as_str()
            } else {
                state.regular_output_channel.as_str()
            };
            if state.output_channel_conflicts(channel, other_channel) {
                print_regular_line(
                    state,
                    &source_error(
                        current_source_last_token_position(state),
                        &format!(
                            "refusing SMT-LIB {key} path {channel}: it aliases another transcript channel or a solver artifact"
                        ),
                    ),
                );
                state.note_recoverable_error();
                return true;
            }
            match prepare_transcript_channel(channel) {
                Ok(file) => {
                    if key == "regular-output-channel" {
                        state.regular_output_channel = channel.to_string();
                        state.regular_output_file.replace(file);
                    } else {
                        state.diagnostic_output_channel = channel.to_string();
                        state.diagnostic_output_file.replace(file);
                    }
                    maybe_print_success(state);
                }
                Err(error) => {
                    print_regular_line(
                        state,
                        &source_error(
                            current_source_last_token_position(state),
                            &format!("failed to open SMT-LIB {key} safely at {channel}: {error}"),
                        ),
                    );
                    state.note_recoverable_error();
                }
            }
            return true;
        }
        if key == "verbosity" && sexpr_numeral(value).is_some() {
            update_transcript_state_after_command(state, cmd);
            maybe_print_success(state);
            return true;
        }
        if key == "rlimit" && sexpr_numeral(value).is_some() {
            update_transcript_state_after_command(state, cmd);
            maybe_print_success(state);
            return true;
        }
        if is_z3_compat_bool_option(key) && sexpr_bool(value).is_some() {
            update_transcript_state_after_command(state, cmd);
            maybe_print_success(state);
            return true;
        }
    }
    false
}

fn sort_text(sort: &Sort) -> String {
    match sort {
        Sort::Simple(name) => name.clone(),
        Sort::Parameterized(name, args) => {
            let mut parts = Vec::with_capacity(args.len() + 1);
            parts.push(name.clone());
            parts.extend(args.iter().map(sort_text));
            format!("({})", parts.join(" "))
        }
        Sort::Indexed(name, indices) => {
            let mut parts = Vec::with_capacity(indices.len() + 2);
            parts.push("_".to_string());
            parts.push(name.clone());
            parts.extend(indices.iter().map(|index| match index {
                Index::Numeral(value) | Index::Hexadecimal(value) | Index::Binary(value) => {
                    value.clone()
                }
                Index::Symbol(value) => quote_symbol(value),
                _ => "<unsupported-index>".to_string(),
            }));
            format!("({})", parts.join(" "))
        }
        _ => "Unknown".to_string(),
    }
}

fn constant_sort_text(value: &Constant) -> String {
    match value {
        Constant::True | Constant::False => "Bool".to_string(),
        Constant::Numeral(_) => "Int".to_string(),
        Constant::Decimal(_) => "Real".to_string(),
        Constant::Hexadecimal(bits) => format!("(_ BitVec {})", bits.len() * 4),
        Constant::Binary(bits) => format!("(_ BitVec {})", bits.len()),
        Constant::String(_) => "String".to_string(),
        _ => "Unknown".to_string(),
    }
}

fn parse_sort_text(text: &str) -> Option<Sort> {
    let sexp = parse_sexp(text).ok()?;
    Sort::from_sexp(&sexp).ok()
}

fn array_sort_parts(sort: &str) -> Option<(String, String)> {
    let Sort::Parameterized(name, args) = parse_sort_text(sort)? else {
        return None;
    };
    if name != "Array" || args.len() != 2 {
        return None;
    }
    Some((sort_text(&args[0]), sort_text(&args[1])))
}

fn infer_numeric_sort_text(
    state: &SmtTranscriptState,
    locals: &HashMap<String, Option<String>>,
    args: &[Term],
) -> Option<String> {
    let mut saw_real = false;
    for arg in args {
        match infer_term_sort_text_with_locals(state, locals, arg)?.as_str() {
            "Int" => {}
            "Real" => saw_real = true,
            _ => return None,
        }
    }
    Some(if saw_real { "Real" } else { "Int" }.to_string())
}

fn all_args_have_sort(
    state: &SmtTranscriptState,
    locals: &HashMap<String, Option<String>>,
    args: &[Term],
    expected: &str,
) -> Option<()> {
    args.iter()
        .all(|arg| {
            infer_term_sort_text_with_locals(state, locals, arg).as_deref() == Some(expected)
        })
        .then_some(())
}

fn infer_app_sort_text(
    state: &SmtTranscriptState,
    locals: &HashMap<String, Option<String>>,
    name: &str,
    args: &[Term],
) -> Option<String> {
    match name {
        "+" | "-" | "*" | "/" if !args.is_empty() => infer_numeric_sort_text(state, locals, args),
        "div" | "mod" | "abs" if !args.is_empty() => {
            all_args_have_sort(state, locals, args, "Int")?;
            Some("Int".to_string())
        }
        "<" | "<=" | ">" | ">=" if !args.is_empty() => {
            infer_numeric_sort_text(state, locals, args)?;
            Some("Bool".to_string())
        }
        "=" | "distinct" if !args.is_empty() => args
            .iter()
            .all(|arg| infer_term_sort_text_with_locals(state, locals, arg).is_some())
            .then_some("Bool".to_string()),
        "and" | "or" | "xor" | "=>" if !args.is_empty() => {
            all_args_have_sort(state, locals, args, "Bool")?;
            Some("Bool".to_string())
        }
        "not" if args.len() == 1 => {
            all_args_have_sort(state, locals, args, "Bool")?;
            Some("Bool".to_string())
        }
        "ite" if args.len() == 3 => {
            (infer_term_sort_text_with_locals(state, locals, &args[0]).as_deref() == Some("Bool"))
                .then_some(())?;
            let then_sort = infer_term_sort_text_with_locals(state, locals, &args[1])?;
            (infer_term_sort_text_with_locals(state, locals, &args[2]).as_deref()
                == Some(then_sort.as_str()))
            .then_some(then_sort)
        }
        "to_real" if args.len() == 1 => {
            all_args_have_sort(state, locals, args, "Int")?;
            Some("Real".to_string())
        }
        "to_int" if args.len() == 1 => {
            all_args_have_sort(state, locals, args, "Real")?;
            Some("Int".to_string())
        }
        "is_int" if args.len() == 1 => {
            all_args_have_sort(state, locals, args, "Real")?;
            Some("Bool".to_string())
        }
        "select" if args.len() == 2 => {
            let array_sort = infer_term_sort_text_with_locals(state, locals, &args[0])?;
            let (index_sort, element_sort) = array_sort_parts(&array_sort)?;
            (infer_term_sort_text_with_locals(state, locals, &args[1]).as_deref()
                == Some(index_sort.as_str()))
            .then_some(element_sort)
        }
        "store" if args.len() == 3 => {
            let array_sort = infer_term_sort_text_with_locals(state, locals, &args[0])?;
            let (index_sort, element_sort) = array_sort_parts(&array_sort)?;
            (infer_term_sort_text_with_locals(state, locals, &args[1]).as_deref()
                == Some(index_sort.as_str()))
            .then_some(())?;
            (infer_term_sort_text_with_locals(state, locals, &args[2]).as_deref()
                == Some(element_sort.as_str()))
            .then_some(array_sort)
        }
        _ => None,
    }
}

fn infer_term_sort_text_with_locals(
    state: &SmtTranscriptState,
    locals: &HashMap<String, Option<String>>,
    term: &Term,
) -> Option<String> {
    match term {
        Term::Const(value) => Some(constant_sort_text(value)),
        Term::Symbol(symbol) => {
            if let Some(local_sort) = locals.get(symbol) {
                return local_sort.clone();
            }
            state.symbol_sorts.get(symbol).cloned().flatten()
        }
        Term::App(name, args) => infer_app_sort_text(state, locals, name, args),
        Term::IndexedApp(name, _, args) => infer_app_sort_text(state, locals, name, args),
        Term::Let(bindings, body) => {
            let mut extended = locals.clone();
            for (name, binding) in bindings {
                extended.insert(
                    name.clone(),
                    infer_term_sort_text_with_locals(state, locals, binding),
                );
            }
            infer_term_sort_text_with_locals(state, &extended, body)
        }
        Term::Annotated(inner, _) => infer_term_sort_text_with_locals(state, locals, inner),
        Term::QualifiedApp(_, sort, _) => Some(sort_text(sort)),
        _ => None,
    }
}

fn extend_sorted_sort_locals(
    locals: &HashMap<String, Option<String>>,
    bindings: &[(String, Sort)],
) -> HashMap<String, Option<String>> {
    let mut extended = locals.clone();
    for (name, sort) in bindings {
        extended.insert(name.clone(), Some(sort_text(sort)));
    }
    extended
}

fn extend_let_sort_locals(
    state: &SmtTranscriptState,
    locals: &HashMap<String, Option<String>>,
    bindings: &[(String, Term)],
) -> HashMap<String, Option<String>> {
    let mut extended = locals.clone();
    for (name, binding) in bindings {
        extended.insert(
            name.clone(),
            infer_term_sort_text_with_locals(state, locals, binding),
        );
    }
    extended
}

fn find_application_arg_sorts(
    state: &SmtTranscriptState,
    term: &Term,
    symbol: &str,
) -> Option<Vec<String>> {
    let locals = HashMap::new();
    find_application_arg_sorts_with_locals(state, &locals, term, symbol)
}

fn find_application_arg_sorts_with_locals(
    state: &SmtTranscriptState,
    locals: &HashMap<String, Option<String>>,
    term: &Term,
    symbol: &str,
) -> Option<Vec<String>> {
    match term {
        Term::App(name, args) | Term::IndexedApp(name, _, args) if name == symbol => args
            .iter()
            .map(|arg| infer_term_sort_text_with_locals(state, locals, arg))
            .collect(),
        Term::QualifiedApp(QualifiedIdentifier::Symbol(name), _, args) if name == symbol => args
            .iter()
            .map(|arg| infer_term_sort_text_with_locals(state, locals, arg))
            .collect(),
        Term::App(_, args) | Term::IndexedApp(_, _, args) | Term::QualifiedApp(_, _, args) => args
            .iter()
            .find_map(|arg| find_application_arg_sorts_with_locals(state, locals, arg, symbol)),
        Term::Let(bindings, body) => {
            let from_bindings = bindings.iter().find_map(|(_, term)| {
                find_application_arg_sorts_with_locals(state, locals, term, symbol)
            });
            let extended = extend_let_sort_locals(state, locals, bindings);
            from_bindings
                .or_else(|| find_application_arg_sorts_with_locals(state, &extended, body, symbol))
        }
        Term::Forall(bindings, body)
        | Term::Exists(bindings, body)
        | Term::Lambda(bindings, body) => {
            let extended = extend_sorted_sort_locals(locals, bindings);
            find_application_arg_sorts_with_locals(state, &extended, body, symbol)
        }
        Term::Annotated(inner, _) => {
            find_application_arg_sorts_with_locals(state, locals, inner, symbol)
        }
        Term::Const(_) | Term::Symbol(_) => None,
        _ => None,
    }
}

fn command_application_arg_sorts(
    state: &SmtTranscriptState,
    cmd: &Command,
    symbol: &str,
) -> Option<Vec<String>> {
    match cmd {
        Command::Assert(term) | Command::Simplify(term) | Command::Eval(term) => {
            find_application_arg_sorts(state, term, symbol)
        }
        Command::CheckSatAssuming(terms) => terms
            .iter()
            .find_map(|term| find_application_arg_sorts(state, term, symbol)),
        Command::GetValue(terms) => terms
            .iter()
            .find_map(|(_, term)| find_application_arg_sorts(state, term, symbol)),
        _ => None,
    }
}

fn is_smt_symbol_boundary(ch: char) -> bool {
    ch.is_whitespace() || matches!(ch, '(' | ')' | ';' | '"')
}

fn find_symbol_byte_offset(text: &str, symbol: &str) -> Option<usize> {
    text.match_indices(symbol).find_map(|(idx, _)| {
        let before_ok = text[..idx]
            .chars()
            .next_back()
            .map_or(true, is_smt_symbol_boundary);
        let after_idx = idx + symbol.len();
        let after_ok = text[after_idx..]
            .chars()
            .next()
            .map_or(true, is_smt_symbol_boundary);
        (before_ok && after_ok).then_some(idx)
    })
}

fn matching_close_paren(text: &str, open_idx: usize) -> Option<usize> {
    let mut depth = 0usize;
    let mut in_comment = false;
    let mut in_string = false;
    let mut chars = text[open_idx..].char_indices().peekable();

    while let Some((relative_idx, ch)) = chars.next() {
        let idx = open_idx + relative_idx;

        if in_comment {
            if ch == '\n' {
                in_comment = false;
            }
            continue;
        }

        if in_string {
            if ch == '"' {
                if let Some((_, '"')) = chars.peek().copied() {
                    let _ = chars.next();
                    continue;
                }
                in_string = false;
            }
            continue;
        }

        match ch {
            ';' => in_comment = true,
            '"' => in_string = true,
            '(' => depth = depth.saturating_add(1),
            ')' => {
                depth = depth.saturating_sub(1);
                if depth == 0 {
                    return Some(idx);
                }
            }
            _ => {}
        }
    }

    None
}

fn previous_non_whitespace(text: &str, before_idx: usize) -> Option<usize> {
    text[..before_idx]
        .char_indices()
        .rev()
        .find_map(|(idx, ch)| (!ch.is_whitespace()).then_some(idx))
}

fn find_application_last_arg_end(text: &str, symbol: &str) -> Option<usize> {
    text.match_indices(symbol).find_map(|(idx, _)| {
        if text[..idx].chars().next_back().is_none_or(|ch| ch != '(') {
            return None;
        }
        let after_idx = idx + symbol.len();
        if !text[after_idx..]
            .chars()
            .next()
            .is_some_and(is_smt_symbol_boundary)
        {
            return None;
        }

        let open_idx = idx.checked_sub(1)?;
        let close_idx = matching_close_paren(text, open_idx)?;
        let last_arg_idx = previous_non_whitespace(text, close_idx)?;
        (last_arg_idx >= after_idx).then_some(last_arg_idx)
    })
}

fn undefined_symbol_position(state: &SmtTranscriptState, symbol: &str) -> Option<SourcePosition> {
    let source = state.current_source.as_ref()?;
    let symbol_idx = find_symbol_byte_offset(&source.text, symbol)?;
    Some(z3_parser_symbol_position(
        state,
        source_position_at(source, symbol_idx),
    ))
}

fn undefined_application_position(
    state: &SmtTranscriptState,
    symbol: &str,
) -> Option<SourcePosition> {
    let source = state.current_source.as_ref()?;
    let last_arg_idx = find_application_last_arg_end(&source.text, symbol)?;
    Some(z3_parser_application_position(
        state,
        source_position_at(source, last_arg_idx),
    ))
}

fn z3_compat_undefined_symbol_error(
    state: &SmtTranscriptState,
    cmd: &Command,
    message: &str,
) -> Option<String> {
    let symbol = message
        .strip_prefix("elaboration error: undefined symbol: ")?
        .trim();
    if symbol.is_empty() {
        return None;
    }
    if let Some(arg_sorts) = command_application_arg_sorts(state, cmd, symbol) {
        let message = format!("unknown constant {} ({}) ", symbol, arg_sorts.join(" "));
        return Some(source_error(
            undefined_application_position(state, symbol)
                .or_else(|| undefined_symbol_position(state, symbol)),
            &message,
        ));
    }
    let message = format!("unknown constant {symbol}");
    Some(source_error(
        undefined_symbol_position(state, symbol),
        &message,
    ))
}

/// A `=`/`distinct`/theory-op **sort mismatch** — e.g. an ill-sorted
/// FloatingPoint equality between different `(_ FloatingPoint eb sb)` widths
/// (`#fp-sort-mismatch`), which AY otherwise bit-blasts into an index-out-of-
/// bounds panic in the FP gate — is reported the way z3 reports it: `(error
/// "...")` on **stdout**, with execution CONTINUING (the offending command is
/// dropped). Mirrors z3's `Sorts A and B are incompatible` wording. The caller
/// then taints the problem so a pending `check-sat` answers `unknown` (fail
/// closed; z3 emits `sat` on the incomplete remainder, AY is deliberately more
/// conservative). Returning the error on stdout + a verdict + rc 1 keeps the
/// "every check-sat emits a verdict" invariant — the previous stderr-and-abort
/// path exited 1 with an EMPTY verdict, the worst shape for a driver.
fn z3_compat_sort_mismatch_error(state: &SmtTranscriptState, message: &str) -> Option<String> {
    let detail = message.strip_prefix("elaboration error: sort mismatch: ")?;
    // `detail` is "expected {E}, got {A}"; re-render to z3's phrasing when the
    // shape matches, else pass the AY detail through verbatim.
    let rendered = match detail
        .strip_prefix("expected ")
        .and_then(|rest| rest.split_once(", got "))
    {
        Some((expected, actual)) => format!("Sorts {expected} and {actual} are incompatible"),
        None => detail.to_string(),
    };
    Some(source_error(
        current_source_last_token_position(state),
        &rendered,
    ))
}

fn maybe_handle_recoverable_execution_error(
    state: &mut SmtTranscriptState,
    cmd: &Command,
    message: &str,
) -> bool {
    if let Some(output) = z3_compat_undefined_symbol_error(state, cmd, message) {
        print_regular_line(state, &output);
        state.note_recoverable_error();
        return true;
    }
    if let Some(output) = z3_compat_sort_mismatch_error(state, message) {
        print_regular_line(state, &output);
        state.note_recoverable_error();
        return true;
    }
    // An unrecognized `(set-logic X)` is IGNORED with z3-identical output: the
    // token z3 does not recognize (validated in the executor via the same
    // structural predicate z3 uses) prints `unsupported` on stdout plus a
    // `; ignoring unsupported logic <TOK> line: <L> position: <P>` diagnostic
    // comment on stderr, then solving CONTINUES with ALL semantics and the exit
    // code is UNAFFECTED (z3 exits 0 on an ignored logic — so, unlike every
    // other recoverable error, this one does NOT call `note_recoverable_error`).
    // The logic is treated as never set (a later `set-logic` still succeeds).
    if let Command::SetLogic(logic) = cmd {
        let comment = format!(
            "; ignoring unsupported logic {logic} {}",
            match z3_unsupported_query_position(state) {
                Some(position) => format!("line: {} position: {}", position.line, position.column),
                None => "line: unsupported".to_string(),
            }
        );
        if state.regular_output_channel == state.diagnostic_output_channel {
            print_regular_line(state, &format!("unsupported\n{comment}"));
        } else {
            print_regular_line(state, "unsupported");
            print_diagnostic_line(state, &comment);
        }
        return true;
    }
    // General fail-closed routing for ANY OTHER elaboration error — datatype
    // member collision (`declare-const hd` when `hd` is a selector), reserved-
    // symbol declaration, sort redeclaration, and the like. Each is a SOUND
    // rejection of a malformed/conflating declaration (they prevent a wrong-
    // UNSAT conflation class), but a dropped problem-contributing command must
    // still leave a verdict: report the error on STDOUT and CONTINUE, so the
    // caller taints the session and the pending check-sat answers `unknown`,
    // rather than aborting the stream to an EMPTY verdict with the error only on
    // stderr (the worst shape for a driver). Mirrors z3's continued-execution;
    // the specific handlers above keep z3's exact wording for the common
    // undefined-symbol / sort-mismatch cases. (#every-check-sat-emits-a-verdict)
    if let Some(detail) = message.strip_prefix("elaboration error: ") {
        let output = source_error(current_source_last_token_position(state), detail);
        print_regular_line(state, &output);
        state.note_recoverable_error();
        return true;
    }
    false
}

fn exit_if_transcript_had_recoverable_error(state: &SmtTranscriptState) {
    if state.had_recoverable_error {
        let _ = io::stdout().flush();
        let _ = io::stderr().flush();
        std::process::exit(1);
    }
}

fn exit_if_timed_out_with_transcript_context(state: &SmtTranscriptState) {
    if is_timed_out() && state.had_recoverable_error && !z3_mode_enabled() {
        let count = state.recoverable_error_count.max(1);
        let plural = if count == 1 { "" } else { "s" };
        print_diagnostic_line(
            state,
            &format!(
                "; ay diagnostic: timeout occurred after {count} recoverable SMT-LIB error{plural}; input had already failed SMT-LIB execution before the timeout"
            ),
        );
    }
    exit_if_timed_out();
}

/// Emit `--stats` counters before a timeout exit (#wp1-stats-on-timeout).
///
/// The runs worth instrumenting are precisely the ones that end by timeout, and
/// those were the only runs that emitted NO counters at all: the normal exit path
/// prints stats, the timeout path did not. That made every measurement on a hard
/// instance a reverse-engineering exercise over env-gated debug channels, and it
/// hid the counters that attribute per-round cost. `-st`/`--stats` is a request
/// for counters, and a timeout is still a run.
///
/// Emits only when stats were actually requested, so default runs are byte-identical.
fn exit_if_timed_out_with_stats(
    state: &SmtTranscriptState,
    executor: &Executor,
    formula_stats: Option<&FormulaStats>,
    stats_cfg: stats_output::StatsConfig,
) {
    if is_timed_out() && stats_cfg.any() {
        print_smt_stats(executor, state, formula_stats, stats_cfg);
    }
    exit_if_timed_out_with_transcript_context(state);
}

fn update_rlimit_after_command(state: &mut SmtTranscriptState, cmd: &Command) {
    match cmd {
        Command::Assert(_) => state.rlimit = state.rlimit.saturating_add(3),
        Command::CheckSat | Command::CheckSatAssuming(_) => {
            state.rlimit = state.rlimit.saturating_add(30);
        }
        Command::Push(_) | Command::Pop(_) | Command::Reset | Command::ResetAssertions => {
            state.rlimit = state.rlimit.saturating_add(1);
        }
        _ => {}
    }
}

fn command_invalidates_public_result(cmd: &Command) -> bool {
    command_mutates_problem(cmd)
}

fn record_nullary_symbol_sort(state: &mut SmtTranscriptState, name: &str, sort: &Sort) {
    let scope_depth = (!state.global_decls).then_some(state.assertion_stack_depth);
    let bindings = state
        .symbol_sort_bindings
        .entry(name.to_string())
        .or_default();
    bindings.push(ScopedSymbolSort {
        sort: sort_text(sort),
        scope_depth,
    });
    let inferred = (bindings.len() == 1).then(|| bindings[0].sort.clone());
    state.symbol_sorts.insert(name.to_string(), inferred);
}

fn expire_scoped_symbol_sorts(state: &mut SmtTranscriptState) {
    let depth = state.assertion_stack_depth;
    state.symbol_sort_bindings.retain(|_, bindings| {
        bindings.retain(|binding| match binding.scope_depth {
            None => true,
            Some(binding_depth) => binding_depth <= depth,
        });
        !bindings.is_empty()
    });
    state.symbol_sorts.clear();
    for (name, bindings) in &state.symbol_sort_bindings {
        let inferred = (bindings.len() == 1).then(|| bindings[0].sort.clone());
        state.symbol_sorts.insert(name.clone(), inferred);
    }
}

fn update_transcript_state_after_command(state: &mut SmtTranscriptState, cmd: &Command) {
    update_rlimit_after_command(state, cmd);

    if command_invalidates_public_result(cmd) {
        state.clear_public_result();
    }

    match cmd {
        Command::SetOption(keyword, value) if keyword_key(keyword) == "print-success" => {
            if let Some(enabled) = sexpr_bool(value) {
                state.print_success = enabled;
            }
        }
        // `:produce-assertions` is the SMT-LIB 2.6 name; `:interactive-mode` is
        // its deprecated 2.5 synonym. Both enable `(get-assertions)`. z3 uses
        // `:produce-assertions`, so accept either (matches z3). (#get-assertions)
        Command::SetOption(keyword, value)
            if matches!(
                keyword_key(keyword),
                "interactive-mode" | "produce-assertions"
            ) =>
        {
            if let Some(enabled) = sexpr_bool(value) {
                state.interactive_mode = enabled;
            }
        }
        Command::SetOption(keyword, value) if keyword_key(keyword) == "produce-assignments" => {
            if let Some(enabled) = sexpr_bool(value) {
                state.produce_assignments = enabled;
            }
        }
        Command::SetOption(keyword, value) if keyword_key(keyword) == "produce-proofs" => {
            if let Some(enabled) = sexpr_bool(value) {
                state.produce_proofs = enabled;
            }
        }
        Command::SetOption(keyword, value)
            if keyword_key(keyword) == "produce-unsat-assumptions" =>
        {
            if let Some(enabled) = sexpr_bool(value) {
                state.produce_unsat_assumptions = enabled;
            }
        }
        Command::SetOption(keyword, value) if is_global_decls_option(keyword_key(keyword)) => {
            if let Some(enabled) = sexpr_bool(value) {
                state.global_decls = enabled;
            }
        }
        Command::SetOption(keyword, value) if keyword_key(keyword) == "auto-config" => {
            if let Some(enabled) = sexpr_bool(value) {
                state.auto_config = enabled;
            }
        }
        Command::SetOption(keyword, value) if keyword_key(keyword) == "model.v2" => {
            if let Some(enabled) = sexpr_bool(value) {
                state.model_v2 = enabled;
            }
        }
        Command::SetOption(keyword, value) if keyword_key(keyword) == "model.compact" => {
            if let Some(enabled) = sexpr_bool(value) {
                state.model_compact = enabled;
            }
        }
        Command::SetOption(keyword, value) if keyword_key(keyword) == "pp.decimal" => {
            if let Some(enabled) = sexpr_bool(value) {
                state.pp_decimal = enabled;
            }
        }
        Command::SetOption(keyword, value) if keyword_key(keyword) == "pp.decimal-precision" => {
            if let Some(precision) = sexpr_numeral(value) {
                state.pp_decimal_precision = precision.to_string();
            }
        }
        Command::SetOption(keyword, value) if keyword_key(keyword) == "pp.max-depth" => {
            if let Some(depth) = sexpr_numeral(value) {
                state.pp_max_depth = depth.to_string();
            }
        }
        Command::SetOption(keyword, value) if keyword_key(keyword) == "pp.max-ribbon" => {
            if let Some(ribbon) = sexpr_numeral(value) {
                state.pp_max_ribbon = ribbon.to_string();
            }
        }
        Command::SetOption(keyword, value) if keyword_key(keyword) == "pp.single-line" => {
            if let Some(enabled) = sexpr_bool(value) {
                state.pp_single_line = enabled;
            }
        }
        Command::SetOption(keyword, value) if keyword_key(keyword) == "pp.bv-literals" => {
            if let Some(enabled) = sexpr_bool(value) {
                state.pp_bv_literals = enabled;
            }
        }
        Command::SetOption(keyword, value) if keyword_key(keyword) == "verbosity" => {
            if let Some(verbosity) = sexpr_numeral(value) {
                state.verbosity = verbosity.to_string();
            }
        }
        Command::SetOption(keyword, value) if keyword_key(keyword) == "rlimit" => {
            if let Some(rlimit) = sexpr_numeral(value) {
                state.rlimit_option = rlimit.to_string();
            }
        }
        Command::SetOption(keyword, value) if is_z3_compat_bool_option(keyword_key(keyword)) => {
            if let Some(enabled) = sexpr_bool(value) {
                state
                    .z3_compat_bool_options
                    .insert(keyword_key(keyword).to_string(), enabled);
            }
        }
        Command::SetInfo(keyword, value) if keyword_key(keyword) == "status" => {
            if let Some(status) = sexpr_status(value) {
                state.status = Some(status.to_string());
            }
        }
        Command::DeclareConst(name, sort) => {
            record_nullary_symbol_sort(state, name, sort);
        }
        Command::DeclareFun(name, args, sort) if args.is_empty() => {
            record_nullary_symbol_sort(state, name, sort);
        }
        Command::DeclareVar(name, sort) => {
            record_nullary_symbol_sort(state, name, sort);
        }
        Command::DefineFun(name, params, sort, _)
        | Command::DefineFunRec(name, params, sort, _)
            if params.is_empty() =>
        {
            record_nullary_symbol_sort(state, name, sort);
        }
        Command::DefineFunsRec(declarations, _) => {
            for (name, params, sort) in declarations {
                if params.is_empty() {
                    record_nullary_symbol_sort(state, name, sort);
                }
            }
        }
        Command::Push(depth) => {
            state.assertion_stack_depth = state.assertion_stack_depth.saturating_add(*depth);
            state.executor_assertion_stack_depth =
                state.executor_assertion_stack_depth.saturating_add(*depth);
        }
        Command::Pop(depth) => {
            state.assertion_stack_depth = state.assertion_stack_depth.saturating_sub(*depth);
            state.executor_assertion_stack_depth =
                state.executor_assertion_stack_depth.saturating_sub(*depth);
            expire_scoped_symbol_sorts(state);
        }
        Command::Reset => {
            state.assertion_stack_depth = 0;
            state.executor_assertion_stack_depth = 0;
            state.symbol_sorts.clear();
            state.symbol_sort_bindings.clear();
            // SMT-LIB 2.6: `(reset)` returns the solver to its initial state, so
            // it must also clear the fail-closed poison a prior recoverable error
            // set. Without this, a dropped problem-contributing command latched
            // every later `check-sat` to `unknown` FOREVER — even for a fresh,
            // fully-valid problem built after the reset — where z3 answers
            // sat/unsat. Clearing here is sound: everything from before the reset
            // (including the dropped command) is gone, so the poison no longer
            // applies. NB: only `(reset)` is a full fresh start;
            // `(reset-assertions)` keeps declarations, so its poison is left
            // intact (a dropped declaration can still matter).
            state.completeness = ProblemCompleteness::Complete;
            state.had_recoverable_error = false;
            state.recoverable_error_count = 0;
        }
        Command::ResetAssertions => {
            state.executor_assertion_stack_depth = 0;
        }
        _ => {}
    }
}

fn maybe_print_success(state: &SmtTranscriptState) {
    if state.print_success {
        print_regular_line(state, "success");
    }
}

fn unsupported_get_info_parameters() -> &'static str {
    "unsupported\n; Suppported get-info parameters:\n; (get-info :reason-unknown)\n; (get-info :status)\n; (get-info :version)\n; (get-info :authors)\n; (get-info :error-behavior)\n; (get-info :parameters)\n; (get-info :rlimit)\n; (get-info :assertion-stack-levels)"
}

/// Z3 version reported under explicit `--z3-mode` (full impersonation). Matches
/// the pinned Z3 baseline that `ay --z3-mode` is documented and smoke-tested
/// against (the development design notes). Kept in sync with that baseline.
const Z3_COMPAT_BASELINE_VERSION: &str = "5.0.0";

fn z3_compat_get_info_output(
    state: &SmtTranscriptState,
    keyword: &str,
    output: &str,
) -> Option<String> {
    match keyword_key(keyword) {
        "reason-unknown" if state.public_verdict == Some(PublicVerdict::Unknown) => {
            let reason = state
                .public_unknown_reason
                .as_deref()
                .or_else(|| reason_unknown_inner(output))
                .unwrap_or("unknown");
            Some(render_public_unknown_reason(reason, z3_mode_enabled()))
        }
        "status" => Some(format!(
            "(:status {})",
            state.status.as_deref().unwrap_or("unknown")
        )),
        "rlimit" => Some(format!("(:rlimit {})", state.rlimit)),
        "assertion-stack-levels" => Some(format!(
            "(:assertion-stack-levels {})",
            state.assertion_stack_depth
        )),
        "name" => Some("(:name \"Z3\")".to_string()),
        "authors" => Some(
            "(:authors \"Leonardo de Moura, Nikolaj Bjorner, Lev Nachmanson and Christoph Wintersteiger\")"
                .to_string(),
        ),
        // Explicit `--z3-mode` is opt-in full Z3 impersonation: this filter
        // already reports `:name "Z3"` and Z3's authors, and the mode is
        // documented (the development design notes) to match the pinned Z3 5.0.0
        // baseline. Report a matching Z3 version so the identity triple
        // (name/authors/version) is internally consistent and tools that gate
        // on the Z3 version see a real one. Plain `-in` (no --z3-mode)
        // deliberately keeps AY's own build provenance instead (honest default,
        // see tests in group_cli/z3_compat_args.rs).
        "version" if z3_mode_enabled() => {
            Some(format!("(:version \"{Z3_COMPAT_BASELINE_VERSION}\")"))
        }
        "parameters" => None,
        "error-behavior" => Some("(:error-behavior continued-execution)".to_string()),
        "reason-unknown" if output == "(error \"no unknown result to explain\")" => Some(
            "(:reason-unknown \"state of the most recent check-sat command is not known\")"
                .to_string(),
        ),
        // Under explicit `--z3-mode` (full Z3 impersonation), remap AY's native
        // reason-unknown vocabulary — which is cvc5/yices-style (`resourceout`,
        // `memout`, bare `incomplete`, `unsupported`, ...) — to Z3's exact
        // strings. A real Z3 consumer parses `(:reason-unknown ...)` by literal
        // match: Verus, for one, only accepts `"canceled"`, `"unknown"`, or an
        // `"(incomplete...` prefix and PANICS on anything else. Native `-in`
        // (no --z3-mode) keeps AY's own descriptive reasons (ay-first mode).
        "reason-unknown" if z3_mode_enabled() => Some(
            reason_unknown_inner(output)
                .map(z3_reason_unknown_output)
                .unwrap_or_else(|| output.to_string()),
        ),
        _ if output.starts_with("(error \"unsupported info keyword:") => {
            if state.regular_output_channel == state.diagnostic_output_channel {
                let comment = z3_unsupported_query_comment(state, keyword);
                let parameters = unsupported_get_info_parameters();
                let (head, tail) = parameters
                    .split_once('\n')
                    .unwrap_or((parameters, ""));
                return Some(format!("{head}\n{comment}\n{tail}"));
            }
            eprintln_z3_unsupported_query_comment(state, keyword);
            Some(unsupported_get_info_parameters().to_string())
        }
        _ => Some(output.to_string()),
    }
}

fn render_public_unknown_reason(reason: &str, z3_mode: bool) -> String {
    if z3_mode {
        z3_reason_unknown_output(reason)
    } else {
        format!("(:reason-unknown {reason})")
    }
}

fn z3_mode_enabled() -> bool {
    Z3_MODE_ENABLED.load(std::sync::atomic::Ordering::Relaxed)
}

fn z3_model_enabled() -> bool {
    Z3_MODEL_ENABLED.load(std::sync::atomic::Ordering::Relaxed)
}

/// Extract the reason token from AY's native `(:reason-unknown <r>)` output.
///
/// AY prints the reason UNQUOTED (its `UnknownReason` `Display`), e.g.
/// `(:reason-unknown incomplete)` or `(:reason-unknown (incomplete
/// quantifier-cegqi))`; the token itself may contain spaces and parens. Returns
/// `None` if `output` is not in that shape (leaving it untouched).
fn reason_unknown_inner(output: &str) -> Option<&str> {
    output
        .strip_prefix("(:reason-unknown ")
        .and_then(|rest| rest.strip_suffix(')'))
}

/// Rewrite AY's native reason-unknown token `inner` (its `UnknownReason`
/// `Display`, cvc5/yices-style) into a `(:reason-unknown "...")` line using
/// Z3's vocabulary, for `--z3-mode` drop-in consumers.
///
/// The mapping is fail-closed and preserves the sat/unsat verdict (this only
/// touches how an `unknown` is *explained*):
///   * resource / time / memory / interrupt exhaustion -> Z3's `"canceled"`
///     (Z3 reports rlimit/timeout as canceled; Verus treats it as retryable);
///   * Z3's own `"unknown"` is kept verbatim (Verus accepts it);
///   * anything already in `(incomplete ...)` form is kept (matches Z3's
///     incompleteness prefix);
///   * every other reason (bare `incomplete`, `unsupported*`, `internal-error`,
///     ...) is wrapped as `(incomplete <reason>)` so a consumer treats the goal
///     as NOT proved — the sound default — while preserving AY's detail.
fn z3_reason_unknown_output(inner: &str) -> String {
    let inner = inner
        .strip_prefix('"')
        .and_then(|value| value.strip_suffix('"'))
        .unwrap_or(inner);
    let z3 = match inner {
        "timeout" | "resourceout" | "memout" | "interrupted" => "canceled".to_string(),
        "unknown" => "unknown".to_string(),
        s if s.starts_with("(incomplete") => s.to_string(),
        "incomplete" => "(incomplete)".to_string(),
        other => format!("(incomplete {other})"),
    };
    format!("(:reason-unknown \"{z3}\")")
}

fn simple_get_option_value<'a>(key: &str, output: &'a str) -> Option<&'a str> {
    let prefix = format!("(:{key} ");
    output.strip_prefix(&prefix)?.strip_suffix(')')
}

fn z3_compat_bool_option_defaults() -> HashMap<String, bool> {
    [
        ("ctrl-c", true),
        ("model.completion", false),
        ("model.partial", false),
        ("model_validate", false),
        ("unsat_core", false),
        ("type-check", true),
        ("well-sorted-check", false),
        ("debug-ref-count", false),
        ("trace", false),
        ("dump-models", false),
        ("stats", false),
    ]
    .into_iter()
    .map(|(key, value)| (key.to_string(), value))
    .collect()
}

fn is_z3_compat_bool_option(key: &str) -> bool {
    matches!(
        key,
        "ctrl-c"
            | "model.completion"
            | "model.partial"
            | "model_validate"
            | "unsat_core"
            | "type-check"
            | "well-sorted-check"
            | "debug-ref-count"
            | "trace"
            | "dump-models"
            | "stats"
    )
}

fn z3_compat_get_option_output(
    state: &SmtTranscriptState,
    keyword: &str,
    output: &str,
) -> Option<String> {
    let key = keyword_key(keyword);
    if key == "interactive-mode" || key == "produce-assertions" {
        return Some(state.interactive_mode.to_string());
    }
    if key == "produce-assignments" {
        return Some(state.produce_assignments.to_string());
    }
    if key == "produce-unsat-assumptions" {
        return Some(state.produce_unsat_assumptions.to_string());
    }
    if is_global_decls_option(key) {
        return Some(state.global_decls.to_string());
    }
    if key == "auto-config" {
        return Some(state.auto_config.to_string());
    }
    if key == "model.v2" {
        return Some(state.model_v2.to_string());
    }
    if key == "model.compact" {
        return Some(state.model_compact.to_string());
    }
    if key == "pp.decimal" {
        return Some(state.pp_decimal.to_string());
    }
    if key == "pp.decimal-precision" {
        return Some(state.pp_decimal_precision.clone());
    }
    if key == "pp.max-depth" {
        return Some(state.pp_max_depth.clone());
    }
    if key == "pp.max-ribbon" {
        return Some(state.pp_max_ribbon.clone());
    }
    if key == "pp.single-line" {
        return Some(state.pp_single_line.to_string());
    }
    if key == "pp.bv-literals" {
        return Some(state.pp_bv_literals.to_string());
    }
    if key == "regular-output-channel" {
        return Some(state.regular_output_channel.clone());
    }
    if key == "diagnostic-output-channel" {
        return Some(state.diagnostic_output_channel.clone());
    }
    if key == "verbosity" {
        return Some(state.verbosity.clone());
    }
    if key == "rlimit" {
        return Some(state.rlimit_option.clone());
    }
    if let Some(value) = state.z3_compat_bool_options.get(key) {
        return Some(value.to_string());
    }

    if key == "timeout" && output == "(error \"unknown option: :timeout\")" {
        return Some("4294967295".to_string());
    }

    if output.starts_with("(error \"unknown option:") {
        if state.regular_output_channel == state.diagnostic_output_channel {
            return Some(format!(
                "unsupported\n{}",
                z3_unsupported_query_comment(state, keyword)
            ));
        }
        eprintln_z3_unsupported_query_comment(state, keyword);
        return Some("unsupported".to_string());
    }

    Some(match key {
        "produce-models"
        | "produce-unsat-cores"
        | "produce-proofs"
        | "produce-assignments"
        | "produce-unsat-assumptions"
        | "global-decls"
        | "auto-config"
        | "pp.decimal"
        | "pp.decimal-precision"
        | "pp.max-depth"
        | "pp.max-ribbon"
        | "regular-output-channel"
        | "diagnostic-output-channel"
        | "print-success"
        | "random-seed"
        | "verbosity"
        | "rlimit"
        | "ctrl-c"
        | "model_validate"
        | "unsat_core"
        | "type-check"
        | "well-sorted-check"
        | "debug-ref-count"
        | "trace"
        | "dump-models"
        | "stats"
        | "timeout" => simple_get_option_value(key, output)
            .map(str::to_string)
            .unwrap_or_else(|| output.to_string()),
        _ => output.to_string(),
    })
}

fn maybe_enable_z3_default_assignment_query(executor: &mut Executor, cmd: &Command) -> bool {
    if !matches!(cmd, Command::GetAssignment) {
        return true;
    }

    executor
        .execute(&Command::SetOption(
            ":produce-assignments".to_string(),
            SExpr::True,
        ))
        .is_ok()
}

fn z3_compat_output_for_command(
    state: &mut SmtTranscriptState,
    cmd: &Command,
    output: &str,
) -> Option<String> {
    match cmd {
        Command::GetInfo(keyword) => z3_compat_get_info_output(state, keyword, output),
        Command::GetOption(keyword) => z3_compat_get_option_output(state, keyword, output),
        Command::GetModel if output == "(error \"model generation is not enabled\")" => {
            state.note_recoverable_error();
            Some(source_error(
                current_source_last_token_position(state),
                "model is not available",
            ))
        }
        Command::GetModel if z3_mode_enabled() && output.starts_with("(model\n") => {
            // z3 4.15.4 and SMT-LIB 2.6 emit get-model as a bare
            // `( <define-fun>* )` sequence; AY's native form prepends a `model`
            // head symbol (a legacy pre-4.8 z3 convention that a strict 2.6
            // reader rejects). --z3-mode exists to produce byte-compatible
            // transcripts, so drop the head. Printer-only: the define-fun body
            // is untouched and both forms parse to the identical model, so this
            // cannot change any verdict. (AY's internal model parsers consume
            // the native `(model …)` form upstream of this CLI print boundary,
            // so they are unaffected.)
            Some(format!("(\n{}", &output["(model\n".len()..]))
        }
        Command::GetValue(_) if output == "(error \"model is not available\")" => {
            state.note_recoverable_error();
            Some(source_error(
                current_source_last_token_position(state),
                "model is not available",
            ))
        }
        Command::GetUnsatCore
            if output
                == "(error \"unsat core generation is not enabled, set :produce-unsat-cores to true\")" =>
        {
            state.note_recoverable_error();
            Some(source_error(
                current_source_last_token_position(state),
                "unsat core construction is not enabled, use command (set-option :produce-unsat-cores true)",
            ))
        }
        Command::GetUnsatAssumptions
            if output == "(error \"no check-sat-assuming has been performed\")" =>
        {
            Some("()".to_string())
        }
        Command::GetUnsatAssumptions
            if output == "(error \"unsat assumptions not available, last result was sat\")" =>
        {
            state.note_recoverable_error();
            Some(source_error(
                current_source_last_token_position(state),
                "unsat assumptions is not available",
            ))
        }
        _ => Some(output.to_string()),
    }
}

/// Authenticate and correlate the invocation-owned decision trace with the
/// executor verdict that is about to become public.
///
/// This is deliberately separate from output: callers must retain and commit
/// the returned guard only after writing SAT/UNSAT/UNKNOWN to the regular
/// channel. Consuming the reservation here also makes the check single-use. A
/// trace invalidated by a public/raw mismatch can never authorize a later
/// result.
fn settle_authoritative_decision_trace(
    transcript: &mut SmtTranscriptState,
    path: Option<&str>,
) -> Result<Option<ay_sat::SettledDecisionTrace>, String> {
    let Some(path) = path else {
        return Ok(None);
    };
    let public_verdict = transcript.public_verdict.ok_or_else(|| {
        "decision trace cannot be settled without a public solver verdict".to_string()
    })?;
    match transcript.decision_trace_publication {
        DecisionTracePublication::Settled(settled) if settled == public_verdict => {
            return Ok(None);
        }
        DecisionTracePublication::Settled(settled) => {
            return Err(format!(
                "decision trace was already settled for {settled:?}, not {public_verdict:?}"
            ));
        }
        DecisionTracePublication::Invalidated => {
            return Err(
                "decision trace was invalidated and cannot authorize a public solver verdict"
                    .to_string(),
            );
        }
        DecisionTracePublication::Pending => {}
    }
    if !transcript.public_verdict_from_executor {
        return Err(
            "decision trace cannot certify a synthesized public solver verdict".to_string(),
        );
    }
    if ay_sat::decision_trace_suppressed_after_public_mismatch() {
        return Err(
            "decision trace was suppressed after the public result diverged from the raw solver result"
                .to_string(),
        );
    }
    let outcome = match public_verdict {
        PublicVerdict::Sat => ay_sat::TraceOutcome::Sat,
        PublicVerdict::Unsat => ay_sat::TraceOutcome::Unsat,
        PublicVerdict::Unknown => ay_sat::TraceOutcome::Unknown,
    };
    let publication = ay_sat::finish_reserved_decision_trace_retained(path, outcome)
        .map_err(|error| format!("failed to finalize decision trace {path}: {error}"))?;
    transcript.decision_trace_publication = DecisionTracePublication::Settled(public_verdict);
    Ok(Some(publication))
}

/// Emit one rendered executor response, settling an authoritative decision
/// trace first whenever the response is a public solver verdict. The injected
/// emitter keeps the ordering invariant directly unit-testable without
/// redirecting process-global stdout.
fn publish_rendered_executor_output(
    transcript: &mut SmtTranscriptState,
    is_decision_query: bool,
    raw_output: &str,
    rendered_output: String,
    decision_trace_path: Option<&str>,
    emit: impl FnOnce(&SmtTranscriptState, &str),
) -> Result<bool, String> {
    if is_decision_query && raw_output == "unsat" && transcript.defer_unsat_publication {
        transcript.pending_unsat_output = Some(rendered_output);
        return Ok(false);
    }

    let emits_verdict = is_decision_query && matches!(raw_output, "sat" | "unsat" | "unknown");
    let mut trace_publication = if emits_verdict {
        settle_authoritative_decision_trace(transcript, decision_trace_path)?
    } else {
        None
    };
    if let Some(trace_publication) = &trace_publication {
        trace_publication
            .validate()
            .map_err(|error| format!("settled decision trace lost same-run authority: {error}"))?;
    }
    emit(transcript, &rendered_output);
    if let Some(trace_publication) = &mut trace_publication {
        trace_publication.commit();
    }
    Ok(emits_verdict)
}

/// Finalize `--decision-trace` for SMT-LIB runs.
///
/// The SAT solver owns the `DecisionTraceWriter` and emits the canonical
/// MAGIC + VERSION + event stream whenever it reaches CDCL. On preprocessing-
/// only UNSAT (e.g., two contradictory unit assertions reduced by Tseitin /
/// early propagation) the DPLL(T) pipeline can short-circuit before the SAT
/// solver is ever constructed — leaving the trace file absent and breaking
/// `--replay` round-trip.
///
/// The normal response path settles the trace immediately before publishing
/// its verdict. This EOF/`exit` backstop handles runs that constructed no
/// response line: if no SAT solver was constructed, it appends a minimal
/// `Result` event through the retained descriptor. A populated pathname is
/// never accepted on its own: the file identity and terminal outcome must
/// belong to this invocation. A synthesized public result is not
/// replay-equivalent to the solver's raw result; those traces are detached and
/// zeroed through their retained descriptors instead of forging a terminal
/// event that replay cannot reproduce.
///
/// Part of `EXPLAINABILITY_AUDIT.md` Finding B.
fn maybe_write_minimal_decision_trace(transcript: &mut SmtTranscriptState) {
    let Some(path) = ay_core::trace_config().decision_trace_path.as_deref() else {
        return;
    };
    if !matches!(
        transcript.decision_trace_publication,
        DecisionTracePublication::Pending
    ) {
        return;
    }
    if ay_sat::decision_trace_suppressed_after_public_mismatch() {
        if let Err(error) = invalidate_decision_trace_for_public_mismatch(transcript) {
            safe_eprintln!("Error: {error}");
            std::process::exit(1);
        }
        return;
    }
    let Some(public_verdict) = transcript.public_verdict else {
        if let Err(error) = invalidate_pending_decision_trace(
            transcript,
            "the invocation completed without a public solver verdict",
        ) {
            safe_eprintln!("Error: {error}");
        }
        transcript.note_recoverable_error();
        return;
    };
    if !transcript.public_verdict_from_executor {
        if let Err(error) = invalidate_decision_trace_for_public_mismatch(transcript) {
            safe_eprintln!("Error: {error}");
            std::process::exit(1);
        }
        return;
    }
    debug_assert!(matches!(
        public_verdict,
        PublicVerdict::Sat | PublicVerdict::Unsat | PublicVerdict::Unknown
    ));
    match settle_authoritative_decision_trace(transcript, Some(path)) {
        Ok(Some(mut publication)) => publication.commit(),
        Ok(None) => {}
        Err(error) => {
            safe_eprintln!("Error: {error}");
            std::process::exit(1);
        }
    }
}

/// Invalidate a decision trace whose raw solver outcome diverges from the
/// public result. The executor must detach all persistent buffered writers
/// first. The retained same-run descriptor is truncated rather than unlinking
/// a pathname that an attacker could replace concurrently.
fn invalidate_non_authoritative_decision_trace(reason: &str) -> Result<(), String> {
    let Some(path) = ay_core::trace_config().decision_trace_path.as_deref() else {
        return Ok(());
    };
    ay_sat::suppress_decision_trace_after_public_mismatch();
    ay_sat::invalidate_reserved_decision_trace(path).map_err(|error| {
        format!(
            "decision trace is non-authoritative but could not be invalidated at {path}: {error}"
        )
    })?;
    safe_eprintln!("ay: decision trace invalidated because {reason}; replay is unavailable");
    Ok(())
}

fn invalidate_pending_decision_trace(
    transcript: &mut SmtTranscriptState,
    reason: &str,
) -> Result<(), String> {
    match transcript.decision_trace_publication {
        DecisionTracePublication::Settled(_) | DecisionTracePublication::Invalidated => {
            return Ok(());
        }
        DecisionTracePublication::Pending => {}
    }
    invalidate_non_authoritative_decision_trace(reason)?;
    transcript.decision_trace_publication = DecisionTracePublication::Invalidated;
    Ok(())
}

fn invalidate_decision_trace_for_public_mismatch(
    transcript: &mut SmtTranscriptState,
) -> Result<(), String> {
    invalidate_pending_decision_trace(
        transcript,
        "the public result differs from the raw solver result",
    )
}

fn print_synthesized_public_unknown(transcript: &mut SmtTranscriptState) -> bool {
    debug_assert_eq!(transcript.public_verdict, Some(PublicVerdict::Unknown));
    debug_assert!(!transcript.public_verdict_from_executor);
    // A synthesized result cannot be replay-equivalent to the solver's raw
    // trace. Retire the retained artifact before making UNKNOWN observable; if
    // path authentication/invalidation fails, do not leak the verdict.
    if let Err(error) = invalidate_decision_trace_for_public_mismatch(transcript) {
        eprintln_smt_error(error);
        return false;
    }
    print_regular_line(transcript, "unknown");
    super::VERDICT_PRINTED.store(true, std::sync::atomic::Ordering::SeqCst);
    if !z3_mode_enabled() {
        let reason = transcript
            .public_unknown_reason
            .as_deref()
            .unwrap_or("(incomplete external-result-boundary)");
        print_diagnostic_line(transcript, &render_public_unknown_reason(reason, false));
    }
    true
}

/// Inspect the executor's last Alethe proof and return `true` when the
/// terminal empty-clause derivation rides on an unverified `:rule trust`
/// fallback (either `AletheRule::Trust` or a trust-emitting
/// `TheoryLemmaKind`, e.g. `Generic`). See #8759.
fn terminal_trust_detected(executor: &Executor) -> bool {
    let trust_or_hole = executor
        .last_proof()
        .map(|p| ay_proof::terminal_trust_report(p).has_terminal_trust())
        .unwrap_or(false);
    // Leak-2: also downgrade when the terminal derivation rides on an `assume`
    // NOT backed by the problem's provenance (a laundered free axiom). The
    // provenance set is executor state (original assertions + quantifier
    // expansions), so the check lives on the executor.
    //
    // TIER-0 leak: also downgrade when the proof references sequence-theory
    // content (`Seq`-sorted terms). Such a proof can be clean (zero hole/trust,
    // no foreign assume — e.g. a `seq.nth` term forced to two distinct integer
    // constants collapses to a pure `la_generic`/`resolution` chain) yet is NOT
    // independently checkable: carcara cannot parse the `Seq` sort, no
    // firewall-Lean lemma covers sequences, and there is no DRAT lane. Shipping
    // it bare under `--strict-proofs` would accept an uncheckable proof, a
    // §0-class certification leak.
    trust_or_hole
        || executor.unsat_proof_terminal_foreign_assume()
        || executor.unsat_proof_references_uncheckable_seq_theory()
}

fn invalidate_artifacts_for_rejected_result() {
    if ay_core::trace_config().dump_bv_cnf_path.is_none() {
        return;
    }
    if let Err(error) = Executor::invalidate_bv_cnf_export_for_rejected_check() {
        eprintln_smt_error(format!(
            "artifact export failed while invalidating a rejected result: {error}"
        ));
    }
}

/// Canonical transition after dropping a command that could change the
/// problem. Revoke both CLI and executor authority immediately, including
/// persisted decision/CNF artefacts; waiting for a later check-sat would leave
/// stale get-model/get-proof queries and EOF emitters observable in the gap.
fn mark_problem_incomplete(executor: &mut Executor, transcript: &mut SmtTranscriptState) {
    transcript.mark_incomplete();
    executor.replace_last_result_with_unknown(UnknownReason::Incomplete);
    invalidate_artifacts_for_rejected_result();
    if let Err(error) = invalidate_decision_trace_for_public_mismatch(transcript) {
        eprintln_smt_error(error);
        transcript.note_recoverable_error();
    }
}

/// Fail closed after an unwind crossed the executor boundary.
///
/// A caught panic says nothing about how far the command mutated internal
/// state. Even a query can populate caches or partially consume a decision, so
/// the executor is no longer authoritative for subsequent verdicts. Keep the
/// session poisoned until a successfully executed full `(reset)` rebuilds the
/// problem epoch.
fn handle_executor_panic(
    executor: &mut Executor,
    cmd: &Command,
    transcript: &mut SmtTranscriptState,
) -> bool {
    let is_decision_query = matches!(cmd, Command::CheckSat | Command::CheckSatAssuming(_));
    mark_problem_incomplete(executor, transcript);

    if is_decision_query {
        update_transcript_state_after_command(transcript, cmd);
        transcript.record_synthesized_unknown("\"internal solver error\"");
        if ay_core::trace_config().dump_bv_cnf_path.is_some() {
            eprintln_smt_error(
                "artifact export failed: solver panicked before the current BV CNF certificate could be finalized",
            );
            return false;
        }
        if !print_synthesized_public_unknown(transcript) {
            return false;
        }
    } else {
        print_regular_line(transcript, "(error \"internal solver error\")");
        // Do not apply transcript effects for a command whose completion is
        // unknown. In particular, a panicking `(reset)` must not clear poison.
        transcript.note_recoverable_error();
    }
    true
}

/// Execute a command and print the result.
///
/// This centralizes executor.execute result handling to avoid duplication.
/// Output is printed to stdout, errors to stderr in SMT-LIB format.
///
/// Per SMT-LIB 2.6, when check-sat returns "unknown", the solver SHOULD
/// emit `(:reason-unknown ...)` so the user knows why satisfiability could
/// not be determined. We emit this to stderr automatically after printing
/// the "unknown" result to stdout.
/// z3's exact redefinition error text if `cmd` redeclares/redefines an existing
/// name in a way z3 4.15.4 rejects, else `None`. Covers `declare-const`,
/// `declare-fun`, `define-fun`, `define-fun-rec`, and `define-funs-rec` (each
/// with z3's distinct collision/overload rules); the message BODY is returned
/// (the CLI prepends the source position). See the call site in
/// [`execute_and_print`] for the full z3-parity rationale.
fn redefinition_error_for_command(executor: &mut Executor, cmd: &Command) -> Option<String> {
    match cmd {
        Command::DeclareConst(name, sort) => {
            executor
                .context_mut()
                .redefinition_error(IntroKind::Declare, name, &[], sort)
        }
        Command::DeclareFun(name, args, ret) => {
            executor
                .context_mut()
                .redefinition_error(IntroKind::Declare, name, args, ret)
        }
        Command::DefineFun(name, params, ret, _) => {
            let arg_sorts: Vec<_> = params.iter().map(|(_, s)| s.clone()).collect();
            executor
                .context_mut()
                .redefinition_error(IntroKind::Macro, name, &arg_sorts, ret)
        }
        Command::DefineFunRec(name, params, ret, _) => {
            let arg_sorts: Vec<_> = params.iter().map(|(_, s)| s.clone()).collect();
            executor
                .context_mut()
                .redefinition_error(IntroKind::Recursive, name, &arg_sorts, ret)
        }
        Command::DefineFunsRec(decls, _) => {
            // A batch defines several names at once; z3 reports the first that
            // collides. Check each against the pre-command context.
            for (name, params, ret) in decls {
                let arg_sorts: Vec<_> = params.iter().map(|(_, s)| s.clone()).collect();
                if let Some(msg) = executor.context_mut().redefinition_error(
                    IntroKind::Recursive,
                    name,
                    &arg_sorts,
                    ret,
                ) {
                    return Some(msg);
                }
            }
            None
        }
        _ => None,
    }
}

fn execute_and_print(
    executor: &mut Executor,
    cmd: &Command,
    transcript: &mut SmtTranscriptState,
    // z3 `-model` inline emission: only the streaming path sets this. The
    // non-incremental file path appends a literal `(get-model)` instead, so it
    // passes false to avoid emitting the model twice.
    emit_z3_model_inline: bool,
) -> bool {
    if (ay_core::trace_config().dump_bv_cnf_path.is_some()
        || ay_core::trace_config().decision_trace_path.is_some())
        && matches!(
            cmd,
            Command::SetOption(keyword, _)
                if matches!(
                    keyword_key(keyword),
                    "regular-output-channel" | "diagnostic-output-channel"
                )
        )
    {
        if ay_core::trace_config().dump_bv_cnf_path.is_some() {
            if let Err(error) = Executor::invalidate_bv_cnf_export_for_rejected_check() {
                eprintln_smt_error(error.to_string());
            }
        }
        eprintln_smt_error(
            "artifact export failed: decision/CNF tracing forbids dynamic SMT-LIB output channels because channel publication could replace a certificate path",
        );
        transcript.note_recoverable_error();
        return false;
    }

    if maybe_handle_cli_transcript_command(transcript, cmd) {
        return true;
    }

    if matches!(cmd, Command::CheckSat | Command::CheckSatAssuming(_)) {
        if transcript.decision_queries_seen > 0
            && ay_core::trace_config().decision_trace_path.is_some()
        {
            if let Err(error) = invalidate_pending_decision_trace(
                transcript,
                "the SMT-LIB session requested more than one decision query",
            ) {
                eprintln_smt_error(error);
            }
            eprintln_smt_error(
                "--decision-trace supports exactly one check-sat/check-sat-assuming query per invocation",
            );
            transcript.note_recoverable_error();
            return false;
        }
        transcript.decision_queries_seen = transcript.decision_queries_seen.saturating_add(1);
    }

    // z3 4.15.4 rejects a redeclaration/redefinition of a name that collides
    // with an existing binding: e.g. `invalid declaration, <kind> '<name>'
    // (with the given signature) already declared` for a same-signature
    // declare, `named expression already defined` for a `define-fun` macro,
    // etc. The offending command is DROPPED (the original binding survives),
    // execution continues, and the run exits 1 at EOF. Overloads z3 permits
    // (a different signature, or a recfun/declare cross pair) are accepted. We
    // detect this at the text-command layer, BEFORE executor.execute, so the
    // programmatic ay-dpll API can enforce its own stricter no-name-reuse
    // contract without changing the CLI's z3-compatible diagnostics. No taint
    // is applied: dropping the redeclaration keeps the original binding, so a
    // pending check-sat retains full z3 verdict parity (e.g. `(= x 1)` then a
    // dropped redeclare then `(= x 2)` is unsat over the SAME x, not a
    // fresh-var sat). See [`redefinition_error_for_command`] for the exact
    // collision matrix. (#P0.3)
    if let Some(message) = redefinition_error_for_command(executor, cmd) {
        print_regular_line(
            transcript,
            &source_error(current_source_last_token_position(transcript), &message),
        );
        transcript.note_recoverable_error();
        return true;
    }

    // z3 accepts some definition overloads (different arity/signature), but
    // the frontend's macro/recursive-definition tables are keyed only by the
    // surface name. Executing such a command would overwrite one binding and
    // let later uses silently select the wrong definition. The collision gate
    // above has already removed cases z3 rejects; conservatively taint every
    // remaining definition that collides with a pre-command binding so the
    // next decision is `unknown`, never a verdict over conflated semantics.
    let unrepresentable_definition_overload = match cmd {
        Command::DefineFun(name, _, _, _) | Command::DefineFunRec(name, _, _, _) => {
            executor.context_mut().has_symbol_binding(name)
        }
        Command::DefineFunsRec(declarations, _) => declarations
            .iter()
            .any(|(name, _, _)| executor.context_mut().has_symbol_binding(name)),
        _ => false,
    };
    if unrepresentable_definition_overload {
        mark_problem_incomplete(executor, transcript);
    }

    // z3 ACCEPTS a `declare-const`/`declare-fun` whose name is already a
    // recursive function (`define-fun-rec`/`define-funs-rec`): it creates an
    // overload and resolves each later reference per-signature (emitting an
    // `ambiguous constant reference` error only when a use is truly ambiguous).
    // AY keeps a single binding per name and cannot represent that overload —
    // it would silently resolve later uses to the wrong `g` and can answer
    // `unsat` where z3 answers `sat`. Since we cannot reproduce z3's semantics
    // soundly, fail closed: mark the problem incomplete so the pending
    // check-sat degrades to `unknown` (always sound) instead of a wrong verdict.
    // This is malformed input z3 itself flags; `unknown` beats a wrong `unsat`.
    // (#P0.3)
    if let Command::DeclareConst(name, _) | Command::DeclareFun(name, _, _) = cmd {
        if executor.context_mut().is_recursive_fun(name) {
            mark_problem_incomplete(executor, transcript);
        }
    }

    // (get-interpolant A B) / (compute-interpolant A B) are computed by the
    // ay-chc Craig/Farkas machinery, which the DPLL(T) executor cannot reach.
    // Intercept them here, before executor.execute(), using the declared sorts
    // from the elaboration context.
    if let Command::GetInterpolant(a, b) | Command::ComputeInterpolant(a, b) = cmd {
        print_regular_line(transcript, &compute_interpolant_output(executor, a, b));
        update_transcript_state_after_command(transcript, cmd);
        return true;
    }

    // SOUNDNESS BACKSTOP (#match-soundness, Part 1): if any problem-contributing
    // command was discarded (failed to parse or elaborate), the executor's
    // assertion set is an incomplete subset of the real problem. A dropped
    // constraint can only flip UNSAT into SAT, so a decision query must fail
    // closed to `unknown` rather than answer definitively on the remainder.
    // Generic over the discarded construct, so this class of unsoundness cannot
    // recur for ANY unsupported syntax.
    if transcript.is_incomplete() && matches!(cmd, Command::CheckSat | Command::CheckSatAssuming(_))
    {
        executor.replace_last_result_with_unknown(UnknownReason::Incomplete);
        update_transcript_state_after_command(transcript, cmd);
        transcript.record_synthesized_unknown("\"a problem-contributing command was discarded\"");
        if let Err(error) = invalidate_decision_trace_for_public_mismatch(transcript) {
            eprintln_smt_error(error);
            return false;
        }
        if let Err(error) = Executor::invalidate_bv_cnf_export_for_rejected_check() {
            eprintln_smt_error(error.to_string());
            return false;
        }
        if ay_core::trace_config().dump_bv_cnf_path.is_some() {
            eprintln_smt_error(
                "artifact export failed: --dump-bv-cnf cannot certify a transcript after a problem-contributing command was discarded",
            );
            return false;
        }
        return print_synthesized_public_unknown(transcript);
    }

    if !maybe_enable_z3_default_assignment_query(executor, cmd) {
        eprintln_smt_error("failed to enable assignment collection for get-assignment".to_string());
        return false;
    }

    let is_decision_query = matches!(cmd, Command::CheckSat | Command::CheckSatAssuming(_));
    if is_decision_query {
        // A failed or panicking new decision must not leave the preceding
        // public result authoritative.
        transcript.clear_public_result();
    }

    // Competition robustness: an internal solver bug must NEVER crash the process
    // (a panic = the whole file/run dies = strictly worse than a wrong answer).
    // Catch any unwinding panic during execution and convert it to a sound,
    // non-crashing outcome — `unknown` for a decision query (always sound), a
    // recoverable `(error ...)` otherwise — then continue with the remaining
    // commands. The release profile is intentionally `panic = "unwind"` so this
    // containment works. Found by the diff_fuzz seq sort-interning crash (a valid
    // QF_SLIA input panicked `mk_eq expects same sort`, exiting the process 101).
    let exec_result =
        match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| executor.execute(cmd))) {
            Ok(r) => r,
            Err(_panic) => return handle_executor_panic(executor, cmd, transcript),
        };
    match exec_result {
        Ok(Some(output)) => {
            // Strict-proof mode: downgrade UNSAT to Unknown when the terminal
            // derivation chain contains a `:rule trust` fallback (#8759).
            // The proof is generated internally regardless of `--proof` because
            // `new_executor()` forces `set_produce_proofs(true)` under strict.
            if output == "unsat" && strict_proofs_enabled() && terminal_trust_detected(executor) {
                let downgraded = executor.reject_last_unsat_as_unknown();
                debug_assert!(downgraded, "strict-proof gate started from UNSAT");
                update_transcript_state_after_command(transcript, cmd);
                transcript.reject_result_certification("(incomplete proof-trusted)");
                invalidate_artifacts_for_rejected_result();
                if let Err(error) = invalidate_decision_trace_for_public_mismatch(transcript) {
                    eprintln_smt_error(error);
                    return false;
                }
                return print_synthesized_public_unknown(transcript);
            }
            // Firewall result gate (`--verify-firewall`). Today's emitters prove
            // diagnostic LOCAL theory obligations only; even when every such
            // lemma kernel-checks, they do not bind the full query/refutation,
            // so this path always downgrades to sound `unknown`. Per-lemma
            // diagnostics go to stderr.
            if output == "unsat" && verify_firewall_enabled() {
                let outcome = firewall_verify::diagnose_firewall_for_unsat(executor);
                firewall_verify::report(&outcome.results);
                let downgraded = executor.reject_last_unsat_as_unknown();
                debug_assert!(downgraded, "firewall gate started from UNSAT");
                update_transcript_state_after_command(transcript, cmd);
                transcript.reject_result_certification(outcome.reason.clone());
                invalidate_artifacts_for_rejected_result();
                if let Err(error) = invalidate_decision_trace_for_public_mismatch(transcript) {
                    eprintln_smt_error(error);
                    return false;
                }
                return print_synthesized_public_unknown(transcript);
            }
            // The executor has already finalized and verified the private BV
            // CNF/DRAT pair before returning `unsat`; the CLI only reports that
            // certification. Library and CLI callers therefore share the same
            // fail-closed result boundary.
            if output == "unsat" && self_check_enabled() && executor.bv_drat_self_cert_pending() {
                print_diagnostic_line(
                    transcript,
                    "c BV unsat self-certified via native DRAT check",
                );
            }
            let raw_output = output;
            let rendered_output = z3_compat_output_for_command(transcript, cmd, &raw_output);
            update_transcript_state_after_command(transcript, cmd);
            if is_decision_query {
                match raw_output.as_str() {
                    "sat" => transcript.record_public_verdict(PublicVerdict::Sat),
                    "unsat" => transcript.record_public_verdict(PublicVerdict::Unsat),
                    "unknown" => {
                        transcript.record_executor_unknown(
                            executor.get_reason_unknown().map(|r| r.to_string()),
                        );
                    }
                    _ => {}
                }
            }
            if let Some(output) = rendered_output {
                let decision_trace_path = ay_core::trace_config().decision_trace_path.as_deref();
                let emitted_verdict = match publish_rendered_executor_output(
                    transcript,
                    is_decision_query,
                    &raw_output,
                    output,
                    decision_trace_path,
                    print_regular_line,
                ) {
                    Ok(emitted_verdict) => emitted_verdict,
                    Err(error) => {
                        safe_eprintln!("Error: {error}");
                        return false;
                    }
                };
                // #verdict-latch: once ANY verdict (sat/unsat/unknown) is on
                // stdout, the timeout/SIGTERM fallbacks must never print a
                // second, potentially contradictory one. Found via QF_ALIA
                // pp-dmem2: the arrays->LIA rescue's `unsat` was followed by
                // a synthesized `unknown` when the internal timeout fired
                // during default-proof materialization.
                if emitted_verdict {
                    super::mark_verdict_printed();
                }
            }
            // SMT-LIB compliance: emit reason-unknown to stderr when
            // check-sat produces "unknown", so users always know why.
            if raw_output == "unknown" {
                // Mark that "unknown" has been printed to prevent duplicate
                // output from exit_if_timed_out (#8674).
                super::VERDICT_PRINTED.store(true, std::sync::atomic::Ordering::SeqCst);
                if !z3_mode_enabled() {
                    if let Some(reason) = executor.get_reason_unknown() {
                        print_diagnostic_line(transcript, &format!("(:reason-unknown {reason})"));
                    } else {
                        print_diagnostic_line(transcript, "(:reason-unknown unknown)");
                    }
                }
            }
            // z3 `-model`: emit the model after a satisfiable `check-sat`, as if
            // `(get-model)` followed. Streaming/incremental only (the file path
            // appends a literal `(get-model)`); output-only, verdict unchanged.
            if emit_z3_model_inline
                && z3_model_enabled()
                && matches!(cmd, Command::CheckSat | Command::CheckSatAssuming(_))
                && executor.last_result_is_sat()
            {
                if let Ok(Some(mut model)) = executor.execute(&Command::GetModel) {
                    if !model.trim_start().starts_with("(error") {
                        // Same head-strip as the explicit-`(get-model)` path: z3
                        // 4.15.4 / SMT-LIB 2.6 emit a bare `( <define-fun>* )`,
                        // not AY's legacy `(model …)` head. Printer-only.
                        if z3_mode_enabled() && model.starts_with("(model\n") {
                            model = format!("(\n{}", &model["(model\n".len()..]);
                        }
                        print_regular_line(transcript, &model);
                    }
                }
            }
            true
        }
        Ok(None) => {
            update_transcript_state_after_command(transcript, cmd);
            maybe_print_success(transcript);
            true
        }
        Err(e) => {
            let message = e.to_string();
            if is_decision_query {
                executor.replace_last_result_with_unknown(UnknownReason::InternalError);
                update_transcript_state_after_command(transcript, cmd);
                transcript.record_synthesized_unknown("(incomplete decision-execution-error)");
                invalidate_artifacts_for_rejected_result();
                if let Err(error) = invalidate_decision_trace_for_public_mismatch(transcript) {
                    eprintln_smt_error(error);
                    return false;
                }
            }
            // Resource limit while expanding a `define-fun-rec` over a symbolic
            // argument (unbounded unfolding). z3 decides these with real
            // recursive-function support; AY cannot unfold an unbounded recursion.
            // Exiting 1 with NO verdict on stdout is the worst possible shape for
            // a driver, so instead taint the problem to fail closed: the pending
            // `check-sat` answers `unknown` (always sound — a dropped constraint
            // can only turn UNSAT into SAT) via the generic is_incomplete() gate,
            // and the run still exits 0. The concrete/ground recursion case is
            // unaffected (it unfolds fully and returns a real verdict). (matches
            // the burndown "every check-sat emits a verdict" principle.)
            if message.contains("recursion depth limit") && command_contributes_to_problem(cmd) {
                eprintln_smt_error(message);
                mark_problem_incomplete(executor, transcript);
                if is_decision_query && !print_synthesized_public_unknown(transcript) {
                    return false;
                }
                return true;
            }
            if maybe_handle_recoverable_execution_error(transcript, cmd, &message) {
                // SOUNDNESS: the command was dropped after a recoverable
                // elaboration failure (e.g. an `assert` over an unknown symbol).
                // If it contributed to the problem, taint so check-sat answers
                // `unknown` rather than a wrong sat on the remaining assertions.
                //
                // Exception: an IGNORED unsupported `(set-logic X)` is handled
                // above with the documented z3-parity contract — solving
                // CONTINUES with ALL semantics (no constraint or declaration is
                // dropped, the logic is simply treated as never set), so it
                // must not taint the session to `unknown`. Tainting here made
                // the following `check-sat` answer `unknown` on a fully intact
                // problem, contradicting the handler's own contract.
                if command_contributes_to_problem(cmd) && !matches!(cmd, Command::SetLogic(_)) {
                    mark_problem_incomplete(executor, transcript);
                }
                if is_decision_query && !print_synthesized_public_unknown(transcript) {
                    return false;
                }
                return true;
            }
            eprintln_smt_error(message);
            if is_decision_query {
                let _ = print_synthesized_public_unknown(transcript);
            }
            false
        }
    }
}

/// Compute the SMT-LIB output for `(get-interpolant A B)`.
///
/// Returns the interpolant as a rendered S-expression on success, or a
/// `(error "...")` message when the request falls outside the supported
/// fragment or no sound interpolant can be produced. Soundness first: a wrong
/// interpolant is never emitted — failures are surfaced as errors.
fn compute_interpolant_output(executor: &Executor, a: &Term, b: &Term) -> String {
    // Resolve declared symbol sorts from the elaboration context so the
    // candidate interpolant is validated in the right arithmetic theory.
    let ctx = executor.context();
    let resolver = |name: &str| -> Option<ay_chc::ChcSort> {
        ctx.symbol_sort(name)
            .map(|s| ay_chc::ChcSort::from(s.clone()))
    };

    match ay_chc::compute_smt_interpolant(a, b, &resolver) {
        Ok(interpolant) => interpolant.to_string(),
        Err(ay_chc::InterpolantError::Unsupported(msg)) => {
            format!("(error \"{}\")", escape_string_contents(&msg))
        }
    }
}

/// Generate human-readable explanation if `--explain` is active.
///
/// Called after all commands have been processed in non-interactive mode.
/// The public transcript verdict is authoritative. Executor details are used
/// only when they belong to that accepted public verdict; synthesized or
/// mismatched outcomes receive a generic UNKNOWN explanation. On UNSAT, the
/// Phase 1 reason-code block (#8693) is also emitted: in `plain` format it
/// prepends to the existing English walk-through, in `json` format it replaces
/// the walk-through entirely (tooling consumers want a clean line).
fn maybe_explain(executor: &mut Executor, transcript: &SmtTranscriptState) {
    if !EXPLAIN_ENABLED.load(std::sync::atomic::Ordering::Relaxed) {
        return;
    }
    let is_json = EXPLAIN_FORMAT_JSON.load(std::sync::atomic::Ordering::Relaxed);
    if !executor_result_matches_public_verdict(executor, transcript) {
        let reason = if transcript.result_certification_rejected {
            "mandatory-result-certification-failed"
        } else {
            transcript
                .public_unknown_reason
                .as_deref()
                .unwrap_or("no-authoritative-public-result")
        };
        if is_json {
            safe_println!(
                "{}",
                serde_json::json!({
                    "result": "unknown",
                    "reason": reason
                })
            );
        } else {
            safe_println!();
            safe_println!("=== Explanation (UNKNOWN) ===");
            safe_println!();
            safe_println!(
                "No executor result is authoritative for the latest public outcome; reporting UNKNOWN ({reason})."
            );
        }
        return;
    }
    let is_unsat = executor.last_result_is_unsat();
    // Phase 1 reason-code block runs first on UNSAT. Unknown and SAT fall
    // through to the existing English explainer.
    if is_unsat {
        let format = if is_json {
            explain_reason::ExplainFormat::Json
        } else {
            explain_reason::ExplainFormat::Plain
        };
        explain_reason::emit_unsat_reason(executor, format);
        // JSON consumers want a single parseable line — skip the rich English
        // block, which is multi-line prose.
        if is_json {
            return;
        }
    }
    explain::explain_result(executor);
}

fn executor_result_matches_public_verdict(
    executor: &Executor,
    transcript: &SmtTranscriptState,
) -> bool {
    if !transcript.public_verdict_from_executor {
        return false;
    }
    match transcript.public_verdict {
        Some(PublicVerdict::Sat) => executor.last_result_is_sat(),
        Some(PublicVerdict::Unsat) => executor.last_result_is_unsat(),
        Some(PublicVerdict::Unknown) => executor.last_result_is_unknown(),
        None => false,
    }
}

/// Render a recognized SAT solution if `--visualize` is active.
///
/// This issues an internal `(get-model)` query after the final `check-sat`.
/// The query is presentation-only and is not printed unless the formatter
/// recognizes a supported board-shaped model.
fn maybe_visualize(
    input: &str,
    executor: &mut Executor,
    transcript: &SmtTranscriptState,
    format: Option<VisualizationFormat>,
) {
    let Some(format) = format else {
        return;
    };
    if transcript.public_verdict != Some(PublicVerdict::Sat) {
        return;
    }

    let Ok(Some(model)) = executor.execute(&Command::GetModel) else {
        return;
    };
    if model.trim_start().starts_with("(error") {
        return;
    }
    if let Some(rendered) = render_solution_visualization(input, &model, format) {
        safe_println!("{rendered}");
    }
}

const SMT_BV_BATCH_TEMPLATE_APPLICATION_COUNTER: &str = "smt_bv_batch_template_applications";
const SMT_LRA_BASIS_REGION_ARTIFACT: &str = "smt-lra-basis-regions";
const SMT_LRA_BASIS_REGION_APPLICATION_COUNTER: &str =
    "solver_program.lra_basis_region.batch_native_applies";
const SMT_LRA_BASIS_REGION_PROFILE_ENABLED_COUNTER: &str =
    "solver_program.profile.lra_basis_region.enabled";
const SMT_LRA_BASIS_REGION_BOUNDARY_CHECKS_COUNTER: &str =
    "solver_program.lra_basis_region.boundary_checks";
const SMT_LRA_BASIS_REGION_REQUESTS_QUEUED_COUNTER: &str =
    "solver_program.lra_basis_region.requests_queued";
const SMT_LRA_SPARSE_SUBSTITUTE_ARTIFACT: &str = "smt-lra-sparse-substitute";
const SMT_LRA_SPARSE_SUBSTITUTE_APPLICATION_COUNTER: &str =
    "lra_external_codegen_backend_substitute_native_applies";
const SMT_LRA_SPARSE_SUBSTITUTE_LEGACY_APPLICATION_COUNTER: &str =
    "lra_external_codegen_backend_substitute_applies";
const SMT_LRA_SPARSE_SUBSTITUTE_WRAPPER_COUNTER: &str =
    "lra_external_codegen_backend_substitute_wrapper_applies";
const SMT_LRA_SPARSE_SUBSTITUTE_NATIVE_EMPTY_TARGET_COUNTER: &str =
    "lra_external_codegen_backend_substitute_native_empty_target_applies";
const SMT_LRA_SPARSE_SUBSTITUTE_NATIVE_NON_EMPTY_TARGET_COUNTER: &str =
    "lra_external_codegen_backend_substitute_native_non_empty_target_applies";
const SMT_LRA_SPARSE_SUBSTITUTE_RUNTIME_COUNTER: &str =
    "lra_external_codegen_backend_substitute_runtime_applies";
const SMT_LRA_SPARSE_SUBSTITUTE_EVIDENCE_WAIT_ATTEMPTS_COUNTER: &str =
    "lra_external_codegen_backend_substitute_evidence_wait_attempts";
const SMT_LRA_SPARSE_SUBSTITUTE_EVIDENCE_WAIT_HITS_COUNTER: &str =
    "lra_external_codegen_backend_substitute_evidence_wait_hits";
const SMT_LRA_SPARSE_SUBSTITUTE_EVIDENCE_WAIT_TIMEOUTS_COUNTER: &str =
    "lra_external_codegen_backend_substitute_evidence_wait_timeouts";
const SMT_LRA_SPARSE_SUBSTITUTE_EVIDENCE_WAIT_POLLS_COUNTER: &str =
    "lra_external_codegen_backend_substitute_evidence_wait_polls";
const SMT_LRA_SPARSE_SUBSTITUTE_EVIDENCE_WAIT_US_TOTAL_COUNTER: &str =
    "lra_external_codegen_backend_substitute_evidence_wait_us_total";
const SMT_LRA_SPARSE_SUBSTITUTE_PROFILE_ENABLED_COUNTER: &str =
    "solver_program.profile.lra_sparse_substitute.enabled";
const SMT_NATIVE_CODE_HELPER_APPLICATION_COUNTER: &str = "smt_native_code_helper_applications";

fn insert_unsupported_smt_jit_application_counters(run_stats: &mut stats_output::RunStatistics) {
    run_stats.insert(SMT_BV_BATCH_TEMPLATE_APPLICATION_COUNTER, 0);
    run_stats.insert(SMT_NATIVE_CODE_HELPER_APPLICATION_COUNTER, 0);
}

fn trimmed_env_value(name: &str) -> Option<String> {
    std::env::var(name)
        .ok()
        .map(|value| value.trim().to_string())
        .filter(|value| !value.is_empty())
}

fn smt_competition_jit_candidate_mode() -> String {
    trimmed_env_value("AY_COMPETITION_JIT_CANDIDATE_MODE")
        .or_else(|| trimmed_env_value("AY_COMPETITION_JIT_MODE"))
        .unwrap_or_else(|| "solver-program".to_string())
}

fn attach_smt_lra_competition_jit_for_artifact(
    run_stats: &mut stats_output::RunStatistics,
    artifact_id: &str,
    candidate_mode: &str,
) {
    let application_counter = match artifact_id {
        SMT_LRA_BASIS_REGION_ARTIFACT => {
            if run_stats
                .counters
                .get(SMT_LRA_BASIS_REGION_PROFILE_ENABLED_COUNTER)
                .copied()
                != Some(1)
            {
                return;
            }
            // #9601: promotion is gated on actual native batch substitute
            // applications; boundary/request counters remain telemetry.
            SMT_LRA_BASIS_REGION_APPLICATION_COUNTER
        }
        SMT_LRA_SPARSE_SUBSTITUTE_ARTIFACT => {
            if !run_stats
                .counters
                .contains_key(SMT_LRA_SPARSE_SUBSTITUTE_PROFILE_ENABLED_COUNTER)
                && !run_stats
                    .counters
                    .contains_key(SMT_LRA_SPARSE_SUBSTITUTE_APPLICATION_COUNTER)
            {
                return;
            }
            SMT_LRA_SPARSE_SUBSTITUTE_APPLICATION_COUNTER
        }
        _ => return,
    };

    let application_count = run_stats
        .counters
        .get(application_counter)
        .copied()
        .unwrap_or(0);
    run_stats.competition_jit = Some(stats_output::CompetitionJitEvidence {
        track: "smt".to_string(),
        artifact_id: artifact_id.to_string(),
        candidate_mode: candidate_mode.to_string(),
        application_counter: Some(stats_output::CompetitionJitApplicationCounter {
            key: application_counter.to_string(),
            value: application_count,
        }),
    });
}

fn attach_smt_lra_competition_jit(run_stats: &mut stats_output::RunStatistics) {
    let requested_artifact = trimmed_env_value("AY_COMPETITION_JIT_ARTIFACT")
        .unwrap_or_else(|| SMT_LRA_BASIS_REGION_ARTIFACT.to_string());
    let candidate_mode = smt_competition_jit_candidate_mode();
    attach_smt_lra_competition_jit_for_artifact(
        run_stats,
        requested_artifact.as_str(),
        candidate_mode.as_str(),
    );
}

/// Print SMT-LIB executor statistics to stderr (Z3 `-st` style)
/// plus the canonical RunStatistics envelope.
fn print_smt_stats(
    executor: &Executor,
    transcript: &SmtTranscriptState,
    formula_stats: Option<&FormulaStats>,
    stats_cfg: stats_output::StatsConfig,
) {
    if stats_cfg.human {
        let dpll_stats = executor.statistics();
        safe_eprintln!("{dpll_stats}");
        if let Some(formula_stats) = formula_stats {
            safe_eprintln!("{formula_stats}");
        }
    }

    // Canonical envelope
    let dpll_stats = executor.statistics();
    let elapsed = super::global_elapsed();
    let result_str = match transcript.public_verdict {
        Some(PublicVerdict::Sat) => "sat",
        Some(PublicVerdict::Unsat) => "unsat",
        Some(PublicVerdict::Unknown) | None => "unknown",
    };
    let mut run_stats =
        stats_output::RunStatistics::new(stats_output::SolveMode::Smt, result_str, elapsed);
    run_stats.insert("conflicts", dpll_stats.conflicts);
    run_stats.insert("decisions", dpll_stats.decisions);
    run_stats.insert("propagations", dpll_stats.propagations);
    run_stats.insert("restarts", dpll_stats.restarts);
    run_stats.insert("smt.theory_conflicts", dpll_stats.theory_conflicts);
    run_stats.insert("smt.theory_propagations", dpll_stats.theory_propagations);
    // #8153: Proof/explainability stats
    if dpll_stats.proof_clause_count > 0 {
        run_stats.insert("smt.proof_clause_count", dpll_stats.proof_clause_count);
        run_stats.insert("smt.proof_complete", u64::from(dpll_stats.proof_complete));
    }
    if dpll_stats.annotated_core_entries > 0 {
        run_stats.insert(
            "smt.annotated_core_entries",
            dpll_stats.annotated_core_entries,
        );
        run_stats.insert(
            "smt.annotated_core_theories",
            dpll_stats.annotated_core_theories,
        );
    }
    // #8640: Resource consumption statistics.
    run_stats.insert(
        "resource.rss_peak_bytes",
        ay_sys::current_rss_bytes() as u64,
    );
    run_stats.insert(
        "resource.memory_limit_bytes",
        ay_sys::get_process_memory_limit() as u64,
    );
    run_stats.insert("resource.term_bytes", dpll_stats.term_bytes);
    run_stats.insert("resource.term_count", dpll_stats.term_count);
    run_stats.insert("resource.learned_clauses", dpll_stats.learned_clauses);
    if dpll_stats.refinement_count > 0 {
        run_stats.insert("resource.refinement_count", dpll_stats.refinement_count);
    }
    run_stats.insert("time.total_ms", elapsed.as_millis() as u64);

    // #8165: Theory solver observability counters from extra stats
    for key in [
        "smt.no_rounds",
        "smt.unknown_returns",
        "smt.diseq_propagations",
        "smt.conflicts.lia",
        "smt.conflicts.lra",
        "smt.conflicts.euf",
        "smt.conflicts.arrays",
        "smt.checks.lia",
        "smt.checks.lra",
        "smt.checks.euf",
        "smt.checks.arrays",
        "arrays_candidate_pairs_calls",
        "arrays_candidate_pairs_generated",
        "arrays_candidate_pairs_memo_hits",
        "smt.props.lia",
        "smt.props.lra",
        "smt.props.euf",
        "smt.partial_clauses",
        "model_validation.checked",
        "model_validation.delegated",
        "model_validation.array_delegated",
        "model_validation.sat_fallback",
        "model_validation.total",
        "lra_external_codegen_backend_substitute_compile_attempts",
        "lra_external_codegen_backend_substitute_compilations",
        "lra_external_codegen_backend_substitute_compile_failures",
        "lra_external_codegen_backend_substitute_backoff_skips",
        "lra_external_codegen_backend_substitute_disabled_skips",
        "lra_external_codegen_backend_substitute_applies",
        "lra_external_codegen_backend_substitute_wrapper_applies",
        "lra_external_codegen_backend_substitute_native_applies",
        "lra_external_codegen_backend_substitute_native_empty_target_applies",
        "lra_external_codegen_backend_substitute_native_non_empty_target_applies",
        "lra_external_codegen_backend_substitute_runtime_applies",
        "lra_external_codegen_backend_substitute_fallback_applies",
        "lra_external_codegen_backend_substitute_overflow_fallbacks",
        "lra_external_codegen_backend_substitute_queue_submissions",
        "lra_external_codegen_backend_substitute_queue_installs",
        "lra_external_codegen_backend_substitute_queue_budget_rejects",
        "lra_external_codegen_backend_substitute_queue_dropped_stale",
        "lra_external_codegen_backend_substitute_queue_compile_us_total",
        "lra_external_codegen_backend_substitute_queue_compile_us_max",
        "lra_external_codegen_backend_substitute_queue_submit_to_install_us_total",
        "lra_external_codegen_backend_substitute_queue_submit_to_install_us_max",
        "lra_external_codegen_backend_substitute_evidence_wait_attempts",
        "lra_external_codegen_backend_substitute_evidence_wait_hits",
        "lra_external_codegen_backend_substitute_evidence_wait_timeouts",
        "lra_external_codegen_backend_substitute_evidence_wait_polls",
        "lra_external_codegen_backend_substitute_evidence_wait_us_total",
    ] {
        if let Some(v) = dpll_stats.get_int(key) {
            if v > 0 {
                run_stats.insert(key, v);
            }
        }
    }
    for (key, value) in &dpll_stats.extra {
        if !key.starts_with("solver_program.") {
            continue;
        }
        let ay_dpll::StatValue::Int(value) = value else {
            continue;
        };
        if *value > 0
            || key == "solver_program.schema_version"
            || key.starts_with("solver_program.profile.")
            || key == SMT_LRA_BASIS_REGION_APPLICATION_COUNTER
            || key == SMT_LRA_BASIS_REGION_BOUNDARY_CHECKS_COUNTER
            || key == SMT_LRA_BASIS_REGION_REQUESTS_QUEUED_COUNTER
        {
            run_stats.insert(key, *value);
        }
    }
    if trimmed_env_value("AY_COMPETITION_JIT_ARTIFACT").as_deref()
        == Some(SMT_LRA_SPARSE_SUBSTITUTE_ARTIFACT)
    {
        let applies = dpll_stats
            .get_int(SMT_LRA_SPARSE_SUBSTITUTE_APPLICATION_COUNTER)
            .unwrap_or(0);
        run_stats.insert(SMT_LRA_SPARSE_SUBSTITUTE_APPLICATION_COUNTER, applies);
        let legacy_applies = dpll_stats
            .get_int(SMT_LRA_SPARSE_SUBSTITUTE_LEGACY_APPLICATION_COUNTER)
            .unwrap_or(applies);
        run_stats.insert(
            SMT_LRA_SPARSE_SUBSTITUTE_LEGACY_APPLICATION_COUNTER,
            legacy_applies,
        );
        let wrapper_applies = dpll_stats
            .get_int(SMT_LRA_SPARSE_SUBSTITUTE_WRAPPER_COUNTER)
            .unwrap_or(0);
        run_stats.insert(SMT_LRA_SPARSE_SUBSTITUTE_WRAPPER_COUNTER, wrapper_applies);
        let native_empty_target_applies = dpll_stats
            .get_int(SMT_LRA_SPARSE_SUBSTITUTE_NATIVE_EMPTY_TARGET_COUNTER)
            .unwrap_or(0);
        run_stats.insert(
            SMT_LRA_SPARSE_SUBSTITUTE_NATIVE_EMPTY_TARGET_COUNTER,
            native_empty_target_applies,
        );
        let native_non_empty_target_applies = dpll_stats
            .get_int(SMT_LRA_SPARSE_SUBSTITUTE_NATIVE_NON_EMPTY_TARGET_COUNTER)
            .unwrap_or(0);
        run_stats.insert(
            SMT_LRA_SPARSE_SUBSTITUTE_NATIVE_NON_EMPTY_TARGET_COUNTER,
            native_non_empty_target_applies,
        );
        let runtime_applies = dpll_stats
            .get_int(SMT_LRA_SPARSE_SUBSTITUTE_RUNTIME_COUNTER)
            .unwrap_or(0);
        run_stats.insert(SMT_LRA_SPARSE_SUBSTITUTE_RUNTIME_COUNTER, runtime_applies);
        for wait_counter in [
            SMT_LRA_SPARSE_SUBSTITUTE_EVIDENCE_WAIT_ATTEMPTS_COUNTER,
            SMT_LRA_SPARSE_SUBSTITUTE_EVIDENCE_WAIT_HITS_COUNTER,
            SMT_LRA_SPARSE_SUBSTITUTE_EVIDENCE_WAIT_TIMEOUTS_COUNTER,
            SMT_LRA_SPARSE_SUBSTITUTE_EVIDENCE_WAIT_POLLS_COUNTER,
            SMT_LRA_SPARSE_SUBSTITUTE_EVIDENCE_WAIT_US_TOTAL_COUNTER,
        ] {
            let value = dpll_stats.get_int(wait_counter).unwrap_or(0);
            run_stats.insert(wait_counter, value);
        }
    }
    insert_unsupported_smt_jit_application_counters(&mut run_stats);
    attach_smt_lra_competition_jit(&mut run_stats);
    run_stats.emit(stats_cfg);
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::time::Duration;

    fn decision_trace_publication_test_lock() -> std::sync::MutexGuard<'static, ()> {
        static LOCK: std::sync::OnceLock<std::sync::Mutex<()>> = std::sync::OnceLock::new();
        LOCK.get_or_init(|| std::sync::Mutex::new(()))
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
    }

    #[test]
    fn mandatory_result_gates_disable_best_effort_proof_budget_and_ungated_routes() {
        let none = ResultGateRequests::default();
        assert!(should_budget_synthesized_proof(true, none));
        assert!(!should_budget_synthesized_proof(false, none));
        assert!(may_use_ungated_solver_route(none));

        for gates in [
            ResultGateRequests {
                strict_proofs: true,
                ..ResultGateRequests::default()
            },
            ResultGateRequests {
                self_check: true,
                ..ResultGateRequests::default()
            },
            ResultGateRequests {
                verify_firewall: true,
                ..ResultGateRequests::default()
            },
            ResultGateRequests {
                emit_firewall_lean: true,
                ..ResultGateRequests::default()
            },
            ResultGateRequests {
                explicit_verify_proof: true,
                ..ResultGateRequests::default()
            },
        ] {
            assert!(!should_budget_synthesized_proof(true, gates));
            assert!(!may_use_ungated_solver_route(gates));
        }
    }

    #[test]
    fn smt_verify_only_temp_proofs_are_not_written_without_a_checker() {
        let temp = ProofConfig::new_temp(
            "/tmp/verify-only.drat".to_string(),
            ProofFormat::Drat,
            false,
        );
        assert!(adapt_proof_config_for_smt(Some(&temp)).is_none());

        let persistent =
            ProofConfig::new_default("/tmp/default.alethe".to_string(), ProofFormat::Alethe);
        assert_eq!(
            adapt_proof_config_for_smt(Some(&persistent)),
            Some(persistent)
        );
    }

    #[test]
    fn explicit_verify_proof_rejects_routes_without_a_checker() {
        assert!(
            unsupported_explicit_proof_verification_error(false, "SMT-LIB", "Alethe").is_none()
        );
        let error = unsupported_explicit_proof_verification_error(true, "SMT-LIB", "Alethe")
            .expect("explicit verification must fail closed");
        assert!(error.contains("DIMACS DRAT/LRAT only"), "got: {error}");
    }

    #[test]
    fn firewall_verification_rejects_every_non_smt_route() {
        assert!(unsupported_firewall_verification_error(false, "DIMACS file").is_none());
        for route in [
            "DIMACS file",
            "DIMACS stdin",
            "CHC file",
            "CHC stdin",
            "fixedpoint file",
            "fixedpoint stdin",
            "forced CHC/portfolio",
        ] {
            let error = unsupported_firewall_verification_error(true, route)
                .expect("enabled firewall must reject unsupported route");
            assert!(error.contains("SMT-LIB DPLL(T) route"), "got: {error}");
            assert!(error.contains(route), "got: {error}");
        }
    }

    #[test]
    fn firewall_emission_rejects_every_non_smt_route() {
        assert!(unsupported_firewall_emission_error(false, "DIMACS file").is_none());
        for route in [
            "DIMACS file",
            "DIMACS stdin",
            "CHC file",
            "CHC stdin",
            "fixedpoint file",
            "fixedpoint stdin",
            "forced CHC/portfolio",
        ] {
            let error = unsupported_firewall_emission_error(true, route)
                .expect("requested firewall artifacts must reject unsupported routes");
            assert!(error.contains("SMT-LIB DPLL(T) route"), "got: {error}");
            assert!(error.contains(route), "got: {error}");
        }
    }

    #[test]
    fn rejected_result_cannot_authorize_eof_unsat_artifacts() {
        let mut transcript = SmtTranscriptState::new();
        transcript.record_public_verdict(PublicVerdict::Unsat);
        assert!(transcript.public_unsat_artifacts_allowed());

        transcript.reject_result_certification("(incomplete test-gate)");
        assert_eq!(transcript.public_verdict, Some(PublicVerdict::Unknown));
        assert!(!transcript.public_unsat_artifacts_allowed());

        // A later independently accepted result restores authority normally.
        transcript.record_public_verdict(PublicVerdict::Unsat);
        assert!(transcript.public_unsat_artifacts_allowed());

        transcript.note_recoverable_error();
        assert!(
            !transcript.public_unsat_artifacts_allowed(),
            "an artifact cannot embed source that failed continued execution"
        );
        transcript.had_recoverable_error = false;
        transcript.record_public_verdict(PublicVerdict::Unsat);
        transcript.mark_incomplete();
        assert_eq!(transcript.public_verdict, None);
        assert!(!transcript.public_unsat_artifacts_allowed());
    }

    #[cfg(unix)]
    #[test]
    fn replaced_decision_trace_path_is_rejected_before_verdict_emission() {
        let _guard = decision_trace_publication_test_lock();
        let temp = tempfile::tempdir().expect("temporary directory");
        let trace_path = temp.path().join("decision.trace");
        let displaced_path = temp.path().join("retained.trace");
        let trace = trace_path.to_str().expect("UTF-8 trace path");
        ay_sat::reserve_decision_trace(trace).expect("reserve decision trace");

        // Keep the reserved inode alive under another name and replace only the
        // public pathname. Settlement must authenticate the path before the
        // supplied emitter is allowed to observe SAT.
        std::fs::rename(&trace_path, &displaced_path).expect("move reserved trace inode");
        std::fs::write(&trace_path, b"attacker replacement").expect("replace trace path");

        let mut transcript = SmtTranscriptState::new();
        transcript.record_public_verdict(PublicVerdict::Sat);
        let mut emitted = Vec::new();
        let result = publish_rendered_executor_output(
            &mut transcript,
            true,
            "sat",
            "sat".to_string(),
            Some(trace),
            |_, output| emitted.push(output.to_string()),
        );

        assert!(result.is_err(), "replaced trace path must fail settlement");
        assert!(
            emitted.is_empty(),
            "SAT leaked before trace-path authentication: {emitted:?}"
        );
    }

    #[test]
    fn mismatched_decision_trace_terminal_is_rejected_before_verdict_emission() {
        let _guard = decision_trace_publication_test_lock();
        let temp = tempfile::tempdir().expect("temporary directory");
        let trace_path = temp.path().join("decision.trace");
        let trace = trace_path.to_str().expect("UTF-8 trace path");
        ay_sat::reserve_decision_trace(trace).expect("reserve decision trace");

        let mut solver = ay_sat::Solver::new(1);
        solver
            .enable_decision_trace(trace)
            .expect("claim reserved decision trace");
        assert!(solver.solve().into_inner().is_sat(), "fixture must be SAT");

        // Model a public/raw-correlation bug: the solver recorded SAT, but the
        // CLI is about to render UNSAT. The settlement gate must fail before
        // invoking the output closure.
        let mut transcript = SmtTranscriptState::new();
        transcript.record_public_verdict(PublicVerdict::Unsat);
        let mut emitted = Vec::new();
        let result = publish_rendered_executor_output(
            &mut transcript,
            true,
            "unsat",
            "unsat".to_string(),
            Some(trace),
            |_, output| emitted.push(output.to_string()),
        );

        assert!(
            result
                .as_ref()
                .is_err_and(|error| error.contains("differs from public outcome")),
            "terminal mismatch must fail correlation, got {result:?}"
        );
        assert!(
            emitted.is_empty(),
            "UNSAT leaked before terminal correlation: {emitted:?}"
        );
    }

    #[test]
    fn problem_mutation_classification_covers_chc_sygus_and_later_buffer_heads() {
        let commands = parse(
            r#"
            (set-logic ALL)
            (declare-rel p (Int))
            (declare-var x Int)
            (rule (p x))
            (query (p 0))
            (synth-fun f ((x Int)) Int)
            (constraint (= (f 0) 0))
            "#,
        )
        .expect("representative semantic commands parse");
        assert!(commands.iter().all(command_mutates_problem));

        let dropped = "; leading comment\n(get-info :version)\n(include \"unsat.smt2\")";
        assert!(parse_drop_contributes_to_problem(dropped));
        let dropped_assert = "(echo \"(not a command)\")\n; comment\n(assert (";
        assert!(parse_drop_contributes_to_problem(dropped_assert));
        assert!(parse_drop_contributes_to_problem(
            "(get-info :version\n(assert false)"
        ));
        assert!(!parse_drop_contributes_to_problem(
            "; (assert false)\n(get-info :version)"
        ));
    }

    #[test]
    fn nullary_symbol_sort_metadata_is_overload_and_scope_safe() {
        let mut transcript = SmtTranscriptState::new();
        for command in parse(
            r#"
            (declare-const x Int)
            (push 1)
            (declare-fun x () Bool)
            "#,
        )
        .expect("metadata fixture parses")
        {
            update_transcript_state_after_command(&mut transcript, &command);
        }
        assert_eq!(
            transcript.symbol_sorts.get("x").cloned().flatten(),
            None,
            "two active nullary overloads must not inherit either sort"
        );

        update_transcript_state_after_command(&mut transcript, &Command::Pop(1));
        assert_eq!(
            transcript.symbol_sorts.get("x").cloned().flatten(),
            Some("Int".to_string()),
            "pop must restore the outer declaration's metadata"
        );

        for command in parse(
            r#"
            (push 1)
            (set-option :global-decls true)
            (declare-const global Real)
            (pop 1)
            "#,
        )
        .expect("global declaration fixture parses")
        {
            update_transcript_state_after_command(&mut transcript, &command);
        }
        assert_eq!(
            transcript.symbol_sorts.get("global").cloned().flatten(),
            Some("Real".to_string()),
            "global declarations made under push must survive pop"
        );

        let non_nullary = parse("(define-fun f ((a Int)) Bool true)")
            .expect("definition parses")
            .pop()
            .expect("one command");
        update_transcript_state_after_command(&mut transcript, &non_nullary);
        assert!(!transcript.symbol_sorts.contains_key("f"));
    }

    #[test]
    fn dimacs_sniff_skips_smt_comments_before_horn_commands() {
        assert_eq!(
            classify_dimacs_prefix(b"; leading SMT-LIB comment\n", false),
            DimacsPrefixKind::NeedMore
        );
        assert_eq!(
            classify_dimacs_prefix(b"; leading SMT-LIB comment\n(set-logic HORN)\n", false),
            DimacsPrefixKind::NotDimacs
        );
    }

    #[test]
    fn rejected_result_reason_remains_specific_in_native_and_z3_transcripts() {
        let reason = "(incomplete firewall-diagnostic-only-no-query-certificate)";
        assert_eq!(
            render_public_unknown_reason(reason, false),
            format!("(:reason-unknown {reason})")
        );
        assert_eq!(
            render_public_unknown_reason(reason, true),
            format!("(:reason-unknown \"{reason}\")")
        );

        let mut transcript = SmtTranscriptState::new();
        transcript.reject_result_certification(reason);
        assert_eq!(
            z3_compat_get_info_output(
                &transcript,
                ":reason-unknown",
                "(:reason-unknown incomplete)"
            ),
            Some(render_public_unknown_reason(reason, z3_mode_enabled()))
        );

        let mut preflight_unknown = SmtTranscriptState::new();
        let preflight_reason = "(incomplete problem-command-discarded)";
        preflight_unknown.record_synthesized_unknown(preflight_reason);
        assert!(!preflight_unknown.result_certification_rejected);
        assert_eq!(
            z3_compat_get_info_output(
                &preflight_unknown,
                ":reason-unknown",
                "(:reason-unknown stale-executor-reason)"
            ),
            Some(render_public_unknown_reason(
                preflight_reason,
                z3_mode_enabled()
            ))
        );
    }

    #[test]
    fn synthesized_unknown_cannot_reuse_stale_executor_explanation() {
        let mut executor = Executor::new();
        for command in parse("(assert false)\n(check-sat)\n").expect("valid script") {
            executor.execute(&command).expect("command executes");
        }
        assert!(executor.last_result_is_unsat());

        let mut transcript = SmtTranscriptState::new();
        transcript.record_public_verdict(PublicVerdict::Unsat);
        assert!(executor_result_matches_public_verdict(
            &executor,
            &transcript
        ));

        transcript.record_synthesized_unknown("(incomplete command-discarded)");
        assert!(!executor_result_matches_public_verdict(
            &executor,
            &transcript
        ));

        executor.replace_last_result_with_unknown(UnknownReason::Incomplete);
        assert!(executor.last_result_is_unknown());
        assert!(!executor_result_matches_public_verdict(
            &executor,
            &transcript
        ));
    }

    #[test]
    fn caught_executor_panic_poison_survives_until_successful_reset() {
        let mut executor = Executor::new();
        let mut transcript = SmtTranscriptState::new();
        let assertion = parse("(assert true)")
            .expect("parse assertion")
            .pop()
            .expect("one assertion");

        assert!(handle_executor_panic(
            &mut executor,
            &assertion,
            &mut transcript
        ));
        assert!(transcript.is_incomplete());

        // The next decision is synthesized without trusting the potentially
        // partially-mutated executor.
        assert!(execute_and_print(
            &mut executor,
            &Command::CheckSat,
            &mut transcript,
            false
        ));
        assert_eq!(transcript.public_verdict, Some(PublicVerdict::Unknown));
        assert!(executor.last_result_is_unknown());

        // Only a reset that actually completes begins a trustworthy epoch.
        assert!(execute_and_print(
            &mut executor,
            &Command::Reset,
            &mut transcript,
            false
        ));
        assert!(!transcript.is_incomplete());
        assert!(execute_and_print(
            &mut executor,
            &Command::CheckSat,
            &mut transcript,
            false
        ));
        assert_eq!(transcript.public_verdict, Some(PublicVerdict::Sat));
    }

    #[test]
    fn caught_decision_panic_poison_blocks_later_definitive_decisions() {
        let mut executor = Executor::new();
        let mut transcript = SmtTranscriptState::new();

        assert!(handle_executor_panic(
            &mut executor,
            &Command::CheckSat,
            &mut transcript
        ));
        assert!(transcript.is_incomplete());
        assert_eq!(transcript.public_verdict, Some(PublicVerdict::Unknown));

        assert!(execute_and_print(
            &mut executor,
            &Command::CheckSat,
            &mut transcript,
            false
        ));
        assert_eq!(transcript.public_verdict, Some(PublicVerdict::Unknown));
        assert!(executor.last_result_is_unknown());
    }

    #[cfg(unix)]
    #[test]
    fn alethe_temp_creation_never_follows_a_preexisting_symlink() {
        use std::os::unix::fs::symlink;

        let temp = tempfile::tempdir().expect("temporary directory");
        let target = temp.path().join("proof.alethe");
        let victim = temp.path().join("victim.txt");
        std::fs::write(&victim, "do not truncate").expect("write victim");

        let pid = 77;
        let nonce = 91;
        let planted = artifact_temp_candidate(&target, pid, nonce).expect("candidate path");
        symlink(&victim, &planted).expect("plant symlink");

        let (reserved, file) = create_artifact_temp_file_from_nonce(&target, pid, nonce)
            .expect("a later exclusive candidate should be available");
        drop(file);
        assert_ne!(reserved, planted);
        assert!(planted.is_symlink());
        assert_eq!(
            std::fs::read_to_string(&victim).expect("read victim"),
            "do not truncate"
        );
        std::fs::remove_file(reserved).expect("remove reserved temporary file");
    }

    #[cfg(unix)]
    #[test]
    fn atomic_artifact_publish_replaces_symlink_without_touching_referent() {
        use std::os::unix::fs::symlink;

        let temp = tempfile::tempdir().expect("temporary directory");
        let target = temp.path().join("firewall_0.lean");
        let victim = temp.path().join("victim.txt");
        std::fs::write(&victim, "do not overwrite").expect("write victim");
        symlink(&victim, &target).expect("plant destination symlink");

        write_artifact_atomically(&target, |file| file.write_all(b"safe artifact"))
            .expect("publish artifact");
        assert!(!target.is_symlink());
        assert_eq!(
            std::fs::read_to_string(&victim).expect("read victim"),
            "do not overwrite"
        );
        assert_eq!(
            std::fs::read_to_string(target).expect("read artifact"),
            "safe artifact"
        );
    }

    #[cfg(target_os = "linux")]
    #[test]
    fn firewall_transaction_publishes_a_new_complete_set_atomically() {
        let temp = tempfile::tempdir().expect("temporary directory");
        let output = temp.path().join("firewall");

        let artifacts = vec!["new zero".to_string(), "new one".to_string()];
        let publication =
            write_firewall_lean_transaction(&output, &artifacts).expect("transaction succeeds");
        assert_eq!(publication.count, 2);
        assert_eq!(
            std::fs::read_to_string(output.join("firewall_0.lean")).unwrap(),
            "new zero"
        );
        assert_eq!(
            std::fs::read_to_string(output.join("firewall_1.lean")).unwrap(),
            "new one"
        );
        assert!(std::fs::read_dir(temp.path()).unwrap().all(|entry| {
            !entry
                .unwrap()
                .file_name()
                .to_string_lossy()
                .contains(".ay-firewall-stage-")
        }));
    }

    #[test]
    fn firewall_transaction_rejects_and_preserves_a_preexisting_path() {
        let temp = tempfile::tempdir().expect("temporary directory");
        let output = temp.path().join("firewall");
        std::fs::create_dir(&output).expect("output directory");
        std::fs::write(output.join("firewall_0.lean"), "old zero").expect("old artifact");
        std::fs::write(output.join("firewall_2.lean"), "old two").expect("old artifact");

        let artifacts = vec!["new zero".to_string(), "new one".to_string()];
        let error = write_firewall_lean_transaction(&output, &artifacts)
            .expect_err("pre-existing output must fail closed");
        assert!(error
            .to_string()
            .contains("refusing to replace pre-existing firewall output path"));
        assert_eq!(
            std::fs::read_to_string(output.join("firewall_0.lean")).unwrap(),
            "old zero"
        );
        assert!(!output.join("firewall_1.lean").exists());
        assert_eq!(
            std::fs::read_to_string(output.join("firewall_2.lean")).unwrap(),
            "old two"
        );
        assert!(std::fs::read_dir(temp.path()).unwrap().all(|entry| {
            !entry
                .unwrap()
                .file_name()
                .to_string_lossy()
                .contains(".ay-firewall-stage-")
        }));
    }

    #[cfg(target_os = "linux")]
    #[test]
    fn firewall_transaction_never_replaces_a_target_created_at_commit() {
        let temp = tempfile::tempdir().expect("temporary directory");
        let output = temp.path().join("firewall");
        let artifacts = vec!["new zero".to_string(), "new one".to_string()];
        let mut retained_stage = None;

        let error = write_firewall_lean_transaction_with(&output, &artifacts, |stage, target| {
            retained_stage = Some(stage.to_path_buf());
            std::fs::create_dir(target)?;
            std::fs::write(target.join("sentinel.txt"), "concurrent owner")
        })
        .expect_err("atomic no-replace publication must reject the raced target");

        assert!(error
            .to_string()
            .contains("unpublished stage members were invalidated"));
        assert_eq!(
            std::fs::read_to_string(output.join("sentinel.txt")).unwrap(),
            "concurrent owner"
        );
        let retained_stage = retained_stage.expect("hook observed stage");
        assert_eq!(
            std::fs::read(retained_stage.join("firewall_0.lean")).unwrap(),
            b""
        );
        assert_eq!(
            std::fs::read(retained_stage.join("firewall_1.lean")).unwrap(),
            b""
        );
    }

    #[cfg(target_os = "linux")]
    #[test]
    fn firewall_post_publish_failure_invalidates_exact_members_not_replacements() {
        let temp = tempfile::tempdir().expect("temporary directory");
        let output = temp.path().join("firewall");
        let displaced = temp.path().join("same-run-firewall-0.lean");
        let artifacts = vec!["new zero".to_string(), "new one".to_string()];

        let error = write_firewall_lean_transaction_with_hooks(
            &output,
            &artifacts,
            |_stage, _target| Ok(()),
            |target| {
                std::fs::rename(target.join("firewall_0.lean"), &displaced)?;
                std::fs::write(target.join("firewall_0.lean"), "foreign replacement")?;
                Err(io::Error::other("injected parent sync failure"))
            },
        )
        .expect_err("post-publication failure must roll back exact members");

        assert!(error.to_string().contains("injected parent sync failure"));
        assert_eq!(std::fs::read(&displaced).unwrap(), b"");
        assert_eq!(
            std::fs::read_to_string(output.join("firewall_0.lean")).unwrap(),
            "foreign replacement"
        );
        assert_eq!(std::fs::read(output.join("firewall_1.lean")).unwrap(), b"");
    }

    #[cfg(target_os = "linux")]
    #[test]
    fn retained_file_validation_rejects_replacement_and_invalidates_only_its_inode() {
        let temp = tempfile::tempdir().expect("temporary directory");
        let target = temp.path().join("proof.alethe");
        let file =
            write_artifact_noreplace_retained(&target, |file| file.write_all(b"same-run proof"))
                .expect("publish proof");
        let publication = RetainedPublication::new(file, target.clone(), PublicationPathKind::File)
            .expect("seal publication");
        let displaced = temp.path().join("displaced.alethe");
        std::fs::rename(&target, &displaced).expect("displace same-run proof");
        std::fs::write(&target, "concurrent replacement").expect("write replacement");

        publication
            .validate("test proof")
            .expect_err("replacement must lose namespace authority");
        invalidate_retained_artifact(&publication.file).expect("invalidate exact descriptor");

        assert_eq!(std::fs::read(&displaced).unwrap(), b"");
        assert_eq!(
            std::fs::read_to_string(&target).unwrap(),
            "concurrent replacement"
        );
    }

    #[cfg(target_os = "linux")]
    #[test]
    fn replaced_proof_before_verdict_cannot_authorize_unsat_or_delete_replacement() {
        let temp = tempfile::tempdir().expect("temporary directory");
        let target = temp.path().join("proof.alethe");
        let file =
            write_artifact_noreplace_retained(&target, |file| file.write_all(b"same-run proof"))
                .expect("publish proof");
        let proof = RetainedPublication::new(file, target.clone(), PublicationPathKind::File)
            .expect("seal proof");

        let mut transcript = SmtTranscriptState::new();
        transcript.record_public_verdict(PublicVerdict::Unsat);
        transcript.pending_unsat_output = Some("unsat".to_string());
        transcript.smt_unsat_publication = SmtUnsatPublicationState::Prepared(Box::new(
            SmtUnsatPublicationTransaction::new(proof, None, None),
        ));

        let displaced = temp.path().join("same-run-displaced.alethe");
        std::fs::rename(&target, &displaced).expect("displace same-run proof");
        std::fs::write(&target, "foreign replacement").expect("write foreign replacement");

        let mut emitted = Vec::new();
        let result = publish_authorized_pending_smt_unsat(
            &mut transcript,
            |_| Ok(None),
            |_, output| emitted.push(output.to_string()),
        );

        assert!(
            result
                .as_ref()
                .is_err_and(|error| error.contains("lost namespace authority")),
            "replacement must revoke UNSAT authority, got {result:?}"
        );
        assert!(emitted.is_empty(), "UNSAT escaped publication gate");
        assert_eq!(std::fs::read(&displaced).unwrap(), b"");
        assert_eq!(
            std::fs::read_to_string(&target).unwrap(),
            "foreign replacement"
        );
    }

    #[cfg(target_os = "linux")]
    #[test]
    fn optional_default_revalidation_failure_is_nonfatal_and_preserves_replacement() {
        let temp = tempfile::tempdir().expect("temporary directory");
        let target = temp.path().join("optional.alethe");
        let file =
            write_artifact_noreplace_retained(&target, |file| file.write_all(b"optional proof"))
                .expect("publish optional proof");
        let proof = RetainedPublication::new(file, target.clone(), PublicationPathKind::File)
            .expect("seal optional proof");
        let publication = SmtUnsatPublicationTransaction::new(proof, None, None);

        let displaced = temp.path().join("same-run-optional.alethe");
        std::fs::rename(&target, &displaced).expect("displace optional proof");
        std::fs::write(&target, "foreign replacement").expect("write foreign replacement");

        let mut transcript = SmtTranscriptState::new();
        transcript.record_public_verdict(PublicVerdict::Unsat);
        let result = finalize_optional_smt_unsat_publication(publication);

        assert!(
            result
                .as_ref()
                .is_err_and(|error| error.contains("lost namespace authority")),
            "optional publication should report a warning-class failure, got {result:?}"
        );
        assert_eq!(transcript.public_verdict, Some(PublicVerdict::Unsat));
        assert_eq!(std::fs::read(&displaced).unwrap(), b"");
        assert_eq!(
            std::fs::read_to_string(&target).unwrap(),
            "foreign replacement"
        );
    }

    #[cfg(target_os = "linux")]
    #[test]
    fn proof_failure_after_trace_settlement_invalidates_both_exact_publications() {
        let _guard = decision_trace_publication_test_lock();
        let temp = tempfile::tempdir().expect("temporary directory");
        let proof_path = temp.path().join("proof.alethe");
        let displaced_proof = temp.path().join("same-run-proof.alethe");
        let proof_file = write_artifact_noreplace_retained(&proof_path, |file| {
            file.write_all(b"same-run proof")
        })
        .expect("publish proof");
        let proof =
            RetainedPublication::new(proof_file, proof_path.clone(), PublicationPathKind::File)
                .expect("seal proof");

        let trace_path = temp.path().join("decision.trace");
        let trace = trace_path.to_str().expect("UTF-8 trace path");
        ay_sat::reserve_decision_trace(trace).expect("reserve decision trace");

        let mut transcript = SmtTranscriptState::new();
        transcript.record_public_verdict(PublicVerdict::Unsat);
        transcript.pending_unsat_output = Some("unsat".to_string());
        transcript.smt_unsat_publication = SmtUnsatPublicationState::Prepared(Box::new(
            SmtUnsatPublicationTransaction::new(proof, None, None),
        ));

        let mut emitted = Vec::new();
        let result = publish_authorized_pending_smt_unsat(
            &mut transcript,
            |transcript| {
                let trace_publication =
                    settle_authoritative_decision_trace(transcript, Some(trace))?;
                std::fs::rename(&proof_path, &displaced_proof)
                    .map_err(|error| error.to_string())?;
                std::fs::write(&proof_path, "foreign proof replacement")
                    .map_err(|error| error.to_string())?;
                Ok(trace_publication)
            },
            |_, output| emitted.push(output.to_string()),
        );

        assert!(
            result
                .as_ref()
                .is_err_and(|error| error.contains("lost namespace authority")),
            "post-settlement proof replacement must fail closed, got {result:?}"
        );
        assert!(emitted.is_empty(), "UNSAT escaped after proof replacement");
        assert_eq!(std::fs::read(&trace_path).unwrap(), b"");
        assert_eq!(std::fs::read(&displaced_proof).unwrap(), b"");
        assert_eq!(
            std::fs::read_to_string(&proof_path).unwrap(),
            "foreign proof replacement"
        );
    }

    #[cfg(target_os = "linux")]
    #[test]
    fn trace_replacement_after_settlement_invalidates_exact_trace_and_proof() {
        let _guard = decision_trace_publication_test_lock();
        let temp = tempfile::tempdir().expect("temporary directory");
        let proof_path = temp.path().join("proof.alethe");
        let proof_file = write_artifact_noreplace_retained(&proof_path, |file| {
            file.write_all(b"same-run proof")
        })
        .expect("publish proof");
        let proof =
            RetainedPublication::new(proof_file, proof_path.clone(), PublicationPathKind::File)
                .expect("seal proof");

        let trace_path = temp.path().join("decision.trace");
        let displaced_trace = temp.path().join("same-run-decision.trace");
        let trace = trace_path.to_str().expect("UTF-8 trace path");
        ay_sat::reserve_decision_trace(trace).expect("reserve decision trace");

        let mut transcript = SmtTranscriptState::new();
        transcript.record_public_verdict(PublicVerdict::Unsat);
        transcript.pending_unsat_output = Some("unsat".to_string());
        transcript.smt_unsat_publication = SmtUnsatPublicationState::Prepared(Box::new(
            SmtUnsatPublicationTransaction::new(proof, None, None),
        ));

        let mut emitted = Vec::new();
        let result = publish_authorized_pending_smt_unsat(
            &mut transcript,
            |transcript| {
                let trace_publication =
                    settle_authoritative_decision_trace(transcript, Some(trace))?;
                std::fs::rename(&trace_path, &displaced_trace)
                    .map_err(|error| error.to_string())?;
                std::fs::write(&trace_path, "foreign trace replacement")
                    .map_err(|error| error.to_string())?;
                Ok(trace_publication)
            },
            |_, output| emitted.push(output.to_string()),
        );

        assert!(
            result.as_ref().is_err_and(
                |error| error.contains("settled decision trace lost same-run authority")
            ),
            "post-settlement trace replacement must fail closed, got {result:?}"
        );
        assert!(emitted.is_empty(), "UNSAT escaped after trace replacement");
        assert_eq!(std::fs::read(&proof_path).unwrap(), b"");
        assert_eq!(std::fs::read(&displaced_trace).unwrap(), b"");
        assert_eq!(
            std::fs::read_to_string(&trace_path).unwrap(),
            "foreign trace replacement"
        );
    }

    #[cfg(target_os = "linux")]
    #[test]
    fn successful_unsat_emission_commits_trace_and_proof_together() {
        let _guard = decision_trace_publication_test_lock();
        let temp = tempfile::tempdir().expect("temporary directory");
        let proof_path = temp.path().join("proof.alethe");
        let proof_file = write_artifact_noreplace_retained(&proof_path, |file| {
            file.write_all(b"same-run proof")
        })
        .expect("publish proof");
        let proof =
            RetainedPublication::new(proof_file, proof_path.clone(), PublicationPathKind::File)
                .expect("seal proof");
        let trace_path = temp.path().join("decision.trace");
        let trace = trace_path.to_str().expect("UTF-8 trace path");
        ay_sat::reserve_decision_trace(trace).expect("reserve decision trace");

        let mut transcript = SmtTranscriptState::new();
        transcript.record_public_verdict(PublicVerdict::Unsat);
        transcript.pending_unsat_output = Some("unsat".to_string());
        transcript.smt_unsat_publication = SmtUnsatPublicationState::Prepared(Box::new(
            SmtUnsatPublicationTransaction::new(proof, None, None),
        ));

        let mut emitted = Vec::new();
        let result = publish_authorized_pending_smt_unsat(
            &mut transcript,
            |transcript| settle_authoritative_decision_trace(transcript, Some(trace)),
            |_, output| emitted.push(output.to_string()),
        );

        assert_eq!(result, Ok(true));
        assert_eq!(emitted, ["unsat"]);
        assert!(matches!(
            transcript.smt_unsat_publication,
            SmtUnsatPublicationState::Committed
        ));
        assert_eq!(std::fs::read(&proof_path).unwrap(), b"same-run proof");
        assert_eq!(
            std::fs::read(&trace_path).unwrap(),
            b"AYDTRC1\0\x01\x08\x01"
        );
    }

    #[cfg(target_os = "linux")]
    #[test]
    fn emission_panic_keeps_trace_and_proof_transactions_armed() {
        let _guard = decision_trace_publication_test_lock();
        let temp = tempfile::tempdir().expect("temporary directory");
        let proof_path = temp.path().join("proof.alethe");
        let proof_file = write_artifact_noreplace_retained(&proof_path, |file| {
            file.write_all(b"same-run proof")
        })
        .expect("publish proof");
        let proof =
            RetainedPublication::new(proof_file, proof_path.clone(), PublicationPathKind::File)
                .expect("seal proof");
        let trace_path = temp.path().join("decision.trace");
        let trace = trace_path.to_str().expect("UTF-8 trace path");
        ay_sat::reserve_decision_trace(trace).expect("reserve decision trace");

        let mut transcript = SmtTranscriptState::new();
        transcript.record_public_verdict(PublicVerdict::Unsat);
        transcript.pending_unsat_output = Some("unsat".to_string());
        transcript.smt_unsat_publication = SmtUnsatPublicationState::Prepared(Box::new(
            SmtUnsatPublicationTransaction::new(proof, None, None),
        ));

        let panic = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let _ = publish_authorized_pending_smt_unsat(
                &mut transcript,
                |transcript| settle_authoritative_decision_trace(transcript, Some(trace)),
                |_, _| panic!("injected output panic"),
            );
        }));

        assert!(panic.is_err(), "injected output panic must propagate");
        assert_eq!(std::fs::read(&trace_path).unwrap(), b"");
        assert_eq!(std::fs::read(&proof_path).unwrap(), b"");
    }

    #[cfg(target_os = "linux")]
    #[test]
    fn trace_settlement_failure_invalidates_exact_proof_without_deleting_foreign_trace() {
        let _guard = decision_trace_publication_test_lock();
        let temp = tempfile::tempdir().expect("temporary directory");
        let proof_path = temp.path().join("proof.alethe");
        let proof_file = write_artifact_noreplace_retained(&proof_path, |file| {
            file.write_all(b"same-run proof")
        })
        .expect("publish proof");
        let proof =
            RetainedPublication::new(proof_file, proof_path.clone(), PublicationPathKind::File)
                .expect("seal proof");

        let trace_path = temp.path().join("decision.trace");
        let retained_trace = temp.path().join("same-run.trace");
        let trace = trace_path.to_str().expect("UTF-8 trace path");
        ay_sat::reserve_decision_trace(trace).expect("reserve decision trace");
        std::fs::rename(&trace_path, &retained_trace).expect("displace reserved trace");
        std::fs::write(&trace_path, b"foreign trace replacement")
            .expect("write foreign trace replacement");

        let mut transcript = SmtTranscriptState::new();
        transcript.record_public_verdict(PublicVerdict::Unsat);
        transcript.pending_unsat_output = Some("unsat".to_string());
        transcript.smt_unsat_publication = SmtUnsatPublicationState::Prepared(Box::new(
            SmtUnsatPublicationTransaction::new(proof, None, None),
        ));

        let mut emitted = Vec::new();
        let result = publish_authorized_pending_smt_unsat(
            &mut transcript,
            |transcript| settle_authoritative_decision_trace(transcript, Some(trace)),
            |_, output| emitted.push(output.to_string()),
        );

        assert!(
            result
                .as_ref()
                .is_err_and(|error| error.contains("failed to finalize decision trace")),
            "trace replacement must fail settlement, got {result:?}"
        );
        assert!(emitted.is_empty(), "UNSAT escaped failed trace settlement");
        assert_eq!(std::fs::read(&proof_path).unwrap(), b"");
        assert_eq!(
            std::fs::read(&trace_path).unwrap(),
            b"foreign trace replacement"
        );
    }

    #[cfg(target_os = "linux")]
    #[test]
    fn retained_firewall_directory_validation_rejects_replacement() {
        let temp = tempfile::tempdir().expect("temporary directory");
        let target = temp.path().join("firewall");
        let artifacts = vec!["same-run lemma".to_string()];
        let publication =
            write_firewall_lean_transaction(&target, &artifacts).expect("publish firewall set");
        let displaced = temp.path().join("displaced-firewall");
        std::fs::rename(&target, &displaced).expect("displace same-run directory");
        std::fs::create_dir(&target).expect("create replacement directory");
        std::fs::write(target.join("sentinel.txt"), "concurrent replacement")
            .expect("write replacement sentinel");

        publication
            .publication
            .validate("test firewall")
            .expect_err("replacement must lose namespace authority");

        assert_eq!(
            std::fs::read_to_string(displaced.join("firewall_0.lean")).unwrap(),
            "same-run lemma"
        );
        assert_eq!(
            std::fs::read_to_string(target.join("sentinel.txt")).unwrap(),
            "concurrent replacement"
        );
    }

    #[cfg(unix)]
    #[test]
    fn artifact_publish_uses_one_canonical_parent_after_symlink_swap() {
        use std::os::unix::fs::symlink;

        let temp = tempfile::tempdir().expect("temporary directory");
        let first = temp.path().join("first");
        let second = temp.path().join("second");
        let alias = temp.path().join("parent");
        std::fs::create_dir(&first).unwrap();
        std::fs::create_dir(&second).unwrap();
        symlink(&first, &alias).unwrap();

        let target = alias.join("proof.alethe");
        let (resolved_target, temp_path, mut file) =
            create_artifact_temp_file(&target).expect("reserve in resolved parent");
        file.write_all(b"proof").unwrap();
        file.sync_all().unwrap();
        drop(file);

        std::fs::remove_file(&alias).unwrap();
        symlink(&second, &alias).unwrap();
        publish_artifact_temp(&temp_path, &resolved_target).expect("publish to original parent");

        assert_eq!(std::fs::read(first.join("proof.alethe")).unwrap(), b"proof");
        assert!(!second.join("proof.alethe").exists());
    }

    #[cfg(unix)]
    #[test]
    fn transcript_channel_publish_replaces_symlink_and_hardlink_targets() {
        use std::os::unix::fs::symlink;

        let temp = tempfile::tempdir().expect("temporary directory");
        for kind in ["symlink", "hardlink"] {
            let victim = temp.path().join(format!("{kind}-victim.txt"));
            let target = temp.path().join(format!("{kind}-channel.txt"));
            std::fs::write(&victim, "protected").expect("write victim");
            if kind == "symlink" {
                symlink(&victim, &target).expect("plant symlink");
            } else {
                std::fs::hard_link(&victim, &target).expect("plant hardlink");
            }

            let mut file = prepare_transcript_channel(target.to_str().expect("UTF-8 path"))
                .expect("publish safe transcript inode")
                .expect("file-backed channel");
            writeln!(file, "safe transcript").expect("write owned channel");
            drop(file);

            assert_eq!(std::fs::read_to_string(&victim).unwrap(), "protected");
            assert_eq!(
                std::fs::read_to_string(&target).unwrap(),
                "safe transcript\n"
            );
        }
    }

    #[cfg(unix)]
    #[test]
    fn transcript_channel_never_reopens_a_replaced_path_or_writes_a_socket() {
        use std::os::unix::fs::symlink;
        use std::os::unix::net::UnixListener;

        let temp = tempfile::tempdir().expect("temporary directory");
        let target = temp.path().join("channel");
        let listener = UnixListener::bind(&target).expect("bind Unix socket fixture");
        let mut file = prepare_transcript_channel(target.to_str().expect("UTF-8 path"))
            .expect("replace non-regular destination atomically")
            .expect("file-backed channel");
        drop(listener);

        let victim = temp.path().join("victim.txt");
        std::fs::write(&victim, "protected").expect("write victim");
        std::fs::remove_file(&target).expect("replace published pathname");
        symlink(&victim, &target).expect("redirect pathname after preparation");

        writeln!(file, "owned inode only").expect("write retained file descriptor");
        drop(file);
        assert_eq!(std::fs::read_to_string(victim).unwrap(), "protected");
    }

    #[test]
    fn transcript_channel_rejects_aliases_and_protected_artifacts() {
        let temp = tempfile::tempdir().expect("temporary directory");
        let channel = temp.path().join("shared.log");
        let alias = temp.path().join(".").join("shared.log");
        let proof = temp.path().join("proof.alethe");
        let mut transcript = SmtTranscriptState::new();
        transcript.regular_output_channel = channel.to_string_lossy().into_owned();

        assert!(transcript.output_channel_conflicts(
            alias.to_str().expect("UTF-8 path"),
            &transcript.regular_output_channel,
        ));
        transcript.protect_path(&proof).expect("protect proof path");
        assert!(transcript.output_channel_conflicts(proof.to_str().expect("UTF-8 path"), "stderr",));
    }

    /// Feed `input` to `IncrementalDepth` one physical line at a time (mirroring
    /// the `read_line` accumulation) and return the final depth.
    fn scan_depth_by_line(input: &str) -> IncrementalDepth {
        let mut d = IncrementalDepth::default();
        for line in input.split_inclusive('\n') {
            d.feed(line);
        }
        d
    }

    #[test]
    fn incremental_depth_balances_single_line_command() {
        assert_eq!(scan_depth_by_line("(check-sat)\n").depth, 0);
        assert_eq!(scan_depth_by_line("(assert (= x 1))\n").depth, 0);
    }

    #[test]
    fn incremental_depth_open_until_closed_across_lines() {
        // A multi-line command is only "complete" (depth 0) on the closing line.
        let mut d = IncrementalDepth::default();
        d.feed("(assert (or\n");
        assert!(d.depth > 0, "mid-command depth must stay positive");
        d.feed("  (= x 1)\n");
        assert!(d.depth > 0);
        d.feed("  (= y 2)))\n");
        assert_eq!(d.depth, 0, "closing line returns to depth 0");
    }

    #[test]
    fn incremental_depth_ignores_parens_in_line_comment() {
        // A ')' inside a `;` comment must not close a real group.
        assert_eq!(scan_depth_by_line("(echo x) ; )))(((\n").depth, 0);
        let mut d = IncrementalDepth::default();
        d.feed("(assert true ; ) ) )\n");
        assert_eq!(d.depth, 1, "comment parens are inert");
    }

    #[test]
    fn incremental_depth_ignores_parens_in_string_and_pipe() {
        // Parens inside a "..." string literal or |...| quoted symbol are inert,
        // including when the literal spans multiple physical lines.
        assert_eq!(scan_depth_by_line("(echo \"(((\")\n").depth, 0);
        assert_eq!(scan_depth_by_line("(echo \"a\"\"b)\")\n").depth, 0);
        // Multi-line quoted symbol (as in `(set-info :source | ... |)`).
        let mut d = IncrementalDepth::default();
        d.feed("(set-info :source |\n");
        assert_eq!(d.depth, 1);
        d.feed("  text with ) ( parens and no effect\n");
        assert_eq!(d.depth, 1, "still inside quoted symbol");
        d.feed("|)\n");
        assert_eq!(d.depth, 0, "closing | then ) balances");
    }

    #[test]
    fn incremental_depth_matches_naive_paren_count_outside_literals() {
        // On the benchmark shape (no strings/pipes mid-command), the tracker's
        // depth equals the naive open-minus-close count the old gate used.
        for s in [
            "(a (b) (c (d)))\n",
            "(assert (<= (+ x y) 3))\n",
            "(push 1)\n(assert x)\n",
        ] {
            let naive = s.matches('(').count() as i64 - s.matches(')').count() as i64;
            assert_eq!(scan_depth_by_line(s).depth, naive, "input: {s:?}");
        }
    }

    #[test]
    fn dedicated_subcommand_redirect_covers_known_non_smt_extensions() {
        // Every extension `looks_like_input_path_arg` (main.rs) classifies as
        // a solver input but `ay solve` cannot parse gets a redirect message.
        for (path, needle) in [
            ("model.fzn", "ay flatzinc solve"),
            ("Model.QDIMACS", "ay qbf solve"),
            ("inst.wcnf", "ay maxsat solve"),
            ("inst.wcnf.xz", "ay maxsat solve"),
            ("inst.opb", "ay pb solve"),
            ("prob.mps", "ay lp solve"),
            ("prob.lp", "ay lp solve"),
            ("circuit.aig", "not supported"),
            ("circuit.aag", "not supported"),
            ("synth.sl", "not supported"),
        ] {
            let msg = dedicated_subcommand_redirect(path)
                .unwrap_or_else(|| panic!("{path} should be redirected"));
            assert!(msg.contains(needle), "{path}: {msg} missing {needle}");
        }

        // SMT-LIB / DIMACS / CHC inputs proceed through normal routing.
        for path in ["input.smt2", "input.cnf", "input.dimacs", "input.smt"] {
            assert_eq!(dedicated_subcommand_redirect(path), None, "{path}");
        }
    }

    #[test]
    fn reason_unknown_inner_extracts_unquoted_token() {
        // AY prints the reason UNQUOTED; the token may contain spaces/parens.
        assert_eq!(
            reason_unknown_inner("(:reason-unknown timeout)"),
            Some("timeout")
        );
        assert_eq!(
            reason_unknown_inner("(:reason-unknown (incomplete quantifier-unhandled))"),
            Some("(incomplete quantifier-unhandled)")
        );
        // Not a reason-unknown line -> untouched.
        assert_eq!(reason_unknown_inner("(:status unknown)"), None);
    }

    #[test]
    fn z3_reason_unknown_maps_resource_family_to_canceled() {
        // Verus's `reason_unknown_canceled_str()` is exactly this line.
        for r in ["timeout", "resourceout", "memout", "interrupted"] {
            assert_eq!(
                z3_reason_unknown_output(r),
                "(:reason-unknown \"canceled\")",
                "{r} should map to Z3 canceled"
            );
        }
    }

    #[test]
    fn z3_reason_unknown_keeps_z3_unknown_verbatim() {
        // Z3's own "unknown" reason; Verus matches it literally.
        assert_eq!(
            z3_reason_unknown_output("unknown"),
            "(:reason-unknown \"unknown\")"
        );
    }

    #[test]
    fn z3_reason_unknown_incompleteness_matches_verus_incomplete_prefix() {
        // Verus routes any `(:reason-unknown "(incomplete...` to Incomplete
        // (goal NOT proved). Every incompleteness form must carry that prefix.
        let incomplete_prefix = "(:reason-unknown \"(incomplete";
        for r in [
            "incomplete",
            "unsupported",
            "(unsupported arithmetic)",
            "(unsupported mixed-collection)",
            "internal-error",
            "(incomplete quantifier-unhandled)",
            "(incomplete proof-trusted)",
            "some-future-reason-code",
        ] {
            let out = z3_reason_unknown_output(r);
            assert!(
                out.starts_with(incomplete_prefix),
                "reason {r:?} produced {out:?}, which is neither canceled/unknown \
                 nor an (incomplete ...) form Verus accepts"
            );
        }
    }

    #[test]
    fn z3_reason_unknown_preserves_already_incomplete_forms() {
        // Quantifier detail is preserved verbatim (already Z3-shaped).
        assert_eq!(
            z3_reason_unknown_output("(incomplete quantifier-unhandled)"),
            "(:reason-unknown \"(incomplete quantifier-unhandled)\")"
        );
    }

    #[test]
    fn smt_lra_competition_jit_uses_batch_native_applies_not_boundary_or_requests() {
        let mut run_stats =
            stats_output::RunStatistics::new(stats_output::SolveMode::Smt, "sat", Duration::ZERO);
        run_stats.insert(SMT_LRA_BASIS_REGION_PROFILE_ENABLED_COUNTER, 1);
        run_stats.insert(SMT_LRA_BASIS_REGION_APPLICATION_COUNTER, 3);
        run_stats.insert(SMT_LRA_BASIS_REGION_BOUNDARY_CHECKS_COUNTER, 4);
        run_stats.insert(SMT_LRA_BASIS_REGION_REQUESTS_QUEUED_COUNTER, 7);

        attach_smt_lra_competition_jit_for_artifact(
            &mut run_stats,
            SMT_LRA_BASIS_REGION_ARTIFACT,
            "solver-program",
        );

        let evidence = run_stats
            .competition_jit
            .expect("enabled LRA basis-region profile should attach SMT competition evidence");
        let application_counter = evidence
            .application_counter
            .expect("SMT LRA competition evidence should include an application counter");
        assert_eq!(evidence.track, "smt");
        assert_eq!(evidence.artifact_id, SMT_LRA_BASIS_REGION_ARTIFACT);
        assert_eq!(evidence.candidate_mode, "solver-program");
        assert_eq!(
            application_counter.key,
            SMT_LRA_BASIS_REGION_APPLICATION_COUNTER
        );
        assert_eq!(application_counter.value, 3);
        assert_eq!(
            run_stats
                .counters
                .get(SMT_LRA_BASIS_REGION_BOUNDARY_CHECKS_COUNTER)
                .copied(),
            Some(4)
        );
        assert_eq!(
            run_stats
                .counters
                .get(SMT_LRA_BASIS_REGION_REQUESTS_QUEUED_COUNTER)
                .copied(),
            Some(7)
        );
    }

    #[test]
    fn smt_lra_competition_jit_can_use_sparse_substitute_applies() {
        let mut run_stats =
            stats_output::RunStatistics::new(stats_output::SolveMode::Smt, "sat", Duration::ZERO);
        run_stats.insert(SMT_LRA_SPARSE_SUBSTITUTE_PROFILE_ENABLED_COUNTER, 1);
        run_stats.insert(SMT_LRA_SPARSE_SUBSTITUTE_APPLICATION_COUNTER, 0);

        attach_smt_lra_competition_jit_for_artifact(
            &mut run_stats,
            SMT_LRA_SPARSE_SUBSTITUTE_ARTIFACT,
            "solver-program",
        );

        let evidence = run_stats
            .competition_jit
            .expect("requested sparse-substitute profile should attach SMT competition evidence");
        let application_counter = evidence
            .application_counter
            .expect("SMT sparse-substitute evidence should include an application counter");
        assert_eq!(evidence.track, "smt");
        assert_eq!(evidence.artifact_id, SMT_LRA_SPARSE_SUBSTITUTE_ARTIFACT);
        assert_eq!(evidence.candidate_mode, "solver-program");
        assert_eq!(
            application_counter.key,
            SMT_LRA_SPARSE_SUBSTITUTE_APPLICATION_COUNTER
        );
        assert_eq!(application_counter.value, 0);
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum PublicationPathKind {
    File,
    Directory,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct PublicationFileState {
    identity: Option<SmtFileIdentity>,
    len: u64,
    #[cfg(unix)]
    mode: u32,
    #[cfg(unix)]
    links: u64,
    #[cfg(unix)]
    modified_seconds: i64,
    #[cfg(unix)]
    modified_nanoseconds: i64,
    #[cfg(unix)]
    changed_seconds: i64,
    #[cfg(unix)]
    changed_nanoseconds: i64,
    #[cfg(not(unix))]
    modified: std::time::SystemTime,
}

impl PublicationFileState {
    fn capture(metadata: &std::fs::Metadata) -> io::Result<Self> {
        #[cfg(unix)]
        {
            use std::os::unix::fs::MetadataExt as _;
            Ok(Self {
                identity: SmtFileIdentity::from_metadata(metadata),
                len: metadata.len(),
                mode: metadata.mode(),
                links: metadata.nlink(),
                modified_seconds: metadata.mtime(),
                modified_nanoseconds: metadata.mtime_nsec(),
                changed_seconds: metadata.ctime(),
                changed_nanoseconds: metadata.ctime_nsec(),
            })
        }
        #[cfg(not(unix))]
        {
            Ok(Self {
                identity: SmtFileIdentity::from_metadata(metadata),
                len: metadata.len(),
                modified: metadata.modified()?,
            })
        }
    }
}

#[derive(Debug)]
struct RetainedPublication {
    file: std::fs::File,
    path: std::path::PathBuf,
    kind: PublicationPathKind,
    state: PublicationFileState,
}

impl RetainedPublication {
    fn new(
        file: std::fs::File,
        path: std::path::PathBuf,
        kind: PublicationPathKind,
    ) -> io::Result<Self> {
        let metadata = match file.metadata() {
            Ok(metadata) => metadata,
            Err(error) => return Err(seal_publication_error(error, &file, kind)),
        };
        let state = match PublicationFileState::capture(&metadata) {
            Ok(state) => state,
            Err(error) => return Err(seal_publication_error(error, &file, kind)),
        };
        Ok(Self {
            file,
            path,
            kind,
            state,
        })
    }

    fn validate(&self, label: &str) -> io::Result<()> {
        let descriptor_metadata = self.file.metadata()?;
        let path_metadata = std::fs::symlink_metadata(&self.path)?;
        let expected_type_matches = match self.kind {
            PublicationPathKind::File => {
                descriptor_metadata.file_type().is_file() && path_metadata.file_type().is_file()
            }
            PublicationPathKind::Directory => {
                descriptor_metadata.file_type().is_dir() && path_metadata.file_type().is_dir()
            }
        };
        if !expected_type_matches {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                format!("{label} changed type at {}", self.path.display()),
            ));
        }
        let descriptor_state = PublicationFileState::capture(&descriptor_metadata)?;
        let path_state = PublicationFileState::capture(&path_metadata)?;
        #[cfg(unix)]
        if descriptor_state.links == 0 || path_state.links == 0 {
            return Err(io::Error::new(
                io::ErrorKind::NotFound,
                format!("{label} was unlinked at {}", self.path.display()),
            ));
        }
        if descriptor_state != self.state || path_state != descriptor_state {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                format!(
                    "{label} no longer matches its retained same-run publication at {}",
                    self.path.display()
                ),
            ));
        }
        Ok(())
    }
}

fn seal_publication_error(
    primary: io::Error,
    file: &std::fs::File,
    kind: PublicationPathKind,
) -> io::Error {
    if kind == PublicationPathKind::Directory {
        return primary;
    }
    match invalidate_retained_artifact(file) {
        Ok(()) => primary,
        Err(invalidation) => io::Error::other(format!(
            "{primary}; invalidating the unsealed publication also failed: {invalidation}"
        )),
    }
}

#[derive(Debug)]
struct FirewallPublication {
    count: usize,
    publication: RetainedPublication,
    members: Vec<RetainedPublication>,
}

/// Arms exact-member rollback before a staged firewall directory becomes
/// public. The public directory name is never removed on failure because it
/// may have been replaced; only these retained writable descriptors are
/// truncated.
struct FirewallMemberInvalidationGuard {
    files: Vec<(String, std::fs::File)>,
    invalidate_on_drop: bool,
}

impl FirewallMemberInvalidationGuard {
    fn new(files: Vec<(String, std::fs::File)>) -> Self {
        Self {
            files,
            invalidate_on_drop: true,
        }
    }

    fn commit(&mut self) {
        self.invalidate_on_drop = false;
    }

    fn invalidate_exact(&self) {
        for (_, file) in &self.files {
            let _ = invalidate_retained_artifact(file);
        }
    }
}

impl Drop for FirewallMemberInvalidationGuard {
    fn drop(&mut self) {
        if self.invalidate_on_drop {
            self.invalidate_exact();
        }
    }
}

/// Write diagnostic firewall Lean lemmas to the `--emit-firewall-lean`
/// directory, one file per groundable local theory obligation in the last
/// proof. These files audit covered theory steps; they do not by themselves
/// certify the complete UNSAT derivation.
///
/// An explicit request is all-or-error: it cannot quietly succeed without an
/// artifact. The requested directory is an immutable, single-run publication:
/// AY stages the complete set in a sibling directory and atomically installs
/// that directory without replacing any pre-existing path.
fn maybe_emit_firewall_lean(executor: &Executor) -> Result<Option<FirewallPublication>, String> {
    let Some(dir) = crate::FIREWALL_LEAN_DIR.get() else {
        return Ok(None);
    };
    let proof = executor.last_proof().ok_or_else(|| {
        "--emit-firewall-lean requested artifacts, but UNSAT produced no reconstructable proof"
            .to_string()
    })?;
    let Some(leans) = executor.emit_datatype_firewall_lean_bounded(
        proof,
        firewall_verify::MAX_DIAGNOSTIC_FILES,
        firewall_verify::MAX_DIAGNOSTIC_SOURCE_BYTES,
    ) else {
        return Err(format!(
            "--emit-firewall-lean artifact limit exceeded (at most {} files and {} aggregate source bytes)",
            firewall_verify::MAX_DIAGNOSTIC_FILES,
            firewall_verify::MAX_DIAGNOSTIC_SOURCE_BYTES
        ));
    };
    if leans.is_empty() {
        return Err(
            "--emit-firewall-lean found no supported local obligation in the refutation"
                .to_string(),
        );
    }
    let publication = write_firewall_lean_transaction(dir, &leans).map_err(|error| {
        format!(
            "failed to publish firewall Lean artifacts in {}: {error}",
            dir.display()
        )
    })?;
    if !crate::quiet_enabled() {
        // Proof-write announcement only; the immutable directory is already
        // published regardless of `-q`/`--quiet`.
        safe_eprintln!(
            "ay: wrote {} diagnostic firewall Lean lemma(s) to {}",
            publication.count,
            dir.display()
        );
    }
    Ok(Some(publication))
}

fn create_firewall_staging_dir(
    resolved_target: &std::path::Path,
) -> io::Result<std::path::PathBuf> {
    use std::sync::atomic::Ordering;

    let parent = resolved_target.parent().ok_or_else(|| {
        io::Error::new(
            io::ErrorKind::InvalidInput,
            "firewall output directory has no parent",
        )
    })?;
    let target_name = resolved_target.file_name().ok_or_else(|| {
        io::Error::new(
            io::ErrorKind::InvalidInput,
            "firewall output directory must name a directory",
        )
    })?;
    let first_nonce =
        ARTIFACT_TEMP_NONCE.fetch_add(ARTIFACT_TEMP_CREATE_ATTEMPTS, Ordering::Relaxed);
    for offset in 0..ARTIFACT_TEMP_CREATE_ATTEMPTS {
        let mut stage_name = std::ffi::OsString::from(".");
        stage_name.push(target_name);
        stage_name.push(format!(
            ".ay-firewall-stage-{}-{}",
            std::process::id(),
            first_nonce.wrapping_add(offset)
        ));
        let candidate = parent.join(stage_name);
        let mut builder = std::fs::DirBuilder::new();
        #[cfg(unix)]
        {
            use std::os::unix::fs::DirBuilderExt as _;
            builder.mode(0o700);
        }
        match builder.create(&candidate) {
            Ok(()) => return Ok(candidate),
            Err(error) if error.kind() == io::ErrorKind::AlreadyExists => continue,
            Err(error) => return Err(error),
        }
    }
    Err(io::Error::new(
        io::ErrorKind::AlreadyExists,
        format!(
            "could not reserve a unique firewall staging directory after {ARTIFACT_TEMP_CREATE_ATTEMPTS} attempts"
        ),
    ))
}

#[cfg(any(target_os = "linux", target_os = "macos"))]
fn rename_path_noreplace(source: &std::path::Path, target: &std::path::Path) -> io::Result<()> {
    ay_sys::fs::rename_noreplace(source, target)
}

#[cfg(not(any(target_os = "linux", target_os = "macos")))]
fn rename_path_noreplace(_source: &std::path::Path, _target: &std::path::Path) -> io::Result<()> {
    Err(io::Error::new(
        io::ErrorKind::Unsupported,
        "atomic no-replace artifact publication is unsupported on this platform",
    ))
}

fn write_firewall_lean_transaction(
    dir: &std::path::Path,
    leans: &[String],
) -> io::Result<FirewallPublication> {
    write_firewall_lean_transaction_with(dir, leans, |_stage, _target| Ok(()))
}

fn write_firewall_lean_transaction_with(
    dir: &std::path::Path,
    leans: &[String],
    before_publish: impl FnMut(&std::path::Path, &std::path::Path) -> io::Result<()>,
) -> io::Result<FirewallPublication> {
    write_firewall_lean_transaction_with_hooks(
        dir,
        leans,
        before_publish,
        sync_firewall_publication_parent,
    )
}

fn sync_firewall_publication_parent(resolved_target: &std::path::Path) -> io::Result<()> {
    #[cfg(unix)]
    {
        std::fs::File::open(
            resolved_target
                .parent()
                .ok_or_else(|| io::Error::other("firewall target lost its parent"))?,
        )?
        .sync_all()
    }
    #[cfg(not(unix))]
    {
        let _ = resolved_target;
        Ok(())
    }
}

fn write_firewall_lean_transaction_with_hooks(
    dir: &std::path::Path,
    leans: &[String],
    mut before_publish: impl FnMut(&std::path::Path, &std::path::Path) -> io::Result<()>,
    mut after_publish: impl FnMut(&std::path::Path) -> io::Result<()>,
) -> io::Result<FirewallPublication> {
    if leans.is_empty() {
        return Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            "firewall transaction requires at least one artifact",
        ));
    }
    let parent = dir
        .parent()
        .filter(|parent| !parent.as_os_str().is_empty())
        .unwrap_or_else(|| std::path::Path::new("."));
    std::fs::create_dir_all(parent)?;
    let resolved_target = resolve_artifact_target(dir)?;
    match std::fs::symlink_metadata(&resolved_target) {
        Ok(_) => {
            return Err(io::Error::new(
                io::ErrorKind::AlreadyExists,
                format!(
                    "refusing to replace pre-existing firewall output path {}; choose a new directory",
                    resolved_target.display()
                ),
            ));
        }
        Err(error) if error.kind() == io::ErrorKind::NotFound => {}
        Err(error) => return Err(error),
    }

    let stage = create_firewall_staging_dir(&resolved_target)?;
    let mut member_files = Vec::with_capacity(leans.len());
    for (index, lean) in leans.iter().enumerate() {
        let name = format!("firewall_{index}.lean");
        let path = stage.join(&name);
        let mut options = std::fs::OpenOptions::new();
        options.write(true).create_new(true);
        #[cfg(unix)]
        {
            use std::os::unix::fs::OpenOptionsExt as _;
            options.mode(0o600);
        }
        let mut file = options.open(&path).map_err(|error| {
            io::Error::new(
                error.kind(),
                format!(
                    "{error}; incomplete private stage retained at {}",
                    stage.display()
                ),
            )
        })?;
        file.write_all(lean.as_bytes())
            .and_then(|()| file.sync_all())
            .map_err(|error| {
                io::Error::new(
                    error.kind(),
                    format!(
                        "{error}; incomplete private stage retained at {}",
                        stage.display()
                    ),
                )
            })?;
        member_files.push((name, file));
    }
    let stage_directory = std::fs::File::open(&stage)?;
    stage_directory.sync_all()?;
    let mut member_guard = FirewallMemberInvalidationGuard::new(member_files);
    if let Err(error) = before_publish(&stage, &resolved_target)
        .and_then(|()| rename_path_noreplace(&stage, &resolved_target))
    {
        return Err(io::Error::new(
            error.kind(),
            format!(
                "{error}; unpublished stage members were invalidated at {}",
                stage.display()
            ),
        ));
    }
    after_publish(&resolved_target)?;
    let target_for_members = resolved_target.clone();
    let publication = RetainedPublication::new(
        stage_directory,
        resolved_target,
        PublicationPathKind::Directory,
    )?;
    let mut members = Vec::with_capacity(member_guard.files.len());
    for (name, file) in &member_guard.files {
        members.push(RetainedPublication::new(
            file.try_clone()?,
            target_for_members.join(name),
            PublicationPathKind::File,
        )?);
    }
    member_guard.commit();
    Ok(FirewallPublication {
        count: leans.len(),
        publication,
        members,
    })
}

const ARTIFACT_TEMP_CREATE_ATTEMPTS: u64 = 16;
static ARTIFACT_TEMP_NONCE: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);

fn artifact_temp_candidate(
    target: &std::path::Path,
    process_id: u32,
    nonce: u64,
) -> io::Result<std::path::PathBuf> {
    let file_name = target.file_name().ok_or_else(|| {
        io::Error::new(io::ErrorKind::InvalidInput, "proof target must name a file")
    })?;
    let mut temp_name = std::ffi::OsString::from(".");
    temp_name.push(file_name);
    temp_name.push(format!(".tmp-{process_id}-{nonce}"));
    Ok(target
        .parent()
        .unwrap_or_else(|| std::path::Path::new("."))
        .join(temp_name))
}

/// Resolve the parent directory once before creating or publishing an
/// artifact. Subsequent operations use this physical parent path, so swapping a
/// symlink in an ancestor cannot redirect the rename to a different directory.
pub(crate) fn resolve_artifact_target(target: &std::path::Path) -> io::Result<std::path::PathBuf> {
    let file_name = target.file_name().ok_or_else(|| {
        io::Error::new(
            io::ErrorKind::InvalidInput,
            "artifact target must name a file",
        )
    })?;
    let parent = target
        .parent()
        .filter(|parent| !parent.as_os_str().is_empty())
        .unwrap_or_else(|| std::path::Path::new("."));
    Ok(std::fs::canonicalize(parent)?.join(file_name))
}

fn publish_artifact_temp(
    temp_path: &std::path::Path,
    resolved_target: &std::path::Path,
) -> io::Result<()> {
    std::fs::rename(temp_path, resolved_target)?;
    #[cfg(unix)]
    {
        let parent = resolved_target.parent().ok_or_else(|| {
            io::Error::new(io::ErrorKind::InvalidInput, "artifact target has no parent")
        })?;
        std::fs::File::open(parent)?.sync_all()?;
    }
    Ok(())
}

fn publish_artifact_temp_noreplace(
    temp_path: &std::path::Path,
    resolved_target: &std::path::Path,
) -> io::Result<()> {
    rename_path_noreplace(temp_path, resolved_target)?;
    #[cfg(unix)]
    {
        let parent = resolved_target.parent().ok_or_else(|| {
            io::Error::new(io::ErrorKind::InvalidInput, "artifact target has no parent")
        })?;
        std::fs::File::open(parent)?.sync_all()?;
    }
    Ok(())
}

fn create_artifact_temp_file_from_nonce(
    target: &std::path::Path,
    process_id: u32,
    first_nonce: u64,
) -> io::Result<(std::path::PathBuf, std::fs::File)> {
    for offset in 0..ARTIFACT_TEMP_CREATE_ATTEMPTS {
        let candidate =
            artifact_temp_candidate(target, process_id, first_nonce.wrapping_add(offset))?;
        match std::fs::OpenOptions::new()
            .read(true)
            .write(true)
            .create_new(true)
            .open(&candidate)
        {
            Ok(file) => return Ok((candidate, file)),
            Err(error) if error.kind() == io::ErrorKind::AlreadyExists => continue,
            Err(error) => return Err(error),
        }
    }
    Err(io::Error::new(
        io::ErrorKind::AlreadyExists,
        format!(
            "could not reserve a unique artifact temporary file after {ARTIFACT_TEMP_CREATE_ATTEMPTS} attempts"
        ),
    ))
}

fn create_artifact_temp_file(
    target: &std::path::Path,
) -> io::Result<(std::path::PathBuf, std::path::PathBuf, std::fs::File)> {
    use std::sync::atomic::Ordering;

    let resolved_target = resolve_artifact_target(target)?;
    let first_nonce =
        ARTIFACT_TEMP_NONCE.fetch_add(ARTIFACT_TEMP_CREATE_ATTEMPTS, Ordering::Relaxed);
    let (temp_path, file) =
        create_artifact_temp_file_from_nonce(&resolved_target, std::process::id(), first_nonce)?;
    Ok((resolved_target, temp_path, file))
}

pub(crate) fn write_artifact_atomically(
    target: &std::path::Path,
    write: impl FnOnce(&mut std::fs::File) -> io::Result<()>,
) -> io::Result<()> {
    write_artifact_atomically_retained(target, write).map(drop)
}

/// Write and publish a new artifact without replacing an existing path, then
/// return the exact writable descriptor used for publication. A caller that
/// has additional transaction participants can invalidate this inode directly
/// if a later participant fails, even when the public pathname is raced.
pub(crate) fn write_artifact_noreplace_retained(
    target: &std::path::Path,
    write: impl FnOnce(&mut std::fs::File) -> io::Result<()>,
) -> io::Result<std::fs::File> {
    write_artifact_with_publication(target, write, publish_artifact_temp_noreplace)
}

fn write_artifact_atomically_retained(
    target: &std::path::Path,
    write: impl FnOnce(&mut std::fs::File) -> io::Result<()>,
) -> io::Result<std::fs::File> {
    write_artifact_with_publication(target, write, publish_artifact_temp)
}

fn write_artifact_with_publication(
    target: &std::path::Path,
    write: impl FnOnce(&mut std::fs::File) -> io::Result<()>,
    publish: fn(&std::path::Path, &std::path::Path) -> io::Result<()>,
) -> io::Result<std::fs::File> {
    let (resolved_target, temp_path, mut file) = create_artifact_temp_file(target)?;
    let write_result = write(&mut file).and_then(|()| file.sync_all());
    let result = write_result.and_then(|()| publish(&temp_path, &resolved_target));
    if let Err(error) = result {
        let invalidation = invalidate_retained_artifact(&file);
        return Err(match invalidation {
            Ok(()) => error,
            Err(invalidation) => io::Error::other(format!(
                "{error}; invalidating the retained artifact descriptor also failed: {invalidation}"
            )),
        });
    }
    Ok(file)
}

fn invalidate_retained_artifact(file: &std::fs::File) -> io::Result<()> {
    file.set_len(0)?;
    file.sync_all()
}

/// Hash exactly the proof bytes accepted by the underlying writer. Capturing
/// this digest while AY still owns the temporary proof descriptor binds later
/// artifact generation to the proof AY actually rendered, not whatever a
/// concurrent pathname replacement might expose after publication.
struct ProofDigestWriter<W> {
    inner: W,
    hasher: Sha256,
}

impl<W> ProofDigestWriter<W> {
    fn new(inner: W) -> Self {
        Self {
            inner,
            hasher: Sha256::new(),
        }
    }

    fn inner(&self) -> &W {
        &self.inner
    }

    fn digest(&self) -> DigestBytes {
        self.hasher.clone().finalize().into()
    }

    fn into_inner(self) -> W {
        self.inner
    }
}

impl<W: Write> Write for ProofDigestWriter<W> {
    fn write(&mut self, bytes: &[u8]) -> io::Result<usize> {
        let written = self.inner.write(bytes)?;
        self.hasher.update(&bytes[..written]);
        Ok(written)
    }

    fn flush(&mut self) -> io::Result<()> {
        self.inner.flush()
    }
}

/// Same-run artifacts that jointly authorize a deferred SMT UNSAT response.
///
/// Every writable file descriptor remains live while the decision trace is
/// settled. A transaction is armed until its paths and descriptor state are
/// revalidated immediately before the verdict. Dropping an armed transaction
/// invalidates only the retained inodes; it never removes a public pathname,
/// which could have been replaced by another process.
struct SmtUnsatPublicationTransaction {
    proof: RetainedPublication,
    artifact: Option<RetainedPublication>,
    firewall: Option<FirewallPublication>,
    invalidate_on_drop: bool,
}

impl SmtUnsatPublicationTransaction {
    fn new(
        proof: RetainedPublication,
        artifact: Option<RetainedPublication>,
        firewall: Option<FirewallPublication>,
    ) -> Self {
        Self {
            proof,
            artifact,
            firewall,
            invalidate_on_drop: true,
        }
    }

    fn validate(&self) -> io::Result<()> {
        self.proof.validate("Alethe proof")?;
        if let Some(artifact) = &self.artifact {
            artifact.validate("proof artifact")?;
        }
        if let Some(firewall) = &self.firewall {
            firewall
                .publication
                .validate("firewall artifact directory")?;
            for member in &firewall.members {
                member.validate("firewall artifact")?;
            }
        }
        Ok(())
    }

    fn invalidate_exact(&mut self) -> String {
        let mut errors = Vec::new();
        if let Some(firewall) = &self.firewall {
            for member in &firewall.members {
                if let Err(error) = invalidate_retained_artifact(&member.file) {
                    errors.push(format!("firewall artifact: {error}"));
                }
            }
        }
        if let Some(artifact) = &self.artifact {
            if let Err(error) = invalidate_retained_artifact(&artifact.file) {
                errors.push(format!("proof artifact: {error}"));
            }
        }
        if let Err(error) = invalidate_retained_artifact(&self.proof.file) {
            errors.push(format!("Alethe proof: {error}"));
        }
        self.invalidate_on_drop = false;
        if errors.is_empty() {
            "; exact same-run SMT publications were descriptor-invalidated".to_string()
        } else {
            format!(
                "; WARNING: retained publication invalidation also failed ({})",
                errors.join("; ")
            )
        }
    }

    fn into_authority(mut self) -> Result<AuthorizedSmtUnsatPublication, String> {
        if let Err(error) = self.validate() {
            let invalidation = self.invalidate_exact();
            return Err(format!(
                "same-run SMT publication lost namespace authority before UNSAT: {error}{invalidation}"
            ));
        }
        Ok(AuthorizedSmtUnsatPublication {
            _publication: Some(self),
        })
    }
}

impl Drop for SmtUnsatPublicationTransaction {
    fn drop(&mut self) {
        if self.invalidate_on_drop {
            let _ = self.invalidate_exact();
        }
    }
}

/// Holds every authenticated publication descriptor through verdict emission.
struct AuthorizedSmtUnsatPublication {
    _publication: Option<SmtUnsatPublicationTransaction>,
}

impl AuthorizedSmtUnsatPublication {
    fn validate(&self) -> Result<(), String> {
        let Some(publication) = &self._publication else {
            return Ok(());
        };
        publication.validate().map_err(|error| {
            format!("same-run SMT publication lost namespace authority before UNSAT: {error}")
        })
    }

    fn commit(&mut self) {
        if let Some(publication) = &mut self._publication {
            publication.invalidate_on_drop = false;
        }
    }
}

enum AletheProofPublication {
    Ready(Option<Box<SmtUnsatPublicationTransaction>>),
    RejectToUnknown { reason: String, diagnostic: String },
    Fatal(String),
}

fn write_alethe_proof(
    executor: &Executor,
    transcript: &SmtTranscriptState,
    proof_config: &ProofConfig,
    problem: ProofArtifactProblem<'_>,
    theory: ProofArtifactTheoryMetadata,
) -> AletheProofPublication {
    if !transcript.public_unsat_artifacts_allowed() {
        return AletheProofPublication::Ready(None);
    }
    if proof_config.format != ProofFormat::Alethe {
        return AletheProofPublication::Fatal(format!(
            "proof file '{}' uses DRAT/LRAT/Lean4 format, but SMT-LIB solving produces Alethe proofs",
            proof_config.path
        ));
    }
    if !executor.last_result_is_unsat() {
        return AletheProofPublication::Ready(None);
    }
    // #8759: In strict-proof mode, suppress proof file writing when the
    // terminal derivation rides on a trust fallback. The CLI has already
    // printed `unknown` + `(:reason-unknown (incomplete proof-trusted))`;
    // emitting a trust-tainted "UNSAT proof" would contradict that verdict.
    if strict_proofs_enabled() && terminal_trust_detected(executor) {
        return AletheProofPublication::Ready(None);
    }
    // #8821: Use the fallible API so printer errors (e.g., missing Farkas
    // annotation for la_generic / lia_generic steps) abort with a non-zero
    // exit status instead of silently writing an `(error ...)` document
    // that a user might mistake for a legitimate proof file.
    //
    // Use the same problem-scoped path as `(get-proof)`: symbols declared by
    // the SMT-LIB problem belong in the problem file, not in the Alethe proof
    // stream that Carcara checks against that problem.
    //
    // Failure posture depends on provenance: an explicit `--proof FILE` fails
    // loud (exit 1) if AY cannot render a checkable certificate. A *synthesized
    // default* certificate (proof-carrying-on-by-default, no explicit `--proof`)
    // must NOT fail the run — the UNSAT verdict is unchanged; only the optional
    // certificate is missing — so it warns and continues.
    let proof_required_by_firewall = crate::FIREWALL_LEAN_DIR.get().is_some();
    let default_only = proof_config.synthesized_default
        && proof_config.artifact_path.is_none()
        && !proof_required_by_firewall;
    let optional_default = default_only && !strict_proofs_enabled();
    let strict_default = default_only && strict_proofs_enabled();
    // #rss-vs-z3: STREAM the certificate to disk instead of materializing it
    // as one in-memory String. Large default-mode certificates (pgm_protocol.4
    // renders 785MB of Alethe) transiently held ~1.5x their size in RAM during
    // String growth — the dominant share of a 1.4GB peak RSS on a 60MB solve.
    // The byte stream is identical to the previous `String` + `fs::write`
    // path. Render into a temp file in the target directory and rename on
    // success so failure modes match the old semantics exactly: no partial
    // certificate ever appears at the target path, and a pre-existing file
    // there is left untouched on failure.
    if executor.last_proof().is_none() {
        if optional_default {
            safe_eprintln!(
                "c warning: no proof certificate emitted (UNSAT produced no reconstructable proof); pass --strict-proofs to require one"
            );
            return AletheProofPublication::Ready(None);
        }
        if strict_default {
            return AletheProofPublication::RejectToUnknown {
                reason: "(incomplete proof-unavailable)".to_string(),
                diagnostic: format!(
                    "strict proof mode rejected UNSAT because {} has no reconstructable proof",
                    proof_config.path
                ),
            };
        }
        let request = if proof_required_by_firewall {
            "--emit-firewall-lean"
        } else if proof_config.artifact_path.is_some() {
            "--proof-artifact"
        } else {
            "--proof"
        };
        return AletheProofPublication::Fatal(format!(
            "{request} requires {}, but UNSAT produced no reconstructable proof",
            proof_config.path
        ));
    }
    let target_path = std::path::Path::new(&proof_config.path);
    let stream_result = match create_artifact_temp_file(target_path) {
        Ok((resolved_target, created_temp_path, file)) => {
            let mut writer = ProofDigestWriter::new(BufWriter::with_capacity(1 << 20, file));
            let render = executor.try_export_last_proof_alethe_for_problem_scope_to(&mut writer);
            match render {
                Some(Ok(())) => {
                    use std::io::Write as _;
                    let flush_result = writer
                        .flush()
                        .and_then(|()| writer.inner().get_ref().sync_all())
                        .map_err(ay_proof::AletheStreamError::Io);
                    let proof_digest = writer.digest();
                    match flush_result {
                        Ok(()) => match writer.into_inner().into_inner() {
                            Ok(file) => {
                                match publish_artifact_temp_noreplace(
                                    &created_temp_path,
                                    &resolved_target,
                                ) {
                                    Ok(()) => Ok((proof_digest, file, resolved_target)),
                                    Err(error) => Err(alethe_error_after_invalidation(
                                        ay_proof::AletheStreamError::Io(error),
                                        &file,
                                    )),
                                }
                            }
                            Err(error) => {
                                let primary =
                                    io::Error::new(error.error().kind(), error.error().to_string());
                                let buffered = error.into_inner();
                                Err(alethe_error_after_invalidation(
                                    ay_proof::AletheStreamError::Io(primary),
                                    buffered.get_ref(),
                                ))
                            }
                        },
                        Err(error) => Err(alethe_error_after_invalidation(
                            error,
                            writer.inner().get_ref(),
                        )),
                    }
                }
                Some(Err(error)) => Err(alethe_error_after_invalidation(
                    error,
                    writer.inner().get_ref(),
                )),
                None => unreachable!("last_proof presence checked above"),
            }
        }
        Err(error) => Err(ay_proof::AletheStreamError::Io(error)),
    };
    let (proof_digest, proof_file, proof_path) = match stream_result {
        Ok(publication) => publication,
        Err(ay_proof::AletheStreamError::Print(error)) => {
            if optional_default {
                safe_eprintln!(
                    "c warning: no proof certificate emitted (proof not fully checkable: {error}); pass --strict-proofs to require one"
                );
                return AletheProofPublication::Ready(None);
            }
            if strict_default {
                return AletheProofPublication::RejectToUnknown {
                    reason: "(incomplete proof-unrenderable)".to_string(),
                    diagnostic: format!(
                        "strict proof mode rejected UNSAT because proof rendering failed: {error}"
                    ),
                };
            }
            return AletheProofPublication::Fatal(if proof_config.synthesized_default {
                format!(
                    "a required default proof at {} could not be rendered: {error}",
                    proof_config.path
                )
            } else {
                format!(
                    "refusing to write unverifiable proof to {} (#8821): {error}",
                    proof_config.path
                )
            });
        }
        Err(ay_proof::AletheStreamError::Io(error)) => {
            if optional_default {
                // A synthesized-default certificate is optional and AY-specific (z3
                // writes no proof by default). A write failure — most commonly a
                // read-only input directory (nix store, docker RO mount, CI cache,
                // mounted corpus) — must NOT change the exit code: the UNSAT verdict
                // is already on stdout and is unaffected. Warn and continue, exactly
                // as the render-failure branches above do for the default case.
                // (Previously this exited 1 with a correct `unsat` on stdout, which
                // broke every read-only deployment.)
                safe_eprintln!(
                    "c warning: could not publish a same-run default proof file {} ({error}); any pre-existing file was preserved and is stale for this run; UNSAT verdict is unaffected",
                    proof_config.path,
                );
                return AletheProofPublication::Ready(None);
            }
            if strict_default {
                return AletheProofPublication::RejectToUnknown {
                    reason: "(incomplete proof-publication-failed)".to_string(),
                    diagnostic: format!(
                        "strict proof mode rejected UNSAT because {} could not be published: {error}",
                        proof_config.path
                    ),
                };
            }
            return AletheProofPublication::Fatal(format!(
                "failed to write required proof file {}: {error}",
                proof_config.path
            ));
        }
    };
    let proof_publication = match RetainedPublication::new(
        proof_file,
        proof_path,
        PublicationPathKind::File,
    ) {
        Ok(publication) => publication,
        Err(error) => {
            if optional_default {
                safe_eprintln!(
                        "c warning: same-run optional default proof could not be sealed ({error}); UNSAT verdict is unaffected"
                    );
                return AletheProofPublication::Ready(None);
            }
            return AletheProofPublication::Fatal(format!(
                "failed to seal the retained Alethe publication: {error}"
            ));
        }
    };
    let artifact_publication = match write_sealed_proof_artifact(
        problem,
        proof_config,
        theory,
        proof_digest,
    ) {
        Ok(Some((file, path))) => {
            match RetainedPublication::new(file, path, PublicationPathKind::File) {
                Ok(publication) => Some(publication),
                Err(error) => {
                    let invalidation =
                        invalidate_smt_publication_members(&proof_publication.file, None);
                    return AletheProofPublication::Fatal(format!(
                            "failed to seal the retained proof artifact publication: {error}{invalidation}"
                        ));
                }
            }
        }
        Ok(None) => None,
        Err(error) => {
            let path = proof_config.artifact_path.as_deref().unwrap_or("<none>");
            let invalidation = invalidate_smt_publication_members(&proof_publication.file, None);
            return AletheProofPublication::Fatal(format!(
                "failed to write proof artifact {path}: {error}{invalidation}"
            ));
        }
    };
    // Publish diagnostics only after their required persistent Alethe proof and
    // any requested proof metadata are durable. If a later participant fails,
    // invalidate the exact already-published inodes before releasing UNSAT.
    let firewall_publication = match maybe_emit_firewall_lean(executor) {
        Ok(publication) => publication,
        Err(error) => {
            let invalidation = invalidate_smt_publication_members(
                &proof_publication.file,
                artifact_publication
                    .as_ref()
                    .map(|publication| &publication.file),
            );
            return AletheProofPublication::Fatal(format!("{error}{invalidation}"));
        }
    };
    let mut publication = SmtUnsatPublicationTransaction::new(
        proof_publication,
        artifact_publication,
        firewall_publication,
    );
    if let Err(error) = publication.validate() {
        let invalidation = publication.invalidate_exact();
        if optional_default {
            safe_eprintln!(
                "c warning: same-run optional default proof lost publication authority ({error}{invalidation}); UNSAT verdict is unaffected"
            );
            return AletheProofPublication::Ready(None);
        }
        return AletheProofPublication::Fatal(format!(
            "same-run SMT publication lost namespace authority before UNSAT: {error}{invalidation}"
        ));
    }
    AletheProofPublication::Ready(Some(Box::new(publication)))
}

fn alethe_error_after_invalidation(
    primary: ay_proof::AletheStreamError,
    file: &std::fs::File,
) -> ay_proof::AletheStreamError {
    match invalidate_retained_artifact(file) {
        Ok(()) => primary,
        Err(invalidation) => ay_proof::AletheStreamError::Io(io::Error::other(format!(
            "{primary}; invalidating the retained proof descriptor also failed: {invalidation}"
        ))),
    }
}

fn invalidate_smt_publication_members(
    proof_file: &std::fs::File,
    artifact_file: Option<&std::fs::File>,
) -> String {
    let mut errors = Vec::new();
    if let Some(artifact_file) = artifact_file {
        if let Err(error) = invalidate_retained_artifact(artifact_file) {
            errors.push(format!("proof artifact: {error}"));
        }
    }
    if let Err(error) = invalidate_retained_artifact(proof_file) {
        errors.push(format!("Alethe proof: {error}"));
    }
    if errors.is_empty() {
        "; exact same-run proof publications were invalidated".to_string()
    } else {
        format!(
            "; WARNING: retained publication invalidation also failed ({})",
            errors.join("; ")
        )
    }
}

fn abort_smt_unsat_publication(transcript: &mut SmtTranscriptState) -> String {
    let state = std::mem::replace(
        &mut transcript.smt_unsat_publication,
        SmtUnsatPublicationState::Rejected,
    );
    match state {
        SmtUnsatPublicationState::Prepared(mut publication) => publication.invalidate_exact(),
        SmtUnsatPublicationState::Unprepared
        | SmtUnsatPublicationState::ReadyWithoutArtifacts
        | SmtUnsatPublicationState::Committed
        | SmtUnsatPublicationState::Rejected => String::new(),
    }
}

fn take_smt_unsat_publication_authority(
    transcript: &mut SmtTranscriptState,
) -> Result<AuthorizedSmtUnsatPublication, String> {
    let state = std::mem::replace(
        &mut transcript.smt_unsat_publication,
        SmtUnsatPublicationState::Rejected,
    );
    let authority = match state {
        SmtUnsatPublicationState::ReadyWithoutArtifacts => {
            AuthorizedSmtUnsatPublication { _publication: None }
        }
        SmtUnsatPublicationState::Prepared(publication) => (*publication).into_authority()?,
        SmtUnsatPublicationState::Unprepared => {
            return Err("SMT UNSAT artifacts were not prepared before publication".to_string());
        }
        SmtUnsatPublicationState::Committed => {
            return Err("SMT UNSAT publication authority was already consumed".to_string());
        }
        SmtUnsatPublicationState::Rejected => {
            return Err("SMT UNSAT publication authority was rejected".to_string());
        }
    };
    Ok(authority)
}

/// Settle every later participant, acquire the retained publication authority,
/// and emit only while that authority still owns all same-run descriptors.
fn publish_authorized_pending_smt_unsat(
    transcript: &mut SmtTranscriptState,
    settle_trace: impl FnOnce(
        &mut SmtTranscriptState,
    ) -> Result<Option<ay_sat::SettledDecisionTrace>, String>,
    emit: impl FnOnce(&SmtTranscriptState, &str),
) -> Result<bool, String> {
    if transcript.pending_unsat_output.is_none() {
        return Ok(false);
    }
    let mut trace_publication = match settle_trace(transcript) {
        Ok(publication) => publication,
        Err(error) => {
            let invalidation = abort_smt_unsat_publication(transcript);
            return Err(format!("{error}{invalidation}"));
        }
    };
    let mut authority = take_smt_unsat_publication_authority(transcript)?;
    if let Some(trace_publication) = &trace_publication {
        if let Err(error) = trace_publication.validate() {
            transcript.smt_unsat_publication = SmtUnsatPublicationState::Rejected;
            return Err(format!(
                "settled decision trace lost same-run authority before UNSAT: {error}"
            ));
        }
    }
    if let Err(error) = authority.validate() {
        transcript.smt_unsat_publication = SmtUnsatPublicationState::Rejected;
        return Err(error);
    }
    let Some(output) = transcript.pending_unsat_output.take() else {
        transcript.smt_unsat_publication = SmtUnsatPublicationState::Rejected;
        return Err("pending SMT UNSAT disappeared before publication".to_string());
    };
    emit(transcript, &output);
    authority.commit();
    if let Some(trace_publication) = &mut trace_publication {
        trace_publication.commit();
    }
    transcript.smt_unsat_publication = SmtUnsatPublicationState::Committed;
    Ok(true)
}

fn fail_required_unsat_publication(
    transcript: &mut SmtTranscriptState,
    error: impl std::fmt::Display,
) -> ! {
    transcript.reject_result_certification("(incomplete required-artifact-publication-failed)");
    invalidate_artifacts_for_rejected_result();
    if let Err(trace_error) = invalidate_decision_trace_for_public_mismatch(transcript) {
        safe_eprintln!(
            "Error: required UNSAT publication failed ({error}); decision trace cleanup also failed: {trace_error}"
        );
    } else {
        safe_eprintln!("Error: required UNSAT publication failed: {error}");
    }
    let _ = io::stdout().flush();
    let _ = io::stderr().flush();
    std::process::exit(1);
}

fn finalize_optional_smt_unsat_publication(
    publication: SmtUnsatPublicationTransaction,
) -> Result<(), String> {
    let mut authority = publication.into_authority()?;
    authority.commit();
    Ok(())
}

fn finalize_smt_unsat_artifacts(
    executor: &mut Executor,
    transcript: &mut SmtTranscriptState,
    proof_config: Option<&ProofConfig>,
    problem: ProofArtifactProblem<'_>,
    theory: ProofArtifactTheoryMetadata,
) {
    if !matches!(
        &transcript.smt_unsat_publication,
        SmtUnsatPublicationState::Unprepared
    ) || !transcript.public_unsat_artifacts_allowed()
    {
        return;
    }
    let Some(proof_config) = proof_config else {
        transcript.smt_unsat_publication = SmtUnsatPublicationState::ReadyWithoutArtifacts;
        return;
    };
    match write_alethe_proof(executor, transcript, proof_config, problem, theory) {
        AletheProofPublication::Ready(publication) => {
            if transcript.defer_unsat_publication {
                transcript.smt_unsat_publication = match publication {
                    Some(publication) => SmtUnsatPublicationState::Prepared(publication),
                    None => SmtUnsatPublicationState::ReadyWithoutArtifacts,
                };
            } else {
                if required_smt_unsat_publication(Some(proof_config)) {
                    fail_required_unsat_publication(
                        transcript,
                        "required SMT UNSAT publication was not deferred before output",
                    );
                }
                // A synthesized default proof is best-effort and its verdict is
                // not deferred. Preserve that behavior, while still validating
                // a successfully written same-run artifact before releasing its
                // retained descriptors.
                if let Some(publication) = publication {
                    if let Err(error) = finalize_optional_smt_unsat_publication(*publication) {
                        safe_eprintln!(
                            "c warning: same-run optional default proof was invalidated before finalization ({error}); UNSAT verdict is unaffected"
                        );
                    }
                }
                transcript.smt_unsat_publication = SmtUnsatPublicationState::Committed;
            }
        }
        AletheProofPublication::RejectToUnknown { reason, diagnostic } => {
            safe_eprintln!("c warning: {diagnostic}; publishing unknown");
            let downgraded = executor.reject_last_unsat_as_unknown();
            debug_assert!(downgraded, "strict proof rejection started from UNSAT");
            transcript.reject_result_certification(reason);
            invalidate_artifacts_for_rejected_result();
            if let Err(error) = invalidate_decision_trace_for_public_mismatch(transcript) {
                fail_required_unsat_publication(transcript, error);
            }
            if !print_synthesized_public_unknown(transcript) {
                safe_eprintln!(
                    "Error: synthesized UNKNOWN was withheld because decision-trace invalidation failed"
                );
                let _ = io::stdout().flush();
                let _ = io::stderr().flush();
                std::process::exit(1);
            }
            transcript.smt_unsat_publication = SmtUnsatPublicationState::Rejected;
        }
        AletheProofPublication::Fatal(error) => {
            fail_required_unsat_publication(transcript, error);
        }
    }
}

fn publish_pending_smt_unsat(
    executor: &mut Executor,
    transcript: &mut SmtTranscriptState,
    proof_config: Option<&ProofConfig>,
    problem: ProofArtifactProblem<'_>,
    theory: ProofArtifactTheoryMetadata,
) {
    if transcript.pending_unsat_output.is_none() {
        return;
    }
    finalize_smt_unsat_artifacts(executor, transcript, proof_config, problem, theory);
    // A proof gate may downgrade the pending UNSAT to a synthesized UNKNOWN,
    // invalidate the trace, and consume the pending line itself.
    if transcript.pending_unsat_output.is_none() {
        return;
    }
    let result = publish_authorized_pending_smt_unsat(
        transcript,
        |transcript| {
            settle_authoritative_decision_trace(
                transcript,
                ay_core::trace_config().decision_trace_path.as_deref(),
            )
        },
        print_regular_line,
    );
    match result {
        Ok(true) => {
            super::mark_verdict_printed();
        }
        Ok(false) => {}
        Err(error) => fail_required_unsat_publication(transcript, error),
    }
}

const DIMACS_STDIN_SNIFF_LIMIT: usize = 64 * 1024;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum DimacsPrefixKind {
    Dimacs,
    NotDimacs,
    NeedMore,
}

fn trim_ascii(mut bytes: &[u8]) -> &[u8] {
    while bytes
        .first()
        .is_some_and(|b| matches!(b, b' ' | b'\t' | b'\r' | b'\n'))
    {
        bytes = &bytes[1..];
    }
    while bytes
        .last()
        .is_some_and(|b| matches!(b, b' ' | b'\t' | b'\r' | b'\n'))
    {
        bytes = &bytes[..bytes.len() - 1];
    }
    bytes
}

fn classify_dimacs_prefix(prefix: &[u8], eof: bool) -> DimacsPrefixKind {
    let mut line_start = 0;
    while line_start < prefix.len() {
        let mut line_end = line_start;
        while line_end < prefix.len() && prefix[line_end] != b'\n' {
            line_end += 1;
        }
        if line_end == prefix.len() && !eof {
            return DimacsPrefixKind::NeedMore;
        }

        let line = trim_ascii(&prefix[line_start..line_end]);
        if line.is_empty() || line.starts_with(b"c") || line.starts_with(b";") {
            line_start = line_end.saturating_add(1);
            continue;
        }
        if line.starts_with(b"p cnf") {
            return DimacsPrefixKind::Dimacs;
        }
        return DimacsPrefixKind::NotDimacs;
    }

    if eof {
        DimacsPrefixKind::NotDimacs
    } else {
        DimacsPrefixKind::NeedMore
    }
}

fn read_piped_input_or_stream_dimacs<R>(
    mut reader: R,
    stats_cfg: stats_output::StatsConfig,
    proof_config: Option<&ProofConfig>,
) -> io::Result<Option<String>>
where
    R: Read,
{
    if let Some(proof) =
        proof_config.filter(|_| !VERIFY_PROOF_ENABLED.load(std::sync::atomic::Ordering::SeqCst))
    {
        let mut prefix = Vec::new();
        let mut eof = false;

        loop {
            match classify_dimacs_prefix(&prefix, eof) {
                DimacsPrefixKind::Dimacs => {
                    reject_bv_cnf_export_for_non_smt_route("DIMACS stdin");
                    reject_firewall_emission_for_route("DIMACS stdin");
                    reject_firewall_verification_for_route("DIMACS stdin");
                    let replay = io::Cursor::new(prefix).chain(reader);
                    dimacs::run_dimacs_proof_from_reader(replay, stats_cfg, proof);
                    return Ok(None);
                }
                DimacsPrefixKind::NotDimacs => break,
                DimacsPrefixKind::NeedMore => {}
            }

            if eof || prefix.len() >= DIMACS_STDIN_SNIFF_LIMIT {
                break;
            }

            let mut buf = [0u8; 8192];
            let limit = (DIMACS_STDIN_SNIFF_LIMIT - prefix.len()).min(buf.len());
            let read = reader.read(&mut buf[..limit])?;
            if read == 0 {
                eof = true;
            } else {
                prefix.extend_from_slice(&buf[..read]);
            }
        }

        let mut bytes = prefix;
        reader.read_to_end(&mut bytes)?;
        return String::from_utf8(bytes)
            .map(Some)
            .map_err(|error| io::Error::new(io::ErrorKind::InvalidData, error));
    }

    let mut content = String::new();
    reader.read_to_string(&mut content)?;
    Ok(Some(content))
}

fn reject_bv_cnf_export_for_non_smt_route(route: &str) {
    if ay_core::trace_config().dump_bv_cnf_path.is_none() {
        return;
    }
    if let Err(error) = Executor::invalidate_bv_cnf_export_for_rejected_check() {
        eprintln_smt_error(error.to_string());
    } else {
        eprintln_smt_error(format!(
            "artifact export failed: --dump-bv-cnf supports only SMT-LIB pure QF_BV checks, not the {route} route"
        ));
    }
    std::process::exit(1);
}

/// Incremental, lexing-aware paren-depth tracker for the line-by-line stdin
/// reader (#inc-lra-parse).
///
/// The line-by-line loop accumulates physical lines into a buffer and must
/// decide when the buffer holds one or more *complete* top-level commands
/// before it hands the buffer to the (O(buffer)) `parse`. The historical gate
/// re-scanned the entire buffer every line (via `parse` + a naive
/// `matches('(')` count), which is O(command_lines × command_bytes) — quadratic
/// on the giant multi-line asserts emitted by BMC k-unrolling (a single assert
/// can span thousands of lines), and the dominant cost on incremental QF_LRA.
///
/// This tracker maintains the running SMT-LIB paren depth by scanning only each
/// *newly appended* line, correctly skipping `;` line comments, `"…"` string
/// literals (with `""` escape), and `|…|` quoted symbols — all of which may
/// carry an unbalanced paren and the latter two of which may span lines. When
/// the depth is `> 0` the command is provably incomplete, so the loop keeps
/// reading without touching `parse`, turning the accumulation into O(bytes).
///
/// Soundness: this only decides *when* to attempt a parse — never the parse
/// result. When the depth reaches `<= 0` the existing `parse` + naive-paren
/// recovery runs exactly as before, so a mis-tracked depth can at worst trigger
/// a parse that then self-heals through the unchanged error path. Gated by
/// `AY_INC_LINEAR_PARSE` (default on; set to `0`/`off` to restore the
/// parse-every-line behavior).
#[derive(Default)]
struct IncrementalDepth {
    depth: i64,
    in_string: bool,
    in_pipe: bool,
}

impl IncrementalDepth {
    /// Fold one freshly read physical line (including any trailing newline)
    /// into the running paren depth.
    fn feed(&mut self, line: &str) {
        let b = line.as_bytes();
        let mut i = 0;
        while i < b.len() {
            let c = b[i];
            if self.in_string {
                if c == b'"' {
                    // `""` inside a string literal is an escaped quote: stay in.
                    if i + 1 < b.len() && b[i + 1] == b'"' {
                        i += 2;
                        continue;
                    }
                    self.in_string = false;
                }
                i += 1;
                continue;
            }
            if self.in_pipe {
                if c == b'|' {
                    self.in_pipe = false;
                }
                i += 1;
                continue;
            }
            match c {
                // Line comment: the rest of this physical line is inert.
                b';' => break,
                b'"' => self.in_string = true,
                b'|' => self.in_pipe = true,
                b'(' => self.depth += 1,
                b')' => self.depth -= 1,
                _ => {}
            }
            i += 1;
        }
    }
}

pub(super) fn run_interactive(
    stats_cfg: stats_output::StatsConfig,
    proof_config: Option<&ProofConfig>,
    incremental: bool,
    visualization: Option<VisualizationFormat>,
    verbose: bool,
    validate: bool,
) {
    use std::io::IsTerminal;

    let stdin = io::stdin();
    let is_tty = stdin.is_terminal();

    // If stdin is piped (not a TTY) and not in incremental mode:
    //  - SMT-LIB is STREAMED command-by-command (like z3's `-in`), so a
    //    coprocess driver that holds stdin open sees each verdict and is not
    //    deadlocked by a read-to-EOF.
    //  - DIMACS and CHC are batch formats (whole content, never coprocess-driven)
    //    and keep the buffered path.
    // `--incremental` always uses the line-by-line path (#5360).
    if !is_tty && !incremental {
        let mut locked = stdin.lock();
        // Classify from a bounded prefix WITHOUT draining the stream. The sniff
        // reads only until the format is decided; a coprocess sends a full
        // command batch up front, so this does not block on input the peer is
        // withholding until it gets our reply. `classify_dimacs_prefix` returns
        // NotDimacs as soon as it sees the first `(` command line, so an SMT
        // coprocess is classified from its very first write.
        let mut prefix = Vec::new();
        let mut eof = false;
        while !eof
            && prefix.len() < DIMACS_STDIN_SNIFF_LIMIT
            && classify_dimacs_prefix(&prefix, eof) == DimacsPrefixKind::NeedMore
        {
            let mut buf = [0u8; 8192];
            let want = (DIMACS_STDIN_SNIFF_LIMIT - prefix.len()).min(buf.len());
            match locked.read(&mut buf[..want]) {
                Ok(0) => eof = true,
                Ok(read) => prefix.extend_from_slice(&buf[..read]),
                Err(e) => {
                    eprintln_smt_error(format_args!("Error reading stdin: {e}"));
                    std::process::exit(1);
                }
            }
        }

        let is_dimacs = classify_dimacs_prefix(&prefix, true) == DimacsPrefixKind::Dimacs;
        // CHC / fixedpoint are SMT-syntax but batch: their markers (`set-logic
        // HORN`, `declare-rel`/`rule`/`query`) appear in the first command or two,
        // well inside the sniff window.
        let is_chc_family = !is_dimacs && {
            let prefix_str = String::from_utf8_lossy(&prefix);
            is_horn_logic(&prefix_str) || is_fixedpoint_format(&prefix_str)
        };

        if !is_dimacs && !is_chc_family {
            // SMT-LIB: stream. Chain the sniffed prefix back in front of the live
            // stream so no byte is lost.
            let reader = io::BufReader::new(io::Cursor::new(prefix).chain(locked));
            run_interactive_smt_stream(
                reader,
                false,
                stats_cfg,
                proof_config,
                visualization,
                verbose,
                validate,
            );
            return;
        }

        // Batch (DIMACS / CHC): the existing buffered dispatch, now fed the
        // sniffed prefix followed by the rest of the stream.
        let combined = io::Cursor::new(prefix).chain(locked);
        let content = match read_piped_input_or_stream_dimacs(combined, stats_cfg, proof_config) {
            Ok(Some(content)) => content,
            Ok(None) => return,
            Err(e) => {
                eprintln_smt_error(format_args!("Error reading stdin: {e}"));
                std::process::exit(1);
            }
        };

        // Check for DIMACS CNF format (content-based detection for stdin)
        if dimacs::is_dimacs_format(&content) {
            reject_bv_cnf_export_for_non_smt_route("DIMACS stdin");
            reject_firewall_emission_for_route("DIMACS stdin");
            reject_firewall_verification_for_route("DIMACS stdin");
            dimacs::run_dimacs_from_content(&content, stats_cfg, proof_config);
            return;
        }

        // Check for HORN logic
        if is_horn_logic(&content) {
            reject_decision_trace_for_route("CHC stdin");
            reject_bv_cnf_export_for_non_smt_route("CHC stdin");
            reject_firewall_emission_for_route("CHC stdin");
            reject_firewall_verification_for_route("CHC stdin");
            reject_explicit_proof_verification_for_route("CHC", "replay");
            let _ = chc_runner::run_chc_from_content(
                &content,
                verbose,
                validate,
                stats_cfg,
                proof_config,
            );
            return;
        }

        // Check for Z3 fixedpoint (declare-rel/rule/query) scripts, which the
        // CHC engine decides with the correct (inverted) sat/unsat polarity.
        if is_fixedpoint_format(&content) {
            reject_decision_trace_for_route("fixedpoint stdin");
            reject_bv_cnf_export_for_non_smt_route("fixedpoint stdin");
            reject_firewall_emission_for_route("fixedpoint stdin");
            reject_firewall_verification_for_route("fixedpoint stdin");
            reject_explicit_proof_verification_for_route("fixedpoint", "CHC replay");
            let _ = chc_runner::run_chc_from_content(
                &content,
                verbose,
                validate,
                stats_cfg,
                proof_config,
            );
            return;
        }

        // Standard DPLL(T) path. Drive the SAME per-command `CommandStream`
        // recovery as file input (`run_smt_file_content`) so a malformed or
        // unknown command prints a z3-style `(error "...")` and execution
        // CONTINUES (advertised `:error-behavior continued-execution`), instead
        // of the old whole-buffer `parse` that aborted the entire stream — and
        // dropped every later command, including `check-sat` — on the first
        // parse error. Keeps piped `-in` behavior identical to file input.
        run_smt_file_content_on_dedicated_stack(
            &content,
            None,
            stats_cfg,
            proof_config,
            visualization,
        );
        return;
    }

    // Line-by-line mode: TTY interactive OR piped incremental (#5360).
    run_interactive_smt_stream(
        stdin.lock(),
        is_tty,
        stats_cfg,
        proof_config,
        visualization,
        verbose,
        validate,
    );
}

/// Drive SMT-LIB input command-by-command from `reader`, flushing stdout after
/// every response so a pipe or coprocess peer sees each verdict immediately.
///
/// This is the path z3's `-in` uses. Reaching it for piped input (not only for a
/// TTY or `--incremental`) is what lets a coprocess driver that holds stdin open
/// — Why3, Dafny, Boogie, an IDE — work instead of deadlocking on a read-to-EOF.
/// `is_tty` only controls whether the interactive prompt is printed.
fn run_interactive_smt_stream(
    mut reader: impl BufRead,
    is_tty: bool,
    stats_cfg: stats_output::StatsConfig,
    proof_config: Option<&ProofConfig>,
    visualization: Option<VisualizationFormat>,
    verbose: bool,
    validate: bool,
) {
    reject_explicit_proof_verification_for_route("SMT-LIB", "Alethe");
    if is_tty {
        safe_println!("{}", super::features::interactive_banner());
    }

    let mut stdout = io::stdout();
    let mut input_buffer = String::new();
    // Running 1-based line number of the first line still in `input_buffer`, so
    // errors report their true position in the whole session (z3's `-in` does not
    // reset the line counter per command). Advanced by the lines consumed each
    // time the buffer is parsed and cleared.
    let mut line_base = 1usize;
    // Linear-time completeness gate for the accumulation buffer (#inc-lra-parse).
    // Default on; `AY_INC_LINEAR_PARSE=0`/`off` restores parse-every-line.
    let linear_parse = std::env::var_os("AY_INC_LINEAR_PARSE")
        .map(|v| v != "0" && v != "off" && v != "false")
        .unwrap_or(true);
    let mut depth_scan = IncrementalDepth::default();
    let mut artifact_input = String::new();
    let mut executor = new_executor();
    let mut transcript = SmtTranscriptState::new();
    let mut formula_stats = FormulaStats::default();
    let mut smt_logic: Option<String> = None;
    // Z3's `-in` is a live stream, so HORN cannot be routed by waiting for
    // EOF. Accumulate only the problem-defining commands, solve at each
    // `check-sat`, and retain the independently validated invariant for the
    // following `get-model` query.
    let mut chc_stream_mode = false;
    let mut chc_problem_input = String::new();
    let mut chc_last_model: Option<String> = None;
    // Rewrite synthesized non-Alethe configs to Alethe for SMT
    // (Finding A in the development design notes).
    let adapted = adapt_proof_config_for_smt(proof_config);
    transcript.defer_unsat_publication = required_smt_unsat_publication(adapted.as_ref());
    seed_smt_transcript_protections_or_exit(&mut transcript, None, adapted.as_ref());
    let retain_artifact_input = visualization.is_some()
        || adapted
            .as_ref()
            .is_some_and(|proof| proof.artifact_path.is_some());
    if let Some(proof) = adapted.as_ref() {
        if proof.format != ProofFormat::Alethe {
            safe_eprintln!(
                "Error: proof file '{}' uses DRAT/LRAT/Lean4 format, but SMT-LIB mode requires Alethe output",
                proof.path
            );
            std::process::exit(1);
        }
        if proof.binary {
            safe_eprintln!(
                "Error: --proof-binary is unsupported for SMT-LIB Alethe output; omit the flag to emit authenticated text"
            );
            std::process::exit(1);
        }
        executor.set_produce_proofs(true);
        apply_default_proof_budget(&mut executor, proof);
    } else if !ResultGateRequests::current().any() {
        // No proof can be emitted this session (`--no-proof` / `--z3-mode` /
        // competition mode), and no mandatory result/artifact gate needs the
        // internal proof surface: skip retaining a deep parsed-AST clone of
        // every assertion (~190 MB of a 318 MB peak on a 6 MB QF_UF input,
        // #rss-vs-z3). An in-script `(set-option :produce-proofs true)`
        // re-enables retention.
        executor.set_retain_parsed_assertions(false);
    }

    loop {
        exit_if_timed_out_with_transcript_context(&transcript);
        if is_tty {
            safe_print!("> ");
        }
        let _ = stdout.flush();

        let mut line = String::new();
        let read_result = reader.read_line(&mut line);
        let eof = match read_result {
            Ok(0) => true,
            Ok(_) => false,
            Err(e) => {
                safe_eprintln!("Error reading input: {e}");
                break;
            }
        };

        if eof {
            if skip_smt_trivia(&input_buffer).is_empty() {
                break;
            }
        } else {
            input_buffer.push_str(&line);
        }

        // Linear completeness gate: while the buffer's top-level parens are
        // still open the command cannot be complete, so keep reading without
        // re-lexing the whole (potentially multi-megabyte) buffer. This is the
        // dominant cost on multi-line BMC asserts. See `IncrementalDepth`.
        if linear_parse && !eof {
            depth_scan.feed(&line);
            if depth_scan.depth > 0 {
                continue;
            }
        }

        match parse(&input_buffer) {
            Ok(commands) => {
                let command_sources = collect_command_sources_from_line(&input_buffer, line_base);
                line_base += input_buffer.matches('\n').count();
                input_buffer.clear();
                depth_scan = IncrementalDepth::default();
                for (cmd_index, cmd) in commands.iter().enumerate() {
                    set_current_command_source(&mut transcript, &command_sources, cmd_index);
                    if smt_logic.is_none() {
                        smt_logic =
                            logic_from_commands(std::slice::from_ref(cmd)).map(str::to_owned);
                    }
                    formula_stats.observe_command(cmd);
                    let enters_horn = matches!(
                        cmd,
                        Command::SetLogic(logic) if logic.eq_ignore_ascii_case("HORN")
                    );
                    if chc_stream_mode || enters_horn {
                        if !chc_stream_mode {
                            reject_decision_trace_for_route("incremental CHC stdin");
                            reject_bv_cnf_export_for_non_smt_route("incremental CHC stdin");
                            reject_firewall_emission_for_route("incremental CHC stdin");
                            reject_firewall_verification_for_route("incremental CHC stdin");
                            reject_explicit_proof_verification_for_route(
                                "incremental CHC",
                                "CHC replay",
                            );
                            chc_stream_mode = true;
                        }

                        match cmd {
                            Command::Exit => {
                                cleanup_temp_proof(adapted.as_ref());
                                return;
                            }
                            Command::Reset => {
                                chc_stream_mode = false;
                                chc_problem_input.clear();
                                chc_last_model = None;
                                formula_stats = FormulaStats::default();
                                smt_logic = None;
                            }
                            Command::GetModel => match &chc_last_model {
                                Some(model) => safe_print!("{model}"),
                                None => safe_println!("(error \"model is not available\")"),
                            },
                            Command::CheckSat => {
                                let mut solve_input = chc_problem_input.clone();
                                solve_input.push_str("(check-sat)\n");
                                chc_last_model = chc_runner::run_chc_from_content(
                                    &solve_input,
                                    verbose,
                                    validate,
                                    stats_cfg,
                                    proof_config,
                                );
                            }
                            _ => {
                                if let Some(source) = command_sources.get(cmd_index) {
                                    // Any accepted problem command starts a new
                                    // model epoch. Serving the previously
                                    // certified invariant after an assertion,
                                    // rule, declaration, push, or pop would
                                    // attach stale evidence to a changed CHC
                                    // problem. A fresh check-sat is the only
                                    // operation allowed to repopulate it.
                                    chc_last_model = None;
                                    chc_problem_input.push_str(&source.text);
                                    if !source.text.ends_with('\n') {
                                        chc_problem_input.push('\n');
                                    }
                                }
                            }
                        }
                        let _ = stdout.flush();
                        continue;
                    }
                    if matches!(cmd, Command::Exit) {
                        publish_pending_smt_unsat(
                            &mut executor,
                            &mut transcript,
                            adapted.as_ref(),
                            ProofArtifactProblem::Text(&artifact_input),
                            ProofArtifactTheoryMetadata::smt_lib(
                                smt_logic.as_deref(),
                                Some(&formula_stats),
                            ),
                        );
                        finalize_smt_unsat_artifacts(
                            &mut executor,
                            &mut transcript,
                            adapted.as_ref(),
                            ProofArtifactProblem::Text(&artifact_input),
                            ProofArtifactTheoryMetadata::smt_lib(
                                smt_logic.as_deref(),
                                Some(&formula_stats),
                            ),
                        );
                        maybe_print_success(&transcript);
                        maybe_explain(&mut executor, &transcript);
                        maybe_visualize(&artifact_input, &mut executor, &transcript, visualization);
                        if stats_cfg.any() {
                            print_smt_stats(
                                &executor,
                                &transcript,
                                Some(&formula_stats),
                                stats_cfg,
                            );
                        }
                        maybe_write_minimal_decision_trace(&mut transcript);
                        cleanup_temp_proof(adapted.as_ref());
                        exit_if_transcript_had_recoverable_error(&transcript);
                        return;
                    }
                    if !execute_and_print(&mut executor, cmd, &mut transcript, true) {
                        let _ = stdout.flush();
                        exit_if_timed_out_with_transcript_context(&transcript);
                        cleanup_temp_proof(adapted.as_ref());
                        std::process::exit(1);
                    }
                    if matches!(cmd, Command::Reset) {
                        // A successful reset begins a fresh artifact epoch. It
                        // discards every prior accepted/rejected command and
                        // keeps payload metadata scoped to the same problem.
                        artifact_input.clear();
                        formula_stats = FormulaStats::default();
                        smt_logic = None;
                    } else if retain_artifact_input {
                        if let Some(source) = command_sources.get(cmd_index) {
                            artifact_input.push_str(&source.text);
                            if !source.text.ends_with('\n') {
                                artifact_input.push('\n');
                            }
                        }
                    }
                    publish_pending_smt_unsat(
                        &mut executor,
                        &mut transcript,
                        adapted.as_ref(),
                        ProofArtifactProblem::Text(&artifact_input),
                        ProofArtifactTheoryMetadata::smt_lib(
                            smt_logic.as_deref(),
                            Some(&formula_stats),
                        ),
                    );
                    // Flush after each command so pipe consumers see responses
                    // immediately (stdout is block-buffered when piped).
                    let _ = stdout.flush();
                    exit_if_timed_out_with_transcript_context(&transcript);
                }
            }
            Err(e) => {
                let opens = input_buffer.matches('(').count();
                let closes = input_buffer.matches(')').count();
                if eof || opens <= closes {
                    // Balanced (or over-closed) buffer that still fails to
                    // parse. `parse` is a pure function of the buffer, so
                    // re-parsing the unchanged text can never succeed — report
                    // the error we already have, mirroring file mode
                    // (`run_smt_file_content`): a recoverable `(error "...")`
                    // on the regular output channel, marked so the process
                    // still exits non-zero. Clear the per-command source first
                    // — it still points at the last successfully parsed
                    // command from a previous batch and would misattribute
                    // this error's position.
                    transcript.current_source = Some(CommandSource {
                        line: line_base,
                        column: 1,
                        text: input_buffer.clone(),
                    });
                    print_recoverable_parse_error(&mut transcript, &e);
                    invalidate_export_after_malformed_decision(&input_buffer);
                    // SOUNDNESS: mirror file mode — a problem-contributing
                    // command (e.g. a malformed `assert`) was dropped, so a
                    // later check-sat must fail closed to `unknown` instead of
                    // answering on the incomplete remainder.
                    if parse_drop_contributes_to_problem(&input_buffer) {
                        mark_problem_incomplete(&mut executor, &mut transcript);
                    }
                    line_base += input_buffer.matches('\n').count();
                    input_buffer.clear();
                    depth_scan = IncrementalDepth::default();
                }
            }
        }
    }
    if chc_stream_mode {
        cleanup_temp_proof(adapted.as_ref());
        return;
    }
    publish_pending_smt_unsat(
        &mut executor,
        &mut transcript,
        adapted.as_ref(),
        ProofArtifactProblem::Text(&artifact_input),
        ProofArtifactTheoryMetadata::smt_lib(smt_logic.as_deref(), Some(&formula_stats)),
    );
    finalize_smt_unsat_artifacts(
        &mut executor,
        &mut transcript,
        adapted.as_ref(),
        ProofArtifactProblem::Text(&artifact_input),
        ProofArtifactTheoryMetadata::smt_lib(smt_logic.as_deref(), Some(&formula_stats)),
    );
    maybe_explain(&mut executor, &transcript);
    if stats_cfg.any() {
        maybe_visualize(&artifact_input, &mut executor, &transcript, visualization);
        print_smt_stats(&executor, &transcript, Some(&formula_stats), stats_cfg);
    } else {
        maybe_visualize(&artifact_input, &mut executor, &transcript, visualization);
    }
    maybe_write_minimal_decision_trace(&mut transcript);
    cleanup_temp_proof(adapted.as_ref());
    exit_if_transcript_had_recoverable_error(&transcript);
}

/// Diagnostic for input files the CLI classifies as solver inputs and routes
/// into `ay solve` (`looks_like_input_path_arg` / `inject_solve_subcommand` in
/// main.rs) but that `ay solve` cannot parse. Returns the redirect message —
/// pointing at the dedicated subcommand where one exists — or `None` when the
/// file may be SMT-LIB/DIMACS/CHC and normal content routing should proceed.
///
/// Must be consulted BEFORE the file is read or content-sniffed: `.qdimacs`
/// keeps a `p cnf` header (the DIMACS sniffer would misroute it to the plain
/// SAT solver, where quantifier lines break), and `.aig` is binary (a
/// `read_to_string` would die with a raw read error).
// False positive: `path` is explicitly ASCII-lowercased before the suffix
// checks, and multi-part suffixes like `.wcnf.xz` don't fit `Path::extension`.
#[allow(clippy::case_sensitive_file_extension_comparisons)]
fn dedicated_subcommand_redirect(path: &str) -> Option<&'static str> {
    let lower = path.to_ascii_lowercase();
    if lower.ends_with(".fzn") {
        Some("FlatZinc input is not supported by `ay solve`; use `ay flatzinc solve FILE`")
    } else if lower.ends_with(".qdimacs") {
        Some("QDIMACS (QBF) input is not supported by `ay solve`; use `ay qbf solve FILE`")
    } else if lower.ends_with(".wcnf") || lower.ends_with(".wcnf.xz") {
        Some(
            "weighted CNF (MaxSAT) input is not supported by `ay solve`; use `ay maxsat solve FILE`",
        )
    } else if lower.ends_with(".opb") {
        Some("OPB pseudo-Boolean input is not supported by `ay solve`; use `ay pb solve FILE`")
    } else if lower.ends_with(".mps") || lower.ends_with(".lp") {
        Some("MPS/CPLEX-LP input is not supported by `ay solve`; use `ay lp solve FILE`")
    } else if lower.ends_with(".aig") || lower.ends_with(".aag") {
        Some("AIGER input is not supported by `ay solve`")
    } else if lower.ends_with(".sl") {
        Some("SyGuS input is not supported by `ay solve`")
    } else {
        None
    }
}

pub(super) fn run_file(
    path: &str,
    preflighted_input: Option<(&str, Option<&std::fs::File>)>,
    stats_cfg: stats_output::StatsConfig,
    proof_config: Option<&ProofConfig>,
    parallel_threads: Option<usize>,
    cube_and_conquer_depth: Option<usize>,
    visualization: Option<VisualizationFormat>,
    verbose: bool,
    validate: bool,
) {
    // Known non-SMT input extensions get an explicit redirect to their
    // dedicated subcommand instead of a raw parse/read error.
    if let Some(redirect) = dedicated_subcommand_redirect(path) {
        safe_eprintln!("Error: {redirect}");
        std::process::exit(1);
    }

    if preflighted_input.is_none() {
        if let Some(proof) = proof_config {
            if parallel_threads.is_none()
                && cube_and_conquer_depth.is_none()
                && dimacs::has_dimacs_file_extension(path)
            {
                reject_bv_cnf_export_for_non_smt_route("DIMACS file");
                reject_firewall_emission_for_route("DIMACS file");
                reject_firewall_verification_for_route("DIMACS file");
                dimacs::run_dimacs_proof_from_file(path, stats_cfg, proof);
                return;
            }
        }
    }

    let mut input_file = match preflighted_input {
        Some((_, Some(file))) => match file.try_clone() {
            Ok(file) => Some(file),
            Err(e) => {
                eprintln_smt_error(format_args!("Error retaining file '{path}': {e}"));
                std::process::exit(1);
            }
        },
        Some((_, None)) => None,
        None => match std::fs::File::open(path) {
            Ok(file) => Some(file),
            Err(e) => {
                eprintln_smt_error(format_args!("Error reading file '{path}': {e}"));
                std::process::exit(1);
            }
        },
    };
    let smt_source = match input_file.as_ref() {
        Some(file) => match SmtFileSource::from_open_file(std::path::Path::new(path), file) {
            Ok(source) => Some(source),
            Err(e) => {
                eprintln_smt_error(format_args!("Error identifying file '{path}': {e}"));
                std::process::exit(1);
            }
        },
        None => None,
    };
    let mut content = String::new();
    let read_result = match preflighted_input {
        Some((preflighted, _)) => {
            content.push_str(preflighted);
            Ok(())
        }
        None => input_file
            .as_mut()
            .expect("non-preloaded input must retain its open descriptor")
            .read_to_string(&mut content)
            .map(|_| ()),
    };
    match read_result {
        Ok(()) => {
            // Check for DIMACS CNF format first (by extension or content)
            if dimacs::has_cnf_extension(path) || dimacs::is_dimacs_format(&content) {
                reject_bv_cnf_export_for_non_smt_route("DIMACS file");
                reject_firewall_emission_for_route("DIMACS file");
                reject_firewall_verification_for_route("DIMACS file");
                if dimacs::has_structural_sidecar(path)
                    && (cube_and_conquer_depth.is_some() || parallel_threads.is_some())
                {
                    safe_eprintln!(
                        "c structural-sidecar: adjacent sidecar present; using checked sequential DIMACS route"
                    );
                    dimacs::run_dimacs_from_file(path, &content, stats_cfg, proof_config);
                } else if let Some(depth) = cube_and_conquer_depth {
                    let num_threads = parallel_threads.unwrap_or_else(|| {
                        std::thread::available_parallelism()
                            .map(std::num::NonZero::get)
                            .unwrap_or(4)
                    });
                    dimacs::run_dimacs_cube_and_conquer(
                        &content,
                        stats_cfg,
                        proof_config,
                        depth,
                        num_threads,
                    );
                } else if let Some(num_threads) = parallel_threads {
                    dimacs::run_dimacs_parallel(&content, stats_cfg, proof_config, num_threads);
                } else {
                    dimacs::run_dimacs_from_file(path, &content, stats_cfg, proof_config);
                }
                return;
            }

            // Check for HORN logic and route to CHC solver if found
            if is_horn_logic(&content) {
                reject_decision_trace_for_route("CHC file");
                reject_bv_cnf_export_for_non_smt_route("CHC file");
                reject_firewall_emission_for_route("CHC file");
                reject_firewall_verification_for_route("CHC file");
                reject_explicit_proof_verification_for_route("CHC", "replay");
                let _ = chc_runner::run_chc_from_content(
                    &content,
                    verbose,
                    validate,
                    stats_cfg,
                    proof_config,
                );
                return;
            }

            // Z3 fixedpoint (declare-rel/rule/query) scripts also route to the
            // CHC engine (correct inverted sat/unsat polarity handled there).
            if is_fixedpoint_format(&content) {
                reject_decision_trace_for_route("fixedpoint file");
                reject_bv_cnf_export_for_non_smt_route("fixedpoint file");
                reject_firewall_emission_for_route("fixedpoint file");
                reject_firewall_verification_for_route("fixedpoint file");
                reject_explicit_proof_verification_for_route("fixedpoint", "CHC replay");
                let _ = chc_runner::run_chc_from_content(
                    &content,
                    verbose,
                    validate,
                    stats_cfg,
                    proof_config,
                );
                return;
            }

            run_smt_file_content_on_dedicated_stack(
                &content,
                smt_source.as_ref(),
                stats_cfg,
                proof_config,
                visualization,
            );
        }
        Err(e) => {
            eprintln_smt_error(format_args!("Error reading file '{path}': {e}"));
            std::process::exit(1);
        }
    }
}

fn run_smt_file_content_on_dedicated_stack(
    content: &str,
    source: Option<&SmtFileSource>,
    stats_cfg: stats_output::StatsConfig,
    proof_config: Option<&ProofConfig>,
    visualization: Option<VisualizationFormat>,
) {
    std::thread::scope(|scope| {
        match std::thread::Builder::new()
            .name("ay-smt-file".to_string())
            .stack_size(SMT_FILE_THREAD_STACK_SIZE)
            .spawn_scoped(scope, move || {
                run_smt_file_content(content, source, stats_cfg, proof_config, visualization)
            }) {
            Ok(handle) => match handle.join() {
                Ok(()) => {}
                Err(payload) => std::panic::resume_unwind(payload),
            },
            Err(_) => run_smt_file_content(content, source, stats_cfg, proof_config, visualization),
        }
    });
}

fn run_smt_file_content(
    content: &str,
    source: Option<&SmtFileSource>,
    stats_cfg: stats_output::StatsConfig,
    proof_config: Option<&ProofConfig>,
    visualization: Option<VisualizationFormat>,
) {
    reject_explicit_proof_verification_for_route("SMT-LIB", "Alethe");
    // MILP FAST-PATH (#milp-fastpath): a QF_LRA script that is exactly a big-M
    // MILP feasibility problem — conjunctive linear rows plus 0/1 disjunctions,
    // the shape the downstream optimization consumer's mip-diff pipes in — is decided by ay-milp's branch-and-cut
    // instead of the generic DPLL(T) case-split, which produces no verdict on
    // real NN windows the MILP lane settles in minutes. Fail-closed: anything
    // outside the recognised fragment falls through to the standard lane
    // untouched, and the route is skipped when the caller asked for stats,
    // visualization, an EXPLICIT `--proof`, or a mandatory result gate — the
    // fast path cannot produce Alethe or route its verdict through those gates.
    // Solver-synthesized DEFAULT certificate configs do not block it: a
    // fast-path `sat` needs no certificate, and a fast-path `unsat` trades the
    // best-effort default certificate for a verdict the generic lane cannot
    // reach at all on this shape. The default-on DRAT/LRAT auto-check likewise
    // does not disable this SMT-only lane; an EXPLICIT `--verify-proof` is
    // rejected above because AY has no Alethe post-checker.
    let explicit_proof = proof_config.is_some_and(|p| !p.synthesized_default && !p.is_temp);
    if !explicit_proof
        // These modes promise to inspect the executor's SAT/UNSAT result before
        // it reaches stdout. The standalone MILP lane prints its own verdict
        // and cannot provide those checks/certificates, so it must not bypass
        // the common result-gate path.
        && may_use_ungated_solver_route(ResultGateRequests::current())
        // Decision traces are produced by the SAT-backed executor. The MILP
        // fast path prints directly and cannot finalize the reserved trace.
        && ay_core::trace_config().decision_trace_path.is_none()
        && visualization.is_none()
        && !stats_cfg.human
        && !stats_cfg.json
        && crate::milp_fastpath::try_milp_fastpath(content)
    {
        return;
    }

    // Per-command error recovery (continued-execution) for FILE input.
    //
    // We drive the same parser internals as `parse`, but command-by-command via
    // `CommandStream`, so a malformed or unknown command no longer aborts the
    // whole file: we print a z3-style `(error "...")` and continue with the
    // remaining commands (advertised `:error-behavior continued-execution`).
    //
    // `formula_stats`/`smt_logic` are accumulated incrementally (as in the
    // interactive path) because we can no longer collect the full command list
    // up front — a bad command must not prevent stats/logic from the commands
    // that DID parse.
    let mut executor = new_executor();
    let mut transcript = SmtTranscriptState::new();
    let mut formula_stats = FormulaStats::default();
    let mut smt_logic: Option<String> = None;
    let command_sources = collect_command_sources(content);
    // Rewrite synthesized non-Alethe configs to Alethe for SMT
    // (Finding A in the development design notes).
    let adapted = adapt_proof_config_for_smt(proof_config);
    transcript.defer_unsat_publication = required_smt_unsat_publication(adapted.as_ref());
    seed_smt_transcript_protections_or_exit(&mut transcript, source, adapted.as_ref());
    if let Some(proof) = adapted.as_ref() {
        if proof.format != ProofFormat::Alethe {
            safe_eprintln!(
                "Error: proof file '{}' uses DRAT/LRAT/Lean4 format, but SMT-LIB mode requires Alethe output",
                proof.path
            );
            std::process::exit(1);
        }
        if proof.binary {
            safe_eprintln!(
                "Error: --proof-binary is unsupported for SMT-LIB Alethe output; omit the flag to emit authenticated text"
            );
            std::process::exit(1);
        }
        executor.set_produce_proofs(true);
        apply_default_proof_budget(&mut executor, proof);
    } else if !ResultGateRequests::current().any() {
        // No proof can be emitted this session (`--no-proof` / `--z3-mode` /
        // competition mode), and no mandatory result/artifact gate needs the
        // internal proof surface: skip retaining a deep parsed-AST clone of
        // every assertion (~190 MB of a 318 MB peak on a 6 MB QF_UF input,
        // #rss-vs-z3). An in-script `(set-option :produce-proofs true)`
        // re-enables retention.
        executor.set_retain_parsed_assertions(false);
    }

    let mut cmd_index = 0usize;
    // Start byte of the current full-reset epoch. Proof payloads and
    // visualization must describe exactly the problem that produced the
    // authoritative decision, never rejected text from an earlier epoch.
    let mut artifact_epoch_start = 0usize;
    let mut stream = CommandStream::new(content);
    loop {
        // Delimit the exact source slice this command consumes (used below to
        // classify a dropped command on a parse error, independent of the
        // possibly-misaligned `command_sources` re-chunking).
        let consumed_start = stream.position();
        let Some(item) = stream.next_command() else {
            break;
        };
        let consumed = content
            .get(consumed_start..stream.position())
            .unwrap_or_default();
        // Source tracking advances per top-level command (both successful and
        // failed ones occupy a slot), keeping positions aligned with the
        // balanced-paren chunks `collect_command_sources` recorded.
        set_current_command_source(&mut transcript, &command_sources, cmd_index);
        cmd_index += 1;
        match item {
            CommandStreamItem::Error(err) => {
                // z3-style continued-execution: report the bad command and keep
                // going. Marked recoverable so the process still exits non-zero.
                print_recoverable_parse_error(&mut transcript, &err);
                invalidate_export_after_malformed_decision(consumed);
                // SOUNDNESS: a problem-contributing command (e.g. an `assert`
                // using an unsupported construct) just failed to parse and was
                // dropped. Taint the session so a later check-sat fails closed to
                // `unknown` instead of answering on the incomplete remainder.
                if parse_drop_contributes_to_problem(consumed) {
                    mark_problem_incomplete(&mut executor, &mut transcript);
                }
                exit_if_timed_out_with_transcript_context(&transcript);
            }
            CommandStreamItem::Command(cmd) => {
                let cmd = *cmd;
                formula_stats.observe_command(&cmd);
                if smt_logic.is_none() {
                    smt_logic = logic_from_commands(std::slice::from_ref(&cmd)).map(str::to_owned);
                }
                match cmd {
                    Command::Exit => {
                        let artifact_input = &content[artifact_epoch_start..stream.position()];
                        publish_pending_smt_unsat(
                            &mut executor,
                            &mut transcript,
                            adapted.as_ref(),
                            ProofArtifactProblem::Text(artifact_input),
                            ProofArtifactTheoryMetadata::smt_lib(
                                smt_logic.as_deref(),
                                Some(&formula_stats),
                            ),
                        );
                        finalize_smt_unsat_artifacts(
                            &mut executor,
                            &mut transcript,
                            adapted.as_ref(),
                            ProofArtifactProblem::Text(artifact_input),
                            ProofArtifactTheoryMetadata::smt_lib(
                                smt_logic.as_deref(),
                                Some(&formula_stats),
                            ),
                        );
                        maybe_print_success(&transcript);
                        maybe_explain(&mut executor, &transcript);
                        maybe_visualize(artifact_input, &mut executor, &transcript, visualization);
                        if stats_cfg.any() {
                            print_smt_stats(
                                &executor,
                                &transcript,
                                Some(&formula_stats),
                                stats_cfg,
                            );
                        }
                        maybe_write_minimal_decision_trace(&mut transcript);
                        cleanup_temp_proof(adapted.as_ref());
                        exit_if_transcript_had_recoverable_error(&transcript);
                        return;
                    }
                    _ => {
                        if !execute_and_print(&mut executor, &cmd, &mut transcript, false) {
                            exit_if_timed_out_with_transcript_context(&transcript);
                            std::process::exit(1);
                        }
                        if matches!(cmd, Command::Reset) {
                            artifact_epoch_start = stream.position();
                            formula_stats = FormulaStats::default();
                            smt_logic = None;
                        }
                        let artifact_input = &content[artifact_epoch_start..stream.position()];
                        publish_pending_smt_unsat(
                            &mut executor,
                            &mut transcript,
                            adapted.as_ref(),
                            ProofArtifactProblem::Text(artifact_input),
                            ProofArtifactTheoryMetadata::smt_lib(
                                smt_logic.as_deref(),
                                Some(&formula_stats),
                            ),
                        );
                    }
                }
                exit_if_timed_out_with_stats(
                    &transcript,
                    &executor,
                    Some(&formula_stats),
                    stats_cfg,
                );
            }
        }
    }
    let artifact_input = &content[artifact_epoch_start..];
    publish_pending_smt_unsat(
        &mut executor,
        &mut transcript,
        adapted.as_ref(),
        ProofArtifactProblem::Text(artifact_input),
        ProofArtifactTheoryMetadata::smt_lib(smt_logic.as_deref(), Some(&formula_stats)),
    );
    finalize_smt_unsat_artifacts(
        &mut executor,
        &mut transcript,
        adapted.as_ref(),
        ProofArtifactProblem::Text(artifact_input),
        ProofArtifactTheoryMetadata::smt_lib(smt_logic.as_deref(), Some(&formula_stats)),
    );
    maybe_explain(&mut executor, &transcript);
    maybe_visualize(artifact_input, &mut executor, &transcript, visualization);
    if stats_cfg.any() {
        print_smt_stats(&executor, &transcript, Some(&formula_stats), stats_cfg);
    }
    maybe_write_minimal_decision_trace(&mut transcript);
    cleanup_temp_proof(adapted.as_ref());
    exit_if_transcript_had_recoverable_error(&transcript);
}

/// Report a per-command parse/elaboration error (z3 continued-execution).
///
/// Mirrors the recoverable execution-error path: the `(error "...")` line goes
/// to the regular output channel (z3 prints recoverable errors on stdout) with
/// the offending command's source position when available, and the transcript
/// is marked so the process still exits non-zero. Subsequent valid commands are
/// executed by the caller's loop.
fn print_recoverable_parse_error(state: &mut SmtTranscriptState, err: &ay_frontend::ParseError) {
    state.note_recoverable_error();
    // Use the offending command's *absolute* position from `command_sources`
    // (the parser's own line/column are relative to the per-command slice and
    // would be wrong for whole-file reporting). Emit only the bare error
    // `message` so the position is not duplicated by `ParseError`'s Display.
    let position = state.current_source.as_ref().map(|source| SourcePosition {
        line: source.line,
        column: source.column,
    });
    let line = source_error(position, &err.message);
    print_regular_line(state, &line);
}

/// Check if content uses HORN logic
pub(super) fn is_horn_logic(content: &str) -> bool {
    // Avoid parsing large non-HORN SMT-LIB inputs on the caller stack.
    if !content.contains("HORN") {
        return false;
    }
    if content.contains("(set-logic HORN)") {
        return true;
    }
    if let Ok(commands) = parse(content) {
        commands
            .iter()
            .any(|cmd| matches!(cmd, Command::SetLogic(logic) if logic == "HORN"))
    } else {
        // Fallback: simple string check for unparseable content
        content.contains("(set-logic HORN)")
    }
}

/// Detect a Z3 fixedpoint (relational / CHC) script.
///
/// z3 exposes its fixedpoint engine through `declare-rel` / `declare-var` /
/// `rule` / `query` commands, often WITHOUT `(set-logic HORN)`. Such a script
/// is a CHC problem and must be routed to the `ay-chc` engine, not the DPLL(T)
/// solver (which has no notion of relations/rules and would reject `rule` /
/// `query`).
///
/// Detection is precise: `rule` and `query` are not valid SMT-LIB commands in
/// any non-fixedpoint context, so their presence unambiguously identifies a
/// fixedpoint script. A bare `declare-rel` alone (without any `rule`/`query`)
/// is NOT treated as fixedpoint — without a query there is nothing to decide,
/// so we leave it to the normal path rather than risk misrouting.
///
/// SOUNDNESS: this only changes which engine runs; the CHC engine itself emits
/// `sat`/`unsat`/`unknown` soundly (with fixedpoint polarity already handled by
/// `ChcProblem::is_fixedpoint_format`). When in doubt we return `false` and let
/// the standard pipeline handle (and, if truly unsupported, reject) the input.
pub(super) fn is_fixedpoint_format(content: &str) -> bool {
    // Cheap pre-filter: a fixedpoint script must mention `rule` or `query`.
    // This token check avoids parsing large ordinary SMT-LIB inputs and is a
    // strict over-approximation of the precise parse-based check below.
    if !(content.contains("rule") || content.contains("query")) {
        return false;
    }
    let Ok(commands) = parse(content) else {
        return false;
    };
    // Require an actual fixedpoint command — a `rule` or `query`. `declare-rel`
    // alone does not constitute a decidable fixedpoint problem.
    commands
        .iter()
        .any(|cmd| matches!(cmd, Command::Rule(_) | Command::Query(_)))
}
