// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Execution mode implementations for the AY CLI.
//!
//! Contains the interactive (stdin), piped, and file-based execution
//! paths. Extracted from `main.rs` to keep each file under 500 lines.

use std::cell::{Cell, RefCell};
use std::collections::HashMap;
use std::io::{self, BufRead, BufWriter, Read, Write};

use ay_core::{escape_string_contents, quote_symbol};
use ay_dpll::{
    CandidateModelPolicy, CanonicalWorkRefusal, Executor, OverridePlanExit, ProofDeclineMechanism,
    SatReconstructionOutcome, UnboundedCensus, UnknownReason,
};
use ay_frontend::{
    parse, sexp::parse_sexp, Command, CommandStream, CommandStreamItem, Constant,
    FiniteSetTypingMode, FormulaStats, Index, IntroKind, QualifiedIdentifier, SExpr, Sort, Term,
};
use sha2::{Digest as _, Sha256};

use super::firewall_verify;
use super::{
    chc_runner, dimacs, eprintln_smt_error, exit_if_timed_out, explain, explain_reason,
    is_timed_out,
    proof_artifact::{
        write_sealed_proof_artifact, DigestBytes, ProofArtifactProblem, ProofArtifactTheoryMetadata,
    },
    stats_output, ProofConfig, ProofFormat, ALETHE_DIALECT_PINNED, EXPLAIN_ENABLED,
    EXPLAIN_FORMAT_JSON, EXPLICIT_VERIFY_PROOF_ENABLED, GLOBAL_TIMEOUT_MS, INTERRUPT_HANDLE,
    MINIMIZE_MODEL_ENABLED, PROGRESS_ENABLED, PROGRESS_JSON_PATH, PROOF_CYCLE_SHED_ENABLED,
    SELF_CHECK_ENABLED, START_TIME, STRICT_PROOFS_ENABLED, VERIFY_FIREWALL_ENABLED,
    VERIFY_PROOF_ENABLED, Z3_MODEL_ENABLED, Z3_MODE_ENABLED,
};
use ay::solution_visualization::{render_solution_visualization, VisualizationFormat};

const SMT_FILE_THREAD_STACK_SIZE: usize = 64 * 1024 * 1024;

include!("run/smt_proof_config.rs");
include!("run/strict_admission.rs");

/// Create an executor with global timeout interrupt wired in (#2971).
fn new_executor() -> Executor {
    let mut executor = Executor::new();
    // Off by default, NOT `!z3_mode_enabled()`.
    //
    // Strict compliance enforces SMT-LIB's execution-mode preconditions: no
    // declaration, assertion or query before `(set-logic …)`, and no `set-logic`
    // after. The pinned oracle — z3 5.0.0 — enforces none of it, so with this on
    // by default the most ordinary script in existence diverges:
    //
    //   (declare-const x Int) (assert (> x 5)) (check-sat)
    //     z3: sat
    //     ay: (error "… declare-const is not available in start mode")
    //         (error "… assert is not available in start mode")   unknown
    //
    // It gated 18 standard commands (declare-*, define-*, assert, check-sat,
    // push, get-model, get-value, …) plus 11 Z3 extensions, and inversely
    // refused 9 `set-option` keys AFTER a logic was chosen — so
    // `(set-logic X)(set-option :produce-models true)`, one of the two most
    // common prologues, also failed. Requiring `--z3-mode` to turn that off
    // makes the DEFAULT invocation the incompatible one, which is exactly
    // backwards for a binary meant to stand in for z3 unmodified.
    //
    // The strict path is not deleted: it stays reachable through the library
    // API (`set_strict_logic_compliance(true)`), which is how the elaborator's
    // own conformance tests drive it.
    executor.context_mut().set_strict_logic_compliance(false);
    if let Some(maximum) = super::SEQUENCE_POWER_EXPANSION.get() {
        let command = Command::SetOption(
            "rewriter.max_power_expansion".to_owned(),
            SExpr::Numeral(maximum.to_string()),
        );
        if let Err(error) = executor.execute(&command) {
            safe_eprintln!("Error: cannot configure sequence power rewriting: {error}");
            std::process::exit(1);
        }
    }
    if let Some(polynomial) = super::POLYNOMIAL_OPTIONS.get() {
        let configured = polynomial.visit(|name, value| {
            let value = match value {
                ay_dpll::api::TacticParameterValue::Bool(true) => SExpr::True,
                ay_dpll::api::TacticParameterValue::Bool(false) => SExpr::False,
                ay_dpll::api::TacticParameterValue::UInt(n) => SExpr::Numeral(n.to_string()),
                _ => return Err("invalid polynomial configuration".to_owned()),
            };
            executor
                .execute(&Command::SetOption(format!("rewriter.{name}"), value))
                .map(|_| ())
                .map_err(|e| e.to_string())
        });
        if let Err(error) = configured {
            safe_eprintln!("Error: cannot configure polynomial rewriting: {error}");
            std::process::exit(1);
        }
    }
    // `--rigor strict|certified`: authority GRANTS (the closed-sentence
    // certificates) must rest on strictly checked evidence, mirroring the
    // UNSAT screen below that withholds a trust-bearing refutation
    // (#closed-sentence-cert): a closed sentence must not publish `sat` on
    // the refutation its negation is refused.
    executor.set_strict_grant_evidence_required(strict_proofs_enabled() || self_check_enabled());
    if z3_mode_enabled() {
        executor
            .context_mut()
            .set_finite_set_typing_mode(FiniteSetTypingMode::Z3_5Strict);
        // Read the script as z3 reads it where the frontend is otherwise more
        // permissive, and hold `:named` labels to z3's reading.
        executor.context_mut().set_z3_mode(true);
        // The narrow slice of z3's logic enforcement that its shell
        // does apply: a builtin sort or operator outside the declared
        // logic's signature is `unknown sort '...'` / `unknown
        // constant ...` (DR-59). Plain mode keeps AY's own reading
        // (e.g. the `min`/`max` builtins), as the label-guard pairs
        // pin; z3's C-API parser stays permissive, so the library
        // default does too.
        executor
            .context_mut()
            .set_enforce_logic_sort_signatures(true);
        // z3 answers `(get-model)` after `unknown` with the candidate its search
        // stopped at, and z3 clients (Verus/AIR) read it to locate a failing
        // assertion. The printed candidate is marked as unvalidated; outside
        // --z3-mode `(get-model)` after `unknown` stays an error.
        executor.set_candidate_model_policy(CandidateModelPolicy::PublishAfterUnknown);
    }
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
    // `--alethe-dialect`: every Alethe document this executor renders.
    if ALETHE_DIALECT_PINNED.load(std::sync::atomic::Ordering::Relaxed) {
        executor.set_alethe_dialect(ay_proof::AletheDialect::PinnedCarcara);
    }
    // Proof-cycle shedding (#proof-capability B1, generalised): the executor
    // sheds the internal proof cycle on public solves with no proof demand.
    // Keyed on `PROOF_CYCLE_SHED_ENABLED` — competition mode, `--no-proof`,
    // `--z3-mode` — not on the competition latch alone, so the shed posture
    // never drags the SAT-competition verdict grammar, the CHC validation
    // battery, or the DIMACS proof re-check along with it. A plain solve is
    // never shed: batteries are on by default. Setting the mode
    // here is safe alongside the proof wiring below — precedence is evaluated
    // executor-side at every `begin_public_solve`, so a `set_produce_proofs`
    // from `--proof`/`--strict-proofs`/`--self-check` (in any order) or a
    // later in-script `:produce-proofs true` always wins over shedding.
    if PROOF_CYCLE_SHED_ENABLED.load(std::sync::atomic::Ordering::SeqCst) {
        executor.set_competition_mode(true);
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
        // production on even without `--proof`. Collection only: self-check
        // demands verified truth, not the exported artifact, so this must not
        // record an explicit-artifact demand (`proof_artifact_required`) —
        // that flag makes the certification mint refuse the independent
        // lanes self-check's own funnel publishes on (#letleak wall 3).
        executor.set_mandatory_proof_collection();
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

fn should_budget_synthesized_proof(
    synthesized_default: bool,
    has_artifact_path: bool,
    gates: ResultGateRequests,
) -> bool {
    synthesized_default && !has_artifact_path && !gates.any()
}

fn may_use_ungated_solver_route(gates: ResultGateRequests) -> bool {
    !gates.any()
}

/// What a run's proof configuration asks of an executor-produced UNSAT before
/// it reaches the regular output channel. Fixed once, before the first
/// command. Whether ONE query's UNSAT is held back until its certificate is
/// published also depends on the strict request in force when that query is
/// answered, because the in-script spelling is only learned mid-script; see
/// [`Self::holds_unsat`].
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
enum SmtUnsatProofPosture {
    /// No proof configuration: no certificate, so nothing to wait for.
    #[default]
    NoCertificate,
    /// Only the synthesized default certificate (`<input>.alethe`). It is
    /// best-effort unless strict proofs are requested, in either spelling.
    DefaultCertificate,
    /// An explicit proof file, an artifact envelope or a firewall Lean
    /// directory: every UNSAT waits for its publication transaction.
    RequiredCertificate,
}

impl SmtUnsatProofPosture {
    fn of(proof: Option<&ProofConfig>) -> Self {
        match proof {
            None => Self::NoCertificate,
            Some(proof)
                if !proof.synthesized_default
                    || proof.artifact_path.is_some()
                    || crate::FIREWALL_LEAN_DIR.get().is_some() =>
            {
                Self::RequiredCertificate
            }
            Some(_) => Self::DefaultCertificate,
        }
    }

    /// Whether an UNSAT answered under this posture is held back until its
    /// publication transaction commits. `script_strict` is the in-script
    /// option in force for that query; it is combined with the flag by THE
    /// strict predicate (`strict_request`), never read apart from it.
    fn holds_unsat(self, script_strict: bool) -> bool {
        match self {
            Self::NoCertificate => false,
            Self::DefaultCertificate => {
                crate::strict_request::strict_proofs_requested(script_strict)
            }
            Self::RequiredCertificate => true,
        }
    }
}

/// Whether an UNSAT must wait for its certificate: `proof` is the run's proof
/// configuration and `script_strict` the in-script strict option in force for
/// the query. This read the flag alone and was latched before the script ran,
/// while the publication posture (`write_alethe_proof`) read both spellings:
/// with only the option, a failed default publication printed `unsat` and
/// then, at EOF, `unknown` for the same `check-sat`.
fn required_smt_unsat_publication(proof: Option<&ProofConfig>, script_strict: bool) -> bool {
    SmtUnsatProofPosture::of(proof).holds_unsat(script_strict)
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

/// Enable proof production with an explicit typed policy: synthesized-default
/// artifacts are best-effort and budgeted; every user/result-gate request is
/// mandatory and unbudgeted.
fn configure_proof_policy(executor: &mut Executor, proof: &ProofConfig) {
    // Every mandatory result gate needs the complete proof reconstruction it
    // requested. In particular, `--verify-firewall` synthesizes its proof
    // config by default; treating that config as best-effort could stop proof
    // reconstruction before the requested diagnostics run.
    let gates = ResultGateRequests::current();
    if should_budget_synthesized_proof(
        proof.synthesized_default,
        proof.artifact_path.is_some(),
        gates,
    ) {
        executor.set_best_effort_produce_proofs(DEFAULT_PROOF_RECONSTRUCTION_STEP_BUDGET);
    } else if proof.synthesized_default
        && proof.artifact_path.is_none()
        && gates
            == (ResultGateRequests {
                self_check: true,
                ..ResultGateRequests::default()
            })
    {
        // Self-check is the ONLY active result gate and the proof config is
        // the synthesized default with no artifact path: reconstruction must
        // be mandatory and unbudgeted (the internal checker inspects it), but
        // no one demanded the translated artifact itself, so the independent
        // certification lanes stay available (#letleak wall 3). Any other
        // gate, an explicit config, or an artifact path keeps the artifact
        // mandatory below.
        executor.set_mandatory_proof_collection();
    } else {
        executor.set_produce_proofs(true);
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

/// How a file can be reached for a platform identity query.
///
/// Windows does not expose file identity through `Metadata` on stable (the
/// accessors sit behind the perpetually unstable `windows_by_handle` feature,
/// rust-lang/rust#63010), so the source is threaded through to
/// `GetFileInformationByHandle` rather than read off the metadata. The two path
/// variants mirror the resolution behaviour of the call the caller replaced:
/// `Path` follows reparse points like `std::fs::metadata`, `PathNoFollow` does
/// not, like `std::fs::symlink_metadata`.
#[derive(Clone, Copy)]
enum SmtFileRef<'a> {
    Handle(&'a std::fs::File),
    Path(&'a std::path::Path),
    PathNoFollow(&'a std::path::Path),
}

impl SmtFileIdentity {
    fn resolve(source: SmtFileRef<'_>) -> Option<Self> {
        #[cfg(unix)]
        {
            use std::os::unix::fs::MetadataExt as _;
            let metadata = match source {
                SmtFileRef::Handle(file) => file.metadata().ok()?,
                SmtFileRef::Path(path) => std::fs::metadata(path).ok()?,
                SmtFileRef::PathNoFollow(path) => std::fs::symlink_metadata(path).ok()?,
            };
            Some(Self {
                device: metadata.dev(),
                inode: metadata.ino(),
            })
        }
        #[cfg(windows)]
        {
            let info = match source {
                SmtFileRef::Handle(file) => ay_sys::windows_fs::file_info(file),
                SmtFileRef::Path(path) => ay_sys::windows_fs::file_info_follow(path),
                SmtFileRef::PathNoFollow(path) => ay_sys::windows_fs::file_info_no_follow(path),
            }
            .ok()?;
            Some(Self {
                volume: Some(info.volume_serial_number),
                index: Some(info.file_index),
            })
        }
        #[cfg(not(any(unix, windows)))]
        {
            let _ = source;
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
            identity: SmtFileIdentity::resolve(SmtFileRef::Handle(file)),
        })
    }
}

#[derive(Default)]
struct SmtTranscriptState {
    /// `true` unless EVERY cause of incompleteness was a dropped `assert`.
    /// Fail-closed default; see `mark_incomplete_from_dropped_assertion`.
    incomplete_beyond_assertions: bool,
    print_success: bool,
    print_warning: bool,
    exit_on_error: bool,
    int_real_coercions: bool,
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
    /// AY's recorded solver-work counter: what `(get-info :rlimit)` and every
    /// `:rlimit-count` of this session report. As in z3 it only grows until
    /// `(reset)` starts it again at [`INITIAL_RLIMIT_COUNT`]. Commands add
    /// only work the executor actually recorded. It lives here and not in the
    /// executor because the executor is rebuilt after a failed command and its
    /// statistics describe one check-sat; Verus's AIR subtracts successive
    /// readings within a query as `u64`, so a reading below an earlier one
    /// aborts the verifier.
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
    /// Whether ANY `(error ...)` was emitted during the whole run.
    ///
    /// Deliberately separate from [`Self::had_recoverable_error`], which shares
    /// the same trigger but a different LIFETIME. That one gates artifact
    /// authority and is correctly cleared by `(reset)` — a fresh problem built
    /// after a reset may export artifacts again. This one decides the process
    /// EXIT CODE, which is a property of the invocation, not of the current
    /// problem: z3 exits 1 iff it printed an error, and `(reset)` does not
    /// un-print it. Set once, never cleared.
    emitted_any_error: bool,
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
    /// What the run's proof configuration requires before an executor-produced
    /// UNSAT becomes observable on the regular channel. Set once, before the
    /// first command; whether one query's UNSAT is held back is decided when
    /// that query is answered
    /// ([`SmtTranscriptState::holds_unsat_publication`]).
    unsat_proof_posture: SmtUnsatProofPosture,
    /// Whether `(set-option :check-proofs-strict true)` was in force when the
    /// current decision query was answered. Strict proofs are judged per
    /// query: an option set after a `check-sat` applies to later queries only.
    query_script_strict: bool,
    /// The held-back UNSAT of the current query, printed only once a required
    /// persistent proof/firewall transaction commits.
    pending_unsat_output: Option<String>,
    /// Whether this run created its default certificate (`<input>.alethe`).
    /// A run publishes one and never replaces a file, so a later query that
    /// finds the path taken met this run's own certificate for an earlier
    /// query (or the empty stub it was invalidated to), not a stale file from
    /// an earlier run. A fact about the run, so `(reset)` keeps it.
    default_certificate_created: Cell<bool>,
    /// Retained proof/artifact authority for a deferred UNSAT. The prepared
    /// transaction remains armed until the decision trace settles and every
    /// participant is revalidated immediately before the verdict is emitted.
    smt_unsat_publication: SmtUnsatPublicationState,
    /// #model-owed: a `sat` has reached the regular output channel while z3
    /// `-model` is active, and the model that answer owes has NOT been printed
    /// yet. In the non-incremental file path the model is a *separate* stream
    /// command (`append_get_model_command`), so the cooperative timeout could
    /// fire in the gap and exit 124 between the verdict and its model. In
    /// Model-Validation a `sat` carrying no model scores exactly ZERO, so that
    /// gap silently discarded solves AY had already finished paying for.
    owes_model_emission: bool,
    /// Whether a command that fails inside the executor leaves the session
    /// running, as in z3; see [`continue_after_failed_command`].
    continue_after_failure: bool,
    /// Executor mutations kept so the session can survive a failed command.
    /// `None` when not kept, or once a command could not be recorded exactly;
    /// see [`SessionReplayLog`].
    replay_log: Option<SessionReplayLog>,
    /// See [`report_failure_in_surviving_session`].
    failure_reported: bool,
    /// See [`keep_discarded_command_error`].
    discarded_command_error: Option<String>,
    z3_scope: Z3ScopeState,
    /// `:named` label names whose binding here may differ from z3's: z3
    /// binds them and this session did not, or this session binds them and
    /// z3 may not reach them; see [`withhold_after_labels_z3_binds`].
    labels_bound_unlike_z3: std::collections::HashSet<String>,
    /// See [`withhold_answers_out_of_step`].
    answers_out_of_step: bool,
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
            incomplete_beyond_assertions: false,
            print_success: false,
            print_warning: true,
            exit_on_error: false,
            int_real_coercions: true,
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
            rlimit: INITIAL_RLIMIT_COUNT,
            assertion_stack_depth: 0,
            executor_assertion_stack_depth: 0,
            symbol_sorts: HashMap::new(),
            symbol_sort_bindings: HashMap::new(),
            current_source: None,
            current_command_ordinal: 0,
            processed_commands: 0,
            decision_queries_seen: 0,
            had_recoverable_error: false,
            emitted_any_error: false,
            recoverable_error_count: 0,
            completeness: ProblemCompleteness::Complete,
            public_verdict: None,
            public_unknown_reason: None,
            public_verdict_from_executor: false,
            decision_trace_publication: DecisionTracePublication::Pending,
            result_certification_rejected: false,
            unsat_proof_posture: SmtUnsatProofPosture::NoCertificate,
            query_script_strict: false,
            pending_unsat_output: None,
            default_certificate_created: Cell::new(false),
            smt_unsat_publication: SmtUnsatPublicationState::Unprepared,
            owes_model_emission: false,
            continue_after_failure: false,
            replay_log: None,
            failure_reported: false,
            discarded_command_error: None,
            z3_scope: Z3ScopeState::default(),
            labels_bound_unlike_z3: std::collections::HashSet::new(),
            answers_out_of_step: false,
        }
    }

    fn note_recoverable_error(&mut self) {
        self.had_recoverable_error = true;
        self.emitted_any_error = true;
        self.recoverable_error_count = self.recoverable_error_count.saturating_add(1);
    }

    /// Mark the problem as incomplete: a problem-contributing command was
    /// dropped, so a later `check-sat` must answer `unknown` (fail closed).
    fn mark_incomplete(&mut self) {
        // Default to the STRICT form. Only `mark_incomplete_from_dropped_assertion`
        // records the monotone case; every other route (a panic, an
        // unrepresentable overload, a recursive redeclaration, a depth limit)
        // must keep the definitive-verdict block.
        self.incomplete_beyond_assertions = true;
        self.completeness = ProblemCompleteness::Incomplete;
        // A dropped semantic mutation also revokes any result from an earlier
        // check immediately. EOF consumers must never publish that stale
        // proof/model merely because no later check-sat was issued.
        self.clear_public_result();
    }

    /// Restore the "beyond assertions" flag after a `mark_incomplete` whose
    /// cause was ONLY a dropped `assert`.
    ///
    /// That is the single monotone case: the remainder is a WEAKENING of the
    /// real problem, so an `unsat` on it still refutes the whole. Every other
    /// dropped construct changes what the surviving terms MEAN, so the flag
    /// stays set — see `run_incomplete_problem_gate`.
    fn set_incomplete_beyond_assertions(&mut self, beyond: bool) {
        self.incomplete_beyond_assertions = beyond;
    }

    /// Whether anything OTHER than a dropped assertion made the problem
    /// incomplete. Fail-closed: `true` unless every cause was an assertion.
    fn is_incomplete_beyond_assertions(&self) -> bool {
        self.incomplete_beyond_assertions
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
        self.query_script_strict = false;
        self.smt_unsat_publication = SmtUnsatPublicationState::Unprepared;
        self.owes_model_emission = false;
    }

    fn record_public_verdict(&mut self, verdict: PublicVerdict) {
        self.public_verdict = Some(verdict);
        self.public_unknown_reason = None;
        self.public_verdict_from_executor = true;
        self.result_certification_rejected = false;
        self.pending_unsat_output = None;
        self.smt_unsat_publication = SmtUnsatPublicationState::Unprepared;
        self.owes_model_emission = false;
    }

    fn record_executor_unknown(&mut self, reason: Option<String>) {
        self.public_verdict = Some(PublicVerdict::Unknown);
        self.public_unknown_reason = reason;
        self.public_verdict_from_executor = true;
        self.result_certification_rejected = false;
        self.pending_unsat_output = None;
        self.smt_unsat_publication = SmtUnsatPublicationState::Unprepared;
        self.owes_model_emission = false;
    }

    fn record_synthesized_unknown(&mut self, reason: impl Into<String>) {
        self.public_verdict = Some(PublicVerdict::Unknown);
        self.public_unknown_reason = Some(reason.into());
        self.public_verdict_from_executor = false;
        self.result_certification_rejected = false;
        self.pending_unsat_output = None;
        self.smt_unsat_publication = SmtUnsatPublicationState::Unprepared;
        self.owes_model_emission = false;
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

    /// Whether the current query's executor UNSAT is held back until its
    /// publication transaction commits: the run's proof posture under the
    /// strict request in force when the query was answered.
    fn holds_unsat_publication(&self) -> bool {
        self.unsat_proof_posture
            .holds_unsat(self.query_script_strict)
    }

    /// Whether strict proofs, in either spelling, were requested for the
    /// current query.
    fn query_strict_proofs_requested(&self) -> bool {
        crate::strict_request::strict_proofs_requested(self.query_script_strict)
    }

    fn protect_path(&mut self, path: &std::path::Path) -> io::Result<()> {
        let resolved = resolve_artifact_target(path)?;
        let identity = SmtFileIdentity::resolve(SmtFileRef::Path(path));
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
        let identity = SmtFileIdentity::resolve(SmtFileRef::Path(channel_path));
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
///
/// Text that may hold a `:named` label taints too, whatever its command: z3
/// may accept the command and bind the label (`(check-sat-assuming ((! p
/// :named a)) extra)`), and a later label or definition of that name then
/// means something else here.
///
/// Text that holds more than one top-level form taints as well: recovery
/// skipped a command z3 may have run.
fn parse_drop_contributes_to_problem(consumed: &str) -> bool {
    source_has_command_keyword(consumed, command_keyword_contributes_to_problem)
        || consumed.contains(":named")
        || collect_command_sources(consumed).len() > 1
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
    // `|pop|` is the symbol `pop`, and z3 runs `(|pop| 1)` as a pop. No
    // command name holds a `\`, so the escapes in a quoted keyword need no
    // decoding to compare it.
    let keyword = match body.strip_prefix('|') {
        Some(quoted) => &quoted[..quoted_symbol_body_end(quoted)?],
        None => {
            let end = body
                .find(|c: char| c.is_whitespace() || c == '(' || c == ')')
                .unwrap_or(body.len());
            &body[..end]
        }
    };
    (!keyword.is_empty()).then_some(keyword)
}

/// The byte offset of the `|` that ends a quoted symbol whose body starts
/// `text`, with `\` escaping the character after it, or `None` when the
/// symbol does not end.
fn quoted_symbol_body_end(text: &str) -> Option<usize> {
    let bytes = text.as_bytes();
    let mut index = 0usize;
    while index < bytes.len() {
        match bytes[index] {
            b'\\' => index += 2,
            b'|' => return Some(index),
            _ => index += 1,
        }
    }
    None
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
            // `\` escapes the next character, so `\|` does not end the
            // symbol.
            match byte {
                b'\\' => index += 2,
                b'|' => {
                    in_quoted_symbol = false;
                    index += 1;
                }
                _ => index += 1,
            }
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
/// sort, or manipulates the assertion stack. `set-option` counts too: an
/// option such as `:global-declarations` decides which definition a later
/// name means. Pure queries (`get-*`, `echo`, ...) are deliberately excluded
/// — discarding one cannot flip a sat/unsat verdict, so the solver stays
/// answerable (matching z3's continued-execution).
fn command_keyword_contributes_to_problem(keyword: &str) -> bool {
    matches!(
        keyword,
        "assert"
            | "assert-not"
            | "assert-soft"
            | "minimize"
            | "maximize"
            | "declare-const"
            | "declare-fun"
            | "declare-sort"
            | "declare-sort-parameter"
            | "define-sort"
            | "declare-datatype"
            | "declare-datatypes"
            | "define-fun"
            | "define-const"
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
            | "set-option"
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
            | Command::DeclareSortParameter(..)
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

include!("run/model_demand.rs");
include!("run/session_rebuild.rs");
include!("run/z3_quiet_failures.rs");
include!("run/z3_session_scope.rs");
include!("run/z3_session_start.rs");
#[cfg(test)]
mod label_mention_tests;
include!("run/session_rlimit.rs");
include!("run/stream_sources.rs");
include!("run/stdin_buffer.rs");
include!("run/query_alignment.rs");

/// Like [`collect_command_sources`] but numbers the first line `line_base`
/// instead of 1.
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
    let mut quoted_symbol_escape = false;
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
            // `\` escapes the next character, so `\|` does not end the
            // symbol.
            if quoted_symbol_escape {
                quoted_symbol_escape = false;
            } else if ch == '\\' {
                quoted_symbol_escape = true;
            } else if ch == '|' {
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
    let (resolved_target, mut reservation, file) = create_artifact_temp_file(target)?;
    match publish_artifact_temp(reservation.path(), &resolved_target) {
        Ok(()) => {
            reservation.commit();
            Ok(Some(file))
        }
        Err(error) => {
            // The still-armed reservation unlinks the unpublished temp file.
            drop(file);
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

/// Render an internal error message as an SMT-LIB string literal safe to embed
/// in a `(:reason-unknown ...)` s-expression.
///
/// SMT-LIB 2.6 string literals escape a double quote by DOUBLING it and have no
/// other escape, so quoting is: collapse every control character to a space,
/// double the quotes, and bound the length (an elaboration error can carry a
/// whole term). The result always parses as one atom, so a reader that only
/// matches the leading class token is unaffected.
fn smt_quoted_reason_detail(message: &str) -> String {
    /// Longest detail carried into `(:reason-unknown ...)`, in characters.
    const MAX_DETAIL_CHARS: usize = 200;

    let mut body = String::with_capacity(message.len() + 2);
    let mut chars = 0usize;
    let mut truncated = false;
    for ch in message.chars() {
        if chars >= MAX_DETAIL_CHARS {
            truncated = true;
            break;
        }
        chars += 1;
        match ch {
            '"' => body.push_str("\"\""),
            c if c.is_control() => body.push(' '),
            c => body.push(c),
        }
    }
    if truncated {
        body.push_str("...");
    }
    format!("\"{body}\"")
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

/// Position of the VALUE token in a `(set-option :key value)` form.
///
/// This is the column z3 reports for an unknown parameter: it is the start of
/// the token after the keyword, not the end of the keyword and not the end of
/// the value. Measured against the oracle, which reports 18 for every one of
/// `(set-option :foo 1)`, `(set-option :foo 123456)`, and
/// `(set-option :foo verylongvalue)` -- invariant in the value's length.
fn set_option_value_position(state: &SmtTranscriptState, keyword: &str) -> Option<SourcePosition> {
    let source = state.current_source.as_ref()?;
    let key = keyword_with_colon(keyword);

    // Match the keyword as a whole token: a bare `find` would also match the
    // `:foo` prefix of a longer `:foobar` appearing earlier in the command.
    let mut search = 0usize;
    let key_end = loop {
        let idx = search + source.text[search..].find(&key)?;
        let end = idx + key.len();
        let complete = source.text[end..]
            .chars()
            .next()
            .is_none_or(|ch| ch.is_whitespace() || ch == ')' || ch == '(');
        if complete {
            break end;
        }
        search = idx + 1;
    };

    let value_offset = source.text[key_end..]
        .char_indices()
        .find_map(|(idx, ch)| (!ch.is_whitespace()).then_some(idx))?;
    Some(source_position_at(source, key_end + value_offset))
}

/// Position z3 reports on stderr for an unsupported command: the closing
/// parenthesis of the command form.
///
/// NOT the end of the command name. Measured against the oracle:
/// `(bogus arg1 arg2)` reports 17 and `(bogus (nested thing))` reports 22 --
/// both the `)`, invariant in the name's length. Internal whitespace counts
/// too: `( bogus )` reports 9.
///
/// z3's column counter is 1-based on the first line of the FILE and 0-based on
/// every later line -- `(check-sat)(bogus)` reports 18 while the same
/// `(bogus arg)` one line down reports 10. That is an off-by-one in z3's own
/// scanner, and a drop-in has to reproduce it to stay byte-identical.
fn unsupported_command_position(source: &CommandSource) -> SourcePosition {
    let consumed = match source.text.rfind(')') {
        Some(idx) => &source.text[..=idx],
        None => source.text.as_str(),
    };
    let newlines = consumed.matches('\n').count();
    let line = source.line + newlines;

    let one_based = match consumed.rfind('\n') {
        // Continuation line: the column is an offset within that line alone.
        Some(idx) => consumed[idx + 1..].chars().count(),
        None => source.column + consumed.chars().count().saturating_sub(1),
    };
    let column = if line == 1 {
        one_based
    } else {
        one_based.saturating_sub(1)
    };
    SourcePosition { line, column }
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

fn maybe_handle_cli_transcript_command(
    executor: &mut Executor,
    state: &mut SmtTranscriptState,
    cmd: &Command,
) -> bool {
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
            pop_beyond_executor_levels(executor, state);
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

    if matches!(cmd, Command::SetOptionAttribute(_)) {
        // The SMT-LIB grammar admits a generic valueless attribute as an
        // implementation-specific option. AY parses that production and uses
        // the standard `unsupported` response instead of misclassifying it as
        // malformed syntax or silently pretending to implement it.
        print_regular_line(state, "unsupported");
        return true;
    }

    if let Command::SetOption(keyword, value) = cmd {
        let key = keyword_key(keyword);
        if key == "expand-definitions" && sexpr_bool(value).is_some() {
            let comment = z3_unsupported_query_comment(state, keyword);
            if state.regular_output_channel == state.diagnostic_output_channel {
                print_regular_line(state, &format!("unsupported\n{comment}"));
            } else {
                print_regular_line(state, "unsupported");
                print_diagnostic_line(state, &comment);
            }
            return true;
        }
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
        if let Some(numeral) = (key == "rlimit").then(|| sexpr_numeral(value)).flatten() {
            // Forward the deterministic conflict budget to the executor
            // (#8749 class: this arm used to update only the z3-compat
            // `get-option` echo and silently DROP the budget, so through the
            // `ay` binary `:rlimit` bounded nothing while `(get-option
            // :rlimit)` claimed it was set). Semantics — including `0` =
            // unlimited + default-ground-budget opt-out — are the executor's
            // own `apply_rlimit_option`, shared, not re-derived here.
            executor.apply_rlimit_option(numeral);
            record_rlimit_option(state, numeral);
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

/// The terms written in `cmd`.
fn command_terms(cmd: &Command) -> Vec<&Term> {
    match cmd {
        Command::Rule(term)
        | Command::Query(term)
        | Command::SygusConstraint(term)
        | Command::Assert(term)
        | Command::Maximize(term)
        | Command::Minimize(term)
        | Command::Eval(term)
        | Command::Display(term, _)
        | Command::DebugSet(_, term, _)
        | Command::Simplify(term)
        | Command::SimplifyWithParams(term, _)
        | Command::GetAbduct(_, term) => vec![term],
        Command::DefineFun(_, _, _, body) | Command::DefineFunRec(_, _, _, body) => vec![body],
        Command::DefineFunsRec(_, bodies) | Command::CheckSatAssuming(bodies) => {
            bodies.iter().collect()
        }
        Command::AssertSoft { term, .. } => vec![term],
        Command::GetValue(entries) => entries.iter().map(|(_, term)| term).collect(),
        Command::GetConsequences(assumptions, variables) => {
            assumptions.iter().chain(variables).collect()
        }
        Command::GetInterpolant(left, right) | Command::ComputeInterpolant(left, right) => {
            vec![left, right]
        }
        _ => Vec::new(),
    }
}

/// Whether a command other than `assert` carries a `:named` label. z3 binds
/// such a label as a definition; the frontend binds labels only for
/// assertions.
fn command_has_named_label_outside_assert(cmd: &Command) -> bool {
    !matches!(cmd, Command::Assert(_))
        && command_terms(cmd)
            .into_iter()
            .any(ay_frontend::term_has_named_label)
}

fn emit_z3_unknown_attribute_warnings(state: &SmtTranscriptState, cmd: &Command) {
    if !state.print_warning {
        return;
    }

    let mut terms = command_terms(cmd);
    while let Some(term) = terms.pop() {
        match term {
            Term::App(_, arguments)
            | Term::IndexedApp(_, _, arguments)
            | Term::QualifiedApp(_, _, arguments) => terms.extend(arguments),
            Term::Let(bindings, body) => {
                terms.extend(bindings.iter().map(|(_, value)| value));
                terms.push(body);
            }
            Term::Forall(_, body) | Term::Exists(_, body) | Term::Lambda(_, body) => {
                terms.push(body);
            }
            Term::Annotated(body, attributes) => {
                for (keyword, _) in attributes {
                    if !matches!(
                        keyword.as_str(),
                        ":named"
                            | ":weight"
                            | ":qid"
                            | ":skolemid"
                            | ":pattern"
                            | ":no-pattern"
                            | ":lblneg"
                            | ":lblpos"
                    ) {
                        print_diagnostic_line(
                            state,
                            &format!("WARNING: unknown attribute {keyword}"),
                        );
                    }
                }
                terms.push(body);
            }
            Term::Match(scrutinee, cases) => {
                terms.push(scrutinee);
                terms.extend(cases.iter().map(|(_, body)| body));
            }
            Term::Const(_) | Term::Symbol(_) => {}
            _ => {}
        }
    }
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
                Index::Numeral(value)
                | Index::Decimal(value)
                | Index::Hexadecimal(value)
                | Index::Binary(value) => value.clone(),
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
        Constant::Hexadecimal(bits) => {
            format!("(_ BitVec {})", bits.trim_start_matches("#x").len() * 4)
        }
        Constant::Binary(bits) => format!("(_ BitVec {})", bits.trim_start_matches("#b").len()),
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
        Command::Assert(term)
        | Command::Display(term, _)
        | Command::Simplify(term)
        | Command::SimplifyWithParams(term, _)
        | Command::Eval(term) => find_application_arg_sorts(state, term, symbol),
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

/// z3's error for a `check-sat-assuming` argument that is not a formula.
fn z3_compat_non_boolean_assumption_error(
    state: &SmtTranscriptState,
    cmd: &Command,
    message: &str,
) -> Option<String> {
    (matches!(cmd, Command::CheckSatAssuming(_))
        && message.starts_with("elaboration error: sort mismatch: expected Bool"))
    .then(|| {
        source_error(
            current_source_last_token_position(state),
            "invalid check-sat command, argument must be a Boolean literal",
        )
    })
}

include!("run/z3_options.rs");

/// z3's `set-option` error for a parameter it does not recognize, or `None`
/// when the key is legal.
///
/// The accepted set is SMT-LIB 2.6's standard options UNION z3's 24 global
/// parameters, established by probing the pinned oracle rather than from the
/// standard alone — z3 accepts both spellings, e.g. `:produce-models` (SMT-LIB)
/// and `:model` (its own parameter). ay previously accepted EVERY key silently
/// and exited 0, so a typo'd option was invisible:
///
///   (set-logic ALL) (set-option :nonesuch true) ... (check-sat)
///     z3: (error "line 2 column 22: unknown parameter 'nonesuch'
///         Legal parameters are:
///           auto_config (bool) (default: true)
///           ... 24 lines ...")
///         sat                                                    exit 1
///
/// Note the error is multi-line and goes to STDOUT, and z3 CONTINUES after it.
fn z3_unknown_option_error(state: &SmtTranscriptState, keyword: &str) -> Option<String> {
    // z3 resolves the two families differently, and the difference is
    // observable. SMT-LIB options match VERBATIM: `:produce-models` is
    // accepted, `:produce_models` is not. Global parameters are normalized
    // `-` -> `_` first, so `:auto_config` and `:auto-config` both resolve.
    // Verified against the oracle for all four combinations. AY's own keys
    // match verbatim like the SMT-LIB family: `ctx.get_option` looks them up
    // by their exact hyphenated spelling.
    let name = keyword.trim_start_matches(':');
    if SMTLIB_OPTIONS.contains(&name)
        || DISPATCHED_OPTIONS.contains(&name)
        || NATIVE_OPTIONS.contains(&name)
    {
        return None;
    }

    // Module-qualified options (`:opt.priority`, `:smt.arith.solver`) resolve
    // in a separate namespace with their own two diagnostics. The split is at
    // the FIRST dot only: z3 reports `:opt.priority.deeper` as the parameter
    // `priority.deeper` at module `opt`, not as a nested module. Module names
    // are matched case-insensitively (`:OPT.x` resolves to `opt`) and both
    // halves normalize `-` -> `_` before lookup and in the report.
    if let Some((module, parameter)) = name.split_once('.') {
        return z3_unknown_module_option_error(state, keyword, module, parameter);
    }
    let normalized = name.replace('-', "_").to_ascii_lowercase();
    if crate::z3_parameter_help::is_known_global_parameter(&normalized) {
        return None;
    }

    let mut body = String::new();
    body.push_str(&format!(
        "unknown parameter '{normalized}'\nLegal parameters are:"
    ));
    for line in crate::z3_parameter_help::legal_global_parameter_lines() {
        body.push('\n');
        body.push_str(line);
    }
    Some(set_option_error(state, keyword, &body))
}

/// Wrap `body` as z3's positioned `(error "line L column C: <body>")`.
///
/// Built by hand rather than through `source_error`, which ESCAPES control
/// characters -- the newlines came out as `\u{a}`, collapsing z3's multi-line
/// legal-parameter list onto one. z3 puts real newlines inside the quoted
/// string.
///
/// The column is the start of the VALUE token, not a function of where the
/// keyword ends. Measured against the oracle: `(set-option :foo true)` -> 18
/// and `(set-option :foo    true)` -> 21, both the column of `true`. An earlier
/// "just past the keyword" reading only coincided with these because the sample
/// had exactly one space between the keyword and the value.
fn set_option_error(state: &SmtTranscriptState, keyword: &str, body: &str) -> String {
    let position = set_option_value_position(state, keyword).or_else(|| {
        undefined_symbol_position(state, keyword).map(|p| SourcePosition {
            line: p.line,
            column: p.column + keyword.chars().count(),
        })
    });

    let mut out = String::from("(error \"");
    if let Some(p) = position {
        out.push_str(&format!("line {} column {}: ", p.line, p.column));
    }
    out.push_str(body);
    out.push_str("\")");
    out
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
    if let Some(output) = z3_compat_non_boolean_assumption_error(state, cmd, message) {
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
    //
    // EXCEPT when the failure is "the logic has already been set". That is a
    // different condition with the opposite contract — z3 emits a real
    // `(error ...)` and exits 1 — so it must NOT be swallowed by the
    // ignore-and-continue path below, which would report `unsupported` and
    // exit 0. Fall through to the generic recoverable-error handling instead.
    if let (Command::SetLogic(logic), true) =
        (cmd, message.contains("the logic has already been set"))
    {
        // Emit it the way z3 does — positioned `(error ...)` on stdout — and
        // CONTINUE. z3's contract here is `continued-execution`: the redundant
        // `set-logic` is rejected, the session keeps its original logic, and the
        // following `check-sat` still answers.
        //
        //   (set-logic ALL) (set-logic QF_UF) (check-sat)
        //     z3: (error "line 2 column 11: the logic has already been set")
        //         sat                                            exit 1
        //
        // Returning `false` here instead would hand it to the generic path,
        // which aborts the run — right exit code, but the verdict disappears.
        print_regular_line(
            state,
            &source_error(
                undefined_symbol_position(state, logic),
                "the logic has already been set",
            ),
        );
        state.note_recoverable_error();
        return true;
    }
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
    // `emitted_any_error`, NOT `had_recoverable_error`: z3's contract is "exit 1
    // iff an (error ...) was printed", and `(reset)` clears the latter for
    // artifact-authority reasons but cannot un-print an error.
    if state.emitted_any_error {
        let _ = io::stdout().flush();
        let _ = io::stderr().flush();
        std::process::exit(1);
    }
}

/// #model-owed: hold the cooperative timeout exit while a published `sat` still
/// owes the model it promised.
///
/// `-model` on the non-incremental file path appends a literal `(get-model)`
/// *after* the `(check-sat)`, so the verdict and the model it answers with are
/// two different stream commands. The post-command timeout check sits in that
/// gap, and taking it there exits 124 having printed a bare `sat` — which in
/// Model-Validation scores exactly ZERO, identical to never having solved the
/// instance at all. Reproduced on `atan-vega-3-weak-chunk-0144.smt2`, which
/// answers `sat` with zero `define-fun`s at `-T:30` and three at `-T:60`.
///
/// The debt is bounded: it is armed only by a published `sat`, and
/// `execute_and_print` clears it as soon as the `(get-model)` command has run,
/// whatever that command produced. Extracting an already-found assignment is
/// not a search — measured at ~0.1s on the repro (`-T:30` exits at 31.46s;
/// `-T:60` prints verdict *and* model at 31.34s) — so this spends effectively
/// none of the watchdog's existing post-deadline grace, and the hard-exit
/// fallback still bounds the process unconditionally.
fn timeout_exit_would_strand_owed_model(state: &SmtTranscriptState) -> bool {
    state.owes_model_emission && state.public_verdict == Some(PublicVerdict::Sat)
}

fn exit_if_timed_out_with_transcript_context(state: &SmtTranscriptState) {
    if timeout_exit_would_strand_owed_model(state) {
        return;
    }
    super::exit_if_memout_requested();
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
    if timeout_exit_would_strand_owed_model(state) {
        return;
    }
    if (super::run_deadline_passed() || super::memout_requested_by_watchdog()) && stats_cfg.any() {
        print_smt_stats(executor, state, formula_stats, stats_cfg);
    }
    exit_if_timed_out_with_transcript_context(state);
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

/// `(reset)` returns options to their initial values too. These three are
/// echoes of what the SCRIPT set (no host flag writes them); the executor
/// returns its script-set resource options to the host's values on the same
/// command, so `(get-option :rlimit)` must not keep reporting a budget that no
/// longer applies.
fn reset_script_option_echoes(state: &mut SmtTranscriptState) {
    state.verbosity = "0".to_string();
    state.rlimit_option = "0".to_string();
    state.z3_compat_bool_options = z3_compat_bool_option_defaults();
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
        Command::SetOption(keyword, value) if keyword_key(keyword) == "print-warning" => {
            if let Some(enabled) = sexpr_bool(value) {
                state.print_warning = enabled;
            }
        }
        Command::SetOption(keyword, value) if keyword_key(keyword) == "error-behavior" => {
            if let SExpr::Symbol(value) = value {
                if value == "immediate-exit" {
                    state.exit_on_error = true;
                } else if value == "continued-execution" {
                    state.exit_on_error = false;
                }
            }
        }
        Command::SetOption(keyword, value) if keyword_key(keyword) == "int-real-coercions" => {
            if let Some(enabled) = sexpr_bool(value) {
                state.int_real_coercions = enabled;
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
            // Answers out of step with z3's stay withheld: a reset does not
            // bring their positions back in line.
            if !state.answers_out_of_step {
                state.completeness = ProblemCompleteness::Complete;
            }
            state.discarded_command_error = None;
            state.had_recoverable_error = false;
            state.recoverable_error_count = 0;
            state.labels_bound_unlike_z3.clear();
            reset_script_option_echoes(state);
        }
        Command::ResetAssertions => {
            if !z3_mode_enabled() {
                // SMT-LIB 2.7 resets the whole assertion stack to level zero
                // while retaining declarations and options. Keeping only the
                // executor depth at zero left the public
                // `:assertion-stack-levels` response stale and made a later
                // `(pop)` appear valid at the CLI boundary.
                state.assertion_stack_depth = 0;
                expire_scoped_symbol_sorts(state);
            }
            // Z3 5.0.0 instead retains its public assertion-stack level while
            // dropping the asserted formulas. The executor stack is empty here;
            // --z3-mode reopens the retained levels (restore_z3_session_after_reset).
            state.executor_assertion_stack_depth = 0;
        }
        _ => {}
    }
    note_z3_scope_command(state, cmd);
}

fn maybe_print_success(state: &SmtTranscriptState) {
    if state.print_success {
        print_regular_line(state, "success");
    }
}

/// Whether a successfully executed command should receive the generic
/// `:print-success` acknowledgement in Z3 mode.
///
/// Most SMT-LIB commands explicitly request that acknowledgement. The
/// `assert-not` and `dbg-set` debug extensions do not: their Z3 5.0.0 handlers only
/// mutate command-context state. AY deliberately routes them through ordinary
/// command execution so assertion/term validation remains shared, which means
/// the raw command source is the remaining distinction at this presentation
/// boundary.
fn z3_command_implicitly_acknowledges_success(source: Option<&CommandSource>) -> bool {
    !matches!(
        source.and_then(|source| command_source_keyword(&source.text)),
        Some("assert-not" | "dbg-set")
    )
}

fn get_info_parameter_help() -> &'static str {
    "; Suppported get-info parameters:\n; (get-info :reason-unknown)\n; (get-info :status)\n; (get-info :version)\n; (get-info :authors)\n; (get-info :error-behavior)\n; (get-info :parameters)\n; (get-info :rlimit)\n; (get-info :assertion-stack-levels)"
}

fn unsupported_get_info_parameters() -> String {
    format!("unsupported\n{}", get_info_parameter_help())
}

fn z3_initial_statistics(state: &SmtTranscriptState) -> String {
    // Before the first decision query Z3 5.0.0 reports exactly these four
    // process/resource counters. Their values are implementation-specific, but
    // the behavioral gate's statistics comparator deliberately normalizes the
    // numeric cells while retaining the complete key set and layout.
    format!(
        "(:max-memory   0.00\n :memory       0.00\n :num-allocs   0\n :rlimit-count {})",
        state.rlimit
    )
}

/// Z3 version reported under explicit `--z3-mode` (full impersonation). Matches
/// the pinned Z3 baseline that `ay --z3-mode` is documented and smoke-tested
/// against (the development design notes). Kept in sync with that baseline.
const Z3_COMPAT_BASELINE_VERSION: &str = "5.1.0";

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
        "all-statistics" if state.public_verdict.is_none() => {
            Some(z3_initial_statistics(state))
        }
        "all-statistics" => Some(with_session_rlimit_count(output, state.rlimit)),
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
        "?" => Some(get_info_parameter_help().to_string()),
        "error-behavior" => Some(format!(
            "(:error-behavior {})",
            if state.exit_on_error {
                "immediate-exit"
            } else {
                "continued-execution"
            }
        )),
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
                    .unwrap_or((parameters.as_str(), ""));
                return Some(format!("{head}\n{comment}\n{tail}"));
            }
            eprintln_z3_unsupported_query_comment(state, keyword);
            Some(unsupported_get_info_parameters())
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
fn z3_reason_unknown_output(reason: &str) -> String {
    // A reason stored as an SMT-LIB string literal is already escaped; any
    // other reason may carry raw quotes (an error detail) that the string
    // literal below must double.
    let (inner, escaped) = match reason
        .strip_prefix('"')
        .and_then(|value| value.strip_suffix('"'))
    {
        Some(inner) => (inner, true),
        None => (reason, false),
    };
    let z3 = match inner {
        "timeout" | "resourceout" | "memout" | "interrupted" => "canceled".to_string(),
        "unknown" => "unknown".to_string(),
        s if s.starts_with("(incomplete") => s.to_string(),
        "incomplete" => "(incomplete)".to_string(),
        other => format!("(incomplete {other})"),
    };
    let z3 = if escaped { z3 } else { z3.replace('"', "\"\"") };
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
    if matches!(
        key,
        "print-warning" | "expand-definitions" | "numeral-as-real" | "reproducible-resource-limit"
    ) {
        if state.regular_output_channel == state.diagnostic_output_channel {
            return Some(format!(
                "unsupported\n{}",
                z3_unsupported_query_comment(state, keyword)
            ));
        }
        eprintln_z3_unsupported_query_comment(state, keyword);
        return Some("unsupported".to_string());
    }
    if key == "error-behavior" {
        return Some(
            if state.exit_on_error {
                "immediate-exit"
            } else {
                "continued-execution"
            }
            .to_string(),
        );
    }
    if key == "int-real-coercions" {
        return Some(state.int_real_coercions.to_string());
    }
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
        | "rewriter.max_power_expansion"
        | "rewriter.som"
        | "rewriter.som_blowup"
        | "rewriter.flat"
        | "rewriter.expand_power"
        | "rewriter.mul_to_power"
        | "rewriter.max_degree"
        | "rewriter.sort_sums"
        | "rewriter.push_to_real"
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

/// The regular-channel text of an executor response, recording every
/// `(error ...)` it prints as an error of the run.
///
/// z3 exits 1 for every error it prints, and no certificate may embed a
/// problem in which a command failed (`public_unsat_artifacts_allowed`). The
/// arms that reword a response into z3's form record their error themselves;
/// every other executor error passed through unrecorded. Measured on main
/// db768acbd: `(get-assignment)` or `(eval a)` with no model, and
/// `(get-proof)` or `(get-unsat-core)` after `sat`, each printed an error,
/// exited 0, and left a later strict `unsat` published with its certificate.
/// `echo` prints the script's own text, which is never an error.
fn z3_compat_output_for_command(
    state: &mut SmtTranscriptState,
    cmd: &Command,
    output: &str,
) -> Option<String> {
    let recorded = state.recoverable_error_count;
    let rendered = z3_compat_render_command_output(state, cmd, output);
    let prints_error = !matches!(cmd, Command::Echo(_))
        && rendered
            .as_deref()
            .is_some_and(|text| text.starts_with("(error "));
    if prints_error && state.recoverable_error_count == recorded {
        state.note_recoverable_error();
    }
    rendered
}

fn z3_compat_render_command_output(
    state: &mut SmtTranscriptState,
    cmd: &Command,
    output: &str,
) -> Option<String> {
    if let Some(message) = z3_result_query_refusal(cmd, output) {
        state.note_recoverable_error();
        return Some(source_error(
            current_source_last_token_position(state),
            message,
        ));
    }
    match cmd {
        Command::GetInfo(keyword) => z3_compat_get_info_output(state, keyword, output),
        Command::GetOption(keyword) => z3_compat_get_option_output(state, keyword, output),
        Command::GetObjectives if z3_mode_enabled() => {
            Some(z3_compat_get_objectives_output(output))
        }
        Command::GetConsequences(assumptions, _) if z3_mode_enabled() => Some(
            z3_compat_get_consequences_output(output, !assumptions.is_empty()),
        ),
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
        Command::GetUnsatAssumptions
            if output == "(error \"no check-sat-assuming has been performed\")" =>
        {
            Some("()".to_string())
        }
        _ => Some(output.to_string()),
    }
}

/// z3's wording for the executor's refusal of a result query (no model, no
/// proof, no core, no assumptions to report), which z3 prints positioned and
/// exits 1 for.
fn z3_result_query_refusal(cmd: &Command, output: &str) -> Option<&'static str> {
    match cmd {
        // Two distinct executor spellings reach this point and BOTH are the same
        // z3 response. The second was unhandled, so it fell through unflagged and
        // unpositioned: ay printed a bare `(error "model is not available")` and
        // exited 0, where z3 emits the positioned form and exits 1.
        //
        //   (set-logic ALL) (get-model)
        //     z3: (error "line 2 column 10: model is not available")   exit 1
        Command::GetModel
            if output == "(error \"model generation is not enabled\")"
                || output == "(error \"model is not available\")" =>
        {
            Some("model is not available")
        }
        // `eval` had the same gap as `get-model` above, and `get-assignment`
        // with no `sat` (or `unknown`) to read printed a bare
        // `(error "assignment is not available")`. Each exited 0 and, because
        // the error went unrecorded, still published a certificate for a later
        // `unsat` in the same problem.
        //
        //   (set-logic QF_UF) (get-assignment) ... (check-sat)
        //     z3: (error "line 2 column 15: model is not available")   exit 1
        Command::GetValue(_) | Command::Eval(_)
            if output == "(error \"model is not available\")" =>
        {
            Some("model is not available")
        }
        Command::GetAssignment if output == "(error \"assignment is not available\")" => {
            Some("model is not available")
        }
        // z3 names no cause for either (no query yet, or the last was not
        // `unsat`): `(error "line 4 column 10: proof is not available")`.
        Command::GetProof if output.starts_with("(error \"proof is not available") => {
            Some("proof is not available")
        }
        Command::GetUnsatCore if output.starts_with("(error \"unsat core is not available") => {
            Some("unsat core is not available")
        }
        Command::GetUnsatCore
            if output
                == "(error \"unsat core generation is not enabled, set :produce-unsat-cores to true\")" =>
        {
            Some("unsat core construction is not enabled, use command (set-option :produce-unsat-cores true)")
        }
        Command::GetUnsatAssumptions
            if output == "(error \"unsat assumptions not available, last result was sat\")" =>
        {
            Some("unsat assumptions is not available")
        }
        _ => None,
    }
}

fn z3_compat_get_objectives_output(output: &str) -> String {
    // `Executor::get_objectives` is also a native API surface and historically
    // returns a complete line ending in `\n`. The CLI transcript writer adds
    // its own newline to every command result, so forwarding that byte here
    // creates a blank line that Z3 5.0.0 does not emit. Strip exactly the
    // executor-owned terminator only at the z3-mode presentation boundary;
    // native callers retain their established string contract.
    output.strip_suffix('\n').unwrap_or(output).to_string()
}

fn z3_compat_get_consequences_output(output: &str, has_assumptions: bool) -> String {
    // The native executor surface returns one machine-friendly S-expression:
    // `(status (consequence ...))`. Z3 5.0.0's CLI instead prints the status,
    // a blank line, then one implication per line; with no explicit assumptions
    // it spells the antecedent `true`. Parse the native value structurally so a
    // nested consequence cannot be split with string heuristics. Any unexpected
    // internal shape is retained verbatim (fail-safe presentation fallback).
    let Ok(ref parsed) = parse_sexp(output) else {
        return output.to_string();
    };
    let SExpr::List(parts) = parsed else {
        return output.to_string();
    };
    let [status, SExpr::List(consequences)] = parts.as_slice() else {
        return output.to_string();
    };
    let Some(status) = status.as_symbol() else {
        return output.to_string();
    };
    if !matches!(status, "sat" | "unsat" | "unknown")
        || (status != "sat" && !consequences.is_empty())
        || (has_assumptions
            && consequences.iter().any(|consequence| {
                !matches!(
                    consequence.as_list(),
                    Some([head, _, _]) if head.is_symbol("=>")
                )
            }))
    {
        return output.to_string();
    }

    let mut rendered = format!("{status}\n");
    if !consequences.is_empty() {
        rendered.push('\n');
        for (index, consequence) in consequences.iter().enumerate() {
            if index != 0 {
                rendered.push('\n');
            }
            if has_assumptions {
                rendered.push_str(&consequence.to_string());
            } else {
                rendered.push_str("(=> true ");
                rendered.push_str(&consequence.to_string());
                rendered.push(')');
            }
        }
    }
    rendered
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
    if is_decision_query && raw_output == "unsat" && transcript.holds_unsat_publication() {
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

/// Publish the CLI-visible result of the #8759 strict-proof terminal-trust
/// gate: `unknown` on stdout plus the `(incomplete proof-trusted)`
/// certification rejection on the transcript.
///
/// Shared by the two ways the gate can fire — the CLI flag observing a raw
/// `unsat`, and the executor's own publication funnel having already withheld
/// it — so the emitted contract is byte-identical either way.
fn publish_strict_proof_trust_rejection(
    transcript: &mut SmtTranscriptState,
    cmd: &Command,
    executor: &Executor,
) -> bool {
    update_transcript_state_after_command(transcript, cmd);
    transcript.reject_result_certification("(incomplete proof-trusted)");
    invalidate_artifacts_for_rejected_result();
    if let Err(error) = invalidate_decision_trace_for_public_mismatch(transcript) {
        eprintln_smt_error(error);
        return false;
    }
    let published = print_synthesized_public_unknown(transcript);
    // The refusal names its cause (D7): which arm of the gate fired and, for
    // an unsupported external-recheck surface, the sort or symbol pinned
    // Carcara cannot parse. `--strict-proofs` claims an external check; this
    // is where that claim is refused, so this is where the reason belongs.
    if published {
        if let Some(detail) = executor.unknown_detail() {
            print_diagnostic_line(transcript, &format!("c strict-proofs: {detail}"));
        }
    }
    published
}

/// Inspect the executor's last Alethe proof and return `true` when the
/// terminal empty-clause derivation is not trust-free. See #8759.
///
/// The predicate itself lives in the library, on
/// `Executor::unsat_proof_terminal_trust_detected`, and that is the point: this
/// function used to be its ONLY definition, so `--strict-proofs` was a
/// driver-level downgrade and a consumer linking `ay-dpll` got no gate at all.
/// The executor's public UNSAT funnel now enforces the same disjunction —
/// terminal `trust`/`hole` step, provenance-unbacked `assume` leaf, or an
/// uncheckable `Seq` reference — so the CLI and the library cannot disagree
/// about the same proof.
fn terminal_trust_detected(executor: &Executor) -> bool {
    executor.unsat_proof_terminal_trust_detected()
}

/// The one attribution line an unevidenced `unsat` must carry.
///
/// `path` names the certificate — the file that exists, or the file that would
/// have been written. Both are useful to a census; a decline with no path is
/// not, because it cannot be joined to anything.
///
/// `mechanism` is what is TRUE OF THIS VERDICT NOW. `recorded=` is what a
/// producer wrote down during assembly, and the two differ exactly when a later
/// repair pass superseded the gap the producer named — a real and measurable
/// event (the finite-enum pigeonhole rebuild replaces the whole proof; the
/// promoters retype heads), and one a census must be able to see rather than
/// infer. Printing only the first would hide supersession; printing only the
/// second would attach "no derivation" to documents that have one.
fn disclose_proof_decline(
    path: &str,
    mechanism: ProofDeclineMechanism,
    recorded: Option<ProofDeclineMechanism>,
) {
    safe_eprintln!(
        "c ay.proof.decline path={path} mechanism={} recorded={} — {}",
        mechanism.tag(),
        recorded.map_or("none", ProofDeclineMechanism::tag),
        mechanism.explanation(),
    );
}

/// How an assembly-time record competes with a fallback the caller computes.
///
/// #evidence-stage-3, and this distinction was MEASURED, not designed. The
/// first version screened the record against the retained proof everywhere, on
/// the reasoning that a proof which stopped carrying a trust step had
/// superseded its own decline. On QF_FP `lt-has-no-other-solution-8331` that
/// reasoning is false: the closer recorded `assume-family-trust-closure`, an FP
/// promoter then RETYPED the same head into a kind AY's own checker validates —
/// `:proof_steps 7`, `:proof_trust 0`, `unsat_admission=strict-proof`, and
/// `:cert.proof_steps_recorded 0` for a bit-blasted refutation — and the screen
/// read "trust-free" and dropped the record. The head was relabelled, not
/// replaced, and the file then blamed the printer for a lane that recorded no
/// derivation at all. That is exactly the misattribution this stage exists to
/// remove.
#[derive(Clone, Copy)]
enum DeclinePrecedence {
    /// A document was written, so the subject is the DOCUMENT. A record the
    /// retained derivation no longer exhibits has been superseded by a repair
    /// pass and must not be printed over a proof that does not have that gap.
    ScreenAgainstRetainedProof,
    /// No document exists. The render is the last stage in the pipeline and
    /// structurally the first gate to speak — the pinned-checker sort screen
    /// runs before a single step is emitted — so anything recorded during
    /// ASSEMBLY is upstream of it and outranks it.
    AssemblyOutranksRender,
}

/// The attribution line, with the record/fallback contest resolved in one place.
///
/// Every caller wants the same answer — the assembly record where it applies,
/// else a fallback only the caller can compute — and the acceptance criterion is
/// that exactly one line comes out of it.
fn disclose_proof_decline_with_fallback(
    executor: &Executor,
    path: &str,
    precedence: DeclinePrecedence,
    fallback: impl FnOnce() -> ProofDeclineMechanism,
) {
    let recorded = executor.last_proof_decline();
    let live = match precedence {
        DeclinePrecedence::ScreenAgainstRetainedProof => executor.live_proof_decline(),
        DeclinePrecedence::AssemblyOutranksRender => recorded,
    };
    let mechanism = live.unwrap_or_else(fallback);
    disclose_proof_decline(path, mechanism, recorded);
    disclose_trust_closure_census(executor, mechanism);
    disclose_semantic_token_census(executor, mechanism);
    disclose_unbounded_census(executor, mechanism);
}

/// What the exact semantic-certificate mint held, for the one mechanism it
/// names.
///
/// #semantic-token census. `checked-semantic-certificate-unrendered` is the
/// campaign's structural thesis in its purest form — a checked derivation
/// that only lacks a writer — and this line is how a corpus scan tests that
/// name against the object: how many leaf obligations the token holds, and
/// whether the sealed root can be the authored assertion at all
/// (`construction_residue=yes` means the authored text names declared symbols
/// the symbol-free sealed root cannot; term construction erased them).
///
/// Diagnostic only. Nothing reads these fields to decide anything.
fn disclose_semantic_token_census(executor: &Executor, mechanism: ProofDeclineMechanism) {
    if !matches!(
        mechanism,
        ProofDeclineMechanism::CheckedSemanticCertificateUnrendered
            | ProofDeclineMechanism::ExactExpansionOverDischargedTrust
            | ProofDeclineMechanism::AuthoredSubsetUnrendered
    ) {
        return;
    }
    let Some(census) = executor.last_semantic_token_census() else {
        return;
    };
    safe_eprintln!(
        "c ay.proof.semantic-token kind={} obligations={} ground_true={} ground_false={} \
         nested_refuted={} nested_negation_refuted={} nested_trust_refuted={} leaf_only={} \
         sealed_root_head={} \
         sealed_root_nodes={} authored_source={} authored_head={} authored_nodes={} \
         authored_symbols={} authored_walk_complete={} construction_residue={} \
         sealed_root=\"{}\"",
        census.kind,
        census.obligations,
        census.ground_true,
        census.ground_false,
        census.nested_refuted,
        census.nested_negation_refuted,
        census.nested_trust_refuted,
        yes_no(census.is_leaf_only()),
        census.sealed_root_head,
        census.sealed_root_nodes,
        census.authored_source.tag(),
        census.authored_head,
        census.authored_nodes,
        census.authored_symbols,
        yes_no(census.authored_walk_complete),
        match census.sealed_root_is_construction_residue() {
            Some(true) => "yes",
            Some(false) => "no",
            None => "undetermined",
        },
        census.sealed_root_surface,
    );
}

/// What was on the other side of the bound, for the two "unbounded" declines.
///
/// #unbounded-population. Both mechanisms say a bound was exceeded and neither
/// says which one, on what, or what lifting it would cost. The sibling class
/// was diagnosed by counting at the site and the count refuted the obvious
/// fix; this is the same count for these two. Diagnostic only.
fn disclose_unbounded_census(executor: &Executor, mechanism: ProofDeclineMechanism) {
    if !matches!(
        mechanism,
        ProofDeclineMechanism::AuthoredSourceRootUnbounded
            | ProofDeclineMechanism::AuthoredSurfaceOverridePlanUnbounded
    ) {
        return;
    }
    let Some(census) = executor.last_unbounded_census() else {
        return;
    };
    match census {
        UnboundedCensus::SourceRoot(c) => {
            let f = c.first_refused;
            let l = c.largest_refused;
            safe_eprintln!(
                "c ay.proof.unbounded mechanism={} site=source-root roots={} refused_roots={} \
                 refusal={} first_nodes={} first_depth={} first_bytes={} first_lets={} \
                 first_let_depth={} first_binders={} first_unpriced={} largest_nodes={} \
                 largest_depth={} largest_bytes={} largest_lets={} largest_let_depth={} \
                 bounded_roots_work={} solve_window_roots={} authored_roots={} \
                 first_canonical_source={} first_canonical_unique={} \
                 first_canonical_expanded={} first_canonical_depth={} \
                 first_canonical_binders={} first_canonical_kind={}",
                mechanism.tag(),
                c.roots,
                c.refused_roots,
                c.refusal.map_or("none", |r| r.tag()),
                f.nodes,
                f.depth,
                f.bytes,
                f.let_bindings,
                f.let_depth,
                f.binders,
                f.unpriced,
                l.nodes,
                l.depth,
                l.bytes,
                l.let_bindings,
                l.let_depth,
                c.bounded_roots_work,
                c.solve_window_roots,
                c.authored_roots,
                c.first_canonical_source,
                c.first_canonical.unique_nodes,
                c.first_canonical.expanded_nodes,
                c.first_canonical.depth,
                c.first_canonical.binders,
                c.first_canonical_kind,
            );
        }
        UnboundedCensus::OverridePlan(c) => {
            let g = c.largest_canonical;
            safe_eprintln!(
                "c ay.proof.unbounded mechanism={} site=override-plan exit={} \
                 problem_assertions={} original_problem_assertions={} parsed_assertions={} \
                 provenance={} source_scan_work={} pair_specs={} canonical_refused_shape={} \
                 canonical_refused_size={} canonical_refused_symbol={} \
                 canonical_first_refusal={} canonical_work={} \
                 largest_unique_nodes={} largest_expanded_nodes={} largest_depth={} \
                 largest_binders={} envelope_remaining={} envelope_charge={} \
                 collector_refused_pair={} overrides={} override_bytes={}",
                mechanism.tag(),
                c.exit.map_or("none", OverridePlanExit::tag),
                c.problem_assertions,
                c.original_problem_assertions,
                c.parsed_assertions,
                yes_no(c.has_provenance),
                c.source_scan_work,
                c.pair_specs,
                c.canonical_roots_refused_shape,
                c.canonical_roots_refused_size,
                c.canonical_roots_refused_symbol,
                c.canonical_first_refusal
                    .map_or("none", CanonicalWorkRefusal::tag),
                c.canonical_work,
                g.unique_nodes,
                g.expanded_nodes,
                g.depth,
                g.binders,
                c.envelope_remaining,
                c.envelope_charge
                    .map_or_else(|| "unbounded".to_string(), |charge| charge.to_string()),
                c.collector_refused_pair
                    .map_or_else(|| "none".to_string(), |pair| pair.to_string()),
                c.overrides,
                c.override_bytes,
            );
        }
    }
}

/// What the last-resort closer was looking at, for the two mechanisms it names.
///
/// #closer-population. `assume-family-trust-closure` is the largest class in
/// the decline census and the census could not say whether it means "AY derived
/// something and the closer could not chain it" or "the lane that decided this
/// query recorded nothing". The artifact cannot answer that — after the closer
/// runs, its own head-and-resolution chain is the whole document — so the
/// counts are taken at the closure site and disclosed here.
///
/// Scoped to the two closure mechanisms on purpose: the closer can have run and
/// then been superseded by a later repair pass, and attaching its census to a
/// decline some other lane recorded would invite exactly the misreading the
/// attribution work exists to remove.
///
/// Diagnostic only. Nothing reads these numbers to decide anything.
const fn yes_no(flag: bool) -> &'static str {
    if flag {
        "yes"
    } else {
        "no"
    }
}

fn disclose_trust_closure_census(executor: &Executor, mechanism: ProofDeclineMechanism) {
    if !matches!(
        mechanism,
        ProofDeclineMechanism::AssumeFamilyTrustClosure
            | ProofDeclineMechanism::DerivedLeafTrustClosure { .. }
    ) {
        return;
    }
    let Some(census) = executor.last_trust_closure_census() else {
        return;
    };
    safe_eprintln!(
        "c ay.proof.closure mechanism={} steps={} assumes={} unit_trust_leaves={} \
         theory_lemmas={} typed_theory_lemmas={} derived_steps={} assumptions_only={} \
         sat_reconstruction={} clause_trace_entries={} clause_trace_has_empty={} \
         mapped_vars={} untranslatable_entries={} proof_work_exhausted={} \
         trace_truncated={} propositional_refutation={} destroyed_entries={} \
         destroyed_originals={} destroyed_learned={} destroyed_learned_with_hints={} \
         destroyed_has_empty={} trace_armings={}",
        mechanism.tag(),
        census.steps,
        census.assumes,
        census.unit_trust_leaves,
        census.theory_lemmas,
        census.typed_theory_lemmas,
        census.derived_steps,
        yes_no(census.is_assumptions_only()),
        census
            .reconstruction
            .outcome
            .map_or("never-ran", SatReconstructionOutcome::tag),
        census.reconstruction.trace_entries,
        yes_no(census.reconstruction.trace_has_empty),
        census.reconstruction.mapped_vars,
        census.reconstruction.untranslatable_entries,
        yes_no(census.reconstruction.proof_work_exhausted),
        yes_no(census.reconstruction.trace_truncated),
        yes_no(census.has_propositional_refutation()),
        census.reconstruction.destroyed_entries,
        census.reconstruction.destroyed_originals,
        census.reconstruction.destroyed_learned,
        census.reconstruction.destroyed_learned_with_hints,
        yes_no(census.reconstruction.destroyed_has_empty),
        ay_sat::clause_trace_armings(),
    );
}

/// What independently re-decided this refutation, when something did.
///
/// #evidence-stage-3. Measured on a 24-file sample of the class AY's own strict
/// checker rejects: 17 of 24 published on a fresh-`Executor` whole-problem
/// re-solve and the rest on a clause-by-clause standalone-tautology discharge.
/// Neither appeared anywhere in the output — only in two statistics counters —
/// so a reader could not tell a verdict that survived an independent
/// re-decision from one that rests on nothing.
///
/// `scope=authored` is not decoration: the re-decision is run over the AUTHORED
/// obligation (`authored_corroboration_scope`), not over the solver's rewritten
/// internal assertion set, and that is the only version of the claim worth
/// anything to a reader of the input file.
///
/// This is REPRODUCIBILITY evidence and never checkability evidence. It does
/// not make a verdict tier A, and the campaign's evidence predicate does not
/// read it.
///
/// P4 of the 2026-10-02 evidence policy: the line names the arm (`method=`),
/// where it ran (`source=`, `nested:…` when a probe an exact theorem sealed
/// ran it) and which strengthenings the re-solve ran without (`disabled=`,
/// `none` printed literally: the re-solve walked the same code). It is read
/// off the certificate the command consumed, so a nested probe's
/// corroboration is disclosed too.
fn disclose_unsat_corroboration(executor: &Executor) {
    if let Some(corroboration) = executor.last_unsat_corroboration() {
        safe_eprintln!(
            "c ay.proof.corroboration method={} source={} disabled={} scope=authored — {}",
            corroboration.method().tag(),
            corroboration.source().tag(),
            corroboration.disabled().tags(),
            corroboration.explanation(),
        );
    }
}

/// `evidence=… corroboration=… disabled=…` for the certificate line and the
/// no-certificate warnings (evidence policy P4, 2026-10-02).
///
/// `evidence=` is the level of the certificate the command consumed: E2 a
/// checker verified the refutation, E1 AY's own code re-derived or re-ran what
/// the refutation could not show (`discharged-trust`, or a
/// `checked-sat-refutation` with a `Generic` premise AY's verifier re-derived),
/// E0 no checked refutation. Only `--rigor strict` publishes on E2 alone.
fn unsat_evidence_fields(executor: &Executor) -> String {
    let evidence = executor.last_command_unsat_evidence();
    let level = evidence.map_or("none-recorded", |evidence| evidence.level().tag());
    let corroboration = evidence.and_then(|evidence| evidence.corroboration());
    format!(
        "evidence={level} corroboration={} disabled={}",
        corroboration.map_or("none", |corroboration| corroboration.method().tag()),
        corroboration.map_or_else(
            || "none".to_string(),
            |corroboration| corroboration.disabled().tags()
        ),
    )
}

/// Classify a render refusal, for use ONLY when no earlier lane declined.
///
/// #evidence-stage-3, and the ordering is the point. The render is the last
/// gate in the pipeline and frequently the FIRST one to speak: before owner
/// decision D7 (2026-09-22) the pinned-Carcara sort screen ran in
/// `prepare_proof` before a single step was emitted, so on a floating-point
/// query — where the lane bit-blasts with proof output off and the refutation
/// is one bare trust lemma — it fired on a document that never had a
/// derivation to print. Reporting it as the cause blamed the printer for 90
/// files whose defect is upstream of the printer entirely. So the caller
/// consults `Executor::live_proof_decline` first and only falls through to
/// this when nothing earlier declined. Since D7 the printer no longer refuses
/// on that screen (the surface is disclosed on the written certificate
/// instead), so the `pinned Carcara` arm below is reached only by an older
/// producer's refusal string; the structural refusals that remain in
/// `prepare_proof` (a term handle outside the store, a malformed `nra_sos`
/// payload) fall to the stale-scope arm, which is the closest class.
fn mechanism_from_print_error(error: &ay_proof::AlethePrintError) -> ProofDeclineMechanism {
    use ay_proof::AlethePrintError as Print;
    match error {
        Print::EmissionBudgetExhausted { .. } => ProofDeclineMechanism::AletheEmissionWorkBudget,
        Print::UndeclarableProofSymbols { .. } => ProofDeclineMechanism::UndeclarableProofSymbols,
        // Same class, found on the bytes: a witness the printer resugared
        // still printed raw somewhere, so the document would be free in a
        // symbol it cannot introduce.
        Print::ResugaredWitnessPrintedRaw { .. } => ProofDeclineMechanism::UndeclarableProofSymbols,
        // Matched on the reason because this one variant carries three
        // unrelated refusals: the pinned checker's grammar, and two staleness
        // checks on AY's own export surface.
        Print::UnavailableAuthenticatedSurface { reason } => {
            if reason.contains("pinned Carcara") {
                ProofDeclineMechanism::PinnedCheckerSurfaceUnsupported
            } else {
                ProofDeclineMechanism::StaleAuthenticatedExportScope
            }
        }
        _ => ProofDeclineMechanism::ProofSurfaceBridgeMissing,
    }
}

/// Disclose, on a published Alethe certificate, exactly which of AY's own
/// checks the certificate passed — and, separately, what backs the verdict.
///
/// Four facts read off the proof AY actually emitted, plus one read off the
/// publication funnel:
///
/// * `unproved_steps` — steps on the path to the empty clause that carry no
///   derivation: `trust` rules, trust-kind theory lemmas, and explicit
///   `hole`s. ALL of them print as `hole` in the emitted document (the wire
///   name for "unproved"), so a certificate with any is *holey* to an
///   external checker, never *valid*.
/// * `foreign_assumes` — `yes` when a premise `assume` of the document is not
///   an assertion of the input as written (compared token for token, up to
///   literal and quoting spelling; see `ay_dpll::normalize_premise_surface`),
///   or when AY's provenance does not back one; `unjudged` when that
///   comparison could not be made.
/// * `trust_free` — no `trust`/`hole` step and no provenance-unbacked
///   `assume` reaches the empty clause.
/// * `ay_self_checkable` — a property OF THE DOCUMENT AT `path`, and of
///   nothing else: `yes` means the file on disk carries NO unproved step
///   (`unproved_steps=0`), assumes only the input's own assertions
///   (`foreign_assumes=no`), AND no terminal trust / foreign-`assume` /
///   uncheckable-`Seq` gap reaches its empty clause (`terminal_trust_detected`,
///   the CLI's own `--rigor strict` screen).
///
///   It is deliberately NOT also conjoined with
///   `Executor::unsat_proof_has_known_wire_gap()`, the second arm of the
///   executor's strict decline gate — that was tried and MEASURED WRONG; see
///   the comment on `strict_screen_refuses` in `disclose_alethe_certificate`.
///
///   `ay_self_checkable=yes` therefore IMPLIES `unproved_steps=0`, which is
///   what makes the flag alone a safe evidence predicate. Before
///   #evidence-stage-0 it was `!terminal_trust_detected(executor)` alone: both
///   internal predicates read the IN-MEMORY proof, and neither can see the
///   printer's own `ay_core::wire_rule_name` downgrade of a rule AY's checker
///   verified but the pinned external checker cannot spell. So
///   `(assert (not (or (= #b10 #b10) (= x #b01))))` published a three-line
///   artifact whose only inference is `:rule hole` under
///   `unproved_steps=1 … ay_self_checkable=yes`, at every rigor level, and at
///   corpus scale that was 78 certificates carrying up to 148 unproved steps
///   scored as evidence.
///
///   The converse is narrower than it looks: `ay_self_checkable=no` predicts
///   that `--rigor strict` withholds the verdict (its admission decision
///   refuses any document with an unproved step or a foreign `assume`,
///   including holes the printer alone introduced, on every input route), and
///   says nothing about the other rigor levels. Before that gate `--rigor strict` decided on the IN-MEMORY
///   derivation alone and published printer-holed documents; measured on four
///   external-codegen bridge/stride queries, each published as `unsat` with
///   `unproved_steps=1 … unsat_admission=strict-proof`.
///   Nor is `yes` a promise that an external checker will answer *valid*: it
///   says the document carries no `hole`, not that every symbol and rule in it
///   is one the pinned checker accepts (the undeclarable-symbol and
///   congruence-premise printer classes are documented in LIMITATIONS.md).
///   Nor is it the `--rigor certified` (`--self-check`) gate: that one is a
///   DISJUNCTION over authorities the Alethe presentation is only one of — see
///   `Executor::check_sat`'s `unsat_proof_self_certified() ||
///   bv_drat_self_cert || checked_refutation_satisfies_self_check()` — so a
///   `hole`-bearing document routinely accompanies a verdict certified by a
///   replayed SAT-resolution refutation or a native BV DRAT re-check.
/// * `unsat_admission` — which certification authority actually admitted this
///   published `unsat`. This is the honest answer to "what is behind the
///   verdict", and it is deliberately reported next to, not merged with, the
///   document's own checkability. In particular `unsat_admission=strict-proof`
///   means `Executor::check_strict_unsat_presentation` ran
///   `ay_proof::check_proof_strict_with_datatypes` over the IN-MEMORY proof and
///   it re-derived every step — that call rejects `trust`/`hole` rules and any
///   theory-lemma family without a semantic validator, so the claim is about
///   the derivation, not about the file. It is therefore consistent, and not a
///   contradiction, for `unsat_admission=strict-proof` to sit beside
///   `unproved_steps=1 ay_self_checkable=no`: AY's checker verified the step,
///   and the printer had no external spelling for it.
///
/// `carcara_surface` is `supported` (pinned Carcara parses the document and
/// the problem, and no step is spelled for one of its invocations only, so
/// the spelling reads the same with or without `--expand-let-bindings`; that
/// every step checks is what `unproved_steps` and `foreign_assumes` add — an
/// `assume` matching a `let` premise only after expansion is
/// `foreign_assumes=yes`), `unsupported` (pinned Carcara cannot
/// parse the proof or the authored problem it is paired with; this wins over
/// `clean-dialect`, whose spellings are moot when the parse stops),
/// `clean-dialect` (it parses, but the render kept a spelling only Clean's
/// vendored Carcara checks, which pinned Carcara 9a352ee refuses; see
/// `ay_proof::AletheDialect`), `without-let-expansion` (the render printed a
/// `:rule let` step over the problem's own `let`, which pinned Carcara checks
/// only in its canonical invocation `carcara check -- PROOF PROBLEM`, never
/// under `--expand-let-bindings`) or `none-recorded`. It is the verdict the
/// streamed export returned beside exactly the bytes at `path`
/// (`Executor::try_export_last_proof_alethe_for_problem_scope_to_with_carcara_surface`).
///
/// Written as SMT-LIB comments on stderr so it never perturbs the solver's
/// stdout answer.
fn disclose_alethe_certificate(
    executor: &Executor,
    path: &str,
    carcara_surface: Option<&ay_proof::CarcaraSurface>,
) {
    let evidence = certificate_evidence(executor, path);
    let unproved = evidence.unproved;
    let premises_verbatim = evidence.premises == AssumedPremises::Verbatim;
    // The derivation's own trust-freeness: no `trust`/`hole` step and no
    // trust-kind lemma on the path to the empty clause, and every premise
    // `assume` the input's own. `trust_free` below additionally demands a
    // hole-free DOCUMENT.
    let derivation_trust_free = evidence.derivation_trust_free && premises_verbatim;
    let trust_free = derivation_trust_free && unproved == 0;
    // The CLI's own `--rigor strict` screen, verbatim
    // (`run_command`'s `strict_derivation_screen_refuses`).
    // When this is true, strict really does answer `unknown`, so the warning
    // below may say so.
    //
    // REFUTED, and deliberately NOT a disjunction with
    // `Executor::unsat_proof_has_known_wire_gap()`. #evidence-stage-0 set out
    // to add that second arm so the disclosure would agree with the executor's
    // funnel (`decline_trust_bearing_unsat_under_strict_proofs`). Measured on
    // `benchmarks/smtlib-all/QF_AX/non-incremental__QF_AX__storeinv__storeinv_t2_np_nf_ai_00001_001.cvc.smt2`:
    // the wire-gap predicate answers TRUE at disclosure time while the very
    // same run publishes `unsat` under `--rigor strict`, on a certificate with
    // `unproved_steps=0 foreign_assumes=no trust_free=yes`. The two predicates
    // are sampled at different points of the pipeline — the funnel screens the
    // proof it is about to certify, this runs after the printer — so forcing
    // them together does not make the flag agree with the gate; it makes the
    // flag lie about a hole-free document, and it did (1 of the 2 hole-free
    // certificates in a seeded 50-file QF_AX/QF_IDL sweep flipped to `no`).
    // The gate is not weakened by leaving it out: a proof the funnel refuses
    // never publishes a certificate for this function to disclose.
    let strict_screen_refuses = terminal_trust_detected(executor);
    // THE FLAG IS A STATEMENT ABOUT THE FILE AT `path`. A document carrying a
    // printed unproved step can never be a clean bill of health, whatever the
    // in-memory predicates say about the derivation behind it, so
    // `ay_self_checkable=yes` now IMPLIES `unproved_steps=0`. See the item
    // doc above for the reproducer this was measured on.
    // It also implies every premise `assume` is the input's own, as the strict
    // gate requires; a premise-only refusal has its own warning, not a `hole`.
    let holed_or_screened = strict_screen_refuses || unproved > 0;
    let self_checkable = !holed_or_screened && premises_verbatim;
    // The external-recheck surface, DISCLOSED (owner decision D7, 2026-09-22).
    // `unsupported` means pinned Carcara cannot parse this file — a `Seq`,
    // `FloatingPoint` or `Char` sort, or a Z3-escaped symbol — so the verdict
    // stands on AY's strict checker alone. The file is still written: only a
    // consumer that CLAIMS an external check (`--strict-proofs`,
    // `--self-check`, a Carcara cross-check) refuses it, and it refuses with
    // the reason printed below. Read on the same proof the strict screen read.
    // A parseable document that keeps a Clean-only spelling is NOT one pinned
    // Carcara accepts (475ba9547's sign-filled `bitblast_ashr` layer was
    // disclosed `supported` and refused by it), nor is one whose `:rule let`
    // step only one pinned invocation accepts: the render reported both, and
    // the streamed export folded that report into `carcara_surface`.
    // Only a spelling pinned Carcara cannot PARSE is a gap of the strict screen.
    let surface_gap = match carcara_surface {
        Some(ay_proof::CarcaraSurface::Unsupported { reason }) => Some(reason.as_str()),
        _ => None,
    };
    let clean_only = match carcara_surface {
        Some(ay_proof::CarcaraSurface::CleanDialect { spelling }) => Some(*spelling),
        _ => None,
    };
    let surface_label = match carcara_surface {
        Some(ay_proof::CarcaraSurface::CleanDialect { .. }) => "clean-dialect",
        Some(ay_proof::CarcaraSurface::WithoutLetExpansion) => "without-let-expansion",
        Some(surface) if surface.is_supported() => "supported",
        Some(_) => "unsupported",
        None => "none-recorded",
    };
    // What actually backs the verdict, as opposed to what the document proves.
    // Every published UNSAT consumed exactly one certification capability; name
    // it, so a reader never has to infer the verdict's authority from the
    // artifact's checkability (which is what made the disclaimer below wrong).
    let admission = executor
        .last_command_unsat_admission_tag()
        .unwrap_or("none-recorded");
    safe_eprintln!(
        "c ay.proof.certificate path={path} unproved_steps={unproved} foreign_assumes={} trust_free={} ay_self_checkable={} carcara_surface={} unsat_admission={admission} {}",
        match &evidence.premises {
            AssumedPremises::Verbatim => "no",
            AssumedPremises::Foreign(_) => "yes",
            AssumedPremises::Unjudged(_) => "unjudged",
        },
        if trust_free { "yes" } else { "no" },
        if self_checkable { "yes" } else { "no" },
        surface_label,
        unsat_evidence_fields(executor),
    );
    let premise_warning = match &evidence.premises {
        AssumedPremises::Verbatim => None,
        // An external checker rejects that `assume` only once it parses the
        // document; when pinned Carcara cannot (`carcara_surface=unsupported`)
        // it stops at the parse instead (measured on D7: BVFPLRA, 2026-10-02).
        AssumedPremises::Foreign(assume) if surface_gap.is_some() => Some(format!("contains an `assume` that is not verbatim an assertion of the input ({assume}); a checker that parses this document rejects it at that step, though pinned Carcara stops earlier, at the parse")),
        AssumedPremises::Foreign(assume) => Some(format!("contains an `assume` that is not verbatim an assertion of the input ({assume}); an external checker rejects it at that step")),
        AssumedPremises::Unjudged(why) => Some(format!("has premise `assume`s that were not compared with the input ({why})")),
    };
    if let Some(warning) = premise_warning {
        safe_eprintln!("c warning: {path} {warning}; `--rigor strict` (`--strict-proofs`) answers `unknown` for this verdict");
    }
    let surface_warning = match (surface_gap, clean_only) {
        (Some(reason), _) => Some(format!("carcara_surface=unsupported — {reason}; pinned Carcara cannot parse this document, so the verdict stands on AY's strict checker alone, and `--strict-proofs` / `--self-check` refuse it with this reason")),
        (None, Some(spelling)) if surface_label == "clean-dialect" => Some(format!(
            "carcara_surface=clean-dialect — {}; Clean's vendored Carcara checks this spelling and pinned Carcara 1.1.0 (9a352ee) refuses it, {}",
            spelling.describe(),
            spelling.pinned_dialect_note()
        )),
        (None, None) if surface_label == "without-let-expansion" => Some(format!(
            "carcara_surface=without-let-expansion — {}; check it as `carcara check -- PROOF PROBLEM`: `--expand-let-bindings` expands that `let` at parse time, before the rule sees it, and pinned Carcara then refuses the step",
            ay_proof::CarcaraSurface::WithoutLetExpansion
                .unsupported_reason()
                .unwrap_or_default()
        )),
        _ => None,
    };
    if let Some(warning) = surface_warning {
        safe_eprintln!("c warning: {path} {warning}");
    }
    // A refutation with NO derivation at all is a different failure from one
    // whose last mile is unproved, and until this line the two were
    // indistinguishable in the emitted artifact and in every corpus census
    // built from it. Name the mechanism so the census says which machinery is
    // missing instead of bucketing every cause under one label.
    //
    // #evidence-stage-3 — EXACTLY ONE line, and only where it is true.
    //
    // Only where it is true: an evidenced document needs no excuse, and a
    // decline recorded during assembly can be superseded by a later repair
    // pass, so printing it beside `ay_self_checkable=yes` would be a false
    // statement of the same species this stage exists to remove. `unproved`
    // and `strict_screen_refuses` are already computed above and settle it.
    //
    // Exactly one: on the measured census 32 unevidenced refutations emitted a
    // holey document and recorded nothing, because the two document-side
    // mechanisms are not producer decisions and no producer records them. They
    // are read off the artifact and the derivation behind it, here, at the only
    // point where both are in hand — and the two arms are the same discriminator
    // the two warning branches below already use, so the label and the advice
    // can never disagree.
    if holed_or_screened {
        disclose_proof_decline_with_fallback(
            executor,
            path,
            DeclinePrecedence::ScreenAgainstRetainedProof,
            || {
                // A trust-free derivation the strict screen refuses ONLY for
                // its surface is the D7 disclosure class, not a trust step.
                //
                // "Trust-free" is the DERIVATION's property, read off the
                // proof AY's strict checker walked — not the document's
                // `unproved` count, which also counts a validated kind the
                // printer downgraded to `hole`. Keyed on the document, every
                // FP refutation whose `FpGroundEval` lemma (validated by the
                // exact IEEE-754 evaluator) prints as `hole` was told "a step
                // AY's own strict checker refuses" while `unsat_admission` read
                // `strict-proof` — the 2026-09-23 fp-strings verifier's E1
                // witnesses, one branch at a time.
                if strict_screen_refuses && derivation_trust_free && surface_gap.is_some() {
                    ProofDeclineMechanism::PinnedCheckerSurfaceUnsupported
                } else if strict_screen_refuses {
                    ProofDeclineMechanism::TerminalTrustStepOnPath
                } else {
                    ProofDeclineMechanism::PrinterRuleWithoutExternalSpelling
                }
            },
        );
    }
    disclose_unsat_corroboration(executor);
    // MEASURED 2026-09-06, and the reason this sentence is no longer the one it
    // was: on a seeded 60-file corpus sweep, two files published `unsat` under
    // `--self-check` while this very line printed `ay_self_checkable=no` and the
    // old text claimed `--self-check` would answer `unknown`. Both were admitted
    // by `checked-sat-refutation` — a replayed, premise-authenticated SAT
    // resolution refutation of the exact authored query — which is precisely
    // what the certified rigor level accepts and the strict level does not. The
    // document really is uncheckable; the claim about the verdict was false.
    //
    // The explanation is SPLIT, because after #evidence-stage-0
    // `ay_self_checkable=no` covers two different situations: an unproved step
    // in AY's own derivation, and a document holed by the printer alone (the
    // `unproved_steps=1 … unsat_admission=strict-proof` reproducer). The
    // consequence for `--rigor strict` is the same for both: its publication
    // gate withholds any certificate that carries an unproved step.
    if holed_or_screened {
        // What pinned Carcara 1.1.0 (9a352ee) answers for this document, in
        // its own order of precedence: a parse failure stops it before any
        // step is checked, a step it refuses makes the document *invalid*
        // however many holes it also carries, and only a document whose every
        // other step checks is *holey*. MEASURED on the 445-file D7 unsat list
        // (main a68e18a38f, `carcara check --allow-int-real-subtyping PROOF
        // PROBLEM`): the old two-way split told 81 documents "reports it as
        // *holey*" — 75 with `carcara_surface=unsupported` that pinned Carcara
        // refused with a parser error, 5 with a foreign `assume` and 1 with a
        // Clean-only spelling that it reported *invalid*.
        let holes = if unproved > 0 {
            format!("; it also prints {unproved} unproved step(s) as `hole`")
        } else {
            String::new()
        };
        let prediction = if surface_gap.is_some() {
            format!("is NOT an externally checkable certificate — pinned Carcara cannot parse it (its surface is outside pinned Carcara's grammar, see carcara_surface above) and stops with a parser error before checking any step{holes}")
        } else if matches!(evidence.premises, AssumedPremises::Foreign(_)) {
            format!("is NOT an externally checkable certificate — pinned Carcara reports it *invalid* at the premise `assume` that is not verbatim an assertion of the input (named above){holes}")
        } else if surface_label == "clean-dialect" {
            format!("is NOT an externally checkable certificate — pinned Carcara reports it *invalid* at the Clean-only spelling named above{holes}")
        } else if unproved > 0 {
            format!("is NOT an externally checkable certificate ({unproved} unproved step(s) print as `hole`) — an external checker reports it as *holey*, never *valid*")
        } else {
            "is NOT an externally checkable certificate of this verdict: AY's strict screen finds a trust-kind step on the derivation's path to the empty clause, though the document prints no `hole`".to_string()
        };
        safe_eprintln!(
            "c warning: {path} {prediction}; the exit status reports the verdict, not the certificate"
        );
        if strict_screen_refuses {
            safe_eprintln!(
                "c warning: {path} — `--rigor strict` (`--strict-proofs`) answers `unknown` for this verdict, and so does `--rigor certified` (`--self-check`) when a translated artifact is also demanded (`--proof`, `:produce-proofs`). Bare `--rigor certified` publishes only on an independent certification lane, named by `unsat_admission=` above"
            );
        } else {
            safe_eprintln!(
                "c warning: {path} — these holes are a PRINTER limitation, not an unproved step in AY's derivation: nothing on the path to the empty clause is a `trust` step, and the verdict was admitted by unsat_admission={admission}. `--rigor strict` (`--strict-proofs`) answers `unknown` for this verdict all the same, because it publishes `unsat` only with a certificate that carries no unproved step. This line is about the document; `unsat_admission=` above is the verdict's authority"
            );
        }
    }
}

/// Standing marker for a certificate artifact the publication path REFUSED
/// after the mint had already produced it.
///
/// Two very different things print no `c ay.proof.certificate` line: a verdict
/// whose proof was never reconstructable (nothing was ever offered), and a
/// verdict whose proof WAS built and was then rejected by the renderer, the
/// writer, or the publication authority check. Until this line the only trace
/// of the second case was prose on stderr, and the campaign's evidence census
/// filed both under "no evidence artifact at all" -- which reads as "AY never
/// tried" when in fact AY tried, produced an artifact, and refused it.
///
/// Printed on every posture. What changes under `--rigor strict` is the
/// VERDICT (the caller routes to `RejectToUnknown`); the refusal itself is the
/// same event and earns the same record either way.
///
/// `rejections`/`nested_rejections` mirror the `cert.publication_rejections`
/// and `cert.publication_rejections_nested` counters, so a census reading this
/// line has the refusal accounting in front of it. The nested cell is the
/// share contributed by internal certification probes, which say nothing about
/// the published verdict.
fn disclose_refused_artifact(stage: &str, path: &str, reason: &dyn std::fmt::Display) {
    let accounting = ay_dpll::CertificationAccounting::snapshot();
    safe_eprintln!(
        "c ay.proof.artifact-refused path={path} stage={stage} rejections={} nested_rejections={} reason={reason}",
        accounting.publication_rejections,
        accounting.publication_rejections_nested,
    );
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
/// As [`mark_problem_incomplete`], but records that the ONLY thing dropped was
/// an `assert` — the one monotone case, where a later `unsat` on the remainder
/// is still a sound verdict for the whole problem.
fn mark_problem_incomplete_from_dropped_assertion(
    executor: &mut Executor,
    transcript: &mut SmtTranscriptState,
) {
    // Capture BEFORE: `mark_incomplete` sets the flag unconditionally, so it has
    // to be restored afterwards, and only to its prior value — an earlier
    // non-assertion drop in the same session must keep the block in force.
    let beyond_before = transcript.is_incomplete_beyond_assertions();
    mark_problem_incomplete(executor, transcript);
    transcript.set_incomplete_beyond_assertions(beyond_before);
}

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

/// Post-solve arm of the incomplete-problem soundness backstop.
///
/// Returns `Some(bool)` when the verdict was downgraded (the bool is
/// `execute_and_print`'s return value), or `None` to publish the result as-is.
///
/// Only a NON-`unsat` remainder is downgraded — see the directional argument at
/// the call site. An `unsat` remainder is republished untouched, including its
/// refutation, because that refutation cites only constraints present in the
/// full problem.
fn run_incomplete_problem_gate(
    executor: &mut Executor,
    cmd: &Command,
    transcript: &mut SmtTranscriptState,
    raw_output: &str,
) -> Option<bool> {
    if !transcript.is_incomplete()
        || !matches!(cmd, Command::CheckSat | Command::CheckSatAssuming(_))
    {
        return None;
    }
    // The unsat pass-through is valid ONLY when every dropped command was an
    // `assert`. Dropping an assertion weakens the problem monotonically, so a
    // refutation of the remainder refutes the whole. Dropping a DEFINITION or
    // DECLARATION does not: it changes what the surviving terms mean. With
    //   (define-fun g () Int 1) (define-fun g ((x Int)) Int 2) (assert (= (g) 2))
    // the second definition is unrepresentable and dropped, `(g)` then binds to
    // `g = 1`, and the remainder is "unsat" only because it is a DIFFERENT
    // problem. Same for a panic, a recursive redeclaration, or a depth limit.
    if raw_output == "unsat" && !transcript.is_incomplete_beyond_assertions() {
        return None;
    }

    executor.replace_last_result_with_unknown(UnknownReason::Incomplete);
    update_transcript_state_after_command(transcript, cmd);
    transcript.record_synthesized_unknown(discarded_command_reason(transcript));
    if let Err(error) = invalidate_decision_trace_for_public_mismatch(transcript) {
        eprintln_smt_error(error);
        return Some(false);
    }
    if let Err(error) = Executor::invalidate_bv_cnf_export_for_rejected_check() {
        eprintln_smt_error(error.to_string());
        return Some(false);
    }
    if ay_core::trace_config().dump_bv_cnf_path.is_some() {
        eprintln_smt_error(
            "artifact export failed: --dump-bv-cnf cannot certify a transcript after a problem-contributing command was discarded",
        );
        return Some(false);
    }
    Some(print_synthesized_public_unknown(transcript))
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
    if matches!(cmd, Command::CheckSat | Command::CheckSatAssuming(_)) {
        // This query owes its own response, whatever earlier ones printed: a
        // run the deadline or a memory breach ends during it answers it
        // `unknown` (see `owe_response_for_new_query`).
        super::owe_response_for_new_query();
    }
    note_z3_session_command(transcript, cmd);
    note_z3_session_start_in_context(executor, transcript);
    withhold_before_label_mention(executor, transcript);
    let continued = execute_and_print_command(executor, cmd, transcript, emit_z3_model_inline);
    withhold_after_labels_z3_binds(executor, transcript, cmd);
    continued
}

fn execute_and_print_command(
    executor: &mut Executor,
    cmd: &Command,
    transcript: &mut SmtTranscriptState,
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

    emit_z3_unknown_attribute_warnings(transcript, cmd);

    let recoverable_errors_before = transcript.recoverable_error_count;
    if maybe_handle_cli_transcript_command(executor, transcript, cmd) {
        return !(transcript.exit_on_error
            && transcript.recoverable_error_count > recoverable_errors_before);
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
    // assertion set is an incomplete SUBSET of the real problem.
    //
    // The backstop is DIRECTIONAL, and it used to be applied in both directions.
    // Dropping a constraint only ever WEAKENS the problem, so for a remainder
    // result R and the true problem P (remainder ⊆ P):
    //
    //   R = unsat  =>  P is unsat too. Adding back the dropped constraints
    //                  cannot satisfy an already-unsatisfiable core, and the
    //                  refutation cites only constraints that are present in P,
    //                  so it is a valid refutation OF P. SOUND to publish.
    //   R = sat    =>  P may still be unsat. MUST fail closed.
    //
    // Answering `unknown` on an unsat remainder is therefore not a soundness
    // requirement, just a loss — and a divergence from z3 5.0.0, which publishes
    // `unsat` here. Measured before this change:
    //
    //   (assert bogus) (assert (> x 5)) (assert (< x 3)) (check-sat)
    //       z3: unsat        ay: unknown        <- pure loss, now fixed
    //   (assert bogus) (assert (> x 5)) (check-sat)
    //       z3: sat          ay: unknown        <- ay is RIGHT; kept
    //
    // So the gate can no longer short-circuit before the solve: it has to see
    // the remainder's verdict first. It now runs after `executor.execute`,
    // alongside the strict-proof and firewall gates, which downgrade the same
    // way. `run_incomplete_problem_gate` below is that post-solve arm.
    //
    // Generic over the discarded construct, so this class of unsoundness cannot
    // recur for ANY unsupported syntax.
    // (moved to `run_incomplete_problem_gate`, invoked post-solve below)

    // An unrecognized `set-option` key is an error to z3, printed on stdout with
    // its full legal-parameter list, after which it CONTINUES and exits 1. ay
    // accepted every key silently at exit 0, so a typo'd option was invisible.
    if let Command::SetOption(keyword, _) | Command::SetOptionAttribute(keyword) = cmd {
        if let Some(error) = z3_unknown_option_error(transcript, keyword) {
            print_regular_line(transcript, &error);
            transcript.note_recoverable_error();
            update_transcript_state_after_command(transcript, cmd);
            return true;
        }
    }
    withhold_after_late_global_declarations(executor, transcript, cmd);
    if reject_z3_fixed_option(executor, transcript, cmd) {
        return true;
    }

    if !maybe_enable_z3_default_assignment_query(executor, cmd) {
        eprintln_smt_error("failed to enable assignment collection for get-assignment".to_string());
        return false;
    }
    if matches!(cmd, Command::GetAssignment) {
        record_session_option(transcript, "(set-option :produce-assignments true)");
    }

    let is_decision_query = matches!(cmd, Command::CheckSat | Command::CheckSatAssuming(_));
    if is_decision_query {
        // A failed or panicking new decision must not leave the preceding
        // public result authoritative.
        transcript.clear_public_result();
        // The in-script half of the strict request this query is answered
        // under (the flag is the other half). With the flag, it decides
        // whether the query's UNSAT waits for its certificate
        // (`publish_rendered_executor_output`) and how that certificate is
        // published (`write_alethe_proof`).
        transcript.query_script_strict = executor.script_strict_proofs_requested();
    }

    // Competition robustness: an internal solver bug must NEVER crash the process
    // (a panic = the whole file/run dies = strictly worse than a wrong answer).
    // Catch any unwinding panic during execution and convert it to a sound,
    // non-crashing outcome — `unknown` for a decision query (always sound), a
    // recoverable `(error ...)` otherwise — then continue with the remaining
    // commands. The release profile is intentionally `panic = "unwind"` so this
    // containment works. Found by the diff_fuzz seq sort-interning crash (a valid
    // QF_SLIA input panicked `mk_eq expects same sort`, exiting the process 101).
    let exec_result = match execute_charging_rlimit(executor, cmd, transcript) {
        Ok(r) => r,
        Err(_panic) => return handle_executor_panic(executor, cmd, transcript),
    };
    // The owed model has now had its turn. Clear the debt HERE, before the
    // result is matched, so it is cleared on EVERY outcome — `Ok(Some)`,
    // `Ok(None)` and `Err` alike.
    //
    // This used to sit inside the `Ok(Some(output))` arm below while its comment
    // claimed it ran "whatever the query produced". It did not: a `(get-model)`
    // returning `Ok(None)` or `Err` skipped it entirely and left the debt armed
    // permanently, disabling cooperative timeout exit for the rest of the run.
    // Bounded by the hard watchdog (`main.rs` `hard_timeout_fallback_exit`), so
    // never a hang and never a soundness break — but the stated invariant was
    // not the implemented one. It is now.
    if matches!(cmd, Command::GetModel) {
        transcript.owes_model_emission = false;
    }
    if exec_result.is_ok() {
        record_accepted_command(transcript, cmd, global_declarations_in_force(executor));
    }
    match exec_result {
        Ok(Some(output)) => {
            // The strict request this response is judged under, read ONCE. A
            // decision query's is the request recorded when it started, the
            // value every later gate of its publication reads too
            // (`write_alethe_proof`); any other response's is the live one.
            let strict = if is_decision_query {
                transcript.query_strict_proofs_requested()
            } else {
                strict_admission_requested(executor)
            };
            // Strict-proof mode: downgrade UNSAT to Unknown when the terminal
            // derivation chain contains a `:rule trust` fallback (#8759).
            // The proof is generated internally regardless of `--proof` because
            // `new_executor()` forces `set_produce_proofs(true)` under strict.
            if output == "unsat" && strict_derivation_screen_refuses(strict, executor) {
                let downgraded = executor.reject_last_unsat_as_unknown();
                debug_assert!(downgraded, "strict-proof gate started from UNSAT");
                debug_assert_eq!(
                    executor.unknown_reason(),
                    Some(UnknownReason::ProofTrusted),
                    "the strict-proof gate must publish its own typed reason"
                );
                return publish_strict_proof_trust_rejection(transcript, cmd, executor);
            }
            // The DOCUMENT half, at the one point every route's `unsat` passes
            // (see `strict_admission.rs`).
            if let Some(refusal) = strict_document_refusal(strict, executor, &output) {
                return publish_strict_document_rejection(transcript, cmd, executor, refusal);
            }
            // The executor's own UNSAT funnel may already have downgraded a
            // verdict under `(set-option :check-proofs-strict true)`. Publish
            // the identical transcript certification rejection rather than
            // letting the two spellings of "strict proofs" produce two
            // different outputs; an `unsat` it admitted passed both gates
            // above (`strict` reads the option too).
            if output == "unknown" && executor.unknown_reason() == Some(UnknownReason::ProofTrusted)
            {
                return publish_strict_proof_trust_rejection(transcript, cmd, executor);
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
            // Incomplete-problem backstop, post-solve. Downgrades a non-`unsat`
            // remainder; an `unsat` remainder is published as-is because it is a
            // sound verdict for the FULL problem (see the note above).
            if let Some(handled) = run_incomplete_problem_gate(executor, cmd, transcript, &output) {
                return handled;
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
                    // Additionally record DECISIVENESS, which the latch above
                    // cannot express. A deadline firing after this point is a
                    // teardown overrun, not a failure to decide, so the
                    // timeout paths must neither emit `(:reason-unknown
                    // "timeout")` over the top of it nor exit non-zero.
                    if raw_output == "sat" || raw_output == "unsat" {
                        super::mark_decisive_verdict_printed();
                        // P4: what admitted an `unsat`, for a memout note
                        // that ends the run before the certificate line.
                        super::record_decisive_verdict_evidence((raw_output == "unsat").then(
                            || {
                                format!(
                                    "unsat_admission={} {}",
                                    executor
                                        .last_command_unsat_admission_tag()
                                        .unwrap_or("none-recorded"),
                                    unsat_evidence_fields(executor),
                                )
                            },
                        ));
                    }
                }
                // #model-owed: arm the debt the instant the `sat` becomes
                // observable. `-model` on the non-incremental file path does
                // NOT print the model here — it appends a literal
                // `(get-model)` that arrives as a later stream command — so
                // from this point until that command runs the process is
                // carrying a `sat` with no model. A cooperative timeout exit
                // taken inside that window publishes a Model-Validation ZERO
                // for a solve that already succeeded.
                if emitted_verdict
                    && raw_output == "sat"
                    && z3_model_enabled()
                    && !emit_z3_model_inline
                {
                    transcript.owes_model_emission = true;
                }
            }
            // (debt already cleared before the match — see the note there)
            // SMT-LIB compliance: emit reason-unknown to stderr when
            // check-sat produces "unknown", so users always know why.
            if raw_output == "unknown" {
                // Mark that "unknown" has been printed to prevent duplicate
                // output from exit_if_timed_out (#8674).
                super::VERDICT_PRINTED.store(true, std::sync::atomic::Ordering::SeqCst);
                // In z3 mode too: an `unknown` the memory budget caused ends
                // the run as a memout after this command.
                if z3_mode_enabled() {
                    super::latch_memout_if_over_budget();
                }
                // A breach the memory watchdog latched is reported as the
                // memout it is, right after this command
                // (`exit_if_memout_requested`), not as the `interrupted` the
                // stopped solve recorded.
                // Likewise a deadline: the run's exit gives the one canonical
                // timeout report (`exit_if_timed_out`), with its exit code.
                if z3_mode_enabled() {
                    // z3's transcript carries no reason line here.
                } else if super::latch_memout_if_over_budget() || super::run_deadline_passed() {
                    // When an earlier query's decisive answer stands, the
                    // run's exit writes only its "verdict stands" note, so
                    // the reason for THIS query's `unknown` is written here.
                    if let Some(line) = super::budget_reason_after_decisive_verdict() {
                        print_diagnostic_line(transcript, line);
                    }
                } else if let Some(reason) = executor.get_reason_unknown() {
                    print_diagnostic_line(transcript, &format!("(:reason-unknown {reason})"));
                } else {
                    print_diagnostic_line(transcript, "(:reason-unknown unknown)");
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
            restore_z3_session_after_reset(executor, transcript, cmd);
            if !z3_mode_enabled()
                || z3_command_implicitly_acknowledges_success(transcript.current_source.as_ref())
            {
                maybe_print_success(transcript);
            }
            true
        }
        Err(e) => {
            let message = e.to_string();
            let label_failure = z3_assertion_label_failure(executor, cmd);
            let rejection = is_decision_query
                .then(|| query_rejection(transcript, &message))
                .flatten();
            if is_decision_query {
                // The error's own reason, as the native API publishes it: a
                // theory mix with no combined decision procedure is a refusal
                // (`incomplete`), any other executor error `internal_error`.
                executor.replace_last_result_with_executor_error(&e);
                update_transcript_state_after_command(transcript, cmd);
                // Carry the underlying error text as the reason DETAIL. A bare
                // `(incomplete decision-execution-error)` cannot be told apart
                // from a crash, so "I have no decision procedure for this
                // fragment" and "I hit an internal defect" looked identical to
                // anyone driving AY as a z3 replacement. The class token stays
                // first so existing reason-classification keeps working.
                transcript.record_synthesized_unknown(format!(
                    "(incomplete decision-execution-error {})",
                    smt_quoted_reason_detail(&message)
                ));
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
                report_dropped_command_error(transcript, cmd, message);
                mark_problem_incomplete(executor, transcript);
                if is_decision_query && !print_synthesized_public_unknown(transcript) {
                    return false;
                }
                return !transcript.exit_on_error;
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
                if label_failure == Some(ay_frontend::LabelFailure::Exact) {
                    // z3 rejects this assertion at the same label, keeping
                    // the labels before it, which are bound here too.
                    let global = global_declarations_in_force(executor);
                    record_rejected_assertion(transcript, cmd, global);
                    note_z3_scope_command(transcript, cmd);
                } else if label_failure.is_some() {
                    // z3 keeps labels this session did not bind.
                    mark_problem_incomplete(executor, transcript);
                } else if command_contributes_to_problem(cmd)
                    && !matches!(cmd, Command::SetLogic(_))
                {
                    // A dropped `assert` is a monotone WEAKENING of the problem,
                    // so a later `unsat` on the remainder still refutes the
                    // whole. Anything else dropped here (a definition, a
                    // declaration, a stack op) changes what the surviving terms
                    // MEAN, and must keep the definitive-verdict block.
                    if matches!(cmd, Command::Assert(_)) {
                        mark_problem_incomplete_from_dropped_assertion(executor, transcript);
                    } else {
                        mark_problem_incomplete(executor, transcript);
                    }
                }
                if let Some(rejection) = rejection {
                    if !rejection.answered {
                        super::mark_verdict_printed();
                    } else if !print_synthesized_public_unknown(transcript) {
                        return false;
                    }
                    if rejection.withhold {
                        withhold_answers_out_of_step(executor, transcript);
                    }
                } else if is_decision_query && !print_synthesized_public_unknown(transcript) {
                    return false;
                }
                return !transcript.exit_on_error;
            }
            report_executor_failure(transcript, cmd, message);
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
    if let Some(interpolant) = constant_craig_interpolant(a, b) {
        return interpolant.to_string();
    }

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

/// Return the universally valid Craig interpolant for a constant-unsat side.
///
/// If `A` is false, `false` is an interpolant because `A => false` and
/// `false /\ B` is unsatisfiable. If `B` is false, `true` is an interpolant
/// because `A => true` and `true /\ B` is unsatisfiable. Check `A` first to
/// match Z3 5.0.0's `(get-interpolant false false)` result.
fn constant_craig_interpolant(a: &Term, b: &Term) -> Option<&'static str> {
    if matches!(a, Term::Const(Constant::False)) {
        Some("false")
    } else if matches!(b, Term::Const(Constant::False)) {
        Some("true")
    } else {
        None
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
    crate::hard_exit_statistics::note_printed();
    if stats_cfg.human {
        use std::io::IsTerminal;
        let dpll_stats = statistics_with_session_rlimit(executor, transcript);
        if stats_cfg.full {
            safe_eprintln!("{dpll_stats}");
        } else {
            let result_str = match transcript.public_verdict {
                Some(PublicVerdict::Sat) => "sat",
                Some(PublicVerdict::Unsat) => "unsat",
                Some(PublicVerdict::Unknown) | None => "unknown",
            };
            safe_eprintln!(
                "{}",
                stats_output::curated_smt_statistics(
                    &dpll_stats,
                    result_str,
                    super::global_elapsed(),
                    io::stderr().is_terminal(),
                )
            );
        }
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
        "model_validation.checked_projection_certificate",
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
    // The `c --- AY statistics ---` block restates a subset of the s-expression
    // block already printed above, under a second set of key spellings and with
    // a third copy of the build stamp. The s-expression block is the SMT idiom —
    // z3 prints one too — so SMT runs emit it alone; DIMACS and PB keep the
    // comment block as their native form.
    run_stats.emit(stats_output::StatsConfig {
        human: false,
        ..stats_cfg
    });
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

    /// The reason detail must stay one parseable SMT-LIB atom whatever the
    /// underlying error text looks like — a user of a Z3 replacement has to be
    /// able to tell "I do not support this" from "I crashed", and the class
    /// token in front of it keeps existing reason-classification working.
    #[test]
    fn reason_detail_quotes_and_bounds_the_underlying_error_text() {
        assert_eq!(
            smt_quoted_reason_detail("unsupported logic: AUFBVDTNIA"),
            "\"unsupported logic: AUFBVDTNIA\""
        );
        assert_eq!(
            smt_quoted_reason_detail("said \"no\"\nand stopped"),
            "\"said \"\"no\"\" and stopped\""
        );
        let long = smt_quoted_reason_detail(&"x".repeat(500));
        assert!(
            long.ends_with("...\""),
            "over-long detail is truncated: {long}"
        );
        assert!(
            long.chars().count() <= 210,
            "detail must stay bounded: {}",
            long.chars().count()
        );
    }

    #[test]
    fn mandatory_result_gates_disable_best_effort_proof_budget_and_ungated_routes() {
        let none = ResultGateRequests::default();
        assert!(should_budget_synthesized_proof(true, false, none));
        assert!(!should_budget_synthesized_proof(false, false, none));
        assert!(
            !should_budget_synthesized_proof(true, true, none),
            "an explicit artifact path makes publication mandatory"
        );
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
            assert!(!should_budget_synthesized_proof(true, false, gates));
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

    /// The in-script strict option holds a default-certificate UNSAT back
    /// exactly as the flag does: both spellings are one predicate. It read the
    /// flag alone, so with only the option a failed default publication
    /// printed `unsat` and then `unknown` for the same `check-sat`.
    #[test]
    fn the_in_script_strict_option_requires_default_certificate_publication() {
        let default =
            ProofConfig::new_default("/tmp/default.alethe".to_string(), ProofFormat::Alethe);
        assert_eq!(
            SmtUnsatProofPosture::of(Some(&default)),
            SmtUnsatProofPosture::DefaultCertificate
        );
        assert!(required_smt_unsat_publication(Some(&default), true));
        assert!(SmtUnsatProofPosture::DefaultCertificate.holds_unsat(true));

        let explicit = ProofConfig::from_path("/tmp/explicit.alethe".to_string());
        let enveloped = default
            .clone()
            .with_artifact_path(Some("/tmp/default.json".to_string()));
        for required in [&explicit, &enveloped] {
            assert_eq!(
                SmtUnsatProofPosture::of(Some(required)),
                SmtUnsatProofPosture::RequiredCertificate
            );
            assert!(required_smt_unsat_publication(Some(required), false));
        }

        assert_eq!(
            SmtUnsatProofPosture::of(None),
            SmtUnsatProofPosture::NoCertificate
        );
        assert!(!required_smt_unsat_publication(None, true));
    }

    /// The hold-back is decided per query, from the strict request in force
    /// when that query was answered, not latched before the script ran.
    #[test]
    fn a_query_answered_under_the_in_script_option_holds_its_unsat_back() {
        let mut transcript = SmtTranscriptState::new();
        transcript.unsat_proof_posture = SmtUnsatProofPosture::DefaultCertificate;
        transcript.query_script_strict = true;
        transcript.record_public_verdict(PublicVerdict::Unsat);
        assert!(transcript.query_strict_proofs_requested());
        let mut emitted = Vec::new();
        let result = publish_rendered_executor_output(
            &mut transcript,
            true,
            "unsat",
            "unsat".to_string(),
            None,
            |_, output| emitted.push(output.to_string()),
        );
        assert_eq!(result, Ok(false));
        assert!(emitted.is_empty(), "a held UNSAT leaked: {emitted:?}");
        assert_eq!(transcript.pending_unsat_output.as_deref(), Some("unsat"));

        // A later query starts from no strict request until it is answered.
        transcript.clear_public_result();
        assert!(!transcript.query_script_strict);
        assert!(transcript.pending_unsat_output.is_none());
    }

    /// Every `(error ...)` an executor response prints is recorded once,
    /// whether or not an arm rewords it; `echo` text never is.
    #[test]
    fn every_printed_executor_error_is_recorded_once() {
        let mut state = SmtTranscriptState::new();
        let unreworded = "(error \"objectives are not available\")";
        let rendered =
            z3_compat_output_for_command(&mut state, &Command::GetObjectives, unreworded);
        assert_eq!(rendered.as_deref(), Some(unreworded));
        assert!(state.had_recoverable_error && state.emitted_any_error);
        assert_eq!(state.recoverable_error_count, 1);

        // An arm that rewords and records its error is not counted twice.
        let rendered = z3_compat_output_for_command(
            &mut state,
            &Command::GetModel,
            "(error \"model is not available\")",
        );
        assert!(rendered.is_some_and(|text| text.contains("model is not available")));
        assert_eq!(state.recoverable_error_count, 2);

        let mut state = SmtTranscriptState::new();
        let echoed = "(error \"x\")";
        let rendered =
            z3_compat_output_for_command(&mut state, &Command::Echo(echoed.to_string()), echoed);
        assert_eq!(rendered.as_deref(), Some(echoed));
        assert!(!state.had_recoverable_error && !state.emitted_any_error);
    }

    /// A held UNSAT whose problem may carry no artifact (an earlier recoverable
    /// error) is settled by its posture, never left unprepared: that failed its
    /// publication with no response to the query.
    #[test]
    fn a_held_unsat_after_a_recoverable_error_gets_its_postures_answer() {
        let mut transcript = SmtTranscriptState::new();
        transcript.record_public_verdict(PublicVerdict::Unsat);
        transcript.note_recoverable_error();
        assert!(!transcript.public_unsat_artifacts_allowed());
        let default =
            ProofConfig::new_default("/tmp/default.alethe".to_string(), ProofFormat::Alethe);
        let explicit = ProofConfig::from_path("/tmp/explicit.alethe".to_string());

        // Not held: already on the regular channel, and no certificate is due.
        for proof in [&default, &explicit] {
            assert!(matches!(
                unsat_publication_without_artifact_authority(&transcript, proof),
                AletheProofPublication::Ready(None)
            ));
        }

        transcript.pending_unsat_output = Some("unsat".to_string());
        match unsat_publication_without_artifact_authority(&transcript, &default) {
            AletheProofPublication::RejectToUnknown { reason, diagnostic } => {
                assert_eq!(reason, "(incomplete proof-publication-failed)");
                assert!(diagnostic.contains("/tmp/default.alethe"), "{diagnostic}");
                assert!(diagnostic.contains("earlier in this problem failed"));
            }
            _ => panic!("a strict default certificate after an error must reject to unknown"),
        }
        match unsat_publication_without_artifact_authority(&transcript, &explicit) {
            AletheProofPublication::Fatal(error) => {
                assert!(error.starts_with("--proof requires /tmp/explicit.alethe"));
                assert!(error.contains("earlier in this problem failed"), "{error}");
            }
            _ => panic!("a required certificate after an error must fail the run"),
        }
        // The request is named with its own target, then the certificate.
        let enveloped = default
            .clone()
            .with_artifact_path(Some("/tmp/default.json".to_string()));
        match unsat_publication_without_artifact_authority(&transcript, &enveloped) {
            AletheProofPublication::Fatal(error) => assert!(
                error.starts_with(
                    "--proof-artifact /tmp/default.json requires the certificate /tmp/default.alethe"
                ),
                "{error}"
            ),
            _ => panic!("a required envelope after an error must fail the run"),
        }
    }

    #[test]
    fn z3_5_info_help_and_initial_statistics_have_the_pinned_shape() {
        let state = SmtTranscriptState::new();
        assert_eq!(
            z3_compat_get_info_output(&state, ":?", "unused"),
            Some(get_info_parameter_help().to_string())
        );
        assert_eq!(
            z3_compat_get_info_output(&state, ":rlimit", "unused"),
            Some("(:rlimit 0)".to_string())
        );
        assert_eq!(
            z3_compat_get_info_output(&state, ":all-statistics", "unused"),
            Some(
                "(:max-memory   0.00\n :memory       0.00\n :num-allocs   0\n :rlimit-count 0)"
                    .to_string()
            )
        );
    }

    #[test]
    fn z3_5_stateful_option_queries_use_bare_values() {
        let mut state = SmtTranscriptState::new();
        update_transcript_state_after_command(
            &mut state,
            &Command::SetOption(
                ":error-behavior".to_string(),
                SExpr::Symbol("immediate-exit".to_string()),
            ),
        );
        update_transcript_state_after_command(
            &mut state,
            &Command::SetOption(":int-real-coercions".to_string(), SExpr::False),
        );
        assert!(state.exit_on_error);
        assert_eq!(
            z3_compat_get_option_output(&state, ":error-behavior", "unused"),
            Some("immediate-exit".to_string())
        );
        assert_eq!(
            z3_compat_get_option_output(&state, ":int-real-coercions", "unused"),
            Some("false".to_string())
        );
        assert_eq!(
            z3_compat_get_info_output(&state, ":error-behavior", "unused"),
            Some("(:error-behavior immediate-exit)".to_string())
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
    fn z3_get_objectives_renderer_removes_only_executor_line_terminator() {
        assert_eq!(
            z3_compat_get_objectives_output("(objectives\n (x 2)\n)\n"),
            "(objectives\n (x 2)\n)"
        );
        assert_eq!(
            z3_compat_get_objectives_output("(objectives\n)\n\n"),
            "(objectives\n)\n"
        );
        assert_eq!(
            z3_compat_get_objectives_output("(error \"objectives are not available\")"),
            "(error \"objectives are not available\")"
        );
    }

    #[test]
    fn z3_get_consequences_renderer_uses_z3_5_transcript_grammar() {
        assert_eq!(
            z3_compat_get_consequences_output("(sat (a b))", false),
            "sat\n\n(=> true a)\n(=> true b)"
        );
        assert_eq!(
            z3_compat_get_consequences_output("(sat ((=> a b)))", true),
            "sat\n\n(=> a b)"
        );
        assert_eq!(
            z3_compat_get_consequences_output("(sat ())", false),
            "sat\n"
        );
        assert_eq!(
            z3_compat_get_consequences_output("(unsat ())", false),
            "unsat\n"
        );
        assert_eq!(
            z3_compat_get_consequences_output("(unknown ())", true),
            "unknown\n"
        );
    }

    #[test]
    fn z3_get_consequences_renderer_preserves_unexpected_internal_shapes() {
        for malformed in [
            "(error \"consequences are unavailable\")",
            "(sat a)",
            "(bogus ())",
            "(unsat (a))",
            "(sat (a)) trailing",
        ] {
            assert_eq!(
                z3_compat_get_consequences_output(malformed, false),
                malformed
            );
        }
        assert_eq!(
            z3_compat_get_consequences_output("(sat (a))", true),
            "(sat (a))",
            "assumption-bearing results must contain explicit implications"
        );
    }

    #[test]
    fn constant_craig_interpolants_match_z3_5() {
        let true_term = Term::Const(Constant::True);
        let false_term = Term::Const(Constant::False);

        assert_eq!(
            constant_craig_interpolant(&false_term, &true_term),
            Some("false")
        );
        assert_eq!(
            constant_craig_interpolant(&true_term, &false_term),
            Some("true")
        );
        assert_eq!(
            constant_craig_interpolant(&false_term, &false_term),
            Some("false"),
            "Z3 5.0.0 chooses false when both sides are false"
        );
        assert_eq!(constant_craig_interpolant(&true_term, &true_term), None);

        let symbol = Term::Symbol("a".to_string());
        let negated_symbol = Term::App("not".to_string(), vec![symbol.clone()]);
        assert_eq!(constant_craig_interpolant(&symbol, &negated_symbol), None);
    }

    #[test]
    fn z3_debug_mutators_omit_the_generic_print_success_acknowledgement() {
        let source = CommandSource {
            line: 1,
            column: 1,
            text: "; leading trivia\n(assert-not true)".to_string(),
        };
        assert!(!z3_command_implicitly_acknowledges_success(Some(&source)));

        let debug_set = CommandSource {
            line: 1,
            column: 1,
            text: "(dbg-set saved true)".to_string(),
        };
        assert!(!z3_command_implicitly_acknowledges_success(Some(
            &debug_set
        )));

        let ordinary_assert = CommandSource {
            line: 1,
            column: 1,
            text: "(assert true)".to_string(),
        };
        assert!(z3_command_implicitly_acknowledges_success(Some(
            &ordinary_assert
        )));
        assert!(z3_command_implicitly_acknowledges_success(None));
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
        assert!(parse_drop_contributes_to_problem("(assert-not ("));
        assert!(parse_drop_contributes_to_problem(
            "(get-info :version\n(assert false)"
        ));
        assert!(!parse_drop_contributes_to_problem(
            "; (assert false)\n(get-info :version)"
        ));
        assert!(parse_drop_contributes_to_problem(
            "(define-const c Int (x))"
        ));
        assert!(parse_drop_contributes_to_problem(
            "(set-option :global-declarations (x))"
        ));
        // Two forms: recovery skipped a command z3 may have run.
        assert!(parse_drop_contributes_to_problem(
            "(get-value ((x))) (check-sat)"
        ));
        assert!(!parse_drop_contributes_to_problem(
            "(get-value ((x))) ; (check-sat)"
        ));
    }

    #[test]
    fn a_dropped_query_withholds_later_answers() {
        assert!(dropped_text_holds_a_query("(check-sat-assuming (p) extra)"));
        assert!(dropped_text_holds_a_query("(check-sat-assuming p)"));
        assert!(dropped_text_holds_a_query("(check-sat extra)"));
        assert!(dropped_text_holds_a_query("(|check-sat-using| 1)"));
        assert!(dropped_text_holds_a_query("(get-value ((x))) (check-sat"));
        assert!(!dropped_text_holds_a_query("(echo \"(check-sat)\" x)"));
        assert!(!dropped_text_holds_a_query("(assert (p)) ; (check-sat)"));
    }

    #[test]
    fn a_quoted_keyword_is_the_command_it_names() {
        assert_eq!(command_source_keyword("(|pop| 1 extra)"), Some("pop"));
        assert_eq!(
            command_source_keyword("( |set-option|:x)"),
            Some("set-option")
        );
        assert_eq!(command_source_keyword("(|a\\|b| 1)"), Some("a\\|b"));
        assert_eq!(command_source_keyword("(|pop"), None);
        assert_eq!(command_source_keyword("(||)"), None);
        assert!(parse_drop_contributes_to_problem("(|pop| 1 extra)"));
        assert!(parse_drop_contributes_to_problem("(|assert| false extra)"));
        assert!(!parse_drop_contributes_to_problem("(|get-info| :x :y)"));
    }

    #[test]
    fn an_escaped_bar_does_not_end_a_quoted_symbol_in_dropped_text() {
        // Read with `\|` as the end of the symbol, the `(pop` would be inside
        // the next quoted symbol and missed.
        assert!(parse_drop_contributes_to_problem(
            "(get-info |a\\|) b|) (pop 1)"
        ));
        assert_eq!(
            collect_command_sources("(get-info |a\\|) (b|) (pop 1)").len(),
            2
        );
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
    fn z3_reason_unknown_doubles_quotes_of_an_error_detail() {
        assert_eq!(
            z3_reason_unknown_output("(incomplete decision-execution-error \"no lane\")"),
            "(:reason-unknown \"(incomplete decision-execution-error \"\"no lane\"\")\")"
        );
        assert_eq!(
            z3_reason_unknown_output("\"internal solver error\""),
            "(:reason-unknown \"(incomplete internal solver error)\")"
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
        let reserved_path = reserved.path().to_path_buf();
        assert_ne!(reserved_path, planted);
        assert!(planted.is_symlink());
        assert_eq!(
            std::fs::read_to_string(&victim).expect("read victim"),
            "do not truncate"
        );
        drop(reserved);
        assert!(
            !reserved_path.exists(),
            "an uncommitted reservation unlinks its temporary file"
        );
    }

    /// Names of the unpublished artifact reservations sitting in `dir`.
    fn artifact_temp_debris(dir: &std::path::Path) -> Vec<String> {
        std::fs::read_dir(dir)
            .expect("read artifact directory")
            .map(|entry| entry.expect("read artifact directory entry").file_name())
            .filter_map(|name| name.to_str().map(str::to_owned))
            .filter(|name| name.contains(".tmp-"))
            .collect()
    }

    /// The defect this guard exists for: an emission that stops mid-document
    /// must leave NOTHING beside the user's input.
    ///
    /// Measured before the fix, on QF_UF `iso_brn492` with the synthesized
    /// default certificate: each `--rigor standard` run left a
    /// `.iso_brn492.smt2.alethe.tmp-<pid>-0` of 29,182,083 bytes, and three
    /// runs left three. That is what this pins, at the exact seam that leaked:
    /// the temp file is unlinked, AND the descriptor is left empty rather than
    /// re-inflated by `BufWriter::drop` flushing its tail past the truncation
    /// point (which is what made the "invalidated" partial 29 MB, not 0).
    #[test]
    fn abandoned_alethe_emission_leaves_no_partial_and_empties_the_inode() {
        let temp = tempfile::tempdir().expect("temporary directory");
        let target = temp.path().join("input.smt2.alethe");
        let (_resolved_target, reservation, file) =
            create_artifact_temp_file(&target).expect("reserve a temporary proof file");
        let reserved_path = reservation.path().to_path_buf();

        // Render more than the writer's buffer, exactly as a budget-exhausting
        // emission does: most of the partial has reached the file, the tail is
        // still buffered.
        let mut writer = ProofDigestWriter::with_self_check(
            BufWriter::with_capacity(1 << 20, file),
            None,
            ay_proof::AletheDialect::default(),
        );
        let chunk = vec![b'x'; 1 << 20];
        for _ in 0..4 {
            writer.write_all(&chunk).expect("render partial proof text");
        }
        writer
            .write_all(b"(step t1 (cl) :rule hole)")
            .expect("leave a tail in the writer buffer");
        assert!(
            std::fs::metadata(&reserved_path)
                .expect("stat the partial")
                .len()
                > 0,
            "the fixture must actually produce a partial on disk"
        );

        let _error = alethe_error_after_abandoning_buffer(
            ay_proof::AletheStreamError::Print(
                ay_proof::AlethePrintError::UnavailableAuthenticatedSurface {
                    reason: "emission work budget exhausted",
                },
            ),
            writer,
        );
        assert_eq!(
            std::fs::metadata(&reserved_path)
                .expect("stat the abandoned partial")
                .len(),
            0,
            "the abandoned descriptor still holds proof text: the discarded buffer must not be flushed back past the invalidation"
        );

        drop(reservation);
        assert!(
            !reserved_path.exists(),
            "an abandoned emission left a partial at {}",
            reserved_path.display()
        );
        assert!(!target.exists(), "an abandoned emission published a proof");
        assert!(
            artifact_temp_debris(temp.path()).is_empty(),
            "abandoned emission debris: {:?}",
            artifact_temp_debris(temp.path())
        );
    }

    /// `--proof-self-check` reads the document in the dialect the executor
    /// renders it in (`--alethe-dialect`): a Clean document may name Clean's
    /// `dt_project`, and a pinned-Carcara document naming it is refused as
    /// `unknown-rule`, as pinned Carcara refuses it (it voids the document).
    ///
    /// The pinned printer never writes `dt_project`, so no CLI run can show
    /// the pinned half; this pins it at the writer `write_alethe_proof`
    /// streams through, built from the executor exactly as there.
    #[test]
    fn proof_self_check_reads_the_document_in_the_executor_dialect() {
        use std::io::Write as _;
        let scope = ay_proof::ProblemScope::from_smtlib_source(
            "(declare-datatypes ((Pair 0)) (((mk (fst Int) (snd Int)))))\n\
             (declare-const a Int)\n(declare-const b Int)\n",
        );
        let document = "(assume t0 (not (= (fst (mk a b)) a)))\n\
                        (step t1 (cl (= (fst (mk a b)) a)) :rule dt_project)\n\
                        (step t2 (cl) :rule resolution :premises (t0 t1))\n";
        let verdict = |mut writer: ProofDigestWriter<Vec<u8>>| {
            writer
                .write_all(document.as_bytes())
                .expect("stream the document");
            let verdict = writer
                .take_self_check_verdict()
                .expect("the self-check is enabled");
            assert_eq!(
                writer.into_inner(),
                document.as_bytes(),
                "the bytes pass through"
            );
            verdict
        };
        for dialect in [
            ay_proof::AletheDialect::Clean,
            ay_proof::AletheDialect::PinnedCarcara,
        ] {
            let mut executor = Executor::new();
            executor.set_alethe_dialect(dialect);
            for (how, writer) in [
                (
                    "with_self_check",
                    ProofDigestWriter::with_self_check(Vec::new(), Some(scope.clone()), dialect),
                ),
                (
                    "for_executor",
                    ProofDigestWriter::for_executor(Vec::new(), Some(scope.clone()), &executor),
                ),
            ] {
                match (dialect, verdict(writer)) {
                    (ay_proof::AletheDialect::Clean, Ok(report)) => assert_eq!(report.steps, 2),
                    (
                        ay_proof::AletheDialect::PinnedCarcara,
                        Err(ay_proof::AletheDefect::UnknownRule { rule, .. }),
                    ) => assert_eq!(rule, "dt_project", "{how}"),
                    (dialect, other) => panic!("{how} in {dialect:?}: {other:?}"),
                }
            }
        }
    }

    /// A no-replace publication that loses to a pre-existing artifact is the
    /// path a corpus scan takes on its SECOND pass over the same directory. It
    /// must leave the existing file untouched AND leave no reservation behind,
    /// or the scan strands one partial per instance per pass.
    #[test]
    fn noreplace_publication_failure_leaves_no_artifact_debris() {
        let temp = tempfile::tempdir().expect("temporary directory");
        let target = temp.path().join("input.smt2.alethe");
        std::fs::write(&target, "pre-existing certificate").expect("plant the earlier artifact");

        let error = write_artifact_noreplace_retained(&target, |file| {
            file.write_all(b"a second run's certificate")
        })
        .expect_err("publication must not replace an existing artifact");
        assert_eq!(error.kind(), io::ErrorKind::AlreadyExists);
        assert_eq!(
            std::fs::read_to_string(&target).expect("read the preserved artifact"),
            "pre-existing certificate"
        );
        assert!(
            artifact_temp_debris(temp.path()).is_empty(),
            "a lost publication left debris: {:?}",
            artifact_temp_debris(temp.path())
        );
    }

    /// A writer that fails part-way is the same abandonment, one layer up.
    #[test]
    fn failed_artifact_write_leaves_no_artifact_debris() {
        let temp = tempfile::tempdir().expect("temporary directory");
        let target = temp.path().join("firewall_0.lean");

        let error = write_artifact_atomically(&target, |file| {
            file.write_all(b"a partial lemma")?;
            Err(io::Error::other("rendering gave up"))
        })
        .expect_err("the write failure must propagate");
        assert_eq!(error.to_string(), "rendering gave up");
        assert!(!target.exists(), "a failed write published an artifact");
        assert!(
            artifact_temp_debris(temp.path()).is_empty(),
            "a failed write left debris: {:?}",
            artifact_temp_debris(temp.path())
        );
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
        let (resolved_target, mut reservation, mut file) =
            create_artifact_temp_file(&target).expect("reserve in resolved parent");
        file.write_all(b"proof").unwrap();
        file.sync_all().unwrap();
        drop(file);

        std::fs::remove_file(&alias).unwrap();
        symlink(&second, &alias).unwrap();
        publish_artifact_temp(reservation.path(), &resolved_target)
            .expect("publish to original parent");
        reservation.commit();

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
    fn capture(metadata: &std::fs::Metadata, source: SmtFileRef<'_>) -> io::Result<Self> {
        #[cfg(unix)]
        {
            use std::os::unix::fs::MetadataExt as _;
            Ok(Self {
                identity: SmtFileIdentity::resolve(source),
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
                identity: SmtFileIdentity::resolve(source),
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
        let state = match PublicationFileState::capture(&metadata, SmtFileRef::Handle(&file)) {
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
        let descriptor_state =
            PublicationFileState::capture(&descriptor_metadata, SmtFileRef::Handle(&self.file))?;
        let path_state =
            PublicationFileState::capture(&path_metadata, SmtFileRef::PathNoFollow(&self.path))?;
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
        "--emit-firewall-lean requested artifacts, but no derivation was retained for this UNSAT"
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

// `ay_sys::fs::rename_noreplace` is implemented for Windows too (MoveFileExW
// without MOVEFILE_REPLACE_EXISTING, the counterpart of Linux
// renameat2(RENAME_NOREPLACE) and macOS renamex_np(RENAME_EXCL)), so artifact
// publication no longer has to fail closed there.
#[cfg(any(target_os = "linux", target_os = "macos", windows))]
fn rename_path_noreplace(source: &std::path::Path, target: &std::path::Path) -> io::Result<()> {
    ay_sys::fs::rename_noreplace(source, target)
}

#[cfg(not(any(target_os = "linux", target_os = "macos", windows)))]
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

/// Owns a reserved artifact temporary path until it is published.
///
/// The reservation lives NEXT TO the caller's own file — `--proof FILE` writes
/// `.FILE.tmp-<pid>-<nonce>` in FILE's directory, and the synthesized default
/// certificate writes `.<input>.alethe.tmp-<pid>-<nonce>` beside the SMT-LIB
/// input. So every path out of an artifact write that does NOT end in the
/// temp -> target rename must unlink the reservation: an error return, an early
/// exit, and above all the *successful-verdict* abandonment where rendering
/// stops mid-document (the synthesized-default Alethe emission work budget of
/// `DEFAULT_ALETHE_EMISSION_WORK_BUDGET`), which is not an error anywhere in
/// this program and therefore had no cleanup at all.
///
/// A partial left behind is not merely untidy. It is a dotfile a plain `ls`
/// does not show, it is written into a directory the user only asked AY to
/// READ, and — because publication is deliberately no-replace — an artifact
/// sitting next to an input makes the NEXT run over that directory fail to
/// publish ("File exists"), so a leak silently under-reports evidence on every
/// later measurement of the same corpus. Measured before this guard existed:
/// three `--rigor standard` runs of one budget-exhausting QF_UF instance left
/// three 29,182,083-byte partials, and a scan of this repository on 2026-09-06
/// found 145 stranded ones (129 of them inside `benchmarks/`, 353 MB apparent).
///
/// Drop-order note for buffered writers: declare the reservation BEFORE the
/// writer that borrows its file, so the writer is dropped (and its buffered
/// tail flushed, or discarded) before the unlink runs.
struct ArtifactTempReservation {
    path: std::path::PathBuf,
    /// Cleared by [`Self::commit`] once the temp file has been published under
    /// its target name and the temp path is therefore gone.
    armed: bool,
}

impl ArtifactTempReservation {
    fn new(path: std::path::PathBuf) -> Self {
        register_live_artifact_temp_path(&path);
        Self { path, armed: true }
    }

    fn path(&self) -> &std::path::Path {
        &self.path
    }

    /// Disarm: the reservation was published (renamed onto the target), so the
    /// temp name no longer exists and must not be unlinked by anyone else.
    fn commit(&mut self) {
        self.armed = false;
        unregister_live_artifact_temp_path(&self.path);
    }
}

impl Drop for ArtifactTempReservation {
    fn drop(&mut self) {
        if self.armed {
            let _ = std::fs::remove_file(&self.path);
            unregister_live_artifact_temp_path(&self.path);
        }
    }
}

/// Reserved-but-unpublished artifact temporary paths, for the exit that runs
/// no destructor.
///
/// [`ArtifactTempReservation`] covers every Rust control-flow exit from a proof
/// write, but not `process::exit`, which is how AY ends a timeout, a SIGTERM
/// wind-down, a memory abort and a fatal CLI error — and a timeout landing
/// DURING emission is not hypothetical here: the emission work budget exists
/// precisely because some certificates rendered for 300s+ after the verdict.
/// This mirrors what the DIMACS proof registry already does for its
/// `.ay-dimacs-proof-<pid>-<nonce>.stage` siblings (`arm_abandoned_dimacs_proof_sweep`)
/// and what `ay-pb` does for `PROOFFILE.tmp-*` under its SIGTERM watchdog.
/// A SIGKILL still strands the file; nothing in the process can prevent that.
static LIVE_ARTIFACT_TEMP_PATHS: std::sync::Mutex<Vec<std::path::PathBuf>> =
    std::sync::Mutex::new(Vec::new());

/// Infix every temporary name reserved by THIS process carries. `ay` supervises
/// each solve behind a `fork()`, so a child inherits a copy of the list above;
/// only the process whose PID names the file may unlink it.
fn artifact_temp_owner_infix() -> String {
    format!(".tmp-{}-", std::process::id())
}

fn register_live_artifact_temp_path(path: &std::path::Path) {
    arm_artifact_temp_sweep();
    LIVE_ARTIFACT_TEMP_PATHS
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner)
        .push(path.to_path_buf());
}

fn unregister_live_artifact_temp_path(path: &std::path::Path) {
    LIVE_ARTIFACT_TEMP_PATHS
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner)
        .retain(|registered| registered != path);
}

/// Arm the process-exit sweep, lazily: a run that never reserves an artifact
/// pays nothing.
fn arm_artifact_temp_sweep() {
    static ARMED: std::sync::OnceLock<()> = std::sync::OnceLock::new();
    ARMED.get_or_init(|| {
        if !ay_sys::at_process_exit(sweep_live_artifact_temp_paths) {
            safe_eprintln!(
                "c Warning: could not arm the artifact staging sweep; an abnormal exit will strand its temporary file"
            );
        }
    });
}

extern "C" fn sweep_live_artifact_temp_paths() {
    // `try_lock`, never `lock`: the exiting thread may already hold this lock,
    // and hanging the process at exit is far worse than stranding one file.
    let Ok(paths) = LIVE_ARTIFACT_TEMP_PATHS.try_lock() else {
        return;
    };
    let owner = artifact_temp_owner_infix();
    for path in paths.iter() {
        let owned_by_this_process = path
            .file_name()
            .and_then(std::ffi::OsStr::to_str)
            .is_some_and(|name| name.contains(&owner));
        if owned_by_this_process {
            let _ = std::fs::remove_file(path);
        }
    }
}

fn create_artifact_temp_file_from_nonce(
    target: &std::path::Path,
    process_id: u32,
    first_nonce: u64,
) -> io::Result<(ArtifactTempReservation, std::fs::File)> {
    for offset in 0..ARTIFACT_TEMP_CREATE_ATTEMPTS {
        let candidate =
            artifact_temp_candidate(target, process_id, first_nonce.wrapping_add(offset))?;
        match std::fs::OpenOptions::new()
            .read(true)
            .write(true)
            .create_new(true)
            .open(&candidate)
        {
            Ok(file) => return Ok((ArtifactTempReservation::new(candidate), file)),
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
) -> io::Result<(std::path::PathBuf, ArtifactTempReservation, std::fs::File)> {
    use std::sync::atomic::Ordering;

    let resolved_target = resolve_artifact_target(target)?;
    let first_nonce =
        ARTIFACT_TEMP_NONCE.fetch_add(ARTIFACT_TEMP_CREATE_ATTEMPTS, Ordering::Relaxed);
    let (reservation, file) =
        create_artifact_temp_file_from_nonce(&resolved_target, std::process::id(), first_nonce)?;
    Ok((resolved_target, reservation, file))
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
    let (resolved_target, mut reservation, mut file) = create_artifact_temp_file(target)?;
    let write_result = write(&mut file).and_then(|()| file.sync_all());
    let result = write_result.and_then(|()| publish(reservation.path(), &resolved_target));
    if let Err(error) = result {
        // `reservation` is still armed on this early return, so its `Drop`
        // unlinks the unpublished temp file on the way out.
        let invalidation = invalidate_retained_artifact(&file);
        return Err(match invalidation {
            Ok(()) => error,
            Err(invalidation) => io::Error::other(format!(
                "{error}; invalidating the retained artifact descriptor also failed: {invalidation}"
            )),
        });
    }
    reservation.commit();
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
    /// Round-trip document self-check, fed the identical byte stream.
    ///
    /// AY has never read an Alethe file back: `check_proof_partial` validates
    /// the in-memory IR while Carcara validates this text, and a measured 50
    /// of 50 Carcara-invalid certificates passed the IR gate. Teeing the
    /// stream is the only hook that does not undo the streaming exporter's
    /// peak-RSS fix — the largest certificate in the corpus is 687 MB.
    self_check: Option<ay_proof::AletheDocumentChecker>,
    self_check_defect: Option<ay_proof::AletheDefect>,
}

impl<W> ProofDigestWriter<W> {
    /// The writer `write_alethe_proof` streams `executor`'s document through:
    /// the round-trip check reads it in the dialect the executor renders it
    /// in (`--alethe-dialect`).
    fn for_executor(inner: W, scope: Option<ay_proof::ProblemScope>, executor: &Executor) -> Self {
        Self::with_self_check(inner, scope, executor.alethe_dialect())
    }

    /// `dialect` is the one the document is rendered in: its checker fixes
    /// the rule vocabulary the round-trip check accepts (`dt_project` only in
    /// [`ay_proof::AletheDialect::Clean`]).
    fn with_self_check(
        inner: W,
        scope: Option<ay_proof::ProblemScope>,
        dialect: ay_proof::AletheDialect,
    ) -> Self {
        Self {
            inner,
            hasher: Sha256::new(),
            self_check: scope
                .map(|scope| ay_proof::AletheDocumentChecker::new(scope).with_dialect(dialect)),
            self_check_defect: None,
        }
    }

    fn inner(&self) -> &W {
        &self.inner
    }

    fn digest(&self) -> DigestBytes {
        self.hasher.clone().finalize().into()
    }

    /// Conclude the round-trip check. `None` when it was never enabled.
    fn take_self_check_verdict(
        &mut self,
    ) -> Option<Result<ay_proof::AletheDocumentReport, ay_proof::AletheDefect>> {
        if let Some(defect) = self.self_check_defect.take() {
            self.self_check = None;
            return Some(Err(defect));
        }
        self.self_check
            .take()
            .map(ay_proof::AletheDocumentChecker::finish)
    }

    fn into_inner(self) -> W {
        self.inner
    }
}

impl<W: Write> Write for ProofDigestWriter<W> {
    fn write(&mut self, bytes: &[u8]) -> io::Result<usize> {
        let written = self.inner.write(bytes)?;
        self.hasher.update(&bytes[..written]);
        if self.self_check_defect.is_none() {
            if let Some(checker) = self.self_check.as_mut() {
                if let Err(defect) = checker.push_bytes(&bytes[..written]) {
                    self.self_check_defect = Some(defect);
                }
            }
        }
        Ok(written)
    }

    fn flush(&mut self) -> io::Result<()> {
        self.inner.flush()
    }
}

/// How hard the Alethe round-trip self-check pushes back.
#[derive(Clone, Copy, PartialEq, Eq)]
enum ProofSelfCheckMode {
    /// Do not run it (the default — see [`proof_self_check_mode`]).
    Off,
    /// Run it and print `c warning:` on a defect; still publish the proof.
    Warn,
    /// Run it and REFUSE to publish a defective document.
    Strict,
}

/// Read the self-check gate. **Default OFF.**
///
/// Why off: this check is new and its false-reject rate is measured over a
/// benchmark corpus, not proved. Turning it on by default would put an
/// unproven gate in front of a verdict AY has already printed, and it costs a
/// per-byte parse over documents that reach 687 MB. `--proof-self-check`
/// enables the warning form, `=strict` the refusing form. Both are opt-in, so
/// the competition path is byte-for-byte unchanged.
fn proof_self_check_mode() -> ProofSelfCheckMode {
    // B41: `--proof-self-check 1|2` (warn | strict); unset = off.
    match ay_core::misc_cli_flags().proof_self_check {
        Some(1) => ProofSelfCheckMode::Warn,
        Some(2) => ProofSelfCheckMode::Strict,
        _ => ProofSelfCheckMode::Off,
    }
}

/// Build the scope the round-trip check resolves symbols against.
///
/// Prefers the problem's real declarations (they include sorts, and they are
/// exactly what Carcara resolves against); falls back to the exporter's own
/// notion of problem scope when the problem is not readable as text.
fn proof_self_check_scope(
    executor: &Executor,
    problem: ProofArtifactProblem<'_>,
) -> ay_proof::ProblemScope {
    let from_disk = match problem {
        ProofArtifactProblem::Text(text) => Some(ay_proof::ProblemScope::from_smtlib_source(text)),
        ProofArtifactProblem::AuthenticatedFilePath { path, .. } => std::fs::read_to_string(path)
            .ok()
            .map(|text| ay_proof::ProblemScope::from_smtlib_source(&text)),
        ProofArtifactProblem::Unavailable(_) => None,
    };
    from_disk.unwrap_or_else(|| {
        ay_proof::ProblemScope::from_symbols(executor.proof_export_problem_symbol_names())
    })
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

/// The publication of an UNSAT that stands while its problem may carry no
/// artifact: an `(error ...)` earlier in this problem (until `(reset)`), or a
/// dropped assertion, and no certificate may embed source that failed
/// continued execution (`public_unsat_artifacts_allowed`).
///
/// An UNSAT that was not held back needs no certificate: it is already on the
/// regular channel and the run writes none. One held back for its certificate
/// (`holds_unsat_publication`) gets the answer its posture gives any
/// certificate that cannot be published, as an I/O failure does
/// (`write_alethe_proof`): under strict proofs, in either spelling, this
/// query's one response is `unknown` and the run goes on; a required
/// certificate (`--proof`, `--proof-artifact`, `--emit-firewall-lean`) fails
/// the run loudly, naming the cause. Measured before this: the held UNSAT
/// reached publication with no transaction prepared, and every such run exited
/// 1 with no response to this `check-sat` and none to the rest of the script
/// ("SMT UNSAT artifacts were not prepared before publication"), under the
/// flag on main aba6406be and under the in-script option once it held its
/// UNSAT back too.
fn unsat_publication_without_artifact_authority(
    transcript: &SmtTranscriptState,
    proof_config: &ProofConfig,
) -> AletheProofPublication {
    if transcript.pending_unsat_output.is_none() {
        return AletheProofPublication::Ready(None);
    }
    let cause = "a command earlier in this problem failed, and no certificate may embed source that failed continued execution";
    match SmtUnsatProofPosture::of(Some(proof_config)) {
        SmtUnsatProofPosture::DefaultCertificate => AletheProofPublication::RejectToUnknown {
            reason: "(incomplete proof-publication-failed)".to_string(),
            diagnostic: format!(
                "strict proof mode rejected UNSAT because {} cannot be published: {cause}",
                proof_config.path
            ),
        },
        SmtUnsatProofPosture::RequiredCertificate | SmtUnsatProofPosture::NoCertificate => {
            AletheProofPublication::Fatal(format!(
                "{}, but it cannot be published: {cause}",
                required_certificate_request(proof_config)
            ))
        }
    }
}

/// Whether the default certificate could not be published because this run
/// already wrote `<input>.alethe` for an earlier query. A run publishes one
/// default certificate and never replaces a file, so the second query finds
/// its own run's file there; calling it a stale file from an earlier run, as
/// the generic message does, sent a reader looking for the wrong file.
fn default_certificate_taken_by_this_run(
    transcript: &SmtTranscriptState,
    proof_config: &ProofConfig,
    error: &io::Error,
) -> bool {
    proof_config.synthesized_default
        && error.kind() == io::ErrorKind::AlreadyExists
        && transcript.default_certificate_created.get()
}

/// The command-line request that makes `proof_config`'s certificate required,
/// with that request's own target and the certificate it requires. Naming the
/// certificate alone read as if `--proof-artifact` or `--emit-firewall-lean`
/// had asked for the default `<input>.alethe` by name.
fn required_certificate_request(proof_config: &ProofConfig) -> String {
    let certificate = &proof_config.path;
    if let Some(dir) = crate::FIREWALL_LEAN_DIR.get() {
        format!(
            "--emit-firewall-lean {} requires the certificate {certificate}",
            dir.display()
        )
    } else if let Some(artifact) = proof_config.artifact_path.as_deref() {
        format!("--proof-artifact {artifact} requires the certificate {certificate}")
    } else {
        format!("--proof requires {certificate}")
    }
}

fn write_alethe_proof(
    executor: &Executor,
    transcript: &SmtTranscriptState,
    proof_config: &ProofConfig,
    problem: ProofArtifactProblem<'_>,
    theory: ProofArtifactTheoryMetadata,
) -> AletheProofPublication {
    if !transcript.public_unsat_artifacts_allowed() {
        return unsat_publication_without_artifact_authority(transcript, proof_config);
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
    // Strict in either spelling, as requested when this query was answered
    // (`holds_unsat_publication`): the ONE value every strict gate of this
    // publication reads. The executor's live option may have changed since
    // (an option set after the `check-sat` applies to later queries only), so
    // none of them re-reads it here.
    let query_strict = transcript.query_strict_proofs_requested();
    // #8759: In strict-proof mode, suppress proof file writing when the
    // terminal derivation rides on a trust fallback. The CLI has already
    // printed `unknown` + `(:reason-unknown (incomplete proof-trusted))`;
    // emitting a trust-tainted "UNSAT proof" would contradict that verdict.
    if strict_derivation_screen_refuses(query_strict, executor) {
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
    let strict_default = default_only && query_strict;
    let optional_default = default_only && !strict_default;
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
        // #evidence-stage-3. Attribute BEFORE the posture split, so the record
        // is the same event whether the verdict publishes or downgrades — the
        // refusal is identical either way, exactly as `disclose_refused_artifact`
        // already argues for its own line.
        disclose_proof_decline_with_fallback(
            executor,
            &proof_config.path,
            DeclinePrecedence::AssemblyOutranksRender,
            || ProofDeclineMechanism::NoDerivationRecorded,
        );
        disclose_unsat_corroboration(executor);
        if optional_default {
            // Name the authority even here — ESPECIALLY here. A published UNSAT
            // with no artifact at all used to disclose nothing about what backs
            // it, which is the worst place for the record to go quiet: measured
            // 2026-09-06, 2 of the 10 `--self-check` UNSATs in a seeded 60-file
            // sweep landed on this branch, each certified by an independent lane
            // that no line of output named.
            // CORRECTED at #evidence-stage-3. This used to read "UNSAT produced
            // no reconstructable proof", and that sentence is FALSE for both of
            // the lanes that dominate this branch. On the closed-sentence
            // semantic-certificate lane a checked derivation is computed and
            // then discarded, because the certificate family has no
            // authored-scope Alethe presentation. On the quantifier firewall a
            // complete `CheckedSatRefutation` is minted and then DELETED,
            // because one leaf names a solver-invented constant. In both, a
            // refutation was produced; what is missing is a renderable
            // authored-scope form of it. Saying "no reconstructable proof" told
            // a reader the search came up empty, which is the opposite of the
            // truth and the wrong repair to go looking for.
            //
            // CORRECTED AGAIN 2026-09-11 (#semantic-token census): for the
            // closed-sentence lane "a checked derivation is computed and then
            // discarded" is itself too generous. Measured at the mint on 23 of
            // 23 files at two fresh seeds, the token holds leaf obligations
            // over a term-construction residue of the authored assertion, and
            // no derivation from the authored text ever existed in AY. The
            // `ay.proof.semantic-token` line beside the decline says exactly
            // what was held.
            //
            // The honest claim is narrow: no derivation was RETAINED for this
            // artifact. Which machinery let go of it is on the
            // `ay.proof.decline` line printed immediately above.
            // #certify-before-presentation: here a derivation WAS retained and
            // went to certification; only its authored-surface document was
            // withheld by the bound the decline line names. Saying "no
            // derivation was retained" would understate what was checked.
            let why = if executor.last_unsat_document_withheld_by().is_some() {
                "a derivation was retained and handed to certification, but its authored-surface document was withheld by the presentation bound the ay.proof.decline line above names, so no file is written for an external checker"
            } else {
                "no derivation was retained for this UNSAT; the ay.proof.decline line above names which machinery let go of it — for several lanes a checked refutation existed and had no renderable authored-scope form"
            };
            safe_eprintln!(
                "c warning: no proof certificate emitted ({why}); the verdict was admitted by unsat_admission={} {}; pass --strict-proofs to require a certificate instead",
                executor
                    .last_command_unsat_admission_tag()
                    .unwrap_or("none-recorded"),
                unsat_evidence_fields(executor),
            );
            return AletheProofPublication::Ready(None);
        }
        if strict_default {
            return AletheProofPublication::RejectToUnknown {
                reason: "(incomplete proof-unavailable)".to_string(),
                diagnostic: format!(
                    "strict proof mode rejected UNSAT because no derivation was retained for {}",
                    proof_config.path
                ),
            };
        }
        return AletheProofPublication::Fatal(format!(
            "{}, but no derivation was retained for this UNSAT",
            required_certificate_request(proof_config)
        ));
    }
    let target_path = std::path::Path::new(&proof_config.path);
    let self_check_mode = proof_self_check_mode();
    let self_check_scope = match self_check_mode {
        ProofSelfCheckMode::Off => None,
        ProofSelfCheckMode::Warn | ProofSelfCheckMode::Strict => {
            Some(proof_self_check_scope(executor, problem))
        }
    };
    let mut self_check_verdict = None;
    let mut carcara_surface = None;
    let stream_result = match create_artifact_temp_file(target_path) {
        Ok((resolved_target, mut reservation, file)) => {
            let mut writer = ProofDigestWriter::for_executor(
                BufWriter::with_capacity(1 << 20, file),
                self_check_scope,
                executor,
            );
            // The surface verdict describes exactly these bytes: the export
            // captures their dialect report around this render. A step whose
            // authored spelling no certified bridge relates to the checked
            // internal step prints as the honest `hole` over its clause
            // (counted in `unproved_steps`; strict rigor withholds the
            // verdict) instead of refusing the document, which cost an
            // explicit `--proof FILE` its `unsat` (#8821;
            // `ay_proof::with_refused_surface_steps_declined_to_hole`).
            let render = ay_proof::with_refused_surface_steps_declined_to_hole(|| {
                executor.try_export_last_proof_alethe_for_problem_scope_to_with_carcara_surface(
                    &mut writer,
                )
            })
            .map(|streamed| {
                streamed.map(|surface| {
                    carcara_surface = Some(surface);
                })
            });
            match render {
                Some(Ok(())) => {
                    use std::io::Write as _;
                    let flush_result = writer
                        .flush()
                        .and_then(|()| writer.inner().get_ref().sync_all())
                        .map_err(ay_proof::AletheStreamError::Io);
                    let proof_digest = writer.digest();
                    self_check_verdict = writer.take_self_check_verdict();
                    // In strict self-check mode a document-layer defect must
                    // stop publication, exactly like an unrenderable step:
                    // the temp file is invalidated and the target pathname is
                    // never created.
                    let flush_result = flush_result.and_then(|()| {
                        match (self_check_mode, self_check_verdict.as_ref()) {
                            (ProofSelfCheckMode::Strict, Some(Err(defect))) => {
                                Err(ay_proof::AletheStreamError::Io(io::Error::new(
                                    io::ErrorKind::InvalidData,
                                    format!(
                                        "Alethe round-trip self-check rejected the emitted document [{}]: {defect}",
                                        defect.tag()
                                    ),
                                )))
                            }
                            _ => Ok(()),
                        }
                    });
                    match flush_result {
                        Ok(()) => match writer.into_inner().into_inner() {
                            Ok(file) => {
                                match publish_artifact_temp_noreplace(
                                    reservation.path(),
                                    &resolved_target,
                                ) {
                                    Ok(()) => {
                                        // Published: the temp name is gone, so
                                        // the reservation must not unlink it.
                                        reservation.commit();
                                        if proof_config.synthesized_default {
                                            transcript.default_certificate_created.set(true);
                                        }
                                        Ok((proof_digest, file, resolved_target))
                                    }
                                    Err(error) => Err(alethe_error_after_invalidation(
                                        ay_proof::AletheStreamError::Io(error),
                                        &file,
                                    )),
                                }
                            }
                            Err(error) => {
                                let primary =
                                    io::Error::new(error.error().kind(), error.error().to_string());
                                let (file, _discarded) = error.into_inner().into_parts();
                                Err(alethe_error_after_invalidation(
                                    ay_proof::AletheStreamError::Io(primary),
                                    &file,
                                ))
                            }
                        },
                        Err(error) => Err(alethe_error_after_abandoning_buffer(error, writer)),
                    }
                }
                Some(Err(error)) => Err(alethe_error_after_abandoning_buffer(error, writer)),
                None => Err(alethe_error_after_abandoning_buffer(
                    ay_proof::AletheStreamError::Print(
                        ay_proof::AlethePrintError::UnavailableAuthenticatedSurface {
                            reason: "proof export returned no artifact despite a retained proof",
                        },
                    ),
                    writer,
                )),
            }
        }
        Err(error) => Err(ay_proof::AletheStreamError::Io(error)),
    };
    // The round-trip verdict is reported whatever happens to the publication:
    // a defect AY can name is worth printing even when the proof still ships.
    match (&self_check_verdict, self_check_mode) {
        (Some(Err(defect)), ProofSelfCheckMode::Warn) => {
            safe_eprintln!(
                "c warning: Alethe round-trip self-check rejected the emitted document [{}]: {defect}",
                defect.tag()
            );
        }
        (Some(Ok(report)), ProofSelfCheckMode::Warn | ProofSelfCheckMode::Strict) => {
            safe_eprintln!(
                "c alethe self-check ok: {} commands, {} steps, {} assumes, {} anchors, {} define-funs",
                report.commands,
                report.steps,
                report.assumes,
                report.anchors,
                report.define_funs
            );
        }
        _ => {}
    }
    let (proof_digest, proof_file, proof_path) = match stream_result {
        Ok(publication) => publication,
        Err(ay_proof::AletheStreamError::Print(error)) => {
            disclose_refused_artifact("render", &proof_config.path, &error);
            // #evidence-stage-3 — AHEAD OF THE RENDER MESSAGE, and that order is
            // the whole fix for the floating-point family.
            //
            // The pinned-Carcara sort screen runs inside `prepare_proof`, before
            // a single step is emitted. On an FP query the lane bit-blasts with
            // proof output OFF, records no clause trace, and closes the
            // refutation with one bare trust lemma — so there is no derivation
            // to print and the sort screen is merely the first gate to speak.
            // Measured over 64 FP-family UNSATs: ZERO print as
            // `proof-unrenderable` under `--rigor strict`; 41 are rejected by
            // AY's own self-check and 23 by trust detection. The surface is
            // never the binding constraint, and reporting it as the cause sent
            // the census after a printer bridge that would have recovered
            // nothing.
            //
            // So consult what declined EARLIER first, and fall through to the
            // render only when nothing did.
            disclose_proof_decline_with_fallback(
                executor,
                &proof_config.path,
                DeclinePrecedence::AssemblyOutranksRender,
                || mechanism_from_print_error(&error),
            );
            disclose_unsat_corroboration(executor);
            if optional_default {
                // Same reason as the no-derivation branch above: when no
                // document is written, the admission tag is the ONLY record of
                // what the verdict rests on.
                //
                // CORRECTED at #evidence-stage-3. "proof not fully checkable"
                // asserts that a proof exists and merely fell short of full
                // checkability. For the FP family that is false — there is no
                // derivation at all — and the sentence sent every reader to the
                // printer. The refusal is now stated as what it is, a refusal AT
                // the render, with the cause named on the line above.
                safe_eprintln!(
                    "c warning: no proof certificate emitted (the render refused the artifact: {error}); a render refusal is the first gate to fire, not necessarily the cause — the ay.proof.decline line above names the cause; the verdict was admitted by unsat_admission={} {}; pass --strict-proofs to require a certificate instead",
                    executor
                        .last_command_unsat_admission_tag()
                        .unwrap_or("none-recorded"),
                    unsat_evidence_fields(executor),
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
            disclose_refused_artifact("write", &proof_config.path, &error);
            // #evidence-stage-3. A write failure says nothing about the
            // derivation, and this is the one branch where that matters: the
            // verdict is still unevidenced from the corpus's point of view, so
            // it must carry a mechanism, and the mechanism must not be mistaken
            // for a producer defect. An earlier decline still outranks it.
            disclose_proof_decline_with_fallback(
                executor,
                &proof_config.path,
                DeclinePrecedence::AssemblyOutranksRender,
                || ProofDeclineMechanism::CertificateWriteFailed,
            );
            disclose_unsat_corroboration(executor);
            let taken_by_this_run =
                default_certificate_taken_by_this_run(transcript, proof_config, &error);
            if optional_default {
                // A synthesized-default certificate is optional and AY-specific (z3
                // writes no proof by default). A write failure — most commonly a
                // read-only input directory (nix store, docker RO mount, CI cache,
                // mounted corpus) — must NOT change the exit code: the UNSAT verdict
                // is already on stdout and is unaffected. Warn and continue, exactly
                // as the render-failure branches above do for the default case.
                // (Previously this exited 1 with a correct `unsat` on stdout, which
                // broke every read-only deployment.)
                let unpublished = if taken_by_this_run {
                    format!(
                        "no default proof file for this UNSAT: {} was already written by this run for an earlier query, and AY never replaces a file",
                        proof_config.path,
                    )
                } else {
                    format!(
                        "could not publish a same-run default proof file {} ({error}); any pre-existing file was preserved and is stale for this run",
                        proof_config.path,
                    )
                };
                safe_eprintln!("c warning: {unpublished}; UNSAT verdict is unaffected");
                return AletheProofPublication::Ready(None);
            }
            if strict_default {
                let diagnostic = if taken_by_this_run {
                    format!(
                        "strict proof mode rejected UNSAT because {} was already written by this run for an earlier query, and AY never replaces a file",
                        proof_config.path
                    )
                } else {
                    format!(
                        "strict proof mode rejected UNSAT because {} could not be published: {error}",
                        proof_config.path
                    )
                };
                return AletheProofPublication::RejectToUnknown {
                    reason: "(incomplete proof-publication-failed)".to_string(),
                    diagnostic,
                };
            }
            return AletheProofPublication::Fatal(format!(
                "failed to write required proof file {}: {error}",
                proof_config.path
            ));
        }
    };
    if let Some(withheld) =
        strict_certificate_withheld(query_strict, executor, proof_config, &proof_file)
    {
        return withheld;
    }
    // PUBLICATION DISCLOSURE. Exit 0 reports the VERDICT; it has never been a
    // statement about the certificate. Without `--strict-proofs` a certificate
    // that still carries `hole` steps is published anyway (it is the honest
    // record of what AY derived), and an external checker reports such a
    // document as *holey* — or, when a residual step is malformed, *invalid* —
    // never *valid*. Say so on the record, naming exactly which checks AY ran
    // and how they came out, so a zero exit status cannot be misread as
    // "externally checkable".
    disclose_alethe_certificate(executor, &proof_config.path, carcara_surface.as_ref());
    let proof_publication = match RetainedPublication::new(
        proof_file,
        proof_path,
        PublicationPathKind::File,
    ) {
        Ok(publication) => publication,
        Err(error) => {
            disclose_refused_artifact("seal", &proof_config.path, &error);
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
        disclose_refused_artifact("authority", &proof_config.path, &error);
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

/// Abandon a partially rendered certificate: take the file back out of its
/// buffered writer WITHOUT flushing, then invalidate that exact descriptor.
///
/// Discarding the buffer is load-bearing, not tidiness. `BufWriter::drop`
/// flushes at the file's CURRENT offset, so plainly dropping the writer after
/// [`invalidate_retained_artifact`] truncated the inode wrote the buffered
/// tail back at the pre-truncation offset: measured on the QF_UF
/// `iso_brn492` emission-budget abandonment, the "invalidated" temp file was
/// a 29,182,083-byte sparse file still holding the last megabyte of the
/// discarded proof text (996 KB of real blocks). The caller's
/// [`ArtifactTempReservation`] then unlinks the path; this makes the inode
/// itself empty even for anyone still holding it open.
fn alethe_error_after_abandoning_buffer(
    primary: ay_proof::AletheStreamError,
    writer: ProofDigestWriter<BufWriter<std::fs::File>>,
) -> ay_proof::AletheStreamError {
    let (file, _discarded) = writer.into_inner().into_parts();
    alethe_error_after_invalidation(primary, &file)
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
    // Whether this query's UNSAT is still held back (`publish_pending_smt_unsat`)
    // or already on the regular channel. Decided when the query was answered,
    // under the strict request in force then (`holds_unsat_publication`).
    let unsat_held = transcript.pending_unsat_output.is_some();
    // A held UNSAT is settled here even when its problem may carry no
    // artifact: leaving it unprepared would fail its publication, with no
    // response to the query (`unsat_publication_without_artifact_authority`).
    if !matches!(
        &transcript.smt_unsat_publication,
        SmtUnsatPublicationState::Unprepared
    ) || (!unsat_held && !transcript.public_unsat_artifacts_allowed())
    {
        return;
    }
    let Some(proof_config) = proof_config else {
        transcript.smt_unsat_publication = SmtUnsatPublicationState::ReadyWithoutArtifacts;
        return;
    };
    match write_alethe_proof(executor, transcript, proof_config, problem, theory) {
        AletheProofPublication::Ready(publication) => {
            if unsat_held {
                transcript.smt_unsat_publication = match publication {
                    Some(publication) => SmtUnsatPublicationState::Prepared(publication),
                    None => SmtUnsatPublicationState::ReadyWithoutArtifacts,
                };
            } else {
                if required_smt_unsat_publication(
                    Some(proof_config),
                    transcript.query_script_strict,
                ) {
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
            if !unsat_held {
                // This query's `unsat` is already on the regular channel. A
                // second response to the same command would retract it, so
                // fail loudly instead (the Ready arm's guard, for this arm).
                fail_required_unsat_publication(
                    transcript,
                    format!(
                        "{diagnostic}, but this query's unsat is already published and a second response cannot retract it"
                    ),
                );
            }
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
            // The deferred line is an `unsat`: decisive, so a deadline after
            // it is teardown overrun, not a failure to decide (the immediate
            // publication path records the same).
            super::mark_decisive_verdict_printed();
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

/// What an interactive session shows a HUMAN, as distinct from what it streams.
///
/// Split out of the old `is_tty` bool because that one flag was answering three
/// different questions — print a banner? print a prompt? which prompt? — and the
/// answers stopped agreeing once a start screen existed.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum ReplSurface {
    /// Nothing but the protocol: no banner, no prompt, no hints. What a pipe,
    /// `-in`, and `--z3-mode` get, byte-identical to every previous release.
    Raw,
    /// The pre-redesign surface: a bare `> ` prompt and nothing else.
    /// `AY_PLAIN_REPL=1`, for expect/pty harnesses that scrape prompts.
    Plain,
    /// The start screen, `ay>` / `..>` prompts, and the human affordances.
    Full,
}

/// Decide the surface once, from every signal that has a say.
///
/// The stdout check is the one that was missing: the gate used to read stdin
/// alone, so `ay > file` on a terminal wrote the banner INTO the file. Both ends
/// must be a terminal before ay assumes a human is watching.
///
/// An explicit `-in`/`--incremental` means "give me z3's command stream", and it
/// wins even on a terminal — that is the invocation a pty-driven harness
/// actually uses, and z3 prints no prompt there either.
fn repl_surface(stdin_tty: bool, incremental: bool) -> ReplSurface {
    use std::io::IsTerminal;
    repl_surface_from(
        stdin_tty,
        io::stdout().is_terminal(),
        incremental,
        super::Z3_MODE_ENABLED.load(std::sync::atomic::Ordering::Relaxed),
        std::env::var_os("AY_PLAIN_REPL").is_some_and(|v| !v.is_empty() && v != "0"),
    )
}

/// The decision table behind [`repl_surface`], with every input handed in.
///
/// Pure because this is the one function in the redesign that can corrupt
/// somebody's data: a `Full` returned for a pipe puts a banner and prompts into
/// a Why3 or Dafny coprocess's stream, and the driver on the other end is
/// parsing s-expressions. Every row is pinned by a test rather than reasoned
/// about at the call site.
fn repl_surface_from(
    stdin_tty: bool,
    stdout_tty: bool,
    incremental: bool,
    z3_mode: bool,
    plain_repl: bool,
) -> ReplSurface {
    if !stdin_tty || !stdout_tty || incremental || z3_mode {
        return ReplSurface::Raw;
    }
    if plain_repl {
        return ReplSurface::Plain;
    }
    ReplSurface::Full
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
        // The memory-budget verdict grammar follows the input format.
        crate::note_verdict_grammar_route(if is_dimacs {
            crate::VerdictGrammarRoute::Dimacs
        } else {
            crate::VerdictGrammarRoute::SmtLib
        });

        if !is_dimacs && !is_chc_family {
            // SMT-LIB: stream. Chain the sniffed prefix back in front of the live
            // stream so no byte is lost.
            let reader = io::BufReader::new(io::Cursor::new(prefix).chain(locked));
            run_interactive_smt_stream(
                reader,
                ReplSurface::Raw,
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
                false,
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
                false,
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
    crate::note_verdict_grammar_route(crate::VerdictGrammarRoute::SmtLib);
    run_interactive_smt_stream(
        stdin.lock(),
        repl_surface(is_tty, incremental),
        stats_cfg,
        proof_config,
        visualization,
        verbose,
        validate,
    );
}

/// Configure an SMT-LIB session executor that emits no proof and serves no
/// mandatory result gate.
fn configure_unproved_smt_executor(executor: &mut Executor) {
    // No proof can be emitted this session (`--no-proof` / `--z3-mode` /
    // competition mode, or stdin with nothing to name a sidecar after),
    // and no mandatory result/artifact gate needs the internal proof
    // surface: skip retaining a deep parsed-AST clone of every assertion
    // (~190 MB of a 318 MB peak on a 6 MB QF_UF input, #rss-vs-z3). An
    // in-script `(set-option :produce-proofs true)` re-enables retention.
    // The check-sat-time definitional-forall pass (#defmacro-named-preuse)
    // gets its own parsed copy, bounded to the node budget its
    // re-elaboration honours anyway, so a small problem still decides
    // exactly as it does for a library embedder while the retention
    // switch — which is also load-bearing for the certification funnel's
    // lane choice — stays off.
    executor.set_retain_parsed_assertions(false);
    executor
        .set_definitional_pass_parsed_budget(ay_frontend::CHECK_SAT_ADOPTION_MAX_RETAINED_NODES);
    // Whatever proof work a NON-shedding executor still does here (the
    // mandatory certificate of a `--rigor standard` stdin session) is
    // best-effort with no artifact behind it, so its bookkeeping meter
    // must be the same budgeted one the synthesized-default file route
    // uses — never `None`. An unbudgeted meter was the `--no-proof` trap:
    // gensys_icl161 materialised a 122k-step proof and strict-checked
    // 3.9M steps for an artifact nobody asked for. A shedding executor
    // never consults it, and an explicit demand (`set_produce_proofs`,
    // in-script `:produce-proofs`) keeps its unbudgeted slot by contract.
    executor.set_proof_reconstruction_step_budget(Some(DEFAULT_PROOF_RECONSTRUCTION_STEP_BUDGET));
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
    surface: ReplSurface,
    stats_cfg: stats_output::StatsConfig,
    proof_config: Option<&ProofConfig>,
    visualization: Option<VisualizationFormat>,
    verbose: bool,
    validate: bool,
) {
    reject_explicit_proof_verification_for_route("SMT-LIB", "Alethe");
    if surface == ReplSurface::Full {
        safe_println!("{}", super::features::interactive_banner());
    }

    let mut stdout = io::stdout();
    let mut input_buffer = String::new();
    // Running 1-based line and column of the first character still in
    // `input_buffer`, so errors report their true position in the whole
    // session (z3's `-in` does not reset the line counter per command).
    // Advanced past the text consumed each time the buffer is read.
    let mut line_base = 1usize;
    let mut column_base = 1usize;
    // The lexer state of `input_buffer`, fed line by line, finds the item
    // still open at its end in time linear in the input (#inc-lra-parse).
    // `--no-inc-linear-parse` rescans the whole buffer on every line instead.
    let linear_parse = !ay_core::misc_cli_flags().no_inc_linear_parse;
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
    // A problem-contributing command was dropped since the last reset, so a
    // streamed CHC check-sat answers `unknown`.
    let mut chc_problem_dropped = false;
    // Rewrite synthesized non-Alethe configs to Alethe for SMT
    // (Finding A in the development design notes).
    let adapted = adapt_proof_config_for_smt(proof_config);
    transcript.unsat_proof_posture = SmtUnsatProofPosture::of(adapted.as_ref());
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
        configure_proof_policy(&mut executor, proof);
    } else if !ResultGateRequests::current().any() {
        configure_unproved_smt_executor(&mut executor);
    }

    enable_session_replay_if_supported(&mut transcript, adapted.as_ref());
    let rebuild_executor = || {
        let mut executor = new_executor();
        if !ResultGateRequests::current().any() {
            configure_unproved_smt_executor(&mut executor);
        }
        executor
    };

    loop {
        exit_if_timed_out_with_transcript_context(&transcript);
        match surface {
            // `ay>` and `..>` are the same width, so a pasted multi-line command
            // stays column-aligned instead of stair-stepping. Dim, because the
            // brightest thing on the screen should be what the user typed.
            ReplSurface::Full => {
                let prompt = if depth_scan.open_item().is_some() {
                    "..>"
                } else {
                    "ay>"
                };
                safe_print!("{} ", super::help_style::dim(prompt));
            }
            ReplSurface::Plain => safe_print!("> "),
            ReplSurface::Raw => {}
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

        // z3 reads a command on across lines until it closes. Run the
        // complete items before the one still open at the end of the
        // buffer, and keep that one to read on; at end of input, read the
        // rest as it is. See `IncrementalDepth`.
        let ready = if eof {
            input_buffer.len()
        } else {
            depth_scan.feed(&line);
            let open = if linear_parse {
                depth_scan.open_item()
            } else {
                IncrementalDepth::scan(&input_buffer).open_item()
            };
            match open {
                Some(0) => continue,
                Some(start) => start,
                None => input_buffer.len(),
            }
        };
        let consumed = &input_buffer[..ready];
        let commands = read_stdin_commands(consumed, line_base, column_base);
        (line_base, column_base) = position_after(consumed, line_base, column_base);
        input_buffer.drain(..ready);
        depth_scan.rebase(ready);
        for item in commands {
            let (cmd, source) = match item {
                StdinCommand::Parsed(cmd, source) => (cmd, source),
                StdinCommand::Dropped(err, source) => {
                    let text = source.text.clone();
                    set_current_source(&mut transcript, source);
                    executor.observe_authored_dropped_source(&text);
                    note_z3_session_failed_source(&mut transcript, &text);
                    print_recoverable_parse_error(&mut transcript, &err);
                    invalidate_export_after_malformed_decision(&text);
                    if transcript.exit_on_error {
                        cleanup_temp_proof(adapted.as_ref());
                        std::process::exit(1);
                    }
                    // SOUNDNESS: a dropped problem-contributing command makes
                    // a later check-sat fail closed to `unknown`, in CHC
                    // streaming too.
                    if parse_drop_contributes_to_problem(&text) {
                        mark_problem_incomplete(&mut executor, &mut transcript);
                        chc_problem_dropped = true;
                    }
                    if dropped_text_holds_a_query(&text) {
                        withhold_answers_out_of_step(&mut executor, &mut transcript);
                        chc_problem_dropped = true;
                    }
                    let _ = stdout.flush();
                    exit_if_timed_out_with_transcript_context(&transcript);
                    continue;
                }
            };
            set_current_source(&mut transcript, source.clone());
            let cmd: &Command = &cmd;
            let source_text = source.text.as_str();
            if smt_logic.is_none() {
                smt_logic = logic_from_commands(std::slice::from_ref(cmd)).map(str::to_owned);
            }
            formula_stats.observe_command(cmd);
            executor.observe_authored_command_source(source_text);
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
                    reject_explicit_proof_verification_for_route("incremental CHC", "CHC replay");
                    chc_stream_mode = true;
                }

                match cmd {
                    Command::Exit => {
                        cleanup_temp_proof(adapted.as_ref());
                        return;
                    }
                    Command::Reset => {
                        chc_stream_mode = false;
                        chc_problem_dropped = transcript.answers_out_of_step;
                        chc_problem_input.clear();
                        chc_last_model = None;
                        formula_stats = FormulaStats::default();
                        smt_logic = None;
                    }
                    Command::GetModel => match &chc_last_model {
                        Some(model) => safe_print!("{model}"),
                        None => safe_println!("(error \"model is not available\")"),
                    },
                    Command::CheckSat if chc_problem_dropped => {
                        super::owe_response_for_new_query();
                        chc_last_model = None;
                        chc_runner::emit_chc_unknown_after_dropped_command(stats_cfg);
                    }
                    Command::CheckSat => {
                        super::owe_response_for_new_query();
                        let mut solve_input = chc_problem_input.clone();
                        solve_input.push_str("(check-sat)\n");
                        chc_last_model = chc_runner::run_chc_from_content(
                            &solve_input,
                            verbose,
                            validate,
                            stats_cfg,
                            proof_config,
                            executor.script_strict_proofs_requested(),
                        );
                    }
                    _ => {
                        // Any accepted problem command starts a new model
                        // epoch. Serving the previously certified invariant
                        // after an assertion, rule, declaration, push, or pop
                        // would attach stale evidence to a changed CHC
                        // problem. A fresh check-sat is the only operation
                        // allowed to repopulate it.
                        chc_last_model = None;
                        chc_problem_input.push_str(source_text);
                        chc_problem_input.push('\n');
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
                    print_smt_stats(&executor, &transcript, Some(&formula_stats), stats_cfg);
                }
                maybe_write_minimal_decision_trace(&mut transcript);
                cleanup_temp_proof(adapted.as_ref());
                exit_if_transcript_had_recoverable_error(&transcript);
                return;
            }
            if !execute_and_print(&mut executor, cmd, &mut transcript, true) {
                let _ = stdout.flush();
                exit_if_timed_out_with_transcript_context(&transcript);
                if continue_after_failed_command(
                    &mut executor,
                    cmd,
                    &mut transcript,
                    &rebuild_executor,
                ) {
                    continue;
                }
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
                chc_problem_dropped = false;
            } else if retain_artifact_input {
                artifact_input.push_str(source_text);
                artifact_input.push('\n');
            }
            publish_pending_smt_unsat(
                &mut executor,
                &mut transcript,
                adapted.as_ref(),
                ProofArtifactProblem::Text(&artifact_input),
                ProofArtifactTheoryMetadata::smt_lib(smt_logic.as_deref(), Some(&formula_stats)),
            );
            // Flush after each command so pipe consumers see responses
            // immediately (stdout is block-buffered when piped).
            let _ = stdout.flush();
            exit_if_timed_out_with_transcript_context(&transcript);
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
                crate::note_verdict_grammar_route(crate::VerdictGrammarRoute::Dimacs);
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
            Err(e) => crate::exit_unreadable_input_file(path, &e),
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
            // Check for DIMACS CNF format first (by extension or content). The
            // memory-budget verdict grammar follows the input format.
            let dimacs_input =
                dimacs::has_cnf_extension(path) || dimacs::is_dimacs_format(&content);
            crate::note_verdict_grammar_route(if dimacs_input {
                crate::VerdictGrammarRoute::Dimacs
            } else {
                crate::VerdictGrammarRoute::SmtLib
            });
            if dimacs_input {
                reject_bv_cnf_export_for_non_smt_route("DIMACS file");
                reject_firewall_emission_for_route("DIMACS file");
                reject_firewall_verification_for_route("DIMACS file");
                if dimacs::has_structural_sidecar(path)
                    && (cube_and_conquer_depth.is_some() || parallel_threads.is_some())
                {
                    safe_eprintln!(
                        "c structural-sidecar: adjacent sidecar present; using checked sequential DIMACS route"
                    );
                    run_dimacs_from_file_on_dedicated_stack(
                        path,
                        &content,
                        stats_cfg,
                        proof_config,
                    );
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
                    run_dimacs_from_file_on_dedicated_stack(
                        path,
                        &content,
                        stats_cfg,
                        proof_config,
                    );
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
                    false,
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
                    false,
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
        Err(e) => crate::exit_unreadable_input_file(path, &e),
    }
}

/// Run the sequential DIMACS solve on a dedicated large-stack thread.
///
/// Same rationale as [`SMT_FILE_THREAD_STACK_SIZE`], for a route that never had
/// the protection: the DIMACS solve ran directly on the process main thread,
/// whose stack is fixed at link time — 1 MiB on Windows, i.e. SMALLER than the
/// ~2 MiB spawned-thread default that already proved insufficient for the PB
/// path. The symmetry preprocessor's backtracking automorphism finder
/// (`find_composite_generators` / `ir::find_automorphisms`) recurses to a depth
/// driven by the instance's orbit structure, so with `AY_SAT_COMPOSITE_SYMMETRY`
/// enabled a small, highly symmetric formula could exhaust that stack and abort
/// the process: measured on SAT-COMP 2026 instance 860788f9 (510 vars, 19652
/// clauses), which died with STATUS_STACK_OVERFLOW (0xC00000FD) after ~2 s and
/// reported `unknown`. The verdict failed CLOSED, so this never cost
/// correctness — only answers.
///
/// Soundness-neutral, exactly as for the SMT and PB paths: a reserved stack is
/// committed lazily, so the headroom is free, and it can only prevent stack
/// exhaustion, never change an outcome.
fn run_dimacs_from_file_on_dedicated_stack(
    path: &str,
    content: &str,
    stats_cfg: stats_output::StatsConfig,
    proof_config: Option<&ProofConfig>,
) {
    std::thread::scope(|scope| {
        match std::thread::Builder::new()
            .name("ay-dimacs-file".to_string())
            .stack_size(SMT_FILE_THREAD_STACK_SIZE)
            .spawn_scoped(scope, move || {
                dimacs::run_dimacs_from_file(path, content, stats_cfg, proof_config)
            }) {
            Ok(handle) => match handle.join() {
                Ok(()) => {}
                Err(payload) => std::panic::resume_unwind(payload),
            },
            // Thread creation failed (resource exhaustion): fall back to the
            // caller's stack rather than losing the solve outright.
            Err(_) => dimacs::run_dimacs_from_file(path, content, stats_cfg, proof_config),
        }
    });
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

include!("run/smt_file.rs");

fn run_smt_file_content(
    content: &str,
    source: Option<&SmtFileSource>,
    stats_cfg: stats_output::StatsConfig,
    proof_config: Option<&ProofConfig>,
    visualization: Option<VisualizationFormat>,
) {
    reject_explicit_proof_verification_for_route("SMT-LIB", "Alethe");
    if try_smt_milp_fastpath(content, &stats_cfg, proof_config, &visualization) {
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
    // MODEL-OUTPUT DEMAND (#model-demand). This lane — and only this lane —
    // holds the entire script before the first solve, so it is the one place
    // that can PROVE no model will ever be read. When that holds and no host
    // flag prints or post-processes one either, tell the executor to skip
    // witness COSMETICS (counterexample minimization). Validation is untouched:
    // AY checks every model it publishes whether or not anyone reads it.
    //
    // Measured motive: ABVFPLRA/inv_Newton is 85 `(check-sat)` and zero
    // `(get-model)`, and every one of those sat answers paid for a minimization
    // pass whose result was discarded unread.
    //
    // Each disqualifier below is a real consumer: `--model` prints the model
    // after a `sat` verdict, `--minimize-model` is an explicit request for a
    // SMALL witness (honour the intent even with no reader in the script), and
    // a visualization renders solver state. The interactive `-in` lane never
    // reaches here, so it always keeps the demand-assumed default.
    let model_output_shedding = !commands_may_consume_a_model(&command_sources)
        && !z3_model_enabled()
        && !MINIMIZE_MODEL_ENABLED.load(std::sync::atomic::Ordering::Relaxed)
        && visualization.is_none();
    executor.set_model_output_shedding(model_output_shedding);
    // Rewrite synthesized non-Alethe configs to Alethe for SMT
    // (Finding A in the development design notes).
    let adapted = adapt_proof_config_for_smt(proof_config);
    transcript.unsat_proof_posture = SmtUnsatProofPosture::of(adapted.as_ref());
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
        configure_proof_policy(&mut executor, proof);
    } else if !ResultGateRequests::current().any() {
        configure_unproved_smt_executor(&mut executor);
    }

    enable_session_replay_if_supported(&mut transcript, adapted.as_ref());
    let rebuild_executor = || {
        let mut executor = new_executor();
        executor.set_model_output_shedding(model_output_shedding);
        if !ResultGateRequests::current().any() {
            configure_unproved_smt_executor(&mut executor);
        }
        executor
    };

    let mut sources = StreamSources::new(1, 1);
    // Start byte of the current full-reset epoch. Proof payloads and
    // visualization must describe exactly the problem that produced the
    // authoritative decision, never rejected text from an earlier epoch.
    let mut artifact_epoch_start = 0usize;
    let mut stream = CommandStream::new(content);
    loop {
        // Delimit the exact source slice this command consumes (used below to
        // classify a dropped command on a parse error).
        let consumed_start = stream.position();
        let Some(item) = stream.next_command() else {
            break;
        };
        let consumed = content
            .get(consumed_start..stream.position())
            .unwrap_or_default();
        // Each item's source is the text it consumed, so a command never
        // reads another one's text after a stray token.
        set_current_source(
            &mut transcript,
            sources.source(content, consumed_start, stream.position()),
        );
        match item {
            CommandStreamItem::Error(err) => {
                // z3-style continued-execution: report the bad command and keep
                // going. Marked recoverable so the process still exits non-zero.
                executor.observe_authored_dropped_source(consumed);
                note_z3_session_failed_source(&mut transcript, consumed);
                print_recoverable_parse_error(&mut transcript, &err);
                invalidate_export_after_malformed_decision(consumed);
                if transcript.exit_on_error {
                    cleanup_temp_proof(adapted.as_ref());
                    std::process::exit(1);
                }
                // SOUNDNESS: a problem-contributing command (e.g. an `assert`
                // using an unsupported construct) just failed to parse and was
                // dropped. Taint the session so a later check-sat fails closed to
                // `unknown` instead of answering on the incomplete remainder.
                if parse_drop_contributes_to_problem(consumed) {
                    mark_problem_incomplete(&mut executor, &mut transcript);
                }
                if dropped_text_holds_a_query(consumed) {
                    withhold_answers_out_of_step(&mut executor, &mut transcript);
                }
                exit_if_timed_out_with_transcript_context(&transcript);
            }
            CommandStreamItem::Command(cmd) => {
                let cmd = *cmd;
                formula_stats.observe_command(&cmd);
                if matches!(cmd, Command::CheckSat | Command::CheckSatAssuming(_)) {
                    // Carcara parses the whole file: read the rest before the
                    // query can publish a certificate for it.
                    executor.observe_authored_commands_ahead(&content[consumed_start..]);
                }
                executor.observe_authored_command_source(consumed);
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
                            if continue_after_failed_command(
                                &mut executor,
                                &cmd,
                                &mut transcript,
                                &rebuild_executor,
                            ) {
                                continue;
                            }
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
    // An UNRECOGNIZED command is not an error to z3. It prints a bare
    // `unsupported` on stdout, a positioned comment on stderr, keeps executing,
    // and exits 0 — the same shape as an unrecognized `(set-logic ...)`:
    //
    //   (set-logic ALL) (frobnicate) (check-sat)
    //     stdout: unsupported | sat
    //     stderr: ; frobnicate line: 2 position: 11
    //     exit 0
    //
    // ay emitted `(error "line 2 column 1: Unknown command: frobnicate")` and
    // exited 1, so a script containing any command ay does not know failed the
    // whole run for a caller that checks the exit status.
    if let Some(name) = err.message.strip_prefix("Unknown command: ") {
        let name = name.trim();
        print_regular_line(state, "unsupported");
        // z3 reports the command form's closing paren -- see
        // `unsupported_command_position`. An earlier reading of "the end of the
        // command name" only matched because `(frobnicate)` puts the `)`
        // immediately after the name; it breaks on `(bogus arg1 arg2)`.
        let comment = state.current_source.as_ref().map_or_else(
            || format!("; {name} unsupported"),
            |source| {
                let position = unsupported_command_position(source);
                format!(
                    "; {name} line: {} position: {}",
                    position.line, position.column
                )
            },
        );
        print_diagnostic_line(state, &comment);
        // Deliberately NOT `note_recoverable_error`: z3 exits 0 here.
        return;
    }
    state.note_recoverable_error();
    // Use the offending command's *absolute* position from its current source
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

#[cfg(test)]
mod repl_surface_tests {
    use super::{repl_surface_from, ReplSurface};

    /// THE INVARIANT THAT PROTECTS SOMEBODY ELSE'S DATA.
    ///
    /// Why3, Dafny and Boogie drive ay as a coprocess over a pipe, parsing
    /// s-expressions off stdout. A banner or a prompt on that stream is not a
    /// cosmetic bug — it is a parse error in a tool that is not ay, reported to
    /// a user who has no idea ay is involved. Every non-terminal shape must be
    /// Raw, and there is no "unless" worth adding to that sentence.
    #[test]
    fn nothing_but_a_two_sided_terminal_ever_gets_a_surface() {
        for &stdin_tty in &[true, false] {
            for &stdout_tty in &[true, false] {
                for &incremental in &[true, false] {
                    for &z3_mode in &[true, false] {
                        for &plain in &[true, false] {
                            let surface = repl_surface_from(
                                stdin_tty,
                                stdout_tty,
                                incremental,
                                z3_mode,
                                plain,
                            );
                            let human = stdin_tty && stdout_tty && !incremental && !z3_mode;
                            if !human {
                                assert_eq!(
                                    surface,
                                    ReplSurface::Raw,
                                    "stdin_tty={stdin_tty} stdout_tty={stdout_tty} \
                                     incremental={incremental} z3_mode={z3_mode} plain={plain} \
                                     must be Raw"
                                );
                            } else {
                                assert_ne!(surface, ReplSurface::Raw);
                            }
                        }
                    }
                }
            }
        }
    }

    /// `ay > file` from a terminal. The old gate read stdin alone, so the banner
    /// went INTO the file — the measured leak this check exists to close.
    #[test]
    fn a_redirected_stdout_gets_no_banner_even_from_a_terminal() {
        assert_eq!(
            repl_surface_from(true, false, false, false, false),
            ReplSurface::Raw
        );
    }

    /// An explicit `-in` is a request for z3's command stream, and it wins even
    /// on a terminal — that is the invocation a pty-driven harness uses, and z3
    /// prints no prompt there either.
    #[test]
    fn explicit_incremental_forces_raw_even_on_a_terminal() {
        assert_eq!(
            repl_surface_from(true, true, true, false, false),
            ReplSurface::Raw
        );
    }

    /// --z3-mode means "no ay-isms", and a start screen is the largest ay-ism
    /// there is.
    #[test]
    fn z3_mode_forces_raw() {
        assert_eq!(
            repl_surface_from(true, true, false, true, false),
            ReplSurface::Raw
        );
    }

    /// The escape hatch: AY_PLAIN_REPL restores the bare `> ` prompt for a
    /// harness that scrapes it, without silencing the session the way `-q`
    /// would. It downgrades the surface; it never resurrects one.
    #[test]
    fn plain_repl_downgrades_a_human_surface_but_never_creates_one() {
        assert_eq!(
            repl_surface_from(true, true, false, false, true),
            ReplSurface::Plain
        );
        assert_eq!(
            repl_surface_from(false, true, false, false, true),
            ReplSurface::Raw
        );
    }

    #[test]
    fn a_plain_two_sided_terminal_gets_the_start_screen() {
        assert_eq!(
            repl_surface_from(true, true, false, false, false),
            ReplSurface::Full
        );
    }
}
