// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![forbid(unsafe_code)]

//! AY - A proof-oriented constraint solver in Rust
//!
//! Usage: ay [OPTIONS] [FILE]
//!        ay solve [OPTIONS] [FILE]
//!        ay check drat FORMULA PROOF
//!        ay bench run [EVALS...]
//!        ay flatzinc solve FILE
//!        ay pb solve FILE

use std::env;
use std::io::{self, Write};
use std::path::{Path as FsPath, PathBuf};
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::sync::Arc;
use std::time::{Duration, Instant};

use clap::{CommandFactory, Parser};

// Import safe_eprintln! from ay-core (non-panicking eprintln replacement)
#[macro_use]
extern crate ay_core;

/// Non-panicking replacement for `println!`. Avoids SIGABRT on broken stdout pipe.
macro_rules! safe_println {
    () => {{
        use std::io::Write;
        let _ = writeln!(std::io::stdout());
    }};
    ($($arg:tt)*) => {{
        use std::io::Write;
        let _ = writeln!(std::io::stdout(), $($arg)*);
    }};
}

/// Non-panicking replacement for `print!`. Avoids SIGABRT on broken stdout pipe.
macro_rules! safe_print {
    ($($arg:tt)*) => {{
        use std::io::Write;
        let _ = write!(std::io::stdout(), $($arg)*);
    }};
}

use ay_core::escape_string_contents;

mod build_info;
mod chc_runner;
mod cmd_allsat;
mod cmd_bench;
mod cmd_bench_compare;
mod cmd_bisect;
mod cmd_check;
mod cmd_competition_jit;
mod cmd_corpus;
mod cmd_diagnose;
mod cmd_flatzinc;
mod cmd_gate;
mod cmd_launch;
mod cmd_launch_packet;
mod cmd_lp;
mod cmd_maxsat;
mod cmd_model_count;
mod cmd_pb;
mod cmd_qbf;
mod cmd_release;
mod cmd_scripts;
mod cmd_simplify;
mod cmd_simplify_printer;
mod cmd_submission;
mod cmd_tool;
mod cmd_tutorial;
mod cmd_verifier_audit;
mod cmd_z3_audit;
mod competition_jit_gate;
mod competition_jit_hot_inputs;
mod competition_jit_probe;
mod competition_jit_release;
mod dimacs;
mod explain;
mod explain_reason;
mod features;
mod firewall_verify;
mod lean_verify;
mod milp_fastpath;
mod proof_artifact;
mod proof_verify;
mod run;
mod stats_output;
mod tracing_setup;
mod z3_params;

// Keep format classifiers in this module's scope for both CLI preflight and
// `main_tests.rs`, which imports them through `use super::*`.
pub(crate) use run::{is_fixedpoint_format, is_horn_logic};

const DEFAULT_TIMEOUT_EXIT_CODE: i32 = 124;
const SAT_COMPETITION_UNKNOWN_EXIT_CODE: i32 = 0;
const SAT_COMPETITION_WRAPPER_ENV: &str = "AY_INTERNAL_SATCOMP_WRAPPER";
const SAT_COMPETITION_WRAPPER_TOKENS: &[&str] = &[
    "main-regular-default-lrat-v1",
    "main-ai-tuned-aggressive-lrat-v1",
    "parallel-parallel-default-lrat-v1",
    "cloud-cloud-default-lrat-v1",
    "experimental-experimental-probe-lrat-v1",
    "satcomp-variant-default-lrat-v1",
    "satcomp-variant-aggressive-lrat-v1",
    "satcomp-variant-minimal-lrat-v1",
    "satcomp-variant-probe-lrat-v1",
];

/// Global timeout in milliseconds (0 = no timeout)
pub(crate) static GLOBAL_TIMEOUT_MS: AtomicU64 = AtomicU64::new(0);
pub(crate) static START_TIME: std::sync::OnceLock<Instant> = std::sync::OnceLock::new();
/// Global timeout flag — set by watchdog thread instead of process::exit (#2971).
/// All solve paths check this cooperatively and return Unknown/timeout.
static TIMED_OUT: AtomicBool = AtomicBool::new(false);
/// Whether a verdict line (`sat`/`unsat`/`unknown`, or a DIMACS `s ...`
/// status line) has already been printed to stdout (#8674, #verdict-latch).
/// Once ANY verdict has been printed, no synthesized timeout/SIGTERM verdict
/// may ever print a second one: `exit_if_timed_out` and
/// `hard_timeout_fallback_exit` degrade to a stderr-only timeout note, so a
/// sound `unsat` printed by the solve path can never be followed by a
/// contradictory `unknown` (contradictory verdict streams are disqualifying).
static VERDICT_PRINTED: AtomicBool = AtomicBool::new(false);
/// Shared interrupt handle for ay-dpll executor integration.
/// Set by the watchdog thread alongside TIMED_OUT.
pub(crate) static INTERRUPT_HANDLE: std::sync::OnceLock<Arc<AtomicBool>> =
    std::sync::OnceLock::new();
/// Whether periodic progress lines should be emitted to stderr.
/// Set by `--progress` CLI flag. Read by SAT, SMT, and CHC solve paths.
pub(crate) static PROGRESS_ENABLED: AtomicBool = AtomicBool::new(false);
/// Whether aggressive model minimization is enabled (#8297).
/// Set by `--minimize-model` CLI flag. Read by executor creation paths.
pub(crate) static MINIMIZE_MODEL_ENABLED: AtomicBool = AtomicBool::new(false);
/// Whether strict proof mode is enabled (#8555).
/// Set by `--strict-proofs` CLI flag. Read by CHC auto-detect path.
pub(crate) static STRICT_PROOFS_ENABLED: AtomicBool = AtomicBool::new(false);
/// Whether fail-closed self-check mode is enabled.
/// Set by `--self-check` CLI flag. Read by executor creation paths
/// (`new_executor`). In this mode AY emits `sat` only when its own
/// independent model evaluator confirms every assertion is true, and `unsat`
/// only when a refutation proof is produced; otherwise it returns a sound
/// `unknown`. The point is that AY checks its own answers — no external oracle
/// is needed to trust a `sat`/`unsat` it emits under `--self-check`.
pub(crate) static SELF_CHECK_ENABLED: AtomicBool = AtomicBool::new(false);
/// Directory to write per-theory diagnostic firewall Lean lemmas into, set by
/// `--emit-firewall-lean <DIR>`. Each file covers one locally groundable theory
/// obligation (datatypes / LIA / EUF / arrays-ROW2 / strings); these files do
/// not by themselves certify the solver's complete UNSAT derivation.
pub(crate) static FIREWALL_LEAN_DIR: std::sync::OnceLock<PathBuf> = std::sync::OnceLock::new();
/// Whether the diagnostic firewall result gate is enabled (`--verify-firewall`).
///
/// Current firewall files prove local theory obligations but are not bound to
/// the complete query/refutation, so every current internal UNSAT is
/// conservatively downgraded to `unknown` after diagnostics. Read on the SMT
/// check-sat result path in `run.rs`.
pub(crate) static VERIFY_FIREWALL_ENABLED: AtomicBool = AtomicBool::new(false);
/// Whether post-solve proof auto-verification is enabled (#8771).
///
/// ON BY DEFAULT (batteries included): every emitted DRAT/LRAT proof is
/// re-checked by AY's built-in checker after UNSAT, in both debug and release,
/// so a bad proof is caught automatically. Cleared by `--no-verify-proof` or
/// `--competition` (speed opt-out); an explicit `--verify-proof` forces it on.
/// Read by `dimacs.rs` after UNSAT and before exit.
pub(crate) static VERIFY_PROOF_ENABLED: AtomicBool = AtomicBool::new(true);
/// Whether the user explicitly requested `--verify-proof` (as opposed to the
/// default-on DRAT/LRAT auto-check). Non-DIMACS routes use this distinction to
/// reject a verification promise they cannot fulfill without disabling their
/// fast paths merely because the default auto-check is enabled.
pub(crate) static EXPLICIT_VERIFY_PROOF_ENABLED: AtomicBool = AtomicBool::new(false);
/// Whether `--lean-verify` is active (#8773, Phase 1 thin wrapper).
///
/// Set by the CLI flag. Read by `dimacs.rs` after UNSAT + proof emission to
/// invoke the Lean verifier on the `.lean4` proof file via the ay-lean-bridge
/// canonical path.
pub(crate) static LEAN_VERIFY_ENABLED: AtomicBool = AtomicBool::new(false);
/// Optional explicit path to the `lean` binary for `--lean-verify`.
/// Set by `--lean-path`. When None, PATH is searched.
pub(crate) static LEAN_BINARY_PATH: std::sync::OnceLock<PathBuf> = std::sync::OnceLock::new();
/// Whether human-readable explanation mode is enabled (#8693).
/// Set by `--explain` CLI flag. Read by run.rs after solve completes.
pub(crate) static EXPLAIN_ENABLED: AtomicBool = AtomicBool::new(false);
/// Whether the Phase 1 reason-code output should be JSON instead of plain text (#8693).
/// Set by `--explain-format json`. Only consulted when `EXPLAIN_ENABLED` is set.
pub(crate) static EXPLAIN_FORMAT_JSON: AtomicBool = AtomicBool::new(false);
/// Whether `--z3-mode` transcript compatibility is active.
///
/// This is intentionally transcript-only: it suppresses AY provenance/details
/// that break Z3 transcript comparisons, but does not downgrade solver
/// behavior or change default output.
pub(crate) static Z3_MODE_ENABLED: AtomicBool = AtomicBool::new(false);
/// Whether z3's `-model` was requested. In the non-incremental path a literal
/// `(get-model)` is appended to the input; the incremental/streaming path
/// cannot pre-inject without deadlocking a live `-in` caller, so it emits the
/// model inline after each satisfiable `check-sat` (run.rs execute_and_print).
pub(crate) static Z3_MODEL_ENABLED: AtomicBool = AtomicBool::new(false);
/// Whether `-q`/`--quiet` commentary suppression is active on `solve`.
///
/// Suppresses only AY's stderr *provenance commentary* — the `c ay.session.*`
/// markers, the `c --- SAT applied run ---` policy preamble, and proof-write
/// announcements. Distinct from `--z3-mode`: it does NOT touch stdout, proof
/// emission, exit codes, error messages, or `--stats` output.
pub(crate) static QUIET_ENABLED: AtomicBool = AtomicBool::new(false);

/// True when `-q`/`--quiet` commentary suppression is active. Read at every
/// AY stderr-commentary emission site so the suppression is centralized.
pub(crate) fn quiet_enabled() -> bool {
    QUIET_ENABLED.load(Ordering::Relaxed)
}
/// JSONL progress file path (#8155 subtask 7b).
/// Set by `--progress-json` CLI flag. Read by executor and DIMACS path to
/// attach [`ay_sat::json_observer::JsonProgressObserver`] to SAT solvers.
pub(crate) static PROGRESS_JSON_PATH: std::sync::OnceLock<String> = std::sync::OnceLock::new();

/// SAT techniques disabled via `--disable` CLI flag (#8331).
/// Populated once by `run_solve()`. Read by `configure_dimacs_solver()` to
/// call `solver.disable_technique()` directly, replacing the old env-var bridge.
pub(crate) static DISABLED_SAT_TECHNIQUES: std::sync::OnceLock<Vec<ay_sat::SatTechnique>> =
    std::sync::OnceLock::new();

/// Debug channels activated via `--debug` CLI flag (#8331).
/// Populated once by `run_solve()` into both this local cache and the
/// global `ay_core::GLOBAL_DEBUG_CONFIG` for library consumers.
pub(crate) static ACTIVE_DEBUG_CHANNELS: std::sync::OnceLock<ay_core::DebugConfig> =
    std::sync::OnceLock::new();

// ---------------------------------------------------------------------------
// Internal enums used by run.rs, dimacs.rs, chc_runner.rs, tests
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ChcMode {
    None,
    Chc,
    Portfolio,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ExecutionMode {
    Interactive,
    PortfolioFile,
    AutoFile,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ProofFormat {
    Drat,
    Lrat,
    Lean4,
    Alethe,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ProofConfig {
    pub(crate) path: String,
    pub(crate) format: ProofFormat,
    pub(crate) binary: bool,
    /// Optional Lean 4 `proof-artifact-v1` JSON sidecar path.
    pub(crate) artifact_path: Option<String>,
    /// True when this proof file was synthesized by `--verify-proof` rather
    /// than requested by the user via `--proof`. Temp proofs are deleted
    /// after verification completes (#8771).
    pub(crate) is_temp: bool,
    /// True when this proof config was synthesized for default proof-artifact
    /// emission (no explicit `--proof`) on a supported file input.
    ///
    /// A synthesized default differs from an explicit `--proof` in its failure
    /// posture: outside a mandatory proof gate, failure to render the default
    /// certificate warns and leaves the verdict standing; under
    /// `--strict-proofs` or `--self-check`, the uncertified result instead
    /// downgrades to `unknown`. An explicit user output failure remains fatal.
    /// This marker also lets logic-specific runners (e.g. CHC) retarget the
    /// path/format to their native certificate kind, since the default path is
    /// chosen from the input extension before the logic is known.
    pub(crate) synthesized_default: bool,
    /// True when the user selected a format-bearing flag (`--proof-format` or
    /// one of the legacy `--drat`/`--lrat` flags), rather than letting AY infer
    /// the format from `--proof FILE`.
    ///
    /// CHC has its own `ay-chc-cert` text format, which is not represented by
    /// the DIMACS/SMT `--proof-format` enum. The CHC preflight uses this marker
    /// to reject an explicit, incompatible format before solving.
    pub(crate) format_was_explicit: bool,
}

impl ProofConfig {
    fn from_path(path: String) -> Self {
        let (format, binary) = infer_proof_format(&path);
        Self {
            path,
            format,
            binary,
            artifact_path: None,
            is_temp: false,
            synthesized_default: false,
            format_was_explicit: false,
        }
    }

    fn new(path: String, format: ProofFormat, binary: bool) -> Self {
        Self {
            path,
            format,
            binary,
            artifact_path: None,
            is_temp: false,
            synthesized_default: false,
            format_was_explicit: true,
        }
    }

    /// Construct a temporary proof config (e.g. synthesized by
    /// `--verify-proof` without an explicit `--proof`). The file at `path`
    /// will be deleted after post-solve verification runs.
    fn new_temp(path: String, format: ProofFormat, binary: bool) -> Self {
        Self {
            path,
            format,
            binary,
            artifact_path: None,
            is_temp: true,
            synthesized_default: false,
            format_was_explicit: false,
        }
    }

    /// Construct the default proof-artifact config for a supported file input
    /// when no explicit `--proof` is given and emission is not opted out
    /// (`--no-proof` / `--z3-mode`).
    fn new_default(path: String, format: ProofFormat) -> Self {
        Self {
            path,
            format,
            binary: false,
            artifact_path: None,
            is_temp: false,
            synthesized_default: true,
            format_was_explicit: false,
        }
    }

    fn with_artifact_path(mut self, artifact_path: Option<String>) -> Self {
        self.artifact_path = artifact_path;
        self
    }
}

fn infer_proof_format(path: &str) -> (ProofFormat, bool) {
    let ext = std::path::Path::new(path)
        .extension()
        .and_then(|e| e.to_str())
        .unwrap_or("");
    match ext {
        "drat" => (ProofFormat::Drat, false),
        "dratb" => (ProofFormat::Drat, true),
        "lrat" => (ProofFormat::Lrat, false),
        "lratb" => (ProofFormat::Lrat, true),
        "lean4" | "lean" => (ProofFormat::Lean4, false),
        // SR (substitution-redundancy) proofs ride the DRAT writer surface: the
        // DSR `a`-lines (`clause… witness… 0`, with the σ substitution witness) are
        // emitted by `DratWriter::add_sr` (#8011 SR route). Text-form DSR for `.sr`,
        // binary for `.srb`. Elaborated externally by dsr-trim.
        "sr" | "dsr" => (ProofFormat::Drat, false),
        "srb" | "dsrb" => (ProofFormat::Drat, true),
        // DPR (PR with witness) also rides the DRAT writer surface: the PR
        // `a`-lines are emitted by `DratWriter::add_pr` (#8011 PR route) and
        // elaborated externally by dpr-trim → cake_lpr (a SAT-COMP 2026
        // sanctioned checker pipeline). Previously `.dpr` fell through to the
        // unknown-extension Alethe default, which silently produced an
        // unusable proof for a DIMACS solve.
        "dpr" => (ProofFormat::Drat, false),
        "dprb" => (ProofFormat::Drat, true),
        "alethe" | "chccert" => (ProofFormat::Alethe, false),
        other => {
            safe_eprintln!(
                "c Warning: unknown proof extension '.{other}', defaulting to Alethe format"
            );
            (ProofFormat::Alethe, false)
        }
    }
}

// ---------------------------------------------------------------------------
// CLI wrapper enums — compile-time bridge to canonical types
// ---------------------------------------------------------------------------

/// CLI wrapper for [`ay_sat::SatTechnique`].
///
/// Every variant here maps 1:1 to a canonical variant. The `From` impl uses
/// an exhaustive match — adding a canonical variant without a CLI counterpart
/// is a compile error.
#[derive(Debug, Clone, Copy, PartialEq, Eq, clap::ValueEnum)]
#[clap(rename_all = "kebab-case")]
enum CliSatTechnique {
    Preprocess,
    Bve,
    Probe,
    Congruence,
    Decompose,
    Sweep,
    Condition,
    Vivify,
    Subsume,
    Bce,
    Cce,
    Transred,
    Htr,
    Gate,
    Factor,
    Sbva,
    Shrink,
    Elimfast,
    Inprocess,
    Flip,
    Jit,
    Walk,
    Warmup,
}

impl From<CliSatTechnique> for ay_sat::SatTechnique {
    fn from(cli: CliSatTechnique) -> Self {
        match cli {
            CliSatTechnique::Preprocess => Self::Preprocess,
            CliSatTechnique::Bve => Self::Bve,
            CliSatTechnique::Probe => Self::Probe,
            CliSatTechnique::Congruence => Self::Congruence,
            CliSatTechnique::Decompose => Self::Decompose,
            CliSatTechnique::Sweep => Self::Sweep,
            CliSatTechnique::Condition => Self::Condition,
            CliSatTechnique::Vivify => Self::Vivify,
            CliSatTechnique::Subsume => Self::Subsume,
            CliSatTechnique::Bce => Self::Bce,
            CliSatTechnique::Cce => Self::Cce,
            CliSatTechnique::Transred => Self::Transred,
            CliSatTechnique::Htr => Self::Htr,
            CliSatTechnique::Gate => Self::Gate,
            CliSatTechnique::Factor => Self::Factor,
            CliSatTechnique::Sbva => Self::Sbva,
            CliSatTechnique::Shrink => Self::Shrink,
            CliSatTechnique::Elimfast => Self::Elimfast,
            CliSatTechnique::Inprocess => Self::Inprocess,
            CliSatTechnique::Flip => Self::Flip,
            CliSatTechnique::Jit => Self::Jit,
            CliSatTechnique::Walk => Self::Walk,
            CliSatTechnique::Warmup => Self::Warmup,
        }
    }
}

/// CLI wrapper for [`ay_core::DebugChannel`].
///
/// Exhaustive `From` match — adding a canonical variant without updating
/// this enum is a compile error.
#[derive(Debug, Clone, Copy, clap::ValueEnum)]
#[clap(rename_all = "kebab-case")]
enum CliDebugChannel {
    Theory,
    Lia,
    LiaCheck,
    LiaBranch,
    LiaNelsonOppen,
    Gcd,
    GcdTab,
    Dioph,
    Hnf,
    Mod,
    Enum,
    Patch,
    Lra,
    LraBounds,
    LraAssert,
    LraReset,
    LraNelsonOppen,
    LraForced,
    Intern,
    FarkasRow,
    Cube,
    Gomory,
    Euf,
    EufNelsonOppen,
    NelsonOppen,
    Nia,
    Nra,
    Fp,
    Dt,
    BoolIte,
    StringCore,
    Dpll,
    Sync,
    Model,
    VarSubst,
    Verify,
    IteEq,
    ConcatEq,
    Auflia,
    IteConditions,
    Linking,
    Preprocessed,
    SatCongruence,
    TransredTrace,
    TransredClause,
    Unknown,
    Prop,
    ChcSmt,
    Algebraic,
    ArrayAxiomSite,
    AufliaFix,
    Row2Components,
    Regex,
    EufFallback,
    Pcr,
    AufliaFixSummary,
}

impl From<CliDebugChannel> for ay_core::DebugChannel {
    fn from(cli: CliDebugChannel) -> Self {
        match cli {
            CliDebugChannel::Theory => Self::Theory,
            CliDebugChannel::Lia => Self::Lia,
            CliDebugChannel::LiaCheck => Self::LiaCheck,
            CliDebugChannel::LiaBranch => Self::LiaBranch,
            CliDebugChannel::LiaNelsonOppen => Self::LiaNelsonOppen,
            CliDebugChannel::Gcd => Self::Gcd,
            CliDebugChannel::GcdTab => Self::GcdTab,
            CliDebugChannel::Dioph => Self::Dioph,
            CliDebugChannel::Hnf => Self::Hnf,
            CliDebugChannel::Mod => Self::Mod,
            CliDebugChannel::Enum => Self::Enum,
            CliDebugChannel::Patch => Self::Patch,
            CliDebugChannel::Lra => Self::Lra,
            CliDebugChannel::LraBounds => Self::LraBounds,
            CliDebugChannel::LraAssert => Self::LraAssert,
            CliDebugChannel::LraReset => Self::LraReset,
            CliDebugChannel::LraNelsonOppen => Self::LraNelsonOppen,
            CliDebugChannel::LraForced => Self::LraForced,
            CliDebugChannel::Intern => Self::Intern,
            CliDebugChannel::FarkasRow => Self::FarkasRow,
            CliDebugChannel::Cube => Self::Cube,
            CliDebugChannel::Gomory => Self::Gomory,
            CliDebugChannel::Euf => Self::Euf,
            CliDebugChannel::EufNelsonOppen => Self::EufNelsonOppen,
            CliDebugChannel::NelsonOppen => Self::NelsonOppen,
            CliDebugChannel::Nia => Self::Nia,
            CliDebugChannel::Nra => Self::Nra,
            CliDebugChannel::Fp => Self::Fp,
            CliDebugChannel::Dt => Self::Dt,
            CliDebugChannel::BoolIte => Self::BoolIte,
            CliDebugChannel::StringCore => Self::StringCore,
            CliDebugChannel::Dpll => Self::Dpll,
            CliDebugChannel::Sync => Self::Sync,
            CliDebugChannel::Model => Self::Model,
            CliDebugChannel::VarSubst => Self::VarSubst,
            CliDebugChannel::Verify => Self::Verify,
            CliDebugChannel::IteEq => Self::IteEq,
            CliDebugChannel::ConcatEq => Self::ConcatEq,
            CliDebugChannel::Auflia => Self::Auflia,
            CliDebugChannel::IteConditions => Self::IteConditions,
            CliDebugChannel::Linking => Self::Linking,
            CliDebugChannel::Preprocessed => Self::Preprocessed,
            CliDebugChannel::SatCongruence => Self::SatCongruence,
            CliDebugChannel::TransredTrace => Self::TransredTrace,
            CliDebugChannel::TransredClause => Self::TransredClause,
            CliDebugChannel::Unknown => Self::Unknown,
            CliDebugChannel::Prop => Self::Prop,
            CliDebugChannel::ChcSmt => Self::ChcSmt,
            CliDebugChannel::Algebraic => Self::Algebraic,
            CliDebugChannel::ArrayAxiomSite => Self::ArrayAxiomSite,
            CliDebugChannel::AufliaFix => Self::AufliaFix,
            CliDebugChannel::Row2Components => Self::Row2Components,
            CliDebugChannel::Regex => Self::Regex,
            CliDebugChannel::EufFallback => Self::EufFallback,
            CliDebugChannel::Pcr => Self::Pcr,
            CliDebugChannel::AufliaFixSummary => Self::AufliaFixSummary,
        }
    }
}

/// CLI wrapper for proof format selection via `--proof-format`.
#[derive(Debug, Clone, Copy, clap::ValueEnum)]
#[clap(rename_all = "kebab-case")]
enum CliProofFormat {
    Drat,
    Lrat,
    Lean4,
    Alethe,
}

impl From<CliProofFormat> for ProofFormat {
    fn from(cli: CliProofFormat) -> Self {
        match cli {
            CliProofFormat::Drat => Self::Drat,
            CliProofFormat::Lrat => Self::Lrat,
            CliProofFormat::Lean4 => Self::Lean4,
            CliProofFormat::Alethe => Self::Alethe,
        }
    }
}

/// CLI wrapper for [`explain_reason::ExplainFormat`] (#8693 Phase 1).
#[derive(Debug, Clone, Copy, Default, clap::ValueEnum)]
#[clap(rename_all = "kebab-case")]
enum CliExplainFormat {
    #[default]
    Plain,
    Json,
}

/// CLI wrapper for solution visualization output (#8702).
#[derive(Debug, Clone, Copy, clap::ValueEnum)]
#[clap(rename_all = "kebab-case")]
enum CliVisualizationFormat {
    Ascii,
    Svg,
}

impl From<CliVisualizationFormat> for ay::VisualizationFormat {
    fn from(format: CliVisualizationFormat) -> Self {
        match format {
            CliVisualizationFormat::Ascii => Self::Ascii,
            CliVisualizationFormat::Svg => Self::Svg,
        }
    }
}

// ---------------------------------------------------------------------------
// Clap top-level structures
// ---------------------------------------------------------------------------

#[derive(Parser)]
#[command(
    name = "ay",
    about = "AY: A proof-oriented constraint solver in Rust",
    version = build_info::CLAP_VERSION,
    long_version = build_info::CLAP_LONG_VERSION,
    long_about = None,
    after_help = "\
File format auto-detection:\n  \
  .cnf / 'p cnf'      DIMACS CNF (SAT competition format)\n  \
  (set-logic HORN)    CHC (Horn clauses, PDR/IC3 solver)\n  \
  Otherwise           SMT-LIB 2.6\n\n\
Z3-compatible options (preprocessed before parsing):\n  \
  -t:N                Timeout in milliseconds\n  \
  -T:N                Timeout in seconds\n  \
  -memory:N           Memory limit in megabytes\n  \
  -smt2               Auto-detected (accepted, dropped)\n  \
  -dimacs             DIMACS mode (accepted, auto-detected)\n  \
  -in                 Read from stdin\n  \
  -file:PATH          Solve PATH\n  \
  -model              Print model for satisfiable SMT-LIB input\n  \
  -st                 Print statistics\n  \
  -nw                 Disable warnings (accepted, dropped)\n  \
  -v:N                Verbosity level (accepted, dropped)\n  \
  -p, -pd             List ay-supported Z3-style parameters\n  \
  -pm[:NAME]          List ay-supported Z3-style module parameters\n  \
  -pp:NAME            Describe a supported Z3-style parameter\n  \
  --z3-mode           Suppress AY transcript provenance for Z3 comparisons\n  \
  --                  End option parsing; useful for files named '-...'\n  \
  timeout=N           Timeout in milliseconds\n  \
  memory_max_size=N   Memory limit in megabytes\n  \
  stats=true          Print statistics\n  \
  dump_models=true, dump-models=true\n  \
                      Print model for satisfiable SMT-LIB input\n  \
  ctrl_c=true|false, ctrl-c=true|false\n  \
                      Accepted interrupt compatibility no-op\n  \
  type-check=true|false, well-sorted-check=true|false\n  \
                      Accepted type-check compatibility no-ops\n  \
  model.v2=true|false, model.compact=true|false,\n  \
  pp.single-line=true|false, pp.bv-literals=true|false,\n  \
  pp.fixed-indent=true|false\n  \
                      Accepted model/pretty-printer compatibility no-ops\n  \
  trace=true|false    Accepted trace compatibility no-op\n  \
  trace_file_name=PATH\n  \
                      Accepted trace-file compatibility no-op\n  \
  fp.engine=spacer    CHC engine (accepted, dropped)\n  \
  -?, -version        Help/version aliases\n\n\
Unsupported Z3 options are rejected explicitly instead of emulated:\n  \
  -dl, -wcnf, -opb, -lp, -log\n  \
  -tactics[:NAME], -simplifiers[:NAME], -probes, -pmmd:NAME",
)]
struct Cli {
    #[command(subcommand)]
    command: Option<Command>,
}

#[allow(clippy::large_enum_variant)]
#[derive(clap::Subcommand)]
enum Command {
    /// Solve an SMT-LIB2, DIMACS CNF, or CHC formula (default subcommand)
    Solve(SolveArgs),
    /// Verify DRAT/LRAT proofs
    #[command(subcommand)]
    Check(cmd_check::CheckCommand),
    /// Run and score reproducible benchmark evaluations
    #[command(subcommand, hide = true)]
    Bench(cmd_bench::BenchCommand),
    /// Manage benchmark corpora published as GitHub release assets
    #[command(subcommand, hide = true)]
    Corpus(cmd_corpus::CorpusCommand),
    /// Build, verify, and locate external tools from pinned recipes
    #[command(hide = true)]
    Tool(cmd_tool::ToolArgs),
    /// Competition JIT matrix, gate, release, and ROI probe tooling
    #[command(subcommand, hide = true)]
    CompetitionJit(cmd_competition_jit::CompetitionJitCommand),
    /// Checked-in CI/release gates
    #[command(subcommand, hide = true)]
    Gate(cmd_gate::GateCommand),
    #[cfg(ay_internal_tools)]
    /// Downstream consumer smoke orchestration and evidence validation
    #[command(name = "consumer-smoke", subcommand, hide = true)]
    ConsumerSmoke(cmd_consumer_smoke::ConsumerSmokeCommand),
    /// FlatZinc / MiniZinc integration
    #[command(subcommand)]
    Flatzinc(cmd_flatzinc::FlatzincCommand),
    /// Pseudo-Boolean solving
    #[command(subcommand)]
    Pb(cmd_pb::PbCommand),
    /// MaxSAT solving
    #[command(subcommand)]
    Maxsat(cmd_maxsat::MaxSatCommand),
    /// Quantified Boolean Formula solving
    #[command(subcommand)]
    Qbf(cmd_qbf::QbfCommand),
    /// Linear and mixed-integer programming (MPS / LP formats)
    #[command(subcommand)]
    Lp(cmd_lp::LpCommand),
    /// Interactive tutorial
    Tutorial(cmd_tutorial::TutorialArgs),
    /// SMT-LIB2 AST simplification
    Simplify(cmd_simplify::SimplifyArgs),
    /// Bisect ay feature-disable CLI flags to localize a soundness bug
    #[command(hide = true)]
    Bisect(cmd_bisect::BisectCommand),
    /// Enumerate all satisfying assignments of a DIMACS CNF formula
    Allsat(cmd_allsat::AllSatArgs),
    /// Emit Model Counting Competition output for exact unweighted MC/PMC CNF
    #[command(name = "model-count")]
    ModelCount(cmd_model_count::ModelCountArgs),
    /// Diagnose a wrong-answer (runs --validate, compares against z3, surfaces --explain)
    Diagnose(cmd_diagnose::DiagnoseCommand),
    /// Run the release-readiness gate
    #[command(name = "launch-gate", hide = true)]
    LaunchGate(cmd_launch::HnGateArgs),
    /// Release evidence generation and verification
    #[command(subcommand, hide = true)]
    Release(cmd_release::ReleaseCommand),
    /// Generate launch benchmark packet metadata sidecars
    #[command(name = "launch-packet", hide = true)]
    LaunchPacket(cmd_launch_packet::LaunchPacketCommand),
    /// Audit the development tree's measured Z3-compatibility surface
    #[command(name = "z3-audit", hide = true)]
    Z3Audit(cmd_z3_audit::Z3AuditArgs),
    /// Generate competition submission skeletons
    #[command(subcommand, hide = true)]
    Submission(cmd_submission::SubmissionCommand),
    /// Audit AY's readiness as the SMT backend for Creusot/Why3 & Verus
    #[command(name = "verifier-audit", hide = true)]
    VerifierAudit(cmd_verifier_audit::VerifierAuditArgs),
    /// Discover, run, and gate the repo's indexed scripts
    #[command(subcommand, long_about = cmd_scripts::GROUP_LONG_ABOUT, hide = true)]
    Scripts(cmd_scripts::ScriptsCommand),
}

/// Arguments for `ay solve` (the default subcommand).
#[derive(clap::Args, Default)]
#[command(after_help = "\
SAT primary path:
  ay solve --sat-variant default FILE.cnf
  ay solve --sat-variant default --proof proof.lrat FILE.cnf

Use `--help=full` to show advanced debugging and tuning options.")]
struct SolveArgs {
    /// Input file (SMT-LIB2, DIMACS CNF, or CHC)
    file: Option<PathBuf>,

    /// Read from stdin
    #[arg(long)]
    stdin: bool,

    /// Suppress AY's stderr provenance commentary.
    ///
    /// Quiets the `c ay.session.*` markers, the `c --- SAT applied run ---`
    /// policy preamble, and proof-write announcements. Does NOT change stdout,
    /// proof emission, exit codes, error messages, or `--stats` output — so a
    /// machine-parsed result stays byte-identical while the human commentary
    /// goes away. Distinct from `--z3-mode`, which reshapes the transcript for
    /// Z3 comparisons.
    #[arg(short = 'q', long = "quiet")]
    quiet: bool,

    /// Internal compatibility flag for Z3 `-model`.
    #[arg(long = "z3-model", hide = true)]
    z3_model: bool,

    /// Opt in to a clean Z3-compatible transcript surface.
    ///
    /// Default AY output keeps richer provenance and diagnostics. This flag
    /// only reshapes visible transcript details for downstream tools that
    /// compare against Z3-style stdout/stderr.
    #[arg(long = "z3-mode")]
    z3_mode: bool,

    /// Internal compatibility carrier for unsupported Z3 `key=value` params.
    #[arg(long = "unsupported-z3-param", hide = true)]
    unsupported_z3_param: Vec<String>,

    /// Internal compatibility carrier for real Z3 `key=value` params AY accepts
    /// but does not implement. Reported on stderr, never silently dropped.
    #[arg(long = "ignored-z3-param", hide = true)]
    ignored_z3_param: Vec<String>,

    /// Internal compatibility flag for Z3 `-p`.
    #[arg(long = "z3-print-params", hide = true)]
    z3_print_params: bool,

    /// Internal compatibility flag for Z3 `-pd`.
    #[arg(long = "z3-print-param-descriptions", hide = true)]
    z3_print_param_descriptions: bool,

    /// Internal compatibility flag for Z3 `-pm[:name]`.
    #[arg(long = "z3-print-param-module", hide = true, value_name = "NAME")]
    z3_print_param_module: Option<String>,

    /// Internal compatibility flag for Z3 `-pp:name`.
    #[arg(long = "z3-print-param-description", hide = true, value_name = "NAME")]
    z3_print_param_description: Option<String>,

    /// Internal compatibility carrier for unsupported Z3 CLI options.
    #[arg(
        long = "unsupported-z3-option",
        hide = true,
        allow_hyphen_values = true
    )]
    unsupported_z3_option: Vec<String>,

    /// Force CHC solving mode
    #[arg(long)]
    chc: bool,

    /// Force CHC portfolio mode
    #[arg(long)]
    portfolio: bool,

    /// Enable verbose output
    #[arg(long)]
    verbose: bool,

    /// DEPRECATED / no-op: runtime result validation is ON BY DEFAULT now.
    /// Kept as a hidden accepted flag so existing scripts don't break. Use
    /// `--no-validate` (or `--competition`) to turn validation off.
    #[arg(long, hide = true, hide_short_help = true, hide_long_help = true)]
    validate: bool,

    /// Turn OFF the default runtime result validation (a speed opt-out).
    /// Validation is on by default (batteries included); this disables it.
    #[arg(long)]
    no_validate: bool,

    /// Competition / benchmark mode: turn the overhead "batteries" OFF for
    /// raw speed. Disables the default runtime validation, the post-solve proof
    /// re-check (`--verify-proof`), and the default proof-certificate emission
    /// (an explicit `--proof FILE` still wins). Capability/soundness defaults
    /// (all solver techniques, the always-on independent model gate, automatic
    /// engine selection) are UNCHANGED. Also implied when an official
    /// SAT-competition wrapper env signal is present, so existing competition
    /// harnesses stay on the fast path automatically.
    #[arg(long)]
    competition: bool,

    /// Fail-closed self-check: only emit a result AY can verify itself.
    ///
    /// `sat` is emitted only when AY's separate in-tree model evaluator confirms
    /// every assertion. `unsat` requires a nonempty refutation accepted by AY's
    /// strict semantic checker, with every reachable assumption bound to the
    /// active problem. Any answer AY cannot self-check becomes `unknown`. This
    /// shares AY's trust boundary; replay with a separately implemented checker
    /// remains the independent acceptance path.
    #[arg(long = "self-check")]
    self_check: bool,

    /// Strict proof diagnostic and terminal-trust screen
    ///
    /// Uses AY's strict semantic checker while constructing SMT proofs and
    /// downgrades a terminal Trust-backed `unsat` to `unknown`. Other checker
    /// failures remain diagnostics. This is neither the fail-closed
    /// `--self-check` gate nor independent external replay.
    #[arg(long)]
    strict_proofs: bool,

    /// Write diagnostic firewall Lean lemmas into DIR on UNSAT (one file per
    /// groundable local theory obligation: datatypes / LIA / EUF / arrays-ROW2
    /// / strings). These lemmas audit covered theory steps but do not certify
    /// the complete UNSAT derivation. Requires a persistent Alethe proof,
    /// either from `--proof FILE.alethe` or default SMT-LIB file emission.
    #[arg(long = "emit-firewall-lean", value_name = "DIR")]
    emit_firewall_lean: Option<PathBuf>,

    /// Fail-closed diagnostic firewall gate for AY's own `unsat`.
    ///
    /// On UNSAT, AY reconstructs the per-theory "firewall" Lean proofs, prepends
    /// the verified theorem sources embedded at build time, and kernel-checks
    /// each with the real Lean toolchain. A mandatory axiom audit permits only
    /// `propext`, `Classical.choice`, and `Quot.sound`. Current files cover local
    /// theory obligations but are not bound to the complete query/refutation,
    /// so current UNSAT results always downgrade to sound `unknown` after the
    /// diagnostic checks. No env vars are needed; the build source tree supplies
    /// the pinned Lean toolchain project and `lake` is auto-located.
    /// Supported only by the SMT-LIB DPLL(T) route; DIMACS, CHC/fixedpoint, and
    /// forced `--chc`/`--portfolio` routes are rejected rather than bypassing it.
    #[arg(long = "verify-firewall")]
    verify_firewall: bool,

    /// Print periodic progress lines to stderr (~5s)
    #[arg(long)]
    progress: bool,

    /// Write JSONL progress events to file
    #[arg(long, value_name = "FILE")]
    progress_json: Option<PathBuf>,

    /// Timeout in milliseconds
    #[arg(short = 't', long)]
    timeout: Option<u64>,

    /// Memory limit in megabytes (default: auto-detect from physical RAM; 0 = unlimited)
    #[arg(long)]
    memory: Option<u64>,

    /// Parallel portfolio solver threads (DIMACS SAT only)
    #[arg(long, value_name = "N")]
    parallel: Option<usize>,

    /// Cube-and-conquer lookahead depth
    #[arg(
        long,
        value_name = "DEPTH",
        hide_short_help = true,
        hide_long_help = true
    )]
    cube_and_conquer: Option<usize>,

    /// Print statistics to stderr
    #[arg(long, visible_alias = "st")]
    stats: bool,

    /// Print statistics as JSON to stderr
    #[arg(long)]
    stats_json: bool,

    /// Write proof certificate on UNSAT (format inferred from extension)
    ///
    /// Member of the mutually-exclusive `proof_output` group together with the
    /// hidden legacy `--drat`/`--drat-binary`/`--lrat`/`--lrat-binary` flags,
    /// so exactly one proof-output destination can be selected.
    #[arg(long, value_name = "FILE", group = "proof_output")]
    proof: Option<PathBuf>,

    /// Proof format (with --proof; overrides extension inference)
    #[arg(long, value_enum, requires = "proof")]
    proof_format: Option<CliProofFormat>,

    /// Write binary DRAT/LRAT proof (with --proof).
    /// SMT Alethe and CHC certificate routes reject binary output.
    #[arg(long, requires = "proof")]
    proof_binary: bool,

    /// Write a Lean 4 proof-artifact-v1 JSON envelope for a DIMACS/SMT proof.
    ///
    /// The envelope is emitted only for UNSAT proof-producing runs and records
    /// ay build provenance, input/proof hashes, proof format, theory metadata,
    /// and the proof payload in a schema accepted by Lean 4's artifact parser.
    /// CHC certificates do not yet have this envelope and reject the request.
    #[arg(
        long,
        value_name = "FILE",
        help_heading = "Proof verification",
        conflicts_with = "no_proof"
    )]
    proof_artifact: Option<PathBuf>,

    /// Opt out of default proof-artifact emission on supported UNSAT paths.
    ///
    /// For supported file inputs, proof emission is ON BY DEFAULT: after an
    /// UNSAT result, ay attempts to write a proof artifact next to the input —
    /// DRAT for DIMACS (`<input>.drat`), Alethe for SMT (`<input>.alethe`), or
    /// an ay-chc-cert for CHC (`<input>.chccert`). Support depends on the solver
    /// path, theory, and format. Outside `--strict-proofs`/`--self-check`, a
    /// default-emission failure warns without changing the solver verdict;
    /// those gates instead fail closed. Treat an artifact as independently
    /// certified only after its intended checker accepts it. Pass `--no-proof`
    /// to suppress the default (e.g. when proof I/O adds benchmark overhead),
    /// or select an explicit `--proof FILE`; clap rejects combining the two.
    #[arg(long, help_heading = "Proof verification", conflicts_with = "proof")]
    no_proof: bool,

    /// Re-check the emitted proof after UNSAT using the built-in DRAT/LRAT
    /// checker. If no `--proof` path is given for DIMACS, a temporary DRAT file
    /// is written and deleted after verification. Default: ON in all builds
    /// (batteries included), turned off by `--no-verify-proof` or
    /// `--competition`; an explicit proof opt-out (`--no-proof` / `--z3-mode`)
    /// also suppresses the temp-proof synthesis this implies (re-checking a
    /// certificate the user declined is incoherent, and the synthesis enables
    /// costly in-solver proof tracking). A rejected explicitly required proof
    /// is an error (exit code 1); failure of an opportunistic synthesized
    /// default proof warns and preserves the solver verdict unless
    /// `--strict-proofs` or `--self-check` makes certification mandatory.
    /// Explicit `--verify-proof` is rejected for SMT-LIB/Alethe and CHC inputs
    /// because this checker supports DIMACS DRAT/LRAT only; it is never
    /// silently treated as verification.
    #[arg(long, help_heading = "Proof verification")]
    verify_proof: bool,

    /// Explicitly disable `--verify-proof`.
    #[arg(
        long,
        help_heading = "Proof verification",
        conflicts_with = "verify_proof"
    )]
    no_verify_proof: bool,

    /// After emitting a Lean4 proof via `--proof FILE.lean4`, invoke the
    /// `lean` binary to kernel-check the proof.
    ///
    /// This is a stricter variant of `--verify-proof`: rather than using ay's
    /// built-in DRAT/LRAT checker, it routes the emitted theorem through Lean.
    /// Requires `--proof FILE.lean4` (or `--proof-format lean4`). Exit codes:
    /// 20 only when Lean accepts the proof; 2 when Lean rejects it, cannot run,
    /// or the requested proof is not Lean4. An unfulfilled explicit kernel
    /// check never publishes UNSAT.
    #[arg(long, help_heading = "Proof verification", requires = "proof")]
    lean_verify: bool,

    /// Path to the `lean` binary for `--lean-verify` (default: PATH lookup).
    #[arg(
        long,
        value_name = "PATH",
        help_heading = "Proof verification",
        requires = "lean_verify"
    )]
    lean_path: Option<PathBuf>,

    /// Replay decision trace
    #[arg(
        long,
        value_name = "FILE",
        hide_short_help = true,
        hide_long_help = true
    )]
    replay: Option<PathBuf>,

    /// Line-by-line stdin (for incremental solvers)
    #[arg(long)]
    incremental: bool,

    /// Disable SAT techniques (comma-separated)
    #[arg(
        long,
        value_enum,
        value_delimiter = ',',
        hide_short_help = true,
        hide_long_help = true
    )]
    disable: Vec<CliSatTechnique>,

    /// Enable debug channels (comma-separated)
    #[arg(
        long,
        value_enum,
        value_delimiter = ',',
        hide_short_help = true,
        hide_long_help = true
    )]
    debug: Vec<CliDebugChannel>,

    // -- SAT feature disable flags (common conveniences; see --disable for the full list) --
    /// Disable bounded variable elimination (BVE)
    #[arg(
        long,
        help_heading = "SAT disable flags",
        hide_short_help = true,
        hide_long_help = true
    )]
    no_bve: bool,

    /// Disable vivification
    #[arg(
        long,
        help_heading = "SAT disable flags",
        hide_short_help = true,
        hide_long_help = true
    )]
    no_vivify: bool,

    /// Disable failed-literal probing
    #[arg(
        long,
        help_heading = "SAT disable flags",
        hide_short_help = true,
        hide_long_help = true
    )]
    no_probe: bool,

    /// Disable subsumption
    #[arg(
        long,
        help_heading = "SAT disable flags",
        hide_short_help = true,
        hide_long_help = true
    )]
    no_subsume: bool,

    /// Disable blocked clause elimination (BCE)
    #[arg(
        long,
        help_heading = "SAT disable flags",
        hide_short_help = true,
        hide_long_help = true
    )]
    no_bce: bool,

    /// Disable inprocessing (all techniques)
    #[arg(
        long,
        help_heading = "SAT disable flags",
        hide_short_help = true,
        hide_long_help = true
    )]
    no_inprocess: bool,

    /// Disable preprocessing (all techniques)
    #[arg(
        long,
        help_heading = "SAT disable flags",
        hide_short_help = true,
        hide_long_help = true
    )]
    no_preprocess: bool,

    /// Disable congruence closure preprocessing
    #[arg(
        long,
        help_heading = "SAT disable flags",
        hide_short_help = true,
        hide_long_help = true
    )]
    no_congruence: bool,

    /// Disable cold restart
    #[arg(
        long,
        help_heading = "SAT disable flags",
        hide_short_help = true,
        hide_long_help = true
    )]
    no_cold_restart: bool,

    /// Aggressive counterexample minimization: pin BV/LIA/LRA values to 0/1
    /// where satisfiability is preserved. Produces minimal models for
    /// vulnerability analysis.
    #[arg(
        long,
        help_heading = "Explainability",
        hide_short_help = true,
        hide_long_help = true
    )]
    minimize_model: bool,

    /// Print a human-readable explanation of the solve result.
    ///
    /// For SAT: shows how each constraint is satisfied by the model values.
    /// For UNSAT: explains which constraints conflict and why, and emits a
    /// stable reason code classifying *why* UNSAT was derived (preprocessing,
    /// theory conflict, unit propagation, ...).
    #[arg(long, help_heading = "Explainability")]
    explain: bool,

    /// Output format for the `--explain` reason-code block.
    ///
    /// `plain` (default) prints alongside the existing English walk-through.
    /// `json` emits a single-line JSON object suitable for tooling consumers
    /// and suppresses the rich English block — only the reason-code JSON is
    /// printed on stdout after `unsat`.
    #[arg(long, value_enum, default_value_t = CliExplainFormat::Plain, help_heading = "Explainability")]
    explain_format: CliExplainFormat,

    /// Render recognized SAT solutions as `ascii` (default) or `svg`.
    ///
    /// Currently recognizes N-Queens (`q1..qN`) and Sudoku-style grids
    /// (`r1c1..rNcN`) from the final SAT model.
    #[arg(
        long,
        value_enum,
        num_args = 0..=1,
        require_equals = true,
        default_missing_value = "ascii",
        value_name = "FORMAT",
        help_heading = "Explainability"
    )]
    visualize: Option<CliVisualizationFormat>,

    /// Print build features and supported logics (JSON)
    #[arg(long)]
    features: bool,

    // -- Theory feature disable flags --
    /// Disable automatic bound axiom generation
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    no_bound_axioms: bool,

    /// Disable theory-level propagation
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    no_theory_propagation: bool,

    /// Disable implied bound inference
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    no_implied_bounds: bool,

    /// Disable iterative bound refinement
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    no_bound_refinement: bool,

    /// Disable BCP-inline theory checking
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    no_bcp_theory_check: bool,

    /// Disable ITE expression deferral
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    no_ite_deferral: bool,

    /// Disable inline NeedLemmas handling (use pending_split fallback)
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    no_inline_lemmas: bool,

    /// Limit Nelson-Oppen fixpoint to N rounds
    #[arg(long, value_name = "N", hide_short_help = true, hide_long_help = true)]
    max_fixpoint_rounds: Option<u64>,

    // -- Trace file flags --
    /// Write JSONL diagnostic events to file
    #[arg(
        long,
        value_name = "FILE",
        hide_short_help = true,
        hide_long_help = true
    )]
    diagnostic_file: Option<PathBuf>,

    /// Write deterministic decision sequence to file
    #[arg(
        long,
        value_name = "FILE",
        hide_short_help = true,
        hide_long_help = true
    )]
    decision_trace: Option<PathBuf>,

    /// Load solution witness for Sam Buss trick debugging
    #[arg(
        long,
        value_name = "FILE",
        hide_short_help = true,
        hide_long_help = true
    )]
    solution_file: Option<PathBuf>,

    /// Write TLA2 JSONL trace to file (CHC/SAT)
    #[arg(
        long,
        value_name = "FILE",
        hide_short_help = true,
        hide_long_help = true
    )]
    trace_file: Option<PathBuf>,

    // -- Explainability flags (#8351) --
    /// Enable clause provenance tracking (tags clauses with origin)
    #[arg(
        long,
        help_heading = "Explainability",
        hide_short_help = true,
        hide_long_help = true
    )]
    clause_provenance: bool,

    /// Dump pre-solve encoding to file (annotated DIMACS)
    #[arg(
        long,
        value_name = "FILE",
        help_heading = "Explainability",
        hide_short_help = true,
        hide_long_help = true
    )]
    dump_encoding: Option<PathBuf>,

    // NOTE (#8833): `--annotated-core`, `--model-provenance`, and
    // `--core-evolution` were previously declared here but never consumed
    // (orphan flags). The underlying Solver APIs --
    // `Solver::annotated_unsat_core()`, `Solver::model_provenance()`, and
    // `Solver::core_evolution()` -- remain available to library consumers.
    // When a binary-level explainability CLI is wired, the explainability
    // design proposes a unified `--explain` mode that replaces these
    // individual flags.
    //
    // Legacy proof flags (hidden, backward compat). All five proof-output
    // destinations (`--proof` + these four) share the mutually-exclusive
    // `proof_output` clap group, so combining any two (e.g. `--drat A --lrat B`)
    // is a parse-time error instead of one silently winning by fixed precedence
    // in `build_proof_config`.
    /// Write DRAT proof
    #[arg(long, value_name = "FILE", hide = true, group = "proof_output")]
    drat: Option<PathBuf>,
    /// Write binary DRAT proof
    #[arg(long, value_name = "FILE", hide = true, group = "proof_output")]
    drat_binary: Option<PathBuf>,
    /// Write LRAT proof
    #[arg(long, value_name = "FILE", hide = true, group = "proof_output")]
    lrat: Option<PathBuf>,
    /// Write binary LRAT proof
    #[arg(long, value_name = "FILE", hide = true, group = "proof_output")]
    lrat_binary: Option<PathBuf>,

    // -- Debug tracing / dump flags (#8726) --
    /// Dump LRA conflict details to stderr
    #[arg(
        long,
        help_heading = "Debug tracing",
        hide_short_help = true,
        hide_long_help = true
    )]
    dump_conflicts: bool,

    /// Trace external conflict reasons during SAT solving
    #[arg(
        long,
        help_heading = "Debug tracing",
        hide_short_help = true,
        hide_long_help = true
    )]
    trace_ext_conflict: bool,

    /// Enable IUC (interpolating UNSAT core) tracing
    #[arg(
        long,
        help_heading = "Debug tracing",
        hide_short_help = true,
        hide_long_help = true
    )]
    iuc_trace: bool,

    /// Hard-fail on zero-Farkas fallbacks during IUC interpolation
    #[arg(
        long,
        help_heading = "Debug tracing",
        hide_short_help = true,
        hide_long_help = true
    )]
    strict_iuc_farkas: bool,

    /// Write adaptive portfolio decision log to file
    #[arg(
        long,
        value_name = "FILE",
        help_heading = "Debug tracing",
        hide_short_help = true,
        hide_long_help = true
    )]
    decision_log: Option<PathBuf>,

    /// Export the complete current pure-QF_BV query to DIMACS (other logics fail)
    #[arg(
        long,
        value_name = "FILE",
        help_heading = "Debug tracing",
        hide_short_help = true,
        hide_long_help = true
    )]
    dump_bv_cnf: Option<PathBuf>,

    /// Dump AUFLIA assertions during theory solving
    #[arg(
        long,
        help_heading = "Debug tracing",
        hide_short_help = true,
        hide_long_help = true
    )]
    dump_auflia_assertions: bool,

    /// Maximum variable count for BVE (bounded variable elimination)
    #[arg(
        long,
        value_name = "N",
        help_heading = "Debug tracing",
        hide_short_help = true,
        hide_long_help = true
    )]
    bve_limit: Option<usize>,

    /// Override BVE round count for bisection / debugging
    #[arg(
        long,
        value_name = "N",
        help_heading = "Debug tracing",
        hide_short_help = true,
        hide_long_help = true
    )]
    bve_max_rounds: Option<usize>,

    /// Enable BVE tracing (per-elimination log output)
    #[arg(
        long,
        help_heading = "Debug tracing",
        hide_short_help = true,
        hide_long_help = true
    )]
    bve_trace: bool,

    // -- DPLL diagnostic / trace flags (#8726 part 2) --
    /// Write DPLL(T) diagnostic JSONL to FILE
    #[arg(
        long,
        value_name = "FILE",
        help_heading = "Debug tracing",
        hide_short_help = true,
        hide_long_help = true
    )]
    dpll_diagnostic_file: Option<PathBuf>,

    /// Enable DPLL(T) diagnostic JSONL to an auto-generated tmp path
    /// Use `--dpll-diagnostic-file` for an explicit path.
    #[arg(
        long,
        help_heading = "Debug tracing",
        hide_short_help = true,
        hide_long_help = true
    )]
    dpll_diagnostic: bool,

    /// Write a single-query SMT-LIB FILE's DPLL(T) decision trace to FILE
    #[arg(
        long,
        value_name = "FILE",
        help_heading = "Debug tracing",
        hide_short_help = true,
        hide_long_help = true
    )]
    dpll_trace_file: Option<PathBuf>,

    /// Dump k-induction TS formulas for external Z3 cross-check
    #[arg(
        long,
        value_name = "DIR",
        help_heading = "Debug tracing",
        hide_short_help = true,
        hide_long_help = true
    )]
    kind_dump_dir: Option<PathBuf>,

    /// SAT solver variant for DIMACS input: default, aggressive, minimal, probe
    #[arg(long, value_name = "VARIANT", help_heading = "SAT primary path")]
    sat_variant: Option<String>,

    /// Enable verbose SAT logging (cfg(ay_logging) builds)
    #[arg(
        long,
        help_heading = "Debug tracing",
        hide_short_help = true,
        hide_long_help = true
    )]
    log: bool,

    /// Trace a specific transred clause by ID.
    /// Also enables `--debug transred-clause` implicitly.
    #[arg(
        long,
        value_name = "CLAUSE_ID",
        help_heading = "Debug tracing",
        hide_short_help = true,
        hide_long_help = true
    )]
    debug_transred_clause: Option<u32>,
}

// ---------------------------------------------------------------------------
// Timeout, exit, and utility functions
// ---------------------------------------------------------------------------

pub(crate) fn sat_competition_wrapper_timeout_policy() -> bool {
    env::var(SAT_COMPETITION_WRAPPER_ENV)
        .is_ok_and(|value| is_sat_competition_wrapper_token(&value))
}

pub(crate) fn is_sat_competition_wrapper_token(value: &str) -> bool {
    let value = value.trim();
    SAT_COMPETITION_WRAPPER_TOKENS
        .iter()
        .any(|token| value.eq_ignore_ascii_case(token))
}

pub(crate) fn timeout_exit_code_for_sat_competition_wrapper(sat_competition_wrapper: bool) -> i32 {
    if sat_competition_wrapper {
        SAT_COMPETITION_UNKNOWN_EXIT_CODE
    } else {
        DEFAULT_TIMEOUT_EXIT_CODE
    }
}

fn timeout_stdout_line_for_sat_competition_wrapper(sat_competition_wrapper: bool) -> &'static [u8] {
    if sat_competition_wrapper {
        b"s UNKNOWN\n"
    } else {
        b"unknown\n"
    }
}

fn timeout_stderr_line_for_sat_competition_wrapper(sat_competition_wrapper: bool) -> &'static [u8] {
    if sat_competition_wrapper {
        b"c timeout\n"
    } else {
        b"(:reason-unknown \"timeout\")\n"
    }
}

fn abandon_unfinished_bv_cnf_export(reason: &str) -> bool {
    if VERDICT_PRINTED.load(Ordering::SeqCst) {
        return false;
    }
    let Some(path) = ay_core::trace_config().dump_bv_cnf_path.as_deref() else {
        return false;
    };
    let _ = std::fs::remove_file(path);
    safe_eprintln!(
        "(error \"artifact export failed: {reason} before the current BV CNF certificate and verdict were finalized\")"
    );
    true
}

fn hard_timeout_fallback_exit() -> ! {
    let sat_competition_wrapper = sat_competition_wrapper_timeout_policy();
    let export_abandoned = abandon_unfinished_bv_cnf_export("hard timeout or termination");
    if !export_abandoned && !VERDICT_PRINTED.swap(true, Ordering::SeqCst) {
        let _ = Write::write_all(
            &mut io::stdout(),
            timeout_stdout_line_for_sat_competition_wrapper(sat_competition_wrapper),
        );
        let _ = Write::flush(&mut io::stdout());
    }
    if !export_abandoned {
        let _ = Write::write_all(
            &mut io::stderr(),
            timeout_stderr_line_for_sat_competition_wrapper(sat_competition_wrapper),
        );
    }
    let _ = Write::flush(&mut io::stderr());
    std::process::exit(timeout_exit_code_for_sat_competition_wrapper(
        sat_competition_wrapper,
    ));
}

/// Set global timeout in milliseconds
fn set_global_timeout(ms: u64) {
    // Z3 treats -t:0 as "no timeout" - honor that convention.
    if ms == 0 {
        // The `GLOBAL_TIMEOUT_MS` atomic is the canonical store; the env var
        // was a dead IPC relic (no production reader) and was removed in
        // #8835. Tests that set `AY_GLOBAL_TIMEOUT_MS` via `EnvVarRestoreGuard`
        // are preserved as a harmless noop.
        return;
    }
    GLOBAL_TIMEOUT_MS.store(ms, Ordering::SeqCst);
    START_TIME.get_or_init(Instant::now);

    // Initialize the shared interrupt handle for ay-dpll integration.
    let handle = INTERRUPT_HANDLE.get_or_init(|| Arc::new(AtomicBool::new(false)));
    let watchdog_handle = handle.clone();

    // Spawn watchdog thread that signals timeout cooperatively (#2971).
    // Previous code called process::exit(124) which skips destructors and can
    // truncate in-progress DRAT/LRAT proofs and TLA traces. Now we set flags
    // that all solve paths check, allowing graceful shutdown.
    //
    // #5877: After the cooperative timeout fires, threads stuck in
    // non-interruptible computation (BvToBoolBitBlaster, ClauseInliner on
    // 10000-node BV transitions) can prevent process exit indefinitely.
    // Add a hard exit after a 2-second grace period as a safety net.
    std::thread::spawn(move || {
        std::thread::sleep(Duration::from_millis(ms));
        TIMED_OUT.store(true, Ordering::SeqCst);
        watchdog_handle.store(true, Ordering::SeqCst);
        // Grace period for cooperative shutdown, then hard exit. SAT-COMP
        // wrapper runs use competition UNKNOWN grammar/exit code; normal CLI
        // runs keep SMT-LIB timeout behavior.
        std::thread::sleep(Duration::from_secs(2));
        hard_timeout_fallback_exit();
    });
}

/// Check whether the global timeout has fired. If so, print an UNKNOWN result
/// and exit with the timeout-policy code.
///
/// Per SMT-LIB 2.6 / CHC-COMP convention, a solver must always emit one of
/// sat/unsat/unknown. Previously this only printed "timeout" to stderr,
/// causing silent exits from the caller's perspective (#8674).
///
/// NOTE: `process::exit` does NOT run Rust destructors on any thread (#3088).
/// We explicitly flush stdout/stderr to avoid truncated output. Proof file
/// writers (DRAT/LRAT, TLA traces) are not accessible here; they rely on the
/// cooperative timeout flag (TIMED_OUT / INTERRUPT_HANDLE) to flush and close
/// before the solver returns.
pub(crate) fn exit_if_timed_out() {
    if TIMED_OUT.load(Ordering::SeqCst) {
        let sat_competition_wrapper = sat_competition_wrapper_timeout_policy();
        let export_abandoned = abandon_unfinished_bv_cnf_export("timeout");
        // Only print "unknown" if no solve path has already printed a result.
        // The SMT executor path prints "unknown" via execute_and_print before
        // reaching this check; the CHC path may not have printed anything yet.
        if !export_abandoned && !VERDICT_PRINTED.swap(true, Ordering::SeqCst) {
            if sat_competition_wrapper {
                safe_println!("s UNKNOWN");
            } else {
                safe_println!("unknown");
            }
        }
        if !export_abandoned {
            if sat_competition_wrapper {
                safe_eprintln!("c timeout");
            } else {
                safe_eprintln!("(:reason-unknown \"timeout\")");
            }
        }
        // Flush buffered I/O before process::exit skips destructors.
        let _ = io::stdout().flush();
        let _ = io::stderr().flush();
        std::process::exit(timeout_exit_code_for_sat_competition_wrapper(
            sat_competition_wrapper,
        ));
    }
}

pub(crate) fn mark_verdict_printed() -> bool {
    VERDICT_PRINTED.swap(true, Ordering::SeqCst)
}

/// Returns true when the global watchdog timeout has fired.
pub(crate) fn is_timed_out() -> bool {
    TIMED_OUT.load(Ordering::Relaxed)
}

pub(crate) fn eprintln_smt_error(message: impl std::fmt::Display) {
    let message = message.to_string();
    safe_eprintln!("(error \"{}\")", escape_string_contents(&message));
}

/// Get elapsed time since process start.
pub(crate) fn global_elapsed() -> Duration {
    START_TIME.get().map_or(Duration::ZERO, Instant::elapsed)
}

const CHC_COMPETITION_JIT_TRACK: &str = "chc";
const CHC_TLA_TRANSITION_CLUSTER_ARTIFACT: &str = "chc-tla-transition-clusters";
const CHC_TLA_TRANSITION_CLUSTER_APPLICATION_COUNTER: &str =
    "chc_tla_transition_cluster_applications";
const CHC_TLA_TRANSITION_CLUSTER_INSTALL_COUNTER: &str =
    "solver_program.tla2_transition_cluster.installs";
const CHC_TLA_TRANSITION_CLUSTER_APPLY_COUNTER: &str =
    "solver_program.tla2_transition_cluster.applies";
const CHC_NATIVE_CODE_HELPER_ARTIFACT: &str = "chc-native-code-helpers";
const CHC_NATIVE_CODE_HELPER_APPLICATION_COUNTER: &str = "chc_native_code_helper_applications";

fn trimmed_env_value(name: &str) -> Option<String> {
    env::var(name)
        .ok()
        .map(|value| value.trim().to_string())
        .filter(|value| !value.is_empty())
}

fn chc_competition_jit_artifact(
    stats: Option<&ay::chc::ChcStatistics>,
    requested_mode: &str,
) -> &'static str {
    if let Some(artifact) = trimmed_env_value("AY_COMPETITION_JIT_ARTIFACT") {
        if artifact == CHC_TLA_TRANSITION_CLUSTER_ARTIFACT {
            return CHC_TLA_TRANSITION_CLUSTER_ARTIFACT;
        }
        if artifact == CHC_NATIVE_CODE_HELPER_ARTIFACT {
            return CHC_NATIVE_CODE_HELPER_ARTIFACT;
        }
    }

    if requested_mode == "current" {
        return CHC_NATIVE_CODE_HELPER_ARTIFACT;
    }

    let tla_applications = stats.map_or(0, |stats| stats.tla_transition_cluster_applications);
    if tla_applications > 0 {
        CHC_TLA_TRANSITION_CLUSTER_ARTIFACT
    } else {
        CHC_NATIVE_CODE_HELPER_ARTIFACT
    }
}

fn chc_competition_jit_application_counter(artifact: &str) -> &'static str {
    if artifact == CHC_TLA_TRANSITION_CLUSTER_ARTIFACT {
        CHC_TLA_TRANSITION_CLUSTER_APPLICATION_COUNTER
    } else {
        CHC_NATIVE_CODE_HELPER_APPLICATION_COUNTER
    }
}

fn chc_competition_jit_application_count(
    stats: Option<&ay::chc::ChcStatistics>,
    artifact: &str,
) -> u64 {
    let Some(stats) = stats else {
        return 0;
    };
    if artifact == CHC_TLA_TRANSITION_CLUSTER_ARTIFACT {
        stats.tla_transition_cluster_applications
    } else {
        stats.native_code_helper_applications
    }
}

fn chc_competition_jit_requested_mode() -> String {
    trimmed_env_value("AY_COMPETITION_JIT_CANDIDATE_MODE")
        .or_else(|| trimmed_env_value("AY_COMPETITION_JIT_MODE"))
        .unwrap_or_else(|| "profile-only".to_string())
}

fn chc_competition_jit_candidate_mode(
    artifact: &str,
    requested_mode: &str,
) -> (&'static str, bool) {
    if artifact == CHC_TLA_TRANSITION_CLUSTER_ARTIFACT {
        match requested_mode {
            "off" => ("off", false),
            "profile-only" => ("profile-only", false),
            "solver-program" => ("solver-program", false),
            _ => ("off", true),
        }
    } else {
        match requested_mode {
            "off" => ("off", false),
            "current" => ("current", false),
            "profile-only" => ("profile-only", false),
            _ => ("off", true),
        }
    }
}

fn chc_competition_jit_json(stats: Option<&ay::chc::ChcStatistics>) -> serde_json::Value {
    let requested_mode = chc_competition_jit_requested_mode();
    let normalized_requested_mode = requested_mode.to_ascii_lowercase();
    let artifact = chc_competition_jit_artifact(stats, normalized_requested_mode.as_str());
    let application_counter = chc_competition_jit_application_counter(artifact);
    let application_count = chc_competition_jit_application_count(stats, artifact);
    let (candidate_mode, unsupported_mode) =
        chc_competition_jit_candidate_mode(artifact, normalized_requested_mode.as_str());
    let native_dispatch = artifact == CHC_NATIVE_CODE_HELPER_ARTIFACT
        && candidate_mode == "current"
        && application_count > 0
        && !unsupported_mode;
    let fail_closed = unsupported_mode
        || (candidate_mode != "off" && application_count == 0)
        || (artifact == CHC_TLA_TRANSITION_CLUSTER_ARTIFACT && candidate_mode == "solver-program")
        || (artifact == CHC_NATIVE_CODE_HELPER_ARTIFACT
            && candidate_mode == "current"
            && !native_dispatch);

    serde_json::json!({
        "schema_version": 1,
        "track": CHC_COMPETITION_JIT_TRACK,
        "artifact": artifact,
        "application_counter": application_counter,
        "requested_mode": requested_mode,
        "candidate_mode": candidate_mode,
        "native_dispatch": native_dispatch,
        "fail_closed": fail_closed,
    })
}

fn chc_run_stats_json(
    run_stats: &stats_output::RunStatistics,
    engine: &str,
    chc_stats: Option<&ay::chc::ChcStatistics>,
    proof_transcript: Option<&ay::chc::ChcProofTranscriptMetadata>,
    proof_manifest: Option<&ay::chc::ChcProofEvidenceManifest>,
) -> String {
    let json = run_stats.to_json();
    let Ok(mut value) = serde_json::from_str::<serde_json::Value>(&json) else {
        return json;
    };
    let Some(map) = value.as_object_mut() else {
        return json;
    };

    map.insert(
        "competition_jit".to_string(),
        chc_competition_jit_json(chc_stats),
    );
    let proof_result = proof_transcript
        .map(|transcript| transcript.result.as_str())
        .unwrap_or("unknown");
    let proof_accepted = proof_transcript.is_some_and(|transcript| transcript.accepted_as_proof);
    let safe_attempt = u64::from(proof_result == "safe");
    let unsafe_attempt = u64::from(proof_result == "unsafe");
    map.insert(
        "chc.validation.safe_attempts".to_string(),
        serde_json::json!(safe_attempt),
    );
    map.insert(
        "chc.validation.safe_successes".to_string(),
        serde_json::json!(u64::from(safe_attempt > 0 && proof_accepted)),
    );
    map.insert(
        "chc.validation.safe_failures".to_string(),
        serde_json::json!(u64::from(safe_attempt > 0 && !proof_accepted)),
    );
    map.insert(
        "chc.validation.unsafe_attempts".to_string(),
        serde_json::json!(unsafe_attempt),
    );
    map.insert(
        "chc.validation.unsafe_successes".to_string(),
        serde_json::json!(u64::from(unsafe_attempt > 0 && proof_accepted)),
    );
    map.insert(
        "chc.validation.unsafe_failures".to_string(),
        serde_json::json!(u64::from(unsafe_attempt > 0 && !proof_accepted)),
    );
    map.insert(
        "chc.transform_memory.reversible_count".to_string(),
        serde_json::json!(0u64),
    );
    map.insert(
        "chc.transform_memory.obligation_count".to_string(),
        serde_json::json!(0u64),
    );
    map.insert("chc.route.name".to_string(), serde_json::json!(engine));
    map.insert(
        "chc.route.accepted_by_firewall".to_string(),
        serde_json::json!(true),
    );
    map.insert(
        "chc.route.fail_closed_reason".to_string(),
        serde_json::json!(""),
    );
    if let Some(proof_transcript) = proof_transcript {
        map.insert(
            "chc_proof_transcript".to_string(),
            proof_transcript.to_json_value(),
        );
    }
    if let Some(proof_manifest) = proof_manifest {
        map.insert(
            "chc_evidence_manifest".to_string(),
            proof_manifest.to_json_value(),
        );
    }
    serde_json::Value::Object(map.clone()).to_string()
}

fn insert_deterministic_bv_bool_transition_stats(
    run_stats: &mut stats_output::RunStatistics,
    stats: &ay::chc::ChcStatistics,
) {
    run_stats.insert(
        "chc.deterministic_bv_bool_transition.attempts",
        stats.deterministic_bv_bool_transition_attempts,
    );
    run_stats.insert(
        "chc.deterministic_bv_bool_transition.recognized",
        stats.deterministic_bv_bool_transition_recognized,
    );
    run_stats.insert(
        "chc.deterministic_bv_bool_transition.bmc_unsafe_validated",
        stats.deterministic_bv_bool_transition_bmc_unsafe_validated,
    );
    run_stats.insert(
        "chc.deterministic_bv_bool_transition.kind_safe_validated",
        stats.deterministic_bv_bool_transition_kind_safe_validated,
    );
    run_stats.insert(
        "chc.deterministic_bv_bool_transition.kind_unsafe_validated",
        stats.deterministic_bv_bool_transition_kind_unsafe_validated,
    );
    run_stats.insert(
        "chc.deterministic_bv_bool_transition.bool_control_safe_validated",
        stats.deterministic_bv_bool_transition_bool_control_safe_validated,
    );
    run_stats.insert(
        "chc.deterministic_bv_bool_transition.validation_rejections",
        stats.deterministic_bv_bool_transition_validation_rejections,
    );
}

/// Print CHC solve statistics to stderr.
///
/// When `chc_stats` is provided, populates the canonical stats envelope with
/// CHC-specific counters under the `chc.*` key namespace. Problem-level
/// counters (`chc.predicates`, `chc.clauses`) are always emitted.
pub(crate) fn print_chc_stats(
    start: &Instant,
    result: &str,
    engine: &str,
    stats_cfg: stats_output::StatsConfig,
    chc_stats: Option<&ay::chc::ChcStatistics>,
    proof_transcript: Option<&ay::chc::ChcProofTranscriptMetadata>,
    proof_manifest: Option<&ay::chc::ChcProofEvidenceManifest>,
    num_predicates: u64,
    num_clauses: u64,
) {
    let elapsed = start.elapsed();
    if stats_cfg.human {
        safe_eprintln!(
            "(:chc-statistics\n  :result {result}\n  :engine {engine}\n  :time {:.3})",
            elapsed.as_secs_f64()
        );
    }

    // Canonical envelope
    let mode = if engine == "portfolio" {
        stats_output::SolveMode::Portfolio
    } else {
        stats_output::SolveMode::Chc
    };
    let mut run_stats = stats_output::RunStatistics::new(mode, result, global_elapsed());

    // Problem-level counters (always available).
    run_stats.insert("chc.predicates", num_predicates);
    run_stats.insert("chc.clauses", num_clauses);

    // Populate CHC-specific counters from engine statistics.
    if let Some(stats) = chc_stats {
        run_stats.insert("chc.iterations", stats.iterations);
        run_stats.insert("chc.lemmas_learned", stats.lemmas_learned);
        run_stats.insert("chc.max_frame", stats.max_frame);
        run_stats.insert("chc.restarts", stats.restarts);
        run_stats.insert("chc.smt_unknowns", stats.smt_unknowns);
        run_stats.insert("chc.cache_hits", stats.cache_hits);
        run_stats.insert("chc.cache_model_rejections", stats.cache_model_rejections);
        run_stats.insert("chc.cache_solver_calls", stats.cache_solver_calls);
        run_stats.insert(
            "chc.native_code_helper_compile_attempts",
            stats.native_code_helper_compile_attempts,
        );
        run_stats.insert(
            "chc.native_code_helper_compile_successes",
            stats.native_code_helper_compile_successes,
        );
        run_stats.insert(
            "chc.native_code_helper_compile_failures",
            stats.native_code_helper_compile_failures,
        );
        run_stats.insert(
            "chc.native_code_helper_evaluations",
            stats.native_code_helper_evaluations,
        );
        run_stats.insert(
            "chc.native_code_helper_deopts",
            stats.native_code_helper_deopts,
        );
        run_stats.insert(
            "chc.native_code_helper_fallbacks",
            stats.native_code_helper_fallbacks,
        );
        run_stats.insert(
            "chc.native_code_helper_missing_var_fallbacks",
            stats.native_code_helper_missing_var_fallbacks,
        );
        run_stats.insert(
            "chc.native_code_helper_interpreter_confirmations",
            stats.native_code_helper_interpreter_confirmations,
        );
        run_stats.insert(
            "chc.native_code_helper_trusted_true_results",
            stats.native_code_helper_trusted_true_results,
        );
        run_stats.insert(
            "chc.native_code_helper_applications",
            stats.native_code_helper_applications,
        );
        run_stats.insert(
            "chc.tla_transition_cluster_applications",
            stats.tla_transition_cluster_applications,
        );
        run_stats.insert(
            "chc.symbolic_scalarization_projected_cells",
            stats.symbolic_scalarization_projected_cells,
        );
        run_stats.insert(
            "chc.symbolic_scalarization_multi_cell_args",
            stats.symbolic_scalarization_multi_cell_args,
        );
        run_stats.insert(
            "chc.lra_affine_original_clause_validation_attempts",
            stats.lra_affine_original_clause_validation_attempts,
        );
        run_stats.insert(
            "chc.lra_affine_original_clause_validation_queries",
            stats.lra_affine_original_clause_validation_queries,
        );
        run_stats.insert(
            "chc.lra_affine_original_clause_validation_successes",
            stats.lra_affine_original_clause_validation_successes,
        );
        run_stats.insert(
            "chc.lra_affine_original_clause_validation_failures",
            stats.lra_affine_original_clause_validation_failures,
        );
        run_stats.insert(
            "chc.lra_affine_original_clause_validation_unknowns",
            stats.lra_affine_original_clause_validation_unknowns,
        );
        insert_deterministic_bv_bool_transition_stats(&mut run_stats, stats);
        // Stable flat aliases for native-helper instrumentation.
        run_stats.insert(
            "chc_native_code_helper_applications",
            stats.native_code_helper_applications,
        );
        run_stats.insert(
            "chc_tla_transition_cluster_applications",
            stats.tla_transition_cluster_applications,
        );
        run_stats.insert(CHC_TLA_TRANSITION_CLUSTER_INSTALL_COUNTER, 0);
        run_stats.insert(CHC_TLA_TRANSITION_CLUSTER_APPLY_COUNTER, 0);
        if stats.trust_proof_fallbacks > 0 {
            run_stats.insert("chc.trust_proof_fallbacks", stats.trust_proof_fallbacks);
        }
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
    run_stats.insert(
        "resource.term_bytes",
        ay_core::TermStore::global_term_bytes() as u64,
    );
    run_stats.insert("time.total_ms", global_elapsed().as_millis() as u64);

    if stats_cfg.human {
        run_stats.print_to_stderr();
        if let Some(proof_transcript) = proof_transcript {
            safe_eprintln!(
                "c chc.normalized_input_sha256: {}",
                proof_transcript.normalized_input_sha256
            );
            safe_eprintln!(
                "c chc.pdr_input_sha256: {}",
                proof_transcript.pdr_input_sha256()
            );
            safe_eprintln!("c chc.proof_status: {}", proof_transcript.proof_status);
            safe_eprintln!(
                "c chc.accepted_as_proof: {}",
                proof_transcript.accepted_as_proof
            );
            safe_eprintln!("c");
        }
    }
    if stats_cfg.json {
        safe_eprintln!(
            "{}",
            chc_run_stats_json(
                &run_stats,
                engine,
                chc_stats,
                proof_transcript,
                proof_manifest,
            )
        );
    }
}

// ---------------------------------------------------------------------------
// Z3 backward compatibility: preprocess raw args before clap parsing
// ---------------------------------------------------------------------------

/// Known subcommand names for injection detection.
const KNOWN_SUBCOMMANDS: &[&str] = &[
    "solve",
    "check",
    "bench",
    "corpus",
    "tool",
    "competition-jit",
    "gate",
    #[cfg(ay_internal_tools)]
    "consumer-smoke",
    "flatzinc",
    "pb",
    "maxsat",
    "qbf",
    "lp",
    "tutorial",
    "simplify",
    "bisect",
    "allsat",
    "model-count",
    "diagnose",
    "launch-packet",
    "launch-gate",
    "release",
    "z3-audit",
    "submission",
    "verifier-audit",
    "scripts",
    "help",
];

/// Internal env var used by the solve-session provenance wrapper.
const SESSION_PROVENANCE_CHILD_ENV: &str = "AY_INTERNAL_PROVENANCE_CHILD";

struct Z3CompatModuleInfo {
    name: &'static str,
    description: &'static str,
}

struct Z3CompatParamInfo {
    module: Option<&'static str>,
    name: &'static str,
    ty: &'static str,
    default: &'static str,
    description: &'static str,
}

const Z3_COMPAT_MODULES: &[Z3CompatModuleInfo] = &[
    Z3CompatModuleInfo {
        name: "fp",
        description: "fixedpoint and CHC compatibility parameters",
    },
    Z3CompatModuleInfo {
        name: "nlsat",
        description: "nonlinear arithmetic compatibility parameters",
    },
    Z3CompatModuleInfo {
        name: "sat",
        description: "SAT compatibility parameters",
    },
    Z3CompatModuleInfo {
        name: "smt",
        description: "SMT compatibility parameters",
    },
];

const Z3_COMPAT_PARAMS: &[Z3CompatParamInfo] = &[
    Z3CompatParamInfo {
        module: None,
        name: "auto_config",
        ty: "bool",
        default: "true",
        description: "accepted for Z3 command-line compatibility; ay configures solvers automatically",
    },
    Z3CompatParamInfo {
        module: None,
        name: "ctrl_c",
        ty: "bool",
        default: "true",
        description: "accepted as a compatibility no-op; ay uses its own interrupt handling",
    },
    Z3CompatParamInfo {
        module: None,
        name: "model",
        ty: "bool",
        default: "true",
        description: "accepted as a compatibility no-op; use -model to print a satisfiable SMT model",
    },
    Z3CompatParamInfo {
        module: None,
        name: "dump_models",
        ty: "bool",
        default: "false",
        description: "print a model after satisfiable SMT-LIB checks when set to true",
    },
    Z3CompatParamInfo {
        module: None,
        name: "dump-models",
        ty: "bool",
        default: "false",
        description: "alias for dump_models; print a model after satisfiable SMT-LIB checks when set to true",
    },
    Z3CompatParamInfo {
        module: None,
        name: "memory_max_size",
        ty: "unsigned int",
        default: "0",
        description: "memory limit in megabytes; 0 means no limit",
    },
    Z3CompatParamInfo {
        module: None,
        name: "model_validate",
        ty: "bool",
        default: "false",
        description: "accepted as a compatibility no-op; ay model validation is controlled by --validate",
    },
    Z3CompatParamInfo {
        module: None,
        name: "model.v2",
        ty: "bool",
        default: "true",
        description: "accepted as a compatibility no-op; ay uses its native model printer",
    },
    Z3CompatParamInfo {
        module: None,
        name: "model.compact",
        ty: "bool",
        default: "false",
        description: "accepted as a compatibility no-op; ay uses its native model printer",
    },
    Z3CompatParamInfo {
        module: None,
        name: "model.completion",
        ty: "bool",
        default: "false",
        description: "accepted as a compatibility no-op; ay uses its native model printer",
    },
    Z3CompatParamInfo {
        module: None,
        name: "model.partial",
        ty: "bool",
        default: "false",
        description: "accepted as a compatibility no-op; ay uses its native model printer",
    },
    Z3CompatParamInfo {
        module: None,
        name: "pp.decimal",
        ty: "bool",
        default: "false",
        description: "accepted as a compatibility no-op; ay uses its native pretty-printer",
    },
    Z3CompatParamInfo {
        module: None,
        name: "pp.decimal_precision",
        ty: "unsigned int",
        default: "10",
        description: "accepted as a compatibility no-op; ay uses its native pretty-printer",
    },
    Z3CompatParamInfo {
        module: None,
        name: "pp.single-line",
        ty: "bool",
        default: "false",
        description: "accepted as a compatibility no-op; ay uses its native pretty-printer",
    },
    Z3CompatParamInfo {
        module: None,
        name: "pp.bv-literals",
        ty: "bool",
        default: "true",
        description: "accepted as a compatibility no-op; ay uses its native bit-vector printer",
    },
    Z3CompatParamInfo {
        module: None,
        name: "pp.fixed-indent",
        ty: "bool",
        default: "false",
        description: "accepted as a compatibility no-op; ay uses its native pretty-printer",
    },
    Z3CompatParamInfo {
        module: None,
        name: "pp.max-depth",
        ty: "unsigned int",
        default: "5",
        description: "accepted as a compatibility no-op; ay uses its native pretty-printer",
    },
    Z3CompatParamInfo {
        module: None,
        name: "pp.max-ribbon",
        ty: "unsigned int",
        default: "80",
        description: "accepted as a compatibility no-op; ay uses its native pretty-printer",
    },
    Z3CompatParamInfo {
        module: None,
        name: "proof",
        ty: "bool",
        default: "false",
        description: "accepted as a compatibility no-op; use --proof FILE for proof output",
    },
    Z3CompatParamInfo {
        module: None,
        name: "random_seed",
        ty: "unsigned int",
        default: "0",
        description: "accepted as a compatibility no-op; ay search is deterministic for this CLI path",
    },
    Z3CompatParamInfo {
        module: None,
        name: "rlimit",
        ty: "unsigned int",
        default: "0",
        description: "accepted as a compatibility no-op; use -t:N or timeout=N for time limits",
    },
    Z3CompatParamInfo {
        module: None,
        name: "smtlib2_compliant",
        ty: "bool",
        default: "false",
        description: "accepted as a compatibility no-op; ay parses SMT-LIB2 input by default",
    },
    Z3CompatParamInfo {
        module: None,
        name: "stats",
        ty: "bool",
        default: "false",
        description: "print ay statistics when set to true",
    },
    Z3CompatParamInfo {
        module: None,
        name: "timeout",
        ty: "unsigned int",
        default: "0",
        description: "timeout in milliseconds; 0 means no timeout",
    },
    Z3CompatParamInfo {
        module: None,
        name: "trace",
        ty: "bool",
        default: "false",
        description: "accepted as a compatibility no-op; ay does not emit Z3 VCC trace logs",
    },
    Z3CompatParamInfo {
        module: None,
        name: "trace_file_name",
        ty: "string",
        default: "z3.log",
        description: "accepted as a compatibility no-op for Z3 trace file wrappers",
    },
    Z3CompatParamInfo {
        module: None,
        name: "type_check",
        ty: "bool",
        default: "true",
        description: "accepted as a compatibility no-op",
    },
    Z3CompatParamInfo {
        module: None,
        name: "type-check",
        ty: "bool",
        default: "true",
        description: "alias for type_check; accepted as a compatibility no-op",
    },
    Z3CompatParamInfo {
        module: None,
        name: "unsat_core",
        ty: "bool",
        default: "false",
        description: "accepted as a compatibility no-op; ay does not expose Z3 unsat-core output through this flag",
    },
    Z3CompatParamInfo {
        module: None,
        name: "debug-ref-count",
        ty: "bool",
        default: "false",
        description: "accepted as a compatibility no-op",
    },
    Z3CompatParamInfo {
        module: None,
        name: "verbose",
        ty: "unsigned int",
        default: "0",
        description: "accepted for wrapper compatibility; use --verbose for ay tracing",
    },
    Z3CompatParamInfo {
        module: None,
        name: "warning",
        ty: "bool",
        default: "true",
        description: "accepted as a compatibility no-op",
    },
    Z3CompatParamInfo {
        module: None,
        name: "well_sorted_check",
        ty: "bool",
        default: "false",
        description: "accepted as a compatibility no-op",
    },
    Z3CompatParamInfo {
        module: None,
        name: "well-sorted-check",
        ty: "bool",
        default: "false",
        description: "alias for well_sorted_check; accepted as a compatibility no-op",
    },
    Z3CompatParamInfo {
        module: Some("fp"),
        name: "engine",
        ty: "symbol",
        default: "spacer",
        description: "accepted CHC engine selector values: spacer, auto-config, datalog, bmc",
    },
    Z3CompatParamInfo {
        module: Some("fp"),
        name: "spacer.random_seed",
        ty: "unsigned int",
        default: "0",
        description: "accepted as a compatibility no-op for Spacer random seed settings",
    },
    Z3CompatParamInfo {
        module: Some("nlsat"),
        name: "seed",
        ty: "unsigned int",
        default: "0",
        description: "accepted as a compatibility no-op for nonlinear arithmetic seed settings",
    },
    Z3CompatParamInfo {
        module: Some("sat"),
        name: "random_seed",
        ty: "unsigned int",
        default: "0",
        description: "accepted as a compatibility no-op for SAT random seed settings",
    },
    Z3CompatParamInfo {
        module: Some("smt"),
        name: "random_seed",
        ty: "unsigned int",
        default: "0",
        description: "accepted as a compatibility no-op for SMT random seed settings",
    },
];

fn is_help_or_version_flag(arg: &str) -> bool {
    is_help_flag(arg) || is_version_flag(arg)
}

fn is_help_flag(arg: &str) -> bool {
    matches!(arg, "--help" | "-h" | "-?")
}

fn is_version_flag(arg: &str) -> bool {
    matches!(arg, "--version" | "-V" | "-v" | "-version")
}

fn is_solve_full_help_flag(arg: &str) -> bool {
    matches!(arg, "--help=full" | "--full-help")
}

/// True when a `solve` invocation carries `-q`/`--quiet` before any `--`.
///
/// Consulted in `main()` before the session supervisor forks so the pre-fork
/// `c ay.session.start` marker is suppressed too; `run_solve` re-affirms the
/// flag from the parsed args for the in-process path.
fn solve_quiet_requested(processed: &[String]) -> bool {
    if !matches!(processed.get(1).map(String::as_str), Some("solve")) {
        return false;
    }
    processed
        .iter()
        .skip(2)
        .take_while(|arg| arg.as_str() != "--")
        .any(|arg| matches!(arg.as_str(), "-q" | "--quiet"))
}

fn maybe_print_solve_full_help(processed: &[String]) -> bool {
    if !matches!(processed.get(1).map(String::as_str), Some("solve")) {
        return false;
    }

    let requested = processed
        .iter()
        .skip(2)
        .take_while(|arg| arg.as_str() != "--")
        .any(|arg| is_solve_full_help_flag(arg));
    if !requested {
        return false;
    }

    let mut cmd = Cli::command().mut_subcommand("solve", |solve| {
        solve.mut_args(|arg| arg.hide_short_help(false).hide_long_help(false))
    });
    cmd.build();
    if let Some(solve) = cmd.find_subcommand_mut("solve") {
        safe_print!("{}", solve.render_long_help());
    }
    true
}

fn print_z3_compat_param_line(param: &Z3CompatParamInfo, descriptions: bool) {
    if descriptions {
        safe_println!(
            "    {} ({}) {} (default: {})",
            param.name,
            param.ty,
            param.description,
            param.default
        );
    } else {
        safe_println!(
            "    {} ({}) (default: {})",
            param.name,
            param.ty,
            param.default
        );
    }
}

fn print_z3_compat_global_params(descriptions: bool) {
    safe_println!("Global parameters");
    for param in Z3_COMPAT_PARAMS
        .iter()
        .filter(|param| param.module.is_none())
    {
        print_z3_compat_param_line(param, descriptions);
    }
}

fn print_z3_compat_module_header(module: &Z3CompatModuleInfo) {
    safe_println!(
        "[module] {}, description: {}",
        module.name,
        module.description
    );
}

fn print_z3_compat_module_params(module_name: &str, descriptions: bool) -> bool {
    let Some(module) = Z3_COMPAT_MODULES
        .iter()
        .find(|module| module.name == module_name)
    else {
        return false;
    };

    print_z3_compat_module_header(module);
    for param in Z3_COMPAT_PARAMS
        .iter()
        .filter(|param| param.module == Some(module_name))
    {
        print_z3_compat_param_line(param, descriptions);
    }
    true
}

fn print_z3_compat_module_list() {
    for module in Z3_COMPAT_MODULES {
        print_z3_compat_module_header(module);
    }
}

fn print_z3_compatible_params(descriptions: bool) {
    print_z3_compat_global_params(descriptions);
    safe_println!();
    safe_println!("To set a module parameter, use <module-name>.<parameter-name>=value");
    safe_println!("Example: fp.engine=spacer");
    safe_println!();
    for module in Z3_COMPAT_MODULES {
        print_z3_compat_module_params(module.name, descriptions);
    }
    safe_println!();
    safe_println!(
        "Note: ay lists the Z3-compatible parameters it accepts, not Z3's full parameter database."
    );
}

fn print_unknown_z3_module_and_exit(module_name: &str) -> ! {
    safe_eprintln!("ERROR: unknown module '{module_name}'");
    safe_eprintln!("Legal modules are:");
    for module in Z3_COMPAT_MODULES {
        safe_eprintln!("  {}", module.name);
    }
    std::process::exit(110);
}

fn z3_compat_param_key(param: &Z3CompatParamInfo) -> String {
    match param.module {
        Some(module) => format!("{module}.{}", param.name),
        None => param.name.to_string(),
    }
}

fn find_z3_compat_param(name: &str) -> Option<&'static Z3CompatParamInfo> {
    Z3_COMPAT_PARAMS.iter().find(|param| {
        if param.name == name {
            return true;
        }

        let Some(module) = param.module else {
            return false;
        };
        let Some(rest) = name.strip_prefix(module) else {
            return false;
        };
        rest.strip_prefix('.') == Some(param.name)
    })
}

fn print_z3_compat_param_description_or_exit(name: &str) {
    let Some(param) = find_z3_compat_param(name) else {
        safe_eprintln!("ERROR: unknown parameter '{name}'");
        safe_eprintln!("Legal parameters are:");
        for param in Z3_COMPAT_PARAMS {
            safe_eprintln!(
                "  {} ({}) (default: {})",
                z3_compat_param_key(param),
                param.ty,
                param.default
            );
        }
        std::process::exit(110);
    };

    safe_println!("{}  {}", z3_compat_param_key(param), param.description);
}

fn print_unsupported_z3_option(option: &str) {
    safe_eprintln!("Error: unsupported Z3 option '{option}'");
    match option {
        opt if opt == "-tactics" || opt.starts_with("-tactics:") => {
            safe_eprintln!("       ay does not expose Z3's tactic catalog.");
            safe_eprintln!("       Use `ay simplify` for ay's SMT-LIB simplifier command.");
        }
        opt if opt == "-simplifiers" || opt.starts_with("-simplifiers:") => {
            safe_eprintln!("       ay does not expose Z3's simplifier catalog.");
            safe_eprintln!("       Use `ay simplify` for ay's SMT-LIB simplifier command.");
        }
        "-probes" => {
            safe_eprintln!("       ay does not implement Z3 probes.");
        }
        "-dl" => {
            safe_eprintln!("       Datalog input is not supported by the ay solve path.");
        }
        "-wcnf" => {
            safe_eprintln!("       Weighted CNF DIMACS is not supported by `ay solve`.");
            safe_eprintln!("       For OPB/WBO pseudo-Boolean input, use `ay pb solve FILE`.");
        }
        "-opb" => {
            safe_eprintln!("       Flag-style OPB parsing is not supported.");
            safe_eprintln!("       Use `ay pb solve FILE`.");
        }
        "-lp" => {
            safe_eprintln!("       Flag-style CPLEX LP parsing is not supported.");
            safe_eprintln!("       Use `ay lp solve FILE`.");
        }
        "-log" => {
            safe_eprintln!("       Z3 log input is not supported.");
        }
        "-pp" => {
            safe_eprintln!("       option argument (-pp:name) is missing.");
        }
        opt if opt.starts_with("-v:") => {
            safe_eprintln!("       invalid verbosity level; expected an unsigned integer.");
        }
        opt if opt.starts_with("-pmmd:") => {
            safe_eprintln!("       Markdown Z3 parameter listings are not supported.");
            safe_eprintln!("       Use -pm:name for ay's text compatibility subset.");
        }
        _ => {
            safe_eprintln!("       ay does not implement this Z3 CLI surface.");
        }
    }
}

fn is_unsupported_z3_option(arg: &str) -> bool {
    matches!(
        arg,
        "-dl" | "-wcnf" | "-opb" | "-lp" | "-log" | "-probes" | "-pp"
    ) || arg.starts_with("-tactics:")
        || arg == "-tactics"
        || arg.starts_with("-simplifiers:")
        || arg == "-simplifiers"
        || arg.starts_with("-pmmd:")
}

/// Preprocess raw CLI args for Z3 backward compatibility and subcommand injection.
///
/// Transforms:
/// - `-t:N` -> `--timeout N`
/// - `-T:N` -> `--timeout N000`
/// - `-memory:N` -> `--memory N`
/// - `-smt2` -> (dropped)
/// - `-dimacs` -> (dropped; DIMACS is auto-detected)
/// - `-in` -> `--incremental`
/// - `-file:PATH` -> `PATH`
/// - `-model` -> `--z3-model`
/// - `-st` -> `--stats`
/// - `-nw` -> (dropped)
/// - `-v:N` -> (dropped)
/// - `-p`, `-pd`, `-pm[:name]`, `-pp:name` -> Z3-style parameter listings
/// - `timeout=N` -> `--timeout N`
/// - `memory_max_size=N` -> `--memory N`
/// - `stats=true` -> `--stats`
/// - `dump_models=true`, `dump-models=true` -> `--z3-model`
/// - `fp.engine=spacer` -> (dropped)
/// - `trace=true|false`, `trace_file_name=PATH` -> (dropped)
/// - common Z3 artifact/randomness `key=value` params -> (dropped)
/// - other `key=value` patterns -> explicit unsupported-parameter error
/// - unsupported Z3 input/introspection flags -> explicit unsupported-option error
/// - argv[0] basename `z3` -> `--z3-mode` for solve invocations
///
/// Then, if the first non-flag arg is not a known subcommand, prepends "solve"
/// so that `ay file.smt2` works as `ay solve file.smt2`.
fn preprocess_args(raw: Vec<String>) -> Vec<String> {
    if has_explicit_non_solve_subcommand(&raw) {
        return raw;
    }

    let mut processed = Vec::with_capacity(raw.len() + 1);

    // Always keep argv[0]
    if let Some(prog) = raw.first() {
        processed.push(prog.clone());
    }

    let mut i = 1;
    while i < raw.len() {
        let arg = &raw[i];

        if arg == "--" {
            processed.push(arg.clone());
            processed.extend(raw.iter().skip(i + 1).cloned());
            break;
        } else if arg == "-" {
            // A bare `-` FILE means "read the formula from stdin" — the
            // conventional Unix filter spelling. Map it to `--stdin` so it
            // reuses the batch stdin path instead of clap treating `-` as a
            // positional file and failing with "Error reading file '-'".
            // Z3's live `-in` (-> --incremental) and the explicit `--stdin`
            // flag are handled separately and remain byte-identical.
            processed.push("--stdin".to_string());
        } else if let Some(timeout_str) = arg.strip_prefix("-t:") {
            // Z3: -t:N -> --timeout N
            processed.push("--timeout".to_string());
            processed.push(timeout_str.to_string());
        } else if let Some(timeout_str) = arg.strip_prefix("-T:") {
            // Z3: -T:N is seconds; ay's --timeout is milliseconds.
            processed.push("--timeout".to_string());
            processed.push(z3_seconds_timeout_to_millis(timeout_str));
        } else if let Some(mem_str) = arg.strip_prefix("-memory:") {
            // Z3: -memory:N -> --memory N
            processed.push("--memory".to_string());
            processed.push(mem_str.to_string());
        } else if let Some(file) = arg.strip_prefix("-file:") {
            // Z3: -file:PATH -> PATH
            processed.push(file.to_string());
        } else if arg == "-smt2" {
            // Z3: -smt2 is a no-op (auto-detected)
        } else if arg == "-dimacs" {
            // Z3: -dimacs selects the DIMACS parser. ay auto-detects DIMACS.
        } else if arg == "-in" {
            // Z3's `-in` is a live command stream: callers may keep stdin
            // open and wait for each response before sending the next command.
            // Batch `--stdin` waits for EOF and deadlocks those callers.
            // `--incremental` implies stdin and flushes after every command.
            processed.push("--incremental".to_string());
        } else if arg == "-model" {
            // Z3: -model asks for a model after a satisfiable SMT query.
            processed.push("--z3-model".to_string());
        } else if arg == "--visualize"
            && raw
                .get(i + 1)
                .is_some_and(|next| matches!(next.as_str(), "ascii" | "svg"))
        {
            processed.push(format!("--visualize={}", raw[i + 1]));
            i += 1;
        } else if arg == "-st" {
            // Z3: -st -> --stats
            processed.push("--stats".to_string());
        } else if arg == "-nw" {
            // Z3: -nw disables warning messages. ay has no equivalent warning channel here.
        } else if let Some(verbose_str) = arg.strip_prefix("-v:") {
            // Z3: -v:N sets verbosity. Accept it for drop-in wrappers without
            // changing ay's stdout/stderr contracts.
            if !is_z3_unsigned_value(verbose_str) {
                processed.push("--unsupported-z3-option".to_string());
                processed.push(arg.clone());
            }
        } else if arg == "-p" {
            // Z3: -p lists global and module parameters. ay prints the
            // Z3-style parameter subset this CLI actually accepts.
            processed.push("--z3-print-params".to_string());
        } else if arg == "-pd" {
            // Z3: -pd lists parameter descriptions.
            processed.push("--z3-print-param-descriptions".to_string());
        } else if arg == "-pm" {
            // Z3: -pm lists module names.
            processed.push("--z3-print-param-module".to_string());
            processed.push(String::new());
        } else if let Some(module_name) = arg.strip_prefix("-pm:") {
            // Z3: -pm:name lists one module's parameters.
            processed.push("--z3-print-param-module".to_string());
            processed.push(module_name.to_string());
        } else if let Some(param_name) = arg.strip_prefix("-pp:") {
            // Z3: -pp:name prints one parameter description.
            processed.push("--z3-print-param-description".to_string());
            processed.push(param_name.to_string());
        } else if is_unsupported_z3_option(arg) {
            processed.push("--unsupported-z3-option".to_string());
            processed.push(arg.clone());
        } else if arg == "-?" {
            // Z3: -? -> help
            processed.push("--help".to_string());
        } else if arg == "-v" || arg == "-version" {
            // Convenience aliases for clap's version path.
            processed.push("--version".to_string());
        } else if handle_z3_key_value_param(arg, &mut processed) {
            // Explicitly accepted or translated Z3 parameter compatibility.
        } else if is_allowlisted_z3_param(arg) {
            // Explicitly accepted Z3 parameter compatibility no-op.
        } else if arg.contains('=') && !arg.starts_with('-') {
            if looks_like_input_path_arg(arg) {
                processed.push(arg.clone());
            } else if is_ignorable_z3_module_param(arg) {
                // A real libz3 tuning knob AY does not implement. z3 accepts and
                // honors it; AY accepts and IGNORES it, announcing that on stderr
                // (see `--ignored-z3-param`). Rejecting it — the old behavior —
                // gave a fatal error and NO verdict where z3 simply solved, which
                // broke every consumer that passes `smt.mbqi=false` and friends on
                // each invocation.
                processed.push("--ignored-z3-param".to_string());
                processed.push(arg.clone());
            } else {
                processed.push("--unsupported-z3-param".to_string());
                processed.push(arg.clone());
            }
        } else {
            processed.push(arg.clone());
        }

        i += 1;
    }

    // Subcommand injection: if the first non-flag arg after argv[0] is not a
    // known subcommand, prepend "solve" so `ay file.smt2` works.
    inject_solve_subcommand(&mut processed);
    inject_z3_mode_from_argv0(&raw, &mut processed);

    processed
}

fn inject_z3_mode_from_argv0(raw: &[String], processed: &mut Vec<String>) {
    if !argv0_is_z3(raw) || !matches!(processed.get(1).map(String::as_str), Some("solve")) {
        return;
    }

    if processed
        .iter()
        .skip(2)
        .take_while(|arg| arg.as_str() != "--")
        .any(|arg| arg == "--z3-mode")
    {
        return;
    }

    processed.insert(2, "--z3-mode".to_string());
}

fn argv0_is_z3(raw: &[String]) -> bool {
    let Some(program) = raw.first() else {
        return false;
    };
    matches!(
        std::path::Path::new(program)
            .file_name()
            .and_then(|name| name.to_str()),
        Some("z3" | "z3.exe")
    )
}

fn has_explicit_non_solve_subcommand(raw: &[String]) -> bool {
    for arg in raw.iter().skip(1) {
        if arg == "--" {
            break;
        }
        if arg.starts_with('-') {
            continue;
        }

        let lowered = arg.to_lowercase();
        if KNOWN_SUBCOMMANDS.contains(&lowered.as_str()) {
            return lowered != "solve";
        }

        return false;
    }

    false
}

fn z3_seconds_timeout_to_millis(timeout_str: &str) -> String {
    timeout_str
        .parse::<u64>()
        .map(|seconds| seconds.saturating_mul(1000).to_string())
        .unwrap_or_else(|_| timeout_str.to_string())
}

/// True when `arg` is a `key=value` naming a real libz3 module parameter that AY
/// does not implement, and can therefore accept-and-ignore rather than reject.
///
/// Everything AY genuinely honors is matched earlier in the preprocessor, so
/// reaching here means the knob has no effect in AY. Ignoring it cannot make an
/// answer unsound — these select an internal strategy, not the problem — but the
/// user is told on stderr regardless, because silently dropping a flag the caller
/// set is exactly the trap this project refuses to build.
///
/// A name z3 itself would reject is NOT ignorable: it stays a hard error, so a
/// typo still fails loudly on AY exactly as it fails on z3.
fn is_ignorable_z3_module_param(arg: &str) -> bool {
    split_z3_param(arg).is_some_and(|(key, _)| z3_params::is_known_z3_module_param(key))
}

fn is_allowlisted_z3_param(arg: &str) -> bool {
    let Some((key, value)) = split_z3_param(arg) else {
        return false;
    };

    match key {
        "fp.engine" => matches!(value, "spacer" | "auto-config" | "datalog" | "bmc"),
        "auto_config" | "ctrl_c" | "ctrl-c" | "debug_ref_count" | "debug-ref-count" | "model"
        | "model_validate" | "model.v2" | "model.compact" | "model.completion"
        | "model.partial" | "pp.bv-literals" | "pp.decimal" | "pp.fixed-indent"
        | "pp.single-line" | "proof" | "smtlib2_compliant" | "trace" | "type_check"
        | "type-check" | "unsat_core" | "warning" | "well_sorted_check" | "well-sorted-check" => {
            is_z3_bool_value(value)
        }
        "trace_file_name" => true,
        "random_seed"
        | "rlimit"
        | "pp.decimal_precision"
        | "pp.max-depth"
        | "pp.max-ribbon"
        | "sat.random_seed"
        | "smt.random_seed"
        | "fp.spacer.random_seed"
        | "nlsat.seed" => is_z3_unsigned_value(value),
        _ => false,
    }
}

fn handle_z3_key_value_param(arg: &str, processed: &mut Vec<String>) -> bool {
    let Some((key, value)) = split_z3_param(arg) else {
        return false;
    };

    match key {
        "timeout" if is_z3_unsigned_value(value) => {
            processed.push("--timeout".to_string());
            processed.push(value.to_string());
            true
        }
        "memory_max_size" if is_z3_unsigned_value(value) => {
            processed.push("--memory".to_string());
            processed.push(value.to_string());
            true
        }
        "stats" if is_z3_bool_value(value) => {
            if is_z3_true_value(value) {
                processed.push("--stats".to_string());
            }
            true
        }
        "dump_models" | "dump-models" if is_z3_bool_value(value) => {
            if is_z3_true_value(value) {
                processed.push("--z3-model".to_string());
            }
            true
        }
        "verbose" if is_z3_unsigned_value(value) => true,
        _ => false,
    }
}

fn split_z3_param(arg: &str) -> Option<(&str, &str)> {
    if arg.starts_with('-') {
        return None;
    }
    let (key, value) = arg.split_once('=')?;
    if key.is_empty() || value.is_empty() {
        return None;
    }
    Some((key, value))
}

fn looks_like_input_path_arg(arg: &str) -> bool {
    if std::path::Path::new(arg).exists() {
        return true;
    }

    let lower = arg.to_ascii_lowercase();
    [
        ".smt2",
        ".smt2.xz",
        ".smt2.gz",
        ".smt2.bz2",
        ".cnf",
        ".cnf.xz",
        ".cnf.gz",
        ".cnf.bz2",
        ".wcnf",
        ".wcnf.xz",
        ".qdimacs",
        ".aig",
        ".aag",
        ".sl",
        ".fzn",
        ".opb",
        ".mps",
        ".lp",
    ]
    .iter()
    .any(|suffix| lower.ends_with(suffix))
}

fn is_z3_bool_value(value: &str) -> bool {
    matches!(value, "true" | "false")
}

fn is_z3_true_value(value: &str) -> bool {
    value == "true"
}

fn is_z3_unsigned_value(value: &str) -> bool {
    !value.is_empty() && value.bytes().all(|b| b.is_ascii_digit())
}

struct MaterializedInput {
    logical_path: String,
    content: String,
    source_file: Option<std::fs::File>,
}

impl MaterializedInput {
    fn from_content(
        logical_path: String,
        content: String,
        source_file: Option<std::fs::File>,
    ) -> Self {
        Self {
            logical_path,
            content,
            source_file,
        }
    }

    fn path_string(&self) -> String {
        self.logical_path.clone()
    }

    fn preloaded(&self) -> (&str, Option<&std::fs::File>) {
        (self.content.as_str(), self.source_file.as_ref())
    }
}

fn content_already_requests_model(content: &str) -> bool {
    find_smtlib_command(content, "get-model").is_some()
}

fn append_get_model_command(content: &str) -> String {
    let Some(exit_index) = find_last_smtlib_command(content, "exit") else {
        let mut out = String::with_capacity(content.len() + "\n(get-model)\n".len());
        out.push_str(content);
        if !out.ends_with('\n') {
            out.push('\n');
        }
        out.push_str("(get-model)\n");
        return out;
    };

    let mut out = String::with_capacity(content.len() + "\n(get-model)\n".len());
    out.push_str(&content[..exit_index]);
    if !out.ends_with('\n') {
        out.push('\n');
    }
    out.push_str("(get-model)\n");
    out.push_str(&content[exit_index..]);
    out
}

fn find_smtlib_command(content: &str, command: &str) -> Option<usize> {
    find_smtlib_command_index(content, command, false)
}

fn find_last_smtlib_command(content: &str, command: &str) -> Option<usize> {
    find_smtlib_command_index(content, command, true)
}

fn find_smtlib_command_index(content: &str, command: &str, last: bool) -> Option<usize> {
    let bytes = content.as_bytes();
    let command = command.as_bytes();
    let mut found = None;
    let mut i = 0;
    let mut depth = 0usize;

    while i < bytes.len() {
        match bytes[i] {
            b';' => {
                i += 1;
                while i < bytes.len() && bytes[i] != b'\n' {
                    i += 1;
                }
            }
            b'"' => {
                i += 1;
                while i < bytes.len() {
                    if bytes[i] == b'"' {
                        if i + 1 < bytes.len() && bytes[i + 1] == b'"' {
                            i += 2;
                        } else {
                            i += 1;
                            break;
                        }
                    } else {
                        i += 1;
                    }
                }
            }
            b'|' => {
                i += 1;
                while i < bytes.len() {
                    let done = bytes[i] == b'|';
                    i += 1;
                    if done {
                        break;
                    }
                }
            }
            b'(' => {
                if depth == 0 && smtlib_command_matches_at(bytes, i, command) {
                    found = Some(i);
                    if !last {
                        return found;
                    }
                }
                depth += 1;
                i += 1;
            }
            b')' => {
                depth = depth.saturating_sub(1);
                i += 1;
            }
            _ => i += 1,
        }
    }

    found
}

fn smtlib_command_matches_at(bytes: &[u8], open_index: usize, command: &[u8]) -> bool {
    let mut i = open_index + 1;
    while i < bytes.len() && is_smtlib_whitespace(bytes[i]) {
        i += 1;
    }

    if i + command.len() > bytes.len() {
        return false;
    }

    if !bytes[i..i + command.len()]
        .iter()
        .zip(command)
        .all(|(actual, expected)| actual.eq_ignore_ascii_case(expected))
    {
        return false;
    }

    let next = i + command.len();
    next == bytes.len() || is_smtlib_command_delimiter(bytes[next])
}

fn is_smtlib_whitespace(byte: u8) -> bool {
    matches!(byte, b' ' | b'\t' | b'\n' | b'\r')
}

fn is_smtlib_command_delimiter(byte: u8) -> bool {
    is_smtlib_whitespace(byte) || matches!(byte, b')' | b';')
}

fn materialize_z3_model_input(content: &str) -> MaterializedInput {
    let should_append_model =
        !dimacs::is_dimacs_format(content) && !content_already_requests_model(content);
    let materialized = if should_append_model {
        append_get_model_command(content)
    } else {
        content.to_string()
    };
    MaterializedInput::from_content("<stdin-model>.smt2".to_string(), materialized, None)
}

fn materialize_z3_model_file_input(path: &str) -> Option<MaterializedInput> {
    use std::io::Read as _;

    let Ok(mut source_file) = std::fs::File::open(path) else {
        return None;
    };
    let mut content = String::new();
    if source_file.read_to_string(&mut content).is_err() {
        return None;
    }
    if dimacs::has_cnf_extension(path) || dimacs::is_dimacs_format(&content) {
        return None;
    }
    let materialized = if content_already_requests_model(&content) {
        content
    } else {
        append_get_model_command(&content)
    };
    Some(MaterializedInput::from_content(
        path.to_string(),
        materialized,
        Some(source_file),
    ))
}

/// If no known subcommand is present, inject "solve" at position 1.
///
/// All AY flags (`--stats`, `--verbose`, etc.) are subcommand-level flags
/// owned by `SolveArgs`. Inserting "solve" at position 1 (right after argv[0])
/// ensures clap routes ALL subsequent flags and arguments to the `Solve`
/// subcommand. This preserves backward compatibility: `ay --stats file.cnf`
/// becomes `ay solve --stats file.cnf`.
fn inject_solve_subcommand(args: &mut Vec<String>) {
    let mut has_help = false;
    for a in args.iter().skip(1) {
        if is_version_flag(a) {
            return;
        }
        has_help |= is_help_flag(a);
        if a == "--" {
            break;
        }
    }

    let mut first_non_flag_seen = false;

    for arg in args.iter().skip(1) {
        if arg == "--" {
            break;
        }
        // A flag starting with '-' is never a subcommand.
        if arg.starts_with('-') {
            continue;
        }
        // Non-flag: check if it's a known subcommand.
        if KNOWN_SUBCOMMANDS.contains(&arg.to_lowercase().as_str()) {
            return; // Subcommand already present — nothing to inject.
        }
        first_non_flag_seen = true;
        // First non-flag is NOT a subcommand — stop looking (it's a file path).
        break;
    }

    if has_help && !first_non_flag_seen {
        return;
    }

    // No subcommand found — inject "solve" right after argv[0].
    // This ensures all flags are parsed as SolveArgs, not top-level Cli flags.
    if args.len() > 1 {
        args.insert(1, "solve".to_string());
    } else {
        args.push("solve".to_string());
    }
}

fn solve_session_needs_wrapper(processed: &[String]) -> bool {
    if env::var_os(SESSION_PROVENANCE_CHILD_ENV).is_some()
        || env::var_os("CARGO_TARGET_TMPDIR").is_some()
        || ay_core::bv_cnf_dump_path_from_env().is_some()
    {
        return false;
    }

    if processed
        .iter()
        .skip(1)
        .take_while(|arg| arg.as_str() != "--")
        .any(|arg| is_help_or_version_flag(arg))
    {
        return false;
    }

    if !matches!(processed.get(1).map(String::as_str), Some("solve")) {
        return false;
    }

    for arg in processed
        .iter()
        .skip(2)
        .take_while(|arg| arg.as_str() != "--")
    {
        if arg == "--dump-bv-cnf" || arg.starts_with("--dump-bv-cnf=") {
            // A supervisor cannot authenticate the child's in-flight export
            // generation after an abort, so it must not synthesize Unknown.
            return false;
        }
        if arg == "--z3-mode" {
            return false;
        }
        // Preserve machine-readable stderr contracts.
        if matches!(
            arg.as_str(),
            "--features"
                | "--stats-json"
                | "--z3-print-params"
                | "--z3-print-param-descriptions"
                | "--z3-print-param-module"
                | "--z3-print-param-description"
                | "--unsupported-z3-option"
        ) {
            return false;
        }
    }

    true
}

/// Install a signal reaper that guarantees the re-exec'd solve-session child
/// (see `run_wrapped_solve_session`) always dies with the wrapper on an external
/// SIGINT/SIGTERM/SIGHUP — leaking ZERO orphan processes, exactly like z3.
///
/// The prior implementation merely *forwarded* the received signal to the child.
/// That silently leaked orphans in the common case where a harness kills only
/// the wrapper PID (or the terminal delivers Ctrl-C): the solver child inherits
/// an **ignored SIGINT** disposition when `ay` is launched as a background job,
/// so a forwarded SIGINT was a no-op and the child churned at ~100% CPU forever
/// while the wrapper blocked in `child.wait()`. SIGHUP was not handled at all, so
/// the wrapper died on its default disposition and orphaned the child.
///
/// `child_pid` is a shared slot the reaper reads: `0` means "no live child to
/// reap" (not spawned yet, or already `wait()`ed). The handlers are registered on
/// the *calling* thread before the child is spawned, so there is no startup
/// window in which a fatal signal hits the default disposition.
#[cfg(unix)]
fn install_child_reaper_on_signal(child_pid: Arc<std::sync::atomic::AtomicI32>) {
    use nix::sys::signal::{kill, Signal};
    use nix::unistd::Pid;
    use signal_hook::consts::{SIGHUP, SIGINT, SIGTERM};

    // Registers the sigaction handlers immediately (in this parent thread) so a
    // signal arriving before the reaper thread starts is still captured.
    let Ok(mut signals) = signal_hook::iterator::Signals::new([SIGINT, SIGTERM, SIGHUP]) else {
        return;
    };

    let _ = std::thread::Builder::new()
        .name("ay-wrapper-signals".to_string())
        .spawn(move || {
            for raw_signal in &mut signals {
                let pid = child_pid.load(Ordering::SeqCst);
                if pid <= 0 {
                    // No live child to reap: the signal is aimed at the wrapper
                    // itself. Exit promptly with the conventional 128+signal code
                    // (signal-hook has already suppressed the default terminate
                    // disposition, so without this the wrapper would hang).
                    std::process::exit(128 + raw_signal);
                }
                let target = Pid::from_raw(pid);
                if raw_signal == SIGTERM {
                    // Give the child its cooperative "unknown" shutdown (#8674),
                    // then guarantee death with a SIGKILL safety net if it hangs
                    // (e.g. a churning theory loop that never observes the timeout
                    // flag). The wrapper's main thread is blocked in `child.wait()`
                    // and returns the moment the child exits.
                    let _ = kill(target, Signal::SIGTERM);
                    let killer = Arc::clone(&child_pid);
                    let _ = std::thread::Builder::new()
                        .name("ay-wrapper-killnet".to_string())
                        .spawn(move || {
                            std::thread::sleep(Duration::from_secs(4));
                            let pid = killer.load(Ordering::SeqCst);
                            if pid > 0 {
                                let _ = kill(Pid::from_raw(pid), Signal::SIGKILL);
                            }
                        });
                } else {
                    // SIGINT / SIGHUP: the solver child ignores SIGINT (inherited
                    // background disposition) and has no cooperative path here, so
                    // hard-kill it immediately. ay then dies cleanly like z3,
                    // leaking nothing.
                    let _ = kill(target, Signal::SIGKILL);
                }
            }
        });
}

#[cfg(not(unix))]
fn install_child_reaper_on_signal(_child_pid: Arc<std::sync::atomic::AtomicI32>) {}

/// RAII guard that SIGKILLs the solve-session child if the wrapper unwinds out of
/// `run_wrapped_solve_session` (panic path) before a clean `child.wait()`.
/// `disarm()` runs after a successful wait so a completed run never signals a
/// possibly-reused PID. The normal path exits via `process::exit` (which skips
/// destructors) after already reaping the child through `wait()`, so this guard
/// only fires on abnormal unwinds — belt-and-suspenders atop the signal reaper.
#[cfg(unix)]
struct ChildKillGuard {
    pid: i32,
    armed: bool,
}

#[cfg(unix)]
impl ChildKillGuard {
    fn new(pid: i32) -> Self {
        Self { pid, armed: true }
    }

    fn disarm(&mut self) {
        self.armed = false;
    }
}

#[cfg(unix)]
impl Drop for ChildKillGuard {
    fn drop(&mut self) {
        if self.armed && self.pid > 0 {
            let _ = nix::sys::signal::kill(
                nix::unistd::Pid::from_raw(self.pid),
                nix::sys::signal::Signal::SIGKILL,
            );
        }
    }
}

fn exit_code_from_status(status: &std::process::ExitStatus) -> i32 {
    status
        .code()
        .or_else(|| exit_signal(status).map(|signal| 128 + signal))
        .unwrap_or(1)
}

fn session_outcome_from_status(status: &std::process::ExitStatus) -> build_info::SessionOutcome {
    if let Some(code) = status.code() {
        build_info::SessionOutcome::ExitCode(code)
    } else if let Some(signal) = exit_signal(status) {
        build_info::SessionOutcome::Signal(signal)
    } else {
        build_info::SessionOutcome::LaunchError
    }
}

#[cfg(unix)]
fn exit_signal(status: &std::process::ExitStatus) -> Option<i32> {
    use std::os::unix::process::ExitStatusExt;

    status.signal()
}

#[cfg(not(unix))]
fn exit_signal(_: &std::process::ExitStatus) -> Option<i32> {
    None
}

/// Whether a reaped solve-session child died from a CRASH (abnormal abort), as
/// opposed to exiting deliberately with a status code. Returns a short human
/// description of the crash for the fail-closed diagnostic, `None` otherwise.
///
/// Windows: fatal NTSTATUS codes carry the error-severity nibble (`0xC`), e.g.
/// `STATUS_STACK_BUFFER_OVERRUN` 0xC0000409 — Rust's fail-fast abort path,
/// which is how an allocation failure (`rust_oom`) or `std::process::abort()`
/// exits — `STATUS_STACK_OVERFLOW` 0xC00000FD, and `STATUS_ACCESS_VIOLATION`
/// 0xC0000005. Deliberate exits (0, 1, 2, 124, ...) never carry that severity,
/// so this cannot reclassify an intentional error exit.
///
/// Unix: fatal crash signals only — SIGABRT (the `rust_oom`/`abort()` path),
/// SIGSEGV, SIGBUS, SIGILL, SIGFPE, SIGTRAP. External control signals
/// (SIGTERM/SIGINT/SIGKILL/SIGHUP) keep the existing propagate-the-status
/// behavior: a harness kill is not the solver's crash to reinterpret.
fn solve_session_crash_description(status: &std::process::ExitStatus) -> Option<String> {
    #[cfg(windows)]
    {
        let code = status.code()?;
        let nt = code as u32;
        if nt >> 28 == 0xC {
            return Some(format!("exception code {nt:#010X}"));
        }
        None
    }
    #[cfg(unix)]
    {
        let signal = exit_signal(status)?;
        let fatal: &[i32] = &[
            nix::libc::SIGABRT,
            nix::libc::SIGSEGV,
            nix::libc::SIGBUS,
            nix::libc::SIGILL,
            nix::libc::SIGFPE,
            nix::libc::SIGTRAP,
        ];
        if fatal.contains(&signal) {
            return Some(format!("fatal signal {signal}"));
        }
        None
    }
    #[cfg(not(any(windows, unix)))]
    {
        let _ = status;
        None
    }
}

/// Emit a session provenance marker (`c ay.session.start` / `c ay.session.end`)
/// to stderr, unless `-q`/`--quiet` is active. Centralizes the commentary gate
/// for every supervisor emission site; stdout/proof/exit-code paths are never
/// touched.
fn eprint_session_marker(marker: String) {
    if !quiet_enabled() {
        safe_eprintln!("{marker}");
    }
}

/// Observe a reaped solve-session child (however it was born — `fork` or re-exec)
/// and turn its wait-status into the process's final answer, identically for both
/// supervisor variants. A fatal-signal death becomes the fail-closed `unknown`
/// verdict with a clean `exit(0)` (verdict scorers take the FIRST stdout line, so a
/// child that already printed `sat`/`unsat` before dying keeps its real verdict and
/// this trailing line is inert); a normal exit propagates the child's real exit code
/// untouched (a deliberate nonzero exit is never reclassified — the classifier fires
/// only on fatal signals). Never returns.
fn finish_supervised_session(start: Instant, status: &std::process::ExitStatus) -> ! {
    // A crash of the solve child must never cost the harness record
    // (#chc25-crash): convert an abnormal abort into the fail-closed `unknown`
    // verdict, mirroring the SIGTERM/hard-timeout fallbacks. The observed
    // producer is an allocation failure — `rust_oom` fail-fasts with SIGABRT
    // (0xC0000409 on Windows) when machine-wide memory pressure (e.g. a parallel
    // benchmark harness) exhausts commit before the child's own
    // `process_memory_exceeded()` checkpoints trip (chc-comp25 SLayerCF BV towers
    // at competition budgets). Verdict scorers take the FIRST status line, so if the
    // child already printed a verdict before dying this trailing line is inert; if
    // it died mid-solve this is the only status line and the record is a clean
    // Unknown instead of a crash. The session-end marker still logs the TRUE
    // abnormal outcome for provenance.
    if let Some(crash) = solve_session_crash_description(status) {
        let sat_competition_wrapper = sat_competition_wrapper_timeout_policy();
        safe_eprintln!("c solve session aborted abnormally ({crash}); failing closed to unknown");
        let _ = Write::write_all(
            &mut io::stdout(),
            timeout_stdout_line_for_sat_competition_wrapper(sat_competition_wrapper),
        );
        let _ = Write::flush(&mut io::stdout());
        let _ = Write::write_all(
            &mut io::stderr(),
            if sat_competition_wrapper {
                b"c solver process aborted\n".as_slice()
            } else {
                b"(:reason-unknown \"solver process aborted\")\n".as_slice()
            },
        );
        eprint_session_marker(build_info::session_end_marker(
            session_outcome_from_status(status),
            start.elapsed(),
        ));
        let _ = Write::flush(&mut io::stderr());
        // Exit as a clean "unknown" answer, not as a crash: 0 in both verdict
        // grammars (matches SAT_COMPETITION_UNKNOWN_EXIT_CODE).
        std::process::exit(0);
    }

    eprint_session_marker(build_info::session_end_marker(
        session_outcome_from_status(status),
        start.elapsed(),
    ));
    let _ = io::stdout().flush();
    let _ = io::stderr().flush();
    std::process::exit(exit_code_from_status(status));
}

/// Single-thread assertion — the fail-closed guard for the fork-before-threads
/// supervisor. Returns true only when the process is provably single-threaded, so a
/// `fork()` is the textbook-safe kind (no OTHER thread can hold a malloc/`Once`/
/// allocator lock the child would deadlock on). macOS answers via the libSystem
/// `pthread_is_threaded_np` predicate; every other platform returns false and falls
/// back to the re-exec supervisor — soundness is never at risk, only the speedup is
/// forfeited. Delegates to `ay-sys`, the workspace's only unsafe-permitting crate,
/// since `ay` is `#![forbid(unsafe_code)]`.
#[cfg(unix)]
fn process_is_single_threaded() -> bool {
    ay_sys::supervisor::process_is_single_threaded()
}

/// Crash-injection gate hook (#chc25-crash): when `AY_INTERNAL_TEST_ABORT_SOLVE_CHILD`
/// is set, drive the solve CHILD into the requested fatal-fault / hang class so the
/// crash-injection gate can assert the parent observer converts each one into a sound
/// `unknown` against the REAL binary's fork path. The hook can only terminate or hang
/// the child; it must never synthesize a definitive result before doing so. Never
/// fires on any production invocation (the env var is test-only); the fault
/// primitives live in `ay-sys::supervisor`.
///
/// The hang variants faithfully arm the child's OWN post-fork machinery — the timeout
/// watchdog (`set_global_timeout`, as `run_solve` does) or the cooperative SIGTERM
/// handler (`install_sigterm_handler`) — before livelocking, so they exercise that a
/// thread spawned AFTER the fork still self-terminates the child to `unknown`.
#[cfg(unix)]
fn maybe_inject_test_child_fault() {
    let Some(kind) = env::var_os("AY_INTERNAL_TEST_ABORT_SOLVE_CHILD") else {
        return;
    };
    match kind.to_string_lossy().trim() {
        // SIGABRT — the `rust_oom`/`abort()` OOM producer (default & back-compat "1").
        "" | "1" | "abort" | "abrt" | "oom" => std::process::abort(),
        // SIGSEGV — genuine null dereference.
        "segv" => ay_sys::supervisor::crash_null_deref(),
        // SIGBUS / SIGILL / SIGFPE / SIGTRAP — reliable SIG_DFL-reset + raise.
        "bus" => ay_sys::supervisor::die_with_signal(nix::libc::SIGBUS),
        "ill" => ay_sys::supervisor::die_with_signal(nix::libc::SIGILL),
        "fpe" => ay_sys::supervisor::die_with_signal(nix::libc::SIGFPE),
        "trap" => ay_sys::supervisor::die_with_signal(nix::libc::SIGTRAP),
        // Genuine stack overflow (guard-page fault → SIGILL on arm64 macOS).
        "stackoverflow" => ay_sys::supervisor::crash_stack_overflow(),
        // Livelock guarded by the child's OWN timeout watchdog, armed post-fork.
        "hang-watchdog" => {
            set_global_timeout(800);
            loop {
                std::hint::spin_loop();
            }
        }
        // Livelock ended by an external SIGTERM the parent reaper forwards, handled
        // cooperatively by the child's post-fork SIGTERM handler.
        "hang-sigterm" => {
            install_sigterm_handler();
            loop {
                std::hint::spin_loop();
            }
        }
        // Any other value defaults to the abort path (back-compat).
        _ => std::process::abort(),
    }
}

#[cfg(not(unix))]
fn maybe_inject_test_child_fault() {
    // Non-unix keeps only the original abort hook (the fork matrix is unix-only).
    if env::var_os("AY_INTERNAL_TEST_ABORT_SOLVE_CHILD").is_some() {
        std::process::abort();
    }
}

/// Outcome of the fork-before-threads supervisor for its caller.
#[cfg(unix)]
enum ForkSupervise {
    /// We are the forked CHILD (single-threaded, sharing the parent image): the
    /// caller must return so `main` continues into the in-line solve path.
    ChildContinue,
    /// `fork()` failed: the caller must degrade to the re-exec supervisor.
    FallBack,
}

/// Fork-before-threads supervisor (unix). Replaces the second-dyld `Command::spawn`
/// re-exec with a `fork()`: the child inherits the already-linked image via COW (no
/// process startup paid twice) and continues the in-line solve, while the parent
/// observer is kept VERBATIM — it reaps the child by PID and classifies its
/// wait-status through `finish_supervised_session`, so crash→unknown, OOM(SIGABRT)→
/// unknown, hang→unknown (the child arms its OWN watchdog post-fork, exactly as
/// today) and orphan-reaping on external SIGINT/SIGTERM/SIGHUP are all preserved.
///
/// PRECONDITION: the caller has verified `process_is_single_threaded()`, so this is
/// the textbook-safe use of `fork()` — the child is a normal single-threaded process
/// free to allocate, spawn solver/watchdog threads, and parse args. `start` and the
/// `session_start_marker` are owned by the caller so the marker prints exactly once
/// across the fork-vs-fallback choice, and stdout/stderr are already flushed so the
/// child cannot inherit and re-emit a buffered parent write.
///
/// The raw `fork`/`waitpid`/`pthread_sigmask` syscalls live in `ay-sys::supervisor`
/// (safe wrappers); the soundness-critical orchestration below stays in `ay`.
#[cfg(unix)]
fn fork_supervised_solve_session(start: Instant) -> ForkSupervise {
    use std::os::unix::process::ExitStatusExt;

    // Block the external control signals ACROSS the fork so there is no window in
    // which the child exists but the parent's reaper is not yet installed; a signal
    // arriving in that window stays pending and is handled once the parent unblocks.
    let saved_mask = ay_sys::supervisor::block_control_signals();

    match ay_sys::supervisor::fork_solve_child() {
        ay_sys::supervisor::ForkOutcome::Failed => {
            // fork() failed (resource exhaustion): restore the mask and let the
            // caller fall back to the re-exec supervisor. Never risks soundness.
            ay_sys::supervisor::restore_sigmask(&saved_mask);
            ForkSupervise::FallBack
        }

        ay_sys::supervisor::ForkOutcome::Child => {
            // ---- CHILD: single-threaded, shares the parent image (no second dyld) --
            // Restore the inherited signal mask so the solve sees normal dispositions
            // (cooperative SIGTERM shutdown etc.) exactly as the re-exec'd child does.
            ay_sys::supervisor::restore_sigmask(&saved_mask);

            // (The peak-RSS arena trim already applied in this process's FIRST
            // allocation and is inherited across the fork via COW — see
            // `ay_sys::ensure_arena_reserve_trimmed`; nothing to do here.)

            // Test-only hook (#chc25-crash): make the solve CHILD take a fatal-fault
            // path deterministically so the gate can assert the parent converts each
            // child crash into `unknown`. Re-pointed from the old provenance-child
            // env onto the post-fork child branch — this IS the real crash path now.
            maybe_inject_test_child_fault();

            // Fall through: `main` continues into install_sigterm_handler / parse /
            // run_solve, arming the child's own timeout watchdog just as today.
            ForkSupervise::ChildContinue
        }

        ay_sys::supervisor::ForkOutcome::Parent(pid) => {
            // ---- PARENT observer: reap the child by PID and classify (verbatim) ----
            // Shared PID slot read by the signal reaper; the reaper is installed AFTER
            // the fork so it is never inherited into the child, and while the control
            // signals are still blocked so no fatal signal slips through on the
            // default disposition.
            let child_pid = Arc::new(std::sync::atomic::AtomicI32::new(pid));
            install_child_reaper_on_signal(Arc::clone(&child_pid));
            // Reaper installed: unblock so its handlers can fire on the main thread.
            ay_sys::supervisor::restore_sigmask(&saved_mask);

            // Arm a Drop guard that SIGKILLs the child if this function unwinds
            // (panic) before a clean reap — belt-and-suspenders atop the reaper.
            let mut kill_guard = ChildKillGuard::new(pid);

            // Blocking reap, retrying EINTR internally. No parent-side timeout: the
            // hang/timeout guarantee is the child's OWN watchdog thread
            // (`set_global_timeout`), armed post-fork exactly as today.
            let Some(raw_status) = ay_sys::supervisor::wait_for_child(pid) else {
                // Unrecoverable waitpid failure: never leak the child.
                ay_sys::supervisor::kill_and_reap(pid);
                child_pid.store(0, Ordering::SeqCst);
                kill_guard.disarm();
                safe_eprintln!("Error: failed to wait for solve session");
                eprint_session_marker(build_info::session_end_marker(
                    build_info::SessionOutcome::LaunchError,
                    start.elapsed(),
                ));
                let _ = io::stderr().flush();
                std::process::exit(1);
            };

            // Child reaped cleanly: retire the slot and guard so a late signal can
            // never target a PID the OS may have recycled.
            child_pid.store(0, Ordering::SeqCst);
            kill_guard.disarm();

            finish_supervised_session(start, &std::process::ExitStatus::from_raw(raw_status));
        }
    }
}

/// Dispatch the solve-session supervisor: prefer fork-before-threads (no second
/// dyld) when the process is provably single-threaded, otherwise fail closed to the
/// re-exec supervisor. Prints the `session_start_marker` exactly once and flushes
/// stdio before any fork. Returns ONLY in the forked solve child (so `main`
/// continues into the in-line solve); the parent observer and the re-exec fallback
/// both `exit` and never return.
fn run_wrapped_solve_session(raw_args: &[String]) {
    let start = Instant::now();
    eprint_session_marker(build_info::session_start_marker());
    // The child must not inherit and re-emit a buffered parent write.
    let _ = io::stdout().flush();
    let _ = io::stderr().flush();

    #[cfg(unix)]
    {
        // Fail-closed guard: take the fork path only when provably single-threaded.
        // `AY_INTERNAL_FORCE_REEXEC_SUPERVISOR` is a test-only override that forces
        // the fallback so the gate can prove the re-exec supervisor still converts a
        // crash to a sound `unknown` (never set on any production invocation).
        if process_is_single_threaded()
            && env::var_os("AY_INTERNAL_FORCE_REEXEC_SUPERVISOR").is_none()
        {
            match fork_supervised_solve_session(start) {
                ForkSupervise::ChildContinue => return, // solve in-line in the child
                ForkSupervise::FallBack => {}           // fork() failed → re-exec
            }
        }
    }

    // Non-macOS / threaded / fork-failed / forced: the re-exec supervisor (no return).
    reexec_supervised_solve_session(raw_args, start);
}

/// The original re-exec supervisor, retained as the fail-closed fallback whenever
/// the pre-fork single-thread assertion does not hold (or `fork()` fails), and as
/// the only supervisor on non-unix. It re-execs the full binary as a child so the
/// worst case is exactly today's behavior. Never returns.
fn reexec_supervised_solve_session(raw_args: &[String], start: Instant) -> ! {
    let current_exe = match env::current_exe() {
        Ok(path) => path,
        Err(error) => {
            safe_eprintln!("Error: failed to resolve current executable: {error}");
            eprint_session_marker(build_info::session_end_marker(
                build_info::SessionOutcome::LaunchError,
                start.elapsed(),
            ));
            let _ = io::stderr().flush();
            std::process::exit(1);
        }
    };

    // Shared PID of the child, read by the signal reaper. Installed BEFORE the
    // spawn so the SIGINT/SIGTERM/SIGHUP handlers exist for the child's whole
    // lifetime and no fatal signal can slip through on the default disposition.
    let child_pid = Arc::new(std::sync::atomic::AtomicI32::new(0));
    install_child_reaper_on_signal(Arc::clone(&child_pid));

    let mut command = std::process::Command::new(current_exe);
    command
        .args(raw_args.iter().skip(1))
        .env(SESSION_PROVENANCE_CHILD_ENV, "1")
        .stdin(std::process::Stdio::inherit())
        .stdout(std::process::Stdio::inherit())
        .stderr(std::process::Stdio::inherit());

    // Peak-RSS trim: the solve child is where all the real allocation (and thus
    // peak RSS) lives. mimalloc's eager arena reservation can make the committed
    // high-water mark substantially exceed the live heap on churn-heavy solves.
    // Disabling that reservation lets mimalloc commit OS pages at segment
    // granularity, tracking live bytes more closely. This allocator layout knob
    // does not change solver semantics. It is injected only on the child spawn
    // and only when the user has not set it, so an explicit
    // MIMALLOC_ARENA_RESERVE always wins.
    if env::var_os("MIMALLOC_ARENA_RESERVE").is_none() {
        command.env("MIMALLOC_ARENA_RESERVE", "0");
    }

    let mut child = match command.spawn() {
        Ok(child) => child,
        Err(error) => {
            safe_eprintln!("Error: failed to launch solve session: {error}");
            eprint_session_marker(build_info::session_end_marker(
                build_info::SessionOutcome::LaunchError,
                start.elapsed(),
            ));
            let _ = io::stderr().flush();
            std::process::exit(1);
        }
    };

    // Publish the live PID so the reaper can kill it, and arm a Drop guard that
    // SIGKILLs it if this function unwinds (panic) before a clean `wait()`.
    let raw_pid = i32::try_from(child.id()).unwrap_or(0);
    child_pid.store(raw_pid, Ordering::SeqCst);
    #[cfg(unix)]
    let mut kill_guard = ChildKillGuard::new(raw_pid);

    let status = match child.wait() {
        Ok(status) => status,
        Err(error) => {
            // Never leak the child if we failed to reap it.
            let _ = child.kill();
            let _ = child.wait();
            safe_eprintln!("Error: failed to wait for solve session: {error}");
            eprint_session_marker(build_info::session_end_marker(
                build_info::SessionOutcome::LaunchError,
                start.elapsed(),
            ));
            let _ = io::stderr().flush();
            std::process::exit(1);
        }
    };

    // Child reaped cleanly: retire the slot and guard so a late signal can never
    // target a PID the OS may have recycled.
    child_pid.store(0, Ordering::SeqCst);
    #[cfg(unix)]
    kill_guard.disarm();

    // Classify the wait-status identically to the fork supervisor: crash → sound
    // `unknown`+exit(0), normal exit → propagate the child's real exit code.
    finish_supervised_session(start, &status);
}

// ---------------------------------------------------------------------------
// Execution mode determination (preserved for tests)
// ---------------------------------------------------------------------------

fn determine_execution_mode(
    stdin_mode: bool,
    file_arg: Option<&String>,
    chc_mode: ChcMode,
) -> ExecutionMode {
    if stdin_mode {
        return ExecutionMode::Interactive;
    }

    if file_arg.is_none() {
        return ExecutionMode::Interactive;
    }

    match chc_mode {
        ChcMode::None => ExecutionMode::AutoFile,
        // Keep `--chc` and `--portfolio` as aliases to preserve benchmark behavior.
        ChcMode::Chc | ChcMode::Portfolio => ExecutionMode::PortfolioFile,
    }
}

// ---------------------------------------------------------------------------
// Solve execution bridge
// ---------------------------------------------------------------------------

fn comparable_output_path(path: &FsPath) -> io::Result<PathBuf> {
    match std::fs::symlink_metadata(path) {
        Ok(metadata) if metadata.file_type().is_symlink() => {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                format!(
                    "symbolic-link path '{}' is unsupported at the solver artifact boundary",
                    path.display()
                ),
            ));
        }
        Ok(_) => return std::fs::canonicalize(path),
        Err(error) if error.kind() == io::ErrorKind::NotFound => {}
        Err(error) => return Err(error),
    }
    let absolute = if path.is_absolute() {
        path.to_path_buf()
    } else {
        env::current_dir()?.join(path)
    };
    let mut normalized = PathBuf::new();
    for component in absolute.components() {
        match component {
            std::path::Component::Prefix(prefix) => normalized.push(prefix.as_os_str()),
            std::path::Component::RootDir => normalized.push(std::path::MAIN_SEPARATOR_STR),
            std::path::Component::CurDir => {}
            std::path::Component::ParentDir => {
                if !normalized.pop() {
                    return Err(io::Error::new(
                        io::ErrorKind::InvalidInput,
                        format!("path '{}' escapes the filesystem root", path.display()),
                    ));
                }
            }
            std::path::Component::Normal(component) => normalized.push(component),
        }
    }

    // Resolve the nearest existing ancestor, then append the normalized
    // missing suffix. This keeps `..` and symlinked-parent aliases comparable
    // even when one or more destination directories do not exist yet.
    let mut cursor = normalized.as_path();
    let mut missing = Vec::new();
    loop {
        match std::fs::symlink_metadata(cursor) {
            Ok(_) => break,
            Err(error) if error.kind() == io::ErrorKind::NotFound => {
                let name = cursor.file_name().ok_or_else(|| {
                    io::Error::new(io::ErrorKind::InvalidInput, "path has no existing ancestor")
                })?;
                missing.push(name.to_os_string());
                cursor = cursor.parent().ok_or_else(|| {
                    io::Error::new(io::ErrorKind::InvalidInput, "path has no existing ancestor")
                })?;
            }
            Err(error) => return Err(error),
        }
    }
    let mut comparable = std::fs::canonicalize(cursor)?;
    for component in missing.iter().rev() {
        comparable.push(component);
    }
    Ok(comparable)
}

fn comparable_read_path(path: &FsPath) -> io::Result<PathBuf> {
    match std::fs::canonicalize(path) {
        Ok(path) => Ok(path),
        Err(error) if error.kind() == io::ErrorKind::NotFound => comparable_output_path(path),
        Err(error) => Err(error),
    }
}

fn certificate_path_key(path: &FsPath) -> io::Result<String> {
    // This key is only a conservative preflight: exact filesystem identity is
    // checked separately below. Lossy Unicode case folding may reject two
    // distinct exotic names, but it must never allow a likely case alias to
    // destroy an input or another output.
    Ok(path.as_os_str().to_string_lossy().to_lowercase())
}

fn certificate_paths_may_alias(left: &FsPath, right: &FsPath) -> io::Result<bool> {
    if left == right || certificate_path_key(left)? == certificate_path_key(right)? {
        return Ok(true);
    }

    let (Ok(left_metadata), Ok(right_metadata)) =
        (std::fs::metadata(left), std::fs::metadata(right))
    else {
        return Ok(false);
    };
    #[cfg(unix)]
    {
        use std::os::unix::fs::MetadataExt as _;
        Ok(left_metadata.dev() == right_metadata.dev()
            && left_metadata.ino() == right_metadata.ino())
    }
    #[cfg(windows)]
    {
        use std::os::windows::fs::MetadataExt as _;
        return Ok(left_metadata.volume_serial_number().is_some()
            && left_metadata.volume_serial_number() == right_metadata.volume_serial_number()
            && left_metadata.file_index().is_some()
            && left_metadata.file_index() == right_metadata.file_index());
    }
    #[cfg(not(any(unix, windows)))]
    {
        Ok(false)
    }
}

fn certificate_path_is_within(path: &FsPath, directory: &FsPath) -> io::Result<bool> {
    if certificate_paths_may_alias(path, directory)? {
        return Ok(true);
    }
    let path = certificate_path_key(path)?;
    let mut directory = certificate_path_key(directory)?;
    if !directory.ends_with(std::path::MAIN_SEPARATOR) {
        directory.push(std::path::MAIN_SEPARATOR);
    }
    Ok(path.starts_with(&directory))
}

fn solve_artifact_path_collision(
    args: &SolveArgs,
    dump_bv_cnf: Option<&FsPath>,
) -> io::Result<Option<String>> {
    let mut read_paths: Vec<(&str, PathBuf)> = Vec::new();
    for (label, path) in [
        ("input", args.file.as_deref()),
        ("replay input", args.replay.as_deref()),
        ("Lean binary", args.lean_path.as_deref()),
        ("solution witness", args.solution_file.as_deref()),
    ] {
        if let Some(path) = path {
            read_paths.push((label, comparable_read_path(path)?));
        }
    }

    let mut output_paths: Vec<(&str, PathBuf)> = Vec::new();
    for (label, path) in [
        ("progress JSON", args.progress_json.as_deref()),
        ("proof", args.proof.as_deref()),
        ("proof artifact", args.proof_artifact.as_deref()),
        ("diagnostic output", args.diagnostic_file.as_deref()),
        ("decision trace", args.decision_trace.as_deref()),
        ("trace output", args.trace_file.as_deref()),
        ("encoding dump", args.dump_encoding.as_deref()),
        ("DRAT proof", args.drat.as_deref()),
        ("binary DRAT proof", args.drat_binary.as_deref()),
        ("LRAT proof", args.lrat.as_deref()),
        ("binary LRAT proof", args.lrat_binary.as_deref()),
        ("decision log", args.decision_log.as_deref()),
        (
            "DPLL diagnostic output",
            args.dpll_diagnostic_file.as_deref(),
        ),
        ("DPLL trace output", args.dpll_trace_file.as_deref()),
        ("BV CNF output", dump_bv_cnf),
    ] {
        if let Some(path) = path {
            output_paths.push((label, comparable_output_path(path)?));
        }
    }

    let has_explicit_proof = args.proof.is_some()
        || args.drat.is_some()
        || args.drat_binary.is_some()
        || args.lrat.is_some()
        || args.lrat_binary.is_some();
    if !has_explicit_proof
        && !default_proofs_suppressed(args.no_proof, args.z3_mode, competition_mode(args))
    {
        if let Some((path, format)) = default_proof_path(args.file.as_deref()) {
            output_paths.push(("default proof", comparable_output_path(FsPath::new(&path))?));
            if format == ProofFormat::Drat {
                let status_path = dimacs::dimacs_proof_status_path(&path);
                let status_lock_path = dimacs::dimacs_proof_status_lock_path(&status_path);
                output_paths.push((
                    "default proof status",
                    comparable_output_path(&status_path)?,
                ));
                output_paths.push((
                    "default proof status transaction lock",
                    comparable_output_path(&status_lock_path)?,
                ));
            }
            if format == ProofFormat::Alethe {
                let mut chc_path = PathBuf::from(path);
                chc_path.set_extension("chccert");
                output_paths.push((
                    "default CHC certificate",
                    comparable_output_path(&chc_path)?,
                ));
            }
        }
    }

    for (output_label, output) in &output_paths {
        for (read_label, read) in &read_paths {
            if certificate_paths_may_alias(output, read)? {
                return Ok(Some(format!(
                    "{output_label} path '{}' aliases the {read_label} path '{}'",
                    output.display(),
                    read.display()
                )));
            }
        }
    }
    for left in 0..output_paths.len() {
        for right in (left + 1)..output_paths.len() {
            let (left_label, left_path) = &output_paths[left];
            let (right_label, right_path) = &output_paths[right];
            if certificate_paths_may_alias(left_path, right_path)? {
                return Ok(Some(format!(
                    "{left_label} path '{}' aliases the {right_label} path '{}'",
                    left_path.display(),
                    right_path.display()
                )));
            }
        }
    }

    let mut output_directories = Vec::new();
    for (label, directory) in [
        (
            "firewall Lean output directory",
            args.emit_firewall_lean.as_deref(),
        ),
        ("k-induction dump directory", args.kind_dump_dir.as_deref()),
    ] {
        if let Some(directory) = directory {
            output_directories.push((label, comparable_output_path(directory)?));
        }
    }
    for (directory_label, directory) in &output_directories {
        for (read_label, read) in &read_paths {
            if certificate_path_is_within(read, directory)?
                || certificate_path_is_within(directory, read)?
            {
                return Ok(Some(format!(
                    "{directory_label} '{}' overlaps the {read_label} path '{}'",
                    directory.display(),
                    read.display()
                )));
            }
        }
        for (output_label, output) in &output_paths {
            if certificate_path_is_within(output, directory)?
                || certificate_path_is_within(directory, output)?
            {
                return Ok(Some(format!(
                    "{output_label} path '{}' overlaps the {directory_label} '{}'",
                    output.display(),
                    directory.display()
                )));
            }
        }
    }
    for left in 0..output_directories.len() {
        for right in (left + 1)..output_directories.len() {
            let (left_label, left_path) = &output_directories[left];
            let (right_label, right_path) = &output_directories[right];
            if certificate_path_is_within(left_path, right_path)?
                || certificate_path_is_within(right_path, left_path)?
            {
                return Ok(Some(format!(
                    "{left_label} '{}' overlaps the {right_label} '{}'",
                    left_path.display(),
                    right_path.display()
                )));
            }
        }
    }
    Ok(None)
}

fn bv_cnf_dump_lock_path(dump: &FsPath) -> io::Result<PathBuf> {
    let file_name = dump
        .file_name()
        .ok_or_else(|| io::Error::new(io::ErrorKind::InvalidInput, "path has no file name"))?;
    let parent = dump
        .parent()
        .filter(|parent| !parent.as_os_str().is_empty())
        .unwrap_or_else(|| FsPath::new("."));
    Ok(parent.join(format!(".{}.ay-bv-cnf.lock", file_name.to_string_lossy())))
}

fn bv_cnf_dump_collision(args: &SolveArgs, dump: &FsPath) -> io::Result<Option<String>> {
    let comparable_dump = comparable_output_path(dump)?;
    let cnf_lock = bv_cnf_dump_lock_path(&comparable_dump)?;
    let comparable_cnf_lock = comparable_output_path(&cnf_lock)?;
    let bv_drat = explicit_bv_drat_target(args).map(|(path, _)| PathBuf::from(path));

    // Treat the CNF, its lock, the optional paired DRAT, and its lock as one
    // certificate transaction. Every pair must be disjoint, including aliases
    // through hard links, case folding, `..`, and symlinked parent directories.
    let mut certificate_paths = vec![
        ("CNF output", dump.to_path_buf(), comparable_dump),
        (
            "CNF coordination lock",
            cnf_lock.clone(),
            comparable_cnf_lock,
        ),
    ];
    if let Some(drat) = bv_drat.as_deref() {
        let comparable_drat = comparable_output_path(drat)?;
        let drat_lock = bv_cnf_dump_lock_path(&comparable_drat)?;
        let comparable_drat_lock = comparable_output_path(&drat_lock)?;
        certificate_paths.push(("proof path", drat.to_path_buf(), comparable_drat));
        certificate_paths.push(("DRAT coordination lock", drat_lock, comparable_drat_lock));
    }

    for left in 0..certificate_paths.len() {
        for right in (left + 1)..certificate_paths.len() {
            let (left_label, left_requested, left_comparable) = &certificate_paths[left];
            let (right_label, right_requested, right_comparable) = &certificate_paths[right];
            if certificate_paths_may_alias(left_comparable, right_comparable)? {
                let message = if left == 0 && right_label == &"proof path" {
                    format!(
                        "--dump-bv-cnf output '{}' aliases the proof path '{}'",
                        left_requested.display(),
                        right_requested.display()
                    )
                } else if left == 0 && right == 1 {
                    format!(
                        "--dump-bv-cnf output '{}' aliases its coordination lock '{}'",
                        left_requested.display(),
                        right_requested.display()
                    )
                } else {
                    format!(
                        "BV certificate {left_label} '{}' aliases the {right_label} '{}'",
                        left_requested.display(),
                        right_requested.display()
                    )
                };
                return Ok(Some(message));
            }
        }
    }

    // Every explicit file or directory path in SolveArgs participates in this
    // boundary.  Read-side aliases can be truncated by the export transaction;
    // write-side aliases can replace a finalized certificate after the check.
    let selected_bv_drat = bv_drat.is_some();
    let explicit_paths: [(&str, Option<&FsPath>); 20] = [
        ("input", args.file.as_deref()),
        (
            "firewall Lean output directory",
            args.emit_firewall_lean.as_deref(),
        ),
        ("progress JSON", args.progress_json.as_deref()),
        (
            "proof",
            (!selected_bv_drat)
                .then_some(args.proof.as_deref())
                .flatten(),
        ),
        ("proof artifact", args.proof_artifact.as_deref()),
        ("Lean binary", args.lean_path.as_deref()),
        ("replay input", args.replay.as_deref()),
        ("diagnostic output", args.diagnostic_file.as_deref()),
        ("decision trace", args.decision_trace.as_deref()),
        ("solution witness", args.solution_file.as_deref()),
        ("trace output", args.trace_file.as_deref()),
        ("encoding dump", args.dump_encoding.as_deref()),
        (
            "DRAT proof",
            (!selected_bv_drat)
                .then_some(args.drat.as_deref())
                .flatten(),
        ),
        (
            "binary DRAT proof",
            (!selected_bv_drat)
                .then_some(args.drat_binary.as_deref())
                .flatten(),
        ),
        ("LRAT proof", args.lrat.as_deref()),
        ("binary LRAT proof", args.lrat_binary.as_deref()),
        ("decision log", args.decision_log.as_deref()),
        (
            "DPLL diagnostic output",
            args.dpll_diagnostic_file.as_deref(),
        ),
        ("DPLL trace output", args.dpll_trace_file.as_deref()),
        ("k-induction dump directory", args.kind_dump_dir.as_deref()),
    ];
    for (label, candidate) in explicit_paths {
        if let Some(candidate) = candidate {
            let candidate = comparable_output_path(candidate)?;
            for (certificate_label, requested, comparable) in &certificate_paths {
                if certificate_paths_may_alias(&candidate, comparable)? {
                    let subject = match *certificate_label {
                        "CNF output" => format!("--dump-bv-cnf output '{}'", dump.display()),
                        "CNF coordination lock" => {
                            format!("--dump-bv-cnf coordination lock '{}'", requested.display())
                        }
                        "proof path" => {
                            format!("BV DRAT proof path '{}'", requested.display())
                        }
                        _ => format!("BV DRAT coordination lock '{}'", requested.display()),
                    };
                    return Ok(Some(format!("{subject} aliases the {label} path")));
                }
            }
        }
    }

    for (label, directory) in [
        (
            "firewall Lean output directory",
            args.emit_firewall_lean.as_deref(),
        ),
        ("k-induction dump directory", args.kind_dump_dir.as_deref()),
    ] {
        if let Some(directory) = directory {
            let directory = comparable_output_path(directory)?;
            for (_, _, comparable) in &certificate_paths {
                if certificate_path_is_within(comparable, &directory)? {
                    return Ok(Some(format!(
                        "a BV certificate output or coordination lock is inside the {label}"
                    )));
                }
            }
        }
    }

    let has_explicit_proof = args.proof.is_some()
        || args.drat.is_some()
        || args.drat_binary.is_some()
        || args.lrat.is_some()
        || args.lrat_binary.is_some();
    if !has_explicit_proof
        && !default_proofs_suppressed(args.no_proof, args.z3_mode, competition_mode(args))
    {
        if let Some((default_path, _)) = default_proof_path(args.file.as_deref()) {
            let default_path = comparable_output_path(FsPath::new(&default_path))?;
            for (certificate_label, requested, comparable) in &certificate_paths {
                if certificate_paths_may_alias(&default_path, comparable)? {
                    let subject = if *certificate_label == "CNF output" {
                        format!("--dump-bv-cnf output '{}'", dump.display())
                    } else {
                        format!(
                            "BV certificate {certificate_label} '{}'",
                            requested.display()
                        )
                    };
                    return Ok(Some(format!("{subject} aliases the default proof path")));
                }
            }
        }
    }
    Ok(None)
}

fn trace_config_from_solve_args(
    args: &SolveArgs,
    dump_bv_cnf_path: Option<&FsPath>,
) -> ay_core::TraceConfig {
    // The single-invocation BV DRAT certificate is only wired when the CNF dump
    // is also requested: the dump transaction already fails closed for any
    // non-pure-QF_BV check, so it is the exact gate that keeps a DRAT from ever
    // being emitted for an unsupported (non-bit-blastable) logic.
    let bv_drat = dump_bv_cnf_path.and_then(|_| explicit_bv_drat_target(args));
    ay_core::TraceConfig {
        diagnostic_path: args
            .diagnostic_file
            .as_ref()
            .map(|path| path.to_string_lossy().into_owned()),
        decision_trace_path: args
            .decision_trace
            .as_ref()
            .map(|path| path.to_string_lossy().into_owned()),
        replay_trace_path: args
            .replay
            .as_ref()
            .map(|path| path.to_string_lossy().into_owned()),
        trace_file_path: args
            .trace_file
            .as_ref()
            .map(|path| path.to_string_lossy().into_owned()),
        solution_file_path: args
            .solution_file
            .as_ref()
            .map(|path| path.to_string_lossy().into_owned()),
        decision_log_path: args
            .decision_log
            .as_ref()
            .map(|path| path.to_string_lossy().into_owned()),
        dump_bv_cnf_path: dump_bv_cnf_path
            .and_then(FsPath::to_str)
            .map(ToOwned::to_owned),
        bv_drat_path: bv_drat.as_ref().map(|(path, _)| path.clone()),
        bv_drat_binary: bv_drat.as_ref().map(|(_, binary)| *binary).unwrap_or(false),
        // Populated separately in `run_solve` for `--self-check` (not here — it
        // requires the parsed `SolveArgs.self_check` plus a private temp dir).
        bv_drat_self_cert_cnf_path: None,
        bv_drat_self_cert_drat_path: None,
        kind_dump_dir: args
            .kind_dump_dir
            .as_ref()
            .map(|path| path.to_string_lossy().into_owned()),
        dump_encoding_path: args
            .dump_encoding
            .as_ref()
            .map(|path| path.to_string_lossy().into_owned()),
    }
}

struct PreflightedDecisionTraceFile {
    file: Option<std::fs::File>,
    content: String,
}

fn validate_decision_trace_content(path: &str, content: &str) -> Result<(), String> {
    if dimacs::has_cnf_extension(path) || dimacs::is_dimacs_format(content) {
        ay_sat::parse_dimacs(content).map_err(|error| {
            format!("--decision-trace requires fully parseable DIMACS input: {error}")
        })?;
        return Err(
            "--decision-trace is currently unsupported for DIMACS input; use a single-query SMT-LIB FILE"
                .to_string(),
        );
    }
    if is_horn_logic(content) || is_fixedpoint_format(content) {
        return Err(
            "--decision-trace is incompatible with CHC/fixedpoint input; decision traces support one SMT-LIB decision query"
                .to_string(),
        );
    }
    let commands = ay_frontend::parse(content).map_err(|error| {
        format!("--decision-trace requires a fully parseable single-query SMT-LIB input: {error}")
    })?;
    let query_count = commands
        .iter()
        .filter(|command| {
            matches!(
                command,
                ay_frontend::Command::CheckSat | ay_frontend::Command::CheckSatAssuming(_)
            )
        })
        .count();
    if query_count != 1 {
        return Err(format!(
            "--decision-trace requires exactly one check-sat/check-sat-assuming query; input contains {query_count}"
        ));
    }
    Ok(())
}

fn preflight_decision_trace_file(path: &str) -> Result<PreflightedDecisionTraceFile, String> {
    use std::io::Read as _;

    // Open once and retain this descriptor through solving. The pathname may
    // be replaced after preflight, but the verdict and trace must describe the
    // exact bytes whose single-query shape was validated here.
    let mut file = std::fs::File::open(path)
        .map_err(|error| format!("cannot open decision-trace input '{path}': {error}"))?;
    let mut content = String::new();
    file.read_to_string(&mut content)
        .map_err(|error| format!("cannot read decision-trace input '{path}': {error}"))?;
    validate_decision_trace_content(path, &content)?;
    Ok(PreflightedDecisionTraceFile {
        file: Some(file),
        content,
    })
}

/// Execute the solve subcommand by bridging SolveArgs to existing execution logic.
fn run_solve(args: &SolveArgs) {
    // SIGTERM -> synthesized "unknown" verdict (#8674) is a SOLVE contract:
    // an SMT solver must always emit sat/unsat/unknown. Installed here (at the
    // very top, so the argument-validation preamble is covered too) rather
    // than in main() so non-solve subcommands (`ay check`, `ay bench`, ...)
    // keep default SIGTERM termination instead of printing a spurious solver
    // verdict line on their machine-parsed stdout.
    install_sigterm_handler();

    if args.z3_mode {
        Z3_MODE_ENABLED.store(true, Ordering::SeqCst);
    }
    if args.z3_model {
        Z3_MODEL_ENABLED.store(true, Ordering::SeqCst);
    }

    // `-q`/`--quiet`: suppress AY's stderr provenance commentary only. The
    // supervisor already set this from the raw argv (so the pre-fork session
    // marker is covered); set it again here as the authoritative flag for the
    // in-process solve path. Never touches stdout/proof/exit-code contracts.
    if args.quiet {
        QUIET_ENABLED.store(true, Ordering::SeqCst);
    }

    let dump_bv_cnf_path = args
        .dump_bv_cnf
        .clone()
        .or_else(|| ay_core::bv_cnf_dump_path_from_env().map(PathBuf::from));
    // Path-collision preflight runs in ONE documented, deterministic order:
    // the BV CNF certificate-transaction boundary (`bv_cnf_dump_collision`,
    // which names the certificate member as the subject of every rejection)
    // is checked first when `--dump-bv-cnf` is active, then the generic solve
    // artifact boundary (`solve_artifact_path_collision`). Both checks always
    // run before any solve output is created, so the rejected set is the
    // union of both boundaries regardless of which message fires first.
    if let Some(path) = dump_bv_cnf_path.as_deref() {
        if path.to_str().is_none() {
            safe_eprintln!("Error: --dump-bv-cnf requires a UTF-8 output path");
            std::process::exit(1);
        }
        match bv_cnf_dump_collision(args, path) {
            Ok(Some(message)) => {
                safe_eprintln!("Error: {message}");
                std::process::exit(1);
            }
            Ok(None) => {}
            Err(error) => {
                safe_eprintln!(
                    "Error: cannot validate --dump-bv-cnf output '{}': {error}",
                    path.display()
                );
                std::process::exit(1);
            }
        }
    }
    match solve_artifact_path_collision(args, dump_bv_cnf_path.as_deref()) {
        Ok(Some(message)) => {
            safe_eprintln!("Error: {message}");
            std::process::exit(1);
        }
        Ok(None) => {}
        Err(error) => {
            safe_eprintln!("Error: cannot validate solve input/output paths: {error}");
            std::process::exit(1);
        }
    }

    // `--self-check` BV DRAT self-certification (batteries-included, no env
    // vars): when the user asked AY to check its own answers but did NOT request
    // an explicit `--dump-bv-cnf`, point two private temp files at the eager
    // bit-blast CNF and its single-invocation DRAT. The emission machinery only
    // ever reaches these paths through the thread-local self-cert arm (armed
    // solely around an eligible top-level pure-QF_BV check-sat), so populating
    // them here does NOT turn on any user-facing `--dump-bv-cnf` handling. The
    // files are cleaned up before `run_solve` returns.
    let mut trace_config = trace_config_from_solve_args(args, dump_bv_cnf_path.as_deref());
    let self_cert_bv_paths: Option<(PathBuf, PathBuf)> =
        if args.self_check && dump_bv_cnf_path.is_none() {
            let dir = env::temp_dir();
            let pid = std::process::id();
            let nanos = std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .map(|d| d.as_nanos())
                .unwrap_or(0);
            let cnf = dir.join(format!("ay-selfcert-{pid}-{nanos}.cnf"));
            let drat = dir.join(format!("ay-selfcert-{pid}-{nanos}.drat"));
            match (cnf.to_str(), drat.to_str()) {
                (Some(cnf_str), Some(drat_str)) => {
                    trace_config.bv_drat_self_cert_cnf_path = Some(cnf_str.to_owned());
                    trace_config.bv_drat_self_cert_drat_path = Some(drat_str.to_owned());
                    Some((cnf, drat))
                }
                // Non-UTF-8 temp dir: skip self-cert emission (fail-closed —
                // BV unsat simply stays `unknown` under --self-check).
                _ => None,
            }
        } else {
            None
        };

    // Install the path configuration before any solve-mode early exit.  A
    // requested certificate is invalidated immediately, so argument/setup
    // failures cannot leave a previous process or previous query authoritative.
    if ay_core::set_global_trace_config(trace_config).is_err() {
        if let Some(path) = dump_bv_cnf_path.as_deref() {
            let _ = std::fs::remove_file(path);
        }
        safe_eprintln!(
            "Error: cannot install --dump-bv-cnf configuration because trace configuration was already initialized"
        );
        std::process::exit(1);
    }
    if dump_bv_cnf_path.is_some() {
        if let Err(error) = ay::executor::Executor::invalidate_bv_cnf_export_for_rejected_check() {
            safe_eprintln!("Error: {error}");
            std::process::exit(1);
        }
    }

    let incompatible_non_solve_mode = if args.z3_print_params || args.z3_print_param_descriptions {
        Some("Z3 parameter listing")
    } else if args.z3_print_param_module.is_some() {
        Some("Z3 parameter-module listing")
    } else if args.z3_print_param_description.is_some() {
        Some("Z3 parameter description")
    } else if args.features {
        Some("feature reporting")
    } else if args.chc || args.portfolio {
        Some("forced CHC/portfolio solving")
    } else if args.z3_model {
        Some("Z3 -model input materialization")
    } else if args.dpll_diagnostic {
        Some("auto-generated DPLL diagnostics")
    } else {
        None
    };
    if dump_bv_cnf_path.is_some() {
        if let Some(mode) = incompatible_non_solve_mode {
            safe_eprintln!(
                "Error: BV CNF export is incompatible with {mode}; no check-sat query was executed"
            );
            std::process::exit(1);
        }
    }

    if args.z3_print_params || args.z3_print_param_descriptions {
        print_z3_compatible_params(args.z3_print_param_descriptions);
        return;
    }

    if let Some(module_name) = &args.z3_print_param_module {
        if module_name.is_empty() {
            print_z3_compat_module_list();
        } else if !print_z3_compat_module_params(module_name, args.z3_print_param_descriptions) {
            print_unknown_z3_module_and_exit(module_name);
        }
        return;
    }

    if let Some(param_name) = &args.z3_print_param_description {
        print_z3_compat_param_description_or_exit(param_name);
        return;
    }

    if !args.unsupported_z3_option.is_empty() {
        for option in &args.unsupported_z3_option {
            print_unsupported_z3_option(option);
        }
        std::process::exit(1);
    }

    if !args.unsupported_z3_param.is_empty() {
        for param in &args.unsupported_z3_param {
            safe_eprintln!("Error: unsupported Z3 parameter '{param}'");
        }
        std::process::exit(1);
    }

    // Real Z3 tuning knobs AY does not implement: accepted so the run proceeds
    // (z3 would solve), but announced — a dropped flag must never be silent.
    // `--z3-mode` asks for a Z3-shaped transcript, so the note is suppressed
    // there, exactly like the other AY-only diagnostics.
    if !args.ignored_z3_param.is_empty() && !args.z3_mode && !args.stats_json {
        let names: Vec<&str> = args
            .ignored_z3_param
            .iter()
            .map(|param| param.split('=').next().unwrap_or(param))
            .collect();
        safe_eprintln!(
            "c accepted but NOT honored (ay has no such tuning knob): {}",
            names.join(", ")
        );
    }

    // --features: print and exit
    if args.features {
        features::print_feature_report();
        return;
    }

    // Debug channels are CLI-owned in the `ay` binary. Set an explicit global
    // config, even when empty, so `AY_DEBUG_*` env vars cannot silently steer
    // runtime behavior from outside the documented CLI surface.
    let channels: Vec<ay_core::DebugChannel> =
        args.debug.iter().map(|cli_ch| (*cli_ch).into()).collect();
    let config = ay_core::DebugConfig::from_channels(&channels);
    let _ = ACTIVE_DEBUG_CHANNELS.set(config.clone());
    let _ = ay_core::set_global_debug_config(config);

    // SAT disable flags → populate both `SatDisableFlags` (read on hot paths)
    // and `DISABLED_SAT_TECHNIQUES` (applied via `solver.disable_technique()`).
    {
        let cli_disable = |target: CliSatTechnique| args.disable.contains(&target);
        let techniques: Vec<ay_sat::SatTechnique> = args
            .disable
            .iter()
            .map(|cli_tech| (*cli_tech).into())
            .collect();
        let no_external_codegen_backend = true;
        let cli_flags = ay_core::SatDisableFlags {
            no_bve: args.no_bve || cli_disable(CliSatTechnique::Bve),
            no_probe: args.no_probe || cli_disable(CliSatTechnique::Probe),
            no_congruence: args.no_congruence || cli_disable(CliSatTechnique::Congruence),
            no_decompose: cli_disable(CliSatTechnique::Decompose),
            no_sweep: cli_disable(CliSatTechnique::Sweep),
            no_subsume: args.no_subsume || cli_disable(CliSatTechnique::Subsume),
            no_vivify: args.no_vivify || cli_disable(CliSatTechnique::Vivify),
            no_factor: cli_disable(CliSatTechnique::Factor),
            no_bce: args.no_bce || cli_disable(CliSatTechnique::Bce),
            no_transred: cli_disable(CliSatTechnique::Transred),
            no_preprocess: args.no_preprocess || cli_disable(CliSatTechnique::Preprocess),
            no_inprocess: args.no_inprocess || cli_disable(CliSatTechnique::Inprocess),
            no_cold_restart: args.no_cold_restart,
            no_external_codegen_backend,
        };
        let _ = ay_core::set_global_sat_disable_flags(cli_flags);

        // Also populate the `DISABLED_SAT_TECHNIQUES` list applied per-solver.
        let _ = DISABLED_SAT_TECHNIQUES.set(techniques);
    }

    // Theory feature disable flags are also CLI-owned in the binary.
    {
        let max_fixpoint_rounds = args
            .max_fixpoint_rounds
            .map(|n| n as usize)
            .filter(|&n| n > 0);
        let theory_flags = ay_core::TheoryDisableFlags {
            no_bound_axioms: args.no_bound_axioms,
            no_theory_propagation: args.no_theory_propagation,
            no_bcp_theory_check: args.no_bcp_theory_check,
            no_ite_deferral: args.no_ite_deferral,
            disable_theory_check: false,
            no_inline_lemmas: args.no_inline_lemmas,
            no_implied_bounds: args.no_implied_bounds,
            no_bound_refinement: args.no_bound_refinement,
            // Debug kill switch for the Fix #2 BCP implied-bounds restraint
            // (sat-side-model-search): env-driven, no dedicated CLI arg.
            no_bcp_implied_restraint: env::var_os("AY_NO_BCP_IMPLIED_RESTRAINT").is_some(),
            max_fixpoint_rounds,
        };
        let _ = ay_core::set_global_theory_disable_flags(theory_flags);
    }

    // -- CLI → global config population (#8835) ---------------------------
    //
    // Previously the CLI round-tripped its arguments through `env::set_var`
    // as IPC with downstream libraries: CLI parse flag → set `AY_*` env var →
    // library reads `AY_*` env var. That pattern violated the "no env vars"
    // correctness rule and produced confusing behavior when the same env
    // var was both the CLI's output and the library's input.
    //
    // Each block below populates a centralized config struct in `ay_core`
    // (`TraceConfig`, `SatDebugEnvFlags`, `ChcDebugEnvFlags`,
    // `MiscCliFlags`) directly from CLI arguments so binary runtime behavior
    // is documented in one place.

    // SatDebugEnvFlags — clause_provenance/dump_conflicts/trace_ext_conflict
    //                    /bve_limit/bve_max_rounds/bve_trace/log
    {
        let sat_debug = ay_core::SatDebugEnvFlags {
            trace_ext_conflict: args.trace_ext_conflict,
            bve_limit: args.bve_limit,
            bve_trace: args.bve_trace,
            bve_max_rounds: args.bve_max_rounds,
            log_enabled: args.log,
            dump_conflicts: args.dump_conflicts,
            clause_provenance: args.clause_provenance,
            debug_transred_clause: args.debug_transred_clause,
        };
        let _ = ay_core::set_global_sat_debug_env_flags(sat_debug);
    }

    // ChcDebugEnvFlags — iuc_trace / strict_iuc_farkas
    {
        let chc_debug = ay_core::ChcDebugEnvFlags {
            iuc_trace: args.iuc_trace,
            iuc_require_farkas: args.strict_iuc_farkas,
        };
        let _ = ay_core::set_global_chc_debug_env_flags(chc_debug);
    }

    // MiscCliFlags — dump_auflia_assertions/sat_variant/dpll_{diagnostic_file,
    //                diagnostic,trace_file}
    //
    // Note: --dump-encoding, --kind-dump-dir, and --debug-transred-clause now
    // live on TraceConfig and SatDebugEnvFlags respectively (merged in via
    // #8834 — the fields were added to those existing singletons rather than
    // duplicated in MiscCliFlags).
    {
        let misc = ay_core::MiscCliFlags {
            dump_auflia_assertions: args.dump_auflia_assertions,
            sat_variant: args.sat_variant.clone(),
            dpll_diagnostic_file: args
                .dpll_diagnostic_file
                .as_ref()
                .map(|p| p.to_string_lossy().into_owned()),
            dpll_diagnostic_enabled: args.dpll_diagnostic,
            dpll_trace_file: args
                .dpll_trace_file
                .as_ref()
                .map(|p| p.to_string_lossy().into_owned()),
        };
        let _ = ay_core::set_global_misc_cli_flags(misc);
    }

    // Verbose/stats
    let stats_human = args.stats;
    let stats_cfg = stats_output::StatsConfig {
        human: stats_human,
        json: args.stats_json,
    };

    // Progress
    if args.progress {
        PROGRESS_ENABLED.store(true, Ordering::SeqCst);
    }

    // Strict proof mode (#8555, #8759).
    if args.strict_proofs {
        STRICT_PROOFS_ENABLED.store(true, Ordering::SeqCst);
    }

    // Fail-closed self-check: AY verifies its own sat/unsat answers.
    if args.self_check {
        SELF_CHECK_ENABLED.store(true, Ordering::SeqCst);
    }

    // Diagnostic firewall Lean emission directory.
    if let Some(dir) = &args.emit_firewall_lean {
        let _ = FIREWALL_LEAN_DIR.set(dir.clone());
    }

    // Fail-closed firewall diagnostic gate.
    if args.verify_firewall {
        VERIFY_FIREWALL_ENABLED.store(true, Ordering::SeqCst);
    }

    // Aggressive model minimization (#8297)
    if args.minimize_model {
        MINIMIZE_MODEL_ENABLED.store(true, Ordering::SeqCst);
    }
    // Human-readable explanation mode (#8693)
    if args.explain {
        EXPLAIN_ENABLED.store(true, Ordering::SeqCst);
    }
    // Phase 1 reason-code output format (#8693).
    if matches!(args.explain_format, CliExplainFormat::Json) {
        EXPLAIN_FORMAT_JSON.store(true, Ordering::SeqCst);
    }
    if let Some(ref path) = args.progress_json {
        let path_str = path.to_string_lossy().to_string();
        match std::fs::File::create(&path_str) {
            Ok(_) => {
                let _ = PROGRESS_JSON_PATH.set(path_str);
            }
            Err(e) => {
                safe_eprintln!("Error: cannot create progress-json file: {e}");
                std::process::exit(1);
            }
        }
    }

    // Wall-clock start time for stats envelope
    START_TIME.get_or_init(Instant::now);

    // Timeout
    let timeout_ms = args.timeout;
    if let Some(ms) = timeout_ms {
        set_global_timeout(ms);
    }

    // Memory limit — auto-detect from physical RAM if not explicitly set (#8600).
    //
    // Without a limit, all `global_memory_exceeded()` and `process_memory_exceeded()`
    // checks throughout the codebase are dead code, and the process OOMs instead of
    // gracefully returning Unknown. The auto-detected default (half of physical RAM,
    // clamped to [2GB, 64GB]) provides OOM protection while using all available
    // resources. Pass `--memory 0` to explicitly disable.
    let memory_limit_bytes = if let Some(mb) = args.memory {
        if mb == 0 {
            0
        } else {
            let Some(bytes) = usize::try_from(mb)
                .ok()
                .and_then(|value| value.checked_mul(1024 * 1024))
            else {
                safe_eprintln!(
                    "Error: --memory {mb} MiB exceeds this platform's addressable limit"
                );
                std::process::exit(1);
            };
            bytes
        }
    } else {
        // Auto-detect for the standalone binary: 85% of physical RAM
        // (sole-tenant competition posture; #sparse-gap Cluster A — the
        // phys/2 default plus a transient allocator spike degraded solvable
        // main-track instances to Unknown). Returns 0 if physical memory
        // detection fails (limit disabled).
        ay_sys::default_standalone_memory_limit()
    };
    if memory_limit_bytes > 0 {
        ay_sys::set_process_memory_limit(memory_limit_bytes);
    }

    // Tracing
    tracing_setup::setup_tracing(args.verbose);

    if memory_limit_bytes > 0 {
        tracing::info!(
            limit_mb = memory_limit_bytes / (1024 * 1024),
            "process memory limit active"
        );
    }

    // Proof auto-verification (#8771). ON BY DEFAULT (batteries included); apply
    // CLI overrides here. Precedence: explicit `--verify-proof` forces on;
    // otherwise `--no-verify-proof` or competition/benchmark mode turns it off
    // for speed; otherwise the default (on) stands.
    EXPLICIT_VERIFY_PROOF_ENABLED.store(args.verify_proof, Ordering::SeqCst);
    if args.verify_proof {
        VERIFY_PROOF_ENABLED.store(true, Ordering::SeqCst);
    } else if args.no_verify_proof || competition_mode(args) {
        VERIFY_PROOF_ENABLED.store(false, Ordering::SeqCst);
    }

    // Lean kernel verification (#8773 Phase 1). Gated on --proof via clap
    // `requires = "proof"`; only meaningful when the proof format is Lean4,
    // which is enforced at invocation time in dimacs.rs.
    if args.lean_verify {
        LEAN_VERIFY_ENABLED.store(true, Ordering::SeqCst);
        if let Some(ref p) = args.lean_path {
            let _ = LEAN_BINARY_PATH.set(p.clone());
        }
    }

    // Build proof config from flags. An explicit firewall-artifact request is
    // mandatory: it must never disappear merely because default proof output
    // was suppressed or no persistent proof path could be synthesized.
    let proof_config = build_proof_config(args);
    if let Some(error) =
        firewall_emission_config_error(args.emit_firewall_lean.is_some(), proof_config.as_ref())
    {
        safe_eprintln!("Error: {error}");
        std::process::exit(1);
    }
    let visualization = args.visualize.map(Into::into);

    // Determine CHC mode
    let chc_mode = if args.portfolio {
        ChcMode::Portfolio
    } else if args.chc {
        ChcMode::Chc
    } else {
        ChcMode::None
    };

    // A positional FILE cannot be combined with stdin input: `--stdin` (Z3's
    // `-in`, rewritten by preprocess_args) and `--incremental` both read from
    // stdin, so a user-supplied FILE would be silently ignored. Fail loudly
    // instead. This is a runtime check rather than a clap `conflicts_with` so
    // the message can name both spellings for `z3 -in FILE` drop-in users.
    if (args.stdin || args.incremental) && args.file.is_some() {
        safe_eprintln!(
            "Error: a FILE argument cannot be combined with --stdin (Z3 `-in`) or --incremental; these read from stdin, so the FILE would be ignored. Drop the flag to solve the FILE, or drop the FILE to read from stdin."
        );
        std::process::exit(1);
    }

    // Stdin mode
    let mut stdin_mode = args.stdin || args.incremental;
    let mut file_str = args.file.as_ref().map(|p| p.to_string_lossy().to_string());
    let mut z3_model_input: Option<MaterializedInput> = None;
    if args.z3_model && !args.incremental {
        if stdin_mode {
            use std::io::{IsTerminal, Read};

            if !io::stdin().is_terminal() {
                let mut content = String::new();
                let read_stdin = io::stdin().lock().read_to_string(&mut content);
                if let Err(error) = read_stdin {
                    safe_eprintln!("Error: failed to read stdin for -model: {error}");
                    std::process::exit(1);
                }
                let materialized = materialize_z3_model_input(&content);
                file_str = Some(materialized.path_string());
                z3_model_input = Some(materialized);
                stdin_mode = false;
            }
        } else if let Some(path) = file_str.clone() {
            if let Some(materialized) = materialize_z3_model_file_input(&path) {
                file_str = Some(materialized.path_string());
                z3_model_input = Some(materialized);
            }
        }
    }

    // Runtime result validation is ON BY DEFAULT (batteries included).
    // Precedence: `--no-validate` off; else explicit (deprecated) `--validate`
    // forces on; else competition/benchmark mode turns it off for speed; else on.
    let validate = if args.no_validate {
        false
    } else if args.validate {
        true
    } else {
        !competition_mode(args)
    };

    // `--chc`/`--portfolio` force CHC solving, but the forced mode is only
    // consulted for FILE input (`determine_execution_mode` returns Interactive
    // for stdin / no-file first). Fail loudly instead of silently solving
    // stdin content as plain SMT with the force flag dropped. Checked after
    // the `-model` materialization above, which can turn piped stdin into an
    // immutable in-memory file snapshot.
    if (args.chc || args.portfolio) && (stdin_mode || file_str.is_none()) {
        safe_eprintln!(
            "Error: --chc/--portfolio require an input FILE (not stdin/interactive mode)"
        );
        std::process::exit(1);
    }
    if args.decision_trace.is_some() && (stdin_mode || file_str.is_none()) {
        safe_eprintln!(
            "Error: --decision-trace requires an input FILE so complete single-query preflight can finish before any verdict; stdin/interactive/incremental streams are unsupported"
        );
        std::process::exit(1);
    }
    if args.decision_trace.is_some() && (args.parallel.is_some() || args.cube_and_conquer.is_some())
    {
        safe_eprintln!(
            "Error: --decision-trace is incompatible with --parallel/--cube-and-conquer; those DIMACS routes do not produce the single-solver decision trace"
        );
        std::process::exit(1);
    }
    if args.decision_trace.is_some() && (args.chc || args.portfolio) {
        safe_eprintln!(
            "Error: --decision-trace is incompatible with forced CHC/portfolio solving; decision traces support one SMT-LIB decision query"
        );
        std::process::exit(1);
    }
    if args.chc || args.portfolio {
        run::reject_firewall_emission_for_route("forced CHC/portfolio");
        run::reject_firewall_verification_for_route("forced CHC/portfolio");
        run::reject_explicit_proof_verification_for_route("forced CHC/portfolio", "CHC replay");
    }

    let mut preflighted_decision_input = None;
    if args.decision_trace.is_some() {
        if let Some(path) = file_str.as_deref() {
            if let Some(materialized) = z3_model_input.as_ref() {
                if let Err(error) = validate_decision_trace_content(path, &materialized.content) {
                    safe_eprintln!("Error: {error}");
                    std::process::exit(1);
                }
            } else {
                match preflight_decision_trace_file(path) {
                    Ok(preflighted) => preflighted_decision_input = Some(preflighted),
                    Err(error) => {
                        safe_eprintln!("Error: {error}");
                        std::process::exit(1);
                    }
                }
            }
        }
    }

    // Reserve the single-result decision trace only after every argument-only
    // early exit has completed. Feature/parameter reports and rejected forced
    // CHC routes must not leave an initialized, header-only file that could be
    // mistaken for a replay artifact.
    if let Some(path) = args.decision_trace.as_deref() {
        let Some(path_text) = path.to_str() else {
            safe_eprintln!("Error: --decision-trace requires a UTF-8 output path");
            std::process::exit(1);
        };
        if let Err(error) = ay_sat::reserve_decision_trace(path_text) {
            safe_eprintln!(
                "Error: cannot reserve --decision-trace output '{}': {error}",
                path.display()
            );
            std::process::exit(1);
        }
    }

    // Route to existing execution logic
    match determine_execution_mode(stdin_mode, file_str.as_ref(), chc_mode) {
        ExecutionMode::Interactive => {
            run::run_interactive(
                stats_cfg,
                proof_config.as_ref(),
                args.incremental,
                visualization,
                args.verbose,
                validate,
            );
        }
        ExecutionMode::PortfolioFile => {
            if let Some(ref f) = file_str {
                chc_runner::run_portfolio(
                    f,
                    args.verbose,
                    validate,
                    args.strict_proofs,
                    timeout_ms,
                    stats_cfg,
                    proof_config.as_ref(),
                );
            }
        }
        ExecutionMode::AutoFile => {
            if let Some(ref f) = file_str {
                run::run_file(
                    f,
                    preflighted_decision_input
                        .as_ref()
                        .map(|input| (input.content.as_str(), input.file.as_ref()))
                        .or_else(|| z3_model_input.as_ref().map(MaterializedInput::preloaded)),
                    stats_cfg,
                    proof_config.as_ref(),
                    args.parallel,
                    args.cube_and_conquer,
                    visualization,
                    args.verbose,
                    validate,
                );
            }
        }
    }

    // Clean up the private `--self-check` BV DRAT self-cert temp artifacts.
    // Best-effort: on a hard timeout/exit path a small temp file may linger,
    // which the OS temp reaper collects; it never affects a verdict.
    if let Some((cnf, drat)) = self_cert_bv_paths {
        let _ = std::fs::remove_file(&cnf);
        let _ = std::fs::remove_file(&drat);
    }

    // Final timeout check
    exit_if_timed_out();
}

/// Whether an official SAT-competition / benchmark harness signal is present in
/// the environment. Existing competition wrappers set these (they do not pass
/// `--competition`), so they must auto-enter competition mode to keep the fast
/// path — otherwise turning the batteries on by default would regress them.
///
/// These are the load-bearing competition signals (kept as env vars on purpose,
/// they are set by the wrapper/harness, not by end users).
fn competition_env_active() -> bool {
    const SIGNALS: &[&str] = &[
        SAT_COMPETITION_WRAPPER_ENV, // AY_INTERNAL_SATCOMP_WRAPPER
        "AY_SAT_COMPETITION_PROFILE",
        "AY_SAT_PROFILE_ID",
    ];
    SIGNALS
        .iter()
        .any(|name| env::var(name).is_ok_and(|v| !v.trim().is_empty()))
}

/// Competition / benchmark mode: batteries OFF for raw speed. True when
/// `--competition` is set or an official competition harness env signal is
/// present. Turns off the overhead extras (default validation, proof re-check,
/// default proof emission) — never the capability/soundness defaults.
pub(crate) fn competition_mode(args: &SolveArgs) -> bool {
    args.competition || competition_env_active()
}

/// Resolve an explicit user-requested DRAT proof target `(path, binary)`.
///
/// Mirrors the DRAT branches of [`build_proof_config`]: the legacy
/// `--drat`/`--drat-binary` flags and a `--proof PATH` whose format resolves to
/// DRAT (via `--proof-format drat` or a `.drat`/`.dratb` extension). Returns
/// `None` for any non-DRAT proof request. Used to couple a single-invocation
/// bit-blasted BV DRAT certificate to `--dump-bv-cnf`.
fn explicit_bv_drat_target(args: &SolveArgs) -> Option<(String, bool)> {
    if let Some(path) = args.drat.as_ref() {
        return Some((path.to_string_lossy().into_owned(), false));
    }
    if let Some(path) = args.drat_binary.as_ref() {
        return Some((path.to_string_lossy().into_owned(), true));
    }
    if let Some(path) = args.proof.as_ref() {
        let path_str = path.to_string_lossy().into_owned();
        let format = args
            .proof_format
            .map(ProofFormat::from)
            .unwrap_or_else(|| ProofConfig::from_path(path_str.clone()).format);
        if format == ProofFormat::Drat {
            return Some((path_str, args.proof_binary));
        }
    }
    None
}

/// Build proof config from CLI args, handling legacy --drat/--lrat flags.
fn build_proof_config(args: &SolveArgs) -> Option<ProofConfig> {
    // Single-invocation bit-blasted QF_BV DRAT: when `--proof X.drat` is paired
    // with `--dump-bv-cnf`, the DRAT certificate is emitted by the BV solver
    // itself (beside the dumped CNF, from the same eager bit-blast), not as an
    // SMT-level Alethe proof. Suppress the SMT proof config here so the
    // DRAT/Alethe format mismatch is never rejected; the DRAT path travels via
    // `trace_config().bv_drat_path`. `bv_drat_path` is only ever set when the
    // CNF dump is also configured (see `trace_config_from_solve_args`).
    if ay_core::trace_config().bv_drat_path.is_some() {
        return None;
    }
    let artifact_path = args
        .proof_artifact
        .as_ref()
        .map(|path| path.to_string_lossy().to_string());

    // Legacy explicit flags take precedence
    if let Some(ref path) = args.drat {
        return Some(
            ProofConfig::new(path.to_string_lossy().to_string(), ProofFormat::Drat, false)
                .with_artifact_path(artifact_path),
        );
    }
    if let Some(ref path) = args.drat_binary {
        return Some(
            ProofConfig::new(path.to_string_lossy().to_string(), ProofFormat::Drat, true)
                .with_artifact_path(artifact_path),
        );
    }
    if let Some(ref path) = args.lrat {
        return Some(
            ProofConfig::new(path.to_string_lossy().to_string(), ProofFormat::Lrat, false)
                .with_artifact_path(artifact_path),
        );
    }
    if let Some(ref path) = args.lrat_binary {
        return Some(
            ProofConfig::new(path.to_string_lossy().to_string(), ProofFormat::Lrat, true)
                .with_artifact_path(artifact_path),
        );
    }

    // --proof with optional --proof-format override
    if let Some(path) = args.proof.as_ref() {
        let path_str = path.to_string_lossy().to_string();
        let config = if let Some(fmt) = args.proof_format {
            ProofConfig::new(path_str, fmt.into(), args.proof_binary)
        } else {
            let mut config = ProofConfig::from_path(path_str);
            if args.proof_binary {
                config.binary = true;
            }
            config
        };
        return Some(config.with_artifact_path(artifact_path));
    }

    // No explicit --proof. For a file whose extension maps to a supported
    // proof format, synthesize a persistent artifact path and attempt emission
    // after UNSAT (#8864):
    //
    //   .cnf / .dimacs  -> <input>.drat    (DRAT, SAT core)
    //   .smt2 / .smt    -> <input>.alethe  (Alethe, SMT; CHC retargets to
    //                                       <input>.chccert at write time)
    //
    // Opt out with the `--no-proof` flag (or `--z3-mode`, which keeps a clean
    // Z3-style transcript). Competition mode suppresses this default; a wrapper
    // that requires a proof must request one explicitly. Announce the chosen
    // path to stderr so users know where to find it, but stay silent under
    // `--stats-json`, whose contract is one machine-readable JSON line.
    if !default_proofs_suppressed(args.no_proof, args.z3_mode, competition_mode(args)) {
        if let Some((path, format)) = default_proof_path(args.file.as_deref()) {
            if !args.stats_json && !quiet_enabled() {
                // "on unsat": this is announced before solving, and the
                // certificate is only actually written for an UNSAT verdict —
                // a SAT/unknown run creates no file. `-q`/`--quiet` suppresses
                // this provenance note without changing whether the proof is
                // written.
                safe_eprintln!(
                    "c writing {} proof to {path} on unsat",
                    default_proof_kind(format)
                );
            }
            return Some(ProofConfig::new_default(path, format).with_artifact_path(artifact_path));
        }
    }

    if args.proof_artifact.is_some() {
        safe_eprintln!(
            "Error: --proof-artifact requires an emitted proof; pass --proof FILE or solve a file (DIMACS/SMT-LIB) with default proof emission enabled (not --no-proof)"
        );
        std::process::exit(1);
    }

    // No explicit --proof and no default path (stdin / non-DIMACS input or
    // `--no-proof` opt-out). If `--verify-proof` is on (and not turned off via
    // `--no-verify-proof`), synthesize a temporary DRAT proof path so UNSAT can
    // be re-checked post-solve (#8771).
    //
    // An explicit proof opt-out (`--no-proof` / `--z3-mode` / `--competition`)
    // suppresses this synthesis too: re-checking a certificate the user just
    // declined is incoherent, and the synthesized config is NOT free — it flips
    // `set_produce_proofs(true)` downstream, which enables SAT clause tracing +
    // per-conflict LRAT chain materialization (measured at ~80% of solve time
    // on a 92MB BMC instance, turning solvable instances into timeouts). An
    // explicit `--verify-proof` still wins over the opt-outs (clap already
    // rejects `--verify-proof --no-proof` conflicts where declared; belt and
    // suspenders here keeps the precedence explicit).
    if VERIFY_PROOF_ENABLED.load(Ordering::SeqCst)
        && (!default_proofs_suppressed(args.no_proof, args.z3_mode, competition_mode(args))
            || args.verify_proof)
    {
        if ay_core::trace_config().dump_bv_cnf_path.is_some() {
            if args.verify_proof {
                safe_eprintln!(
                    "Error: --verify-proof without an explicit/default proof path is incompatible with --dump-bv-cnf; the synthesized proof path cannot share a certificate transaction"
                );
                std::process::exit(1);
            }
            return None;
        }
        let mut path = env::temp_dir();
        let nanos = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map(|d| d.as_nanos())
            .unwrap_or(0);
        let pid = std::process::id();
        path.push(format!("ay-verify-{pid}-{nanos}.drat"));
        return Some(ProofConfig::new_temp(
            path.to_string_lossy().to_string(),
            ProofFormat::Drat,
            false,
        ));
    }

    None
}

fn firewall_emission_config_error(
    requested: bool,
    proof_config: Option<&ProofConfig>,
) -> Option<String> {
    if !requested {
        return None;
    }
    let Some(proof) = proof_config else {
        return Some(
            "--emit-firewall-lean requires a persistent Alethe proof; pass --proof FILE.alethe or solve an SMT-LIB file with default proof emission enabled"
                .to_string(),
        );
    };
    if proof.is_temp {
        return Some(
            "--emit-firewall-lean cannot use a temporary checker proof; pass --proof FILE.alethe"
                .to_string(),
        );
    }
    if proof.format != ProofFormat::Alethe {
        return Some(format!(
            "--emit-firewall-lean requires an Alethe proof, but the selected proof format is {:?}",
            proof.format
        ));
    }
    None
}

/// Whether default proof-artifact emission is opted out, via the
/// `--no-proof` flag, `--z3-mode` (Z3 transcript-compatibility mode keeps
/// stderr/stdout clean and must not spontaneously write proof files, matching
/// Z3's default), or `--competition` (speed opt-out; an official competition
/// wrapper still passes an explicit `--proof` when it needs one).
///
/// This only governs the *synthesized default* artifact. An explicit
/// `--proof FILE` (handled earlier in `build_proof_config`) always wins and is
/// unaffected. There is deliberately no environment-variable opt-out for the
/// user-facing switch — it is an explicit, discoverable CLI flag.
pub(crate) fn default_proofs_suppressed(no_proof: bool, z3_mode: bool, competition: bool) -> bool {
    no_proof || z3_mode || competition
}

/// Human-readable name of a default proof format, for the stderr announcement.
fn default_proof_kind(format: ProofFormat) -> &'static str {
    match format {
        ProofFormat::Drat => "DRAT",
        ProofFormat::Lrat => "LRAT",
        ProofFormat::Lean4 => "Lean4",
        ProofFormat::Alethe => "Alethe",
    }
}

/// Compute the default proof-artifact path and format for an input
/// file, dispatching on the file extension (case-insensitive):
///
///   `.cnf` / `.dimacs`  -> `<input>.drat`,   DRAT   (SAT core)
///   `.smt2` / `.smt`    -> `<input>.alethe`, Alethe (SMT; the CHC runner
///                          retargets this to `<input>.chccert` at write time
///                          when the problem turns out to be Horn)
///
/// Returns `None` for stdin input (no file), unknown extensions, or anything
/// without an obvious on-disk home for the artifact. This is a pure function
/// extracted for unit testing; `build_proof_config` wraps the result in a
/// `ProofConfig::new_default`.
fn default_proof_path(file: Option<&std::path::Path>) -> Option<(String, ProofFormat)> {
    let file = file?;
    let ext = file
        .extension()
        .and_then(|e| e.to_str())
        .map(str::to_ascii_lowercase)
        .unwrap_or_default();
    let (proof_ext, format) = match ext.as_str() {
        "cnf" | "dimacs" => ("drat", ProofFormat::Drat),
        "smt2" | "smt" => ("alethe", ProofFormat::Alethe),
        _ => return None,
    };
    Some((sibling_proof_path(file, proof_ext), format))
}

/// Compute the default DRAT proof path for a DIMACS input file (#8864).
///
/// Returns `Some(path)` only for `.cnf` / `.dimacs` inputs (case-insensitive);
/// `None` otherwise. Retained as the DRAT-specific view of [`default_proof_path`]
/// for the DIMACS-default unit tests.
#[cfg(test)]
fn default_drat_proof_path(file: Option<&std::path::Path>) -> Option<String> {
    match default_proof_path(file) {
        Some((path, ProofFormat::Drat)) => Some(path),
        _ => None,
    }
}

/// Append `.<proof_ext>` to the input file name (preserving the original
/// extension so `foo.cnf` -> `foo.cnf.drat`, `foo.smt2` -> `foo.smt2.alethe`),
/// keeping the certificate as a sibling of the input.
fn sibling_proof_path(file: &std::path::Path, proof_ext: &str) -> String {
    let mut path = file.to_path_buf();
    let stem = path
        .file_name()
        .and_then(|f| f.to_str())
        .map(ToString::to_string)
        .unwrap_or_default();
    path.set_file_name(format!("{stem}.{proof_ext}"));
    path.to_string_lossy().to_string()
}

// Deleted: debug_channel_env_var() and sat_technique_env_var() (#8331).
// CLI --debug/--disable now populate globals directly instead of setting env vars.

// ---------------------------------------------------------------------------
// SIGTERM handler (#8674): print "unknown" on external termination
// ---------------------------------------------------------------------------

/// Install a process-wide SIGTERM handler that prints "unknown" and exits
/// gracefully. Without this, an external `kill` or `timeout` command causes
/// ay to exit silently with no output — violating the SMT-LIB contract that
/// a solver must always emit sat/unsat/unknown. SAT-COMP wrapper runs use
/// `s UNKNOWN` and exit 0 instead.
///
/// Uses `signal-hook` crate for safe, portable signal handling. The handler
/// atomically sets a flag, and a dedicated poller thread detects this and
/// initiates shutdown:
/// 1. Sets the cooperative timeout flags (`TIMED_OUT`, `INTERRUPT_HANDLE`)
///    so any in-flight solve can notice and return early.
/// 2. After a 2-second grace period for cooperative shutdown, does a hard
///    exit using the active timeout output policy.
#[cfg(unix)]
fn install_sigterm_handler() {
    // Create an Arc<AtomicBool> flag that signal-hook sets atomically on SIGTERM.
    // signal-hook guarantees the handler is async-signal-safe (no locks, no alloc).
    let sigterm_flag = Arc::new(AtomicBool::new(false));
    let Ok(_sig_id) =
        signal_hook::flag::register(signal_hook::consts::SIGTERM, Arc::clone(&sigterm_flag))
    else {
        return; // Non-fatal: fall back to default SIGTERM behavior.
    };

    // Spawn a poller thread that watches for the SIGTERM flag and initiates
    // graceful shutdown. The poller checks every 50ms — well within the
    // sub-second response time expected by callers like `timeout(1)`.
    let _ = std::thread::Builder::new()
        .name("ay-sigterm".to_string())
        .spawn(move || {
            loop {
                std::thread::sleep(Duration::from_millis(50));
                if sigterm_flag.load(Ordering::SeqCst) {
                    break;
                }
            }

            // Set cooperative timeout flags so in-flight solvers can exit.
            TIMED_OUT.store(true, Ordering::SeqCst);
            if let Some(handle) = INTERRUPT_HANDLE.get() {
                handle.store(true, Ordering::SeqCst);
            }

            // Grace period: let cooperative shutdown paths print their own output.
            std::thread::sleep(Duration::from_secs(2));

            // Hard exit if the process is still alive.
            hard_timeout_fallback_exit();
        });
}

#[cfg(not(unix))]
fn install_sigterm_handler() {
    // No-op on non-Unix platforms.
}

// ---------------------------------------------------------------------------
// main
// ---------------------------------------------------------------------------

// Allocation-bound LIA workloads (see ay-dpll benches/nip-lia-boundary):
// libsystem_malloc was ~20%+ of leaf samples. mimalloc removes that tax for
// the CLI binary only (lib consumers choose their own allocator).
//
// The mimalloc allocator is wrapped in `ay_sys::CountingAllocator`, which keeps
// an exact, instantaneous count of live heap bytes (~2 relaxed atomics per
// allocation, no syscalls). That counter feeds `ay_sys::process_memory_exceeded`
// — already consulted at every solver cancellation checkpoint — so a runaway
// bulk allocation trips the existing `Unknown(MemoryLimit)` path the moment it
// lands, instead of letting the process grow until the OS OOM-killer panics the
// machine. Soundness-neutral: it only observes bytes and drives Unknown, never a
// wrong SAT/UNSAT. Binary-only; library consumers keep their own allocator.
#[cfg(feature = "cli")]
#[global_allocator]
static GLOBAL: ay_sys::CountingAllocator<mimalloc::MiMalloc> =
    ay_sys::CountingAllocator::new(mimalloc::MiMalloc);

fn main() {
    let provenance_args = env::args_os().collect::<Vec<_>>();
    if matches!(provenance_args.as_slice(), [_, flag] if flag == "--provenance") {
        safe_println!("{}", build_info::exact_provenance_json());
        return;
    }

    // The mimalloc `arena_reserve` peak-RSS trim runs from the global
    // allocator's first allocation, before any arena is reserved. A forked
    // solve child inherits the resulting small-arena state via copy-on-write;
    // see `ay_sys::ensure_arena_reserve_trimmed`.
    // Give the PB solver's worker threads an ample stack. Deep solver recursion
    // (conflict analysis / CNF encoding / SAT search) on wide or large instances
    // (e.g. MIPLIB `disctom`: 10000 vars, ~10000-term rows) overflows the ~2 MiB
    // default spawned-thread stack and ABORTS the process — a lost answer.
    // `RUST_MIN_STACK` sizes every `std`-spawned thread (including dependency-internal
    // scoped workers, verified to fix the crash) but must be present from process
    // start, since `std::thread::min_stack()` caches it on first read. Scoped to the
    // `pb` subcommand and gated on the variable being unset, so SMT invocations are
    // completely unaffected; a reserved stack is committed lazily, so the headroom is
    // free. Soundness-neutral: it only prevents stack exhaustion, never an outcome.
    maybe_reexec_pb_with_large_stack();

    let raw_args: Vec<String> = env::args().collect();
    let processed = preprocess_args(raw_args.clone());

    if maybe_print_solve_full_help(&processed) {
        return;
    }

    // Set commentary suppression before the supervisor emits the pre-fork
    // `c ay.session.start` marker, so `-q` quiets it too. `run_solve` sets the
    // same flag from the parsed args for the in-process solve path.
    if solve_quiet_requested(&processed) {
        QUIET_ENABLED.store(true, Ordering::SeqCst);
    }

    if solve_session_needs_wrapper(&processed) {
        run_wrapped_solve_session(&raw_args);
    }

    // Test-only crash-injection hook (#chc25-crash) for the RE-EXEC fallback
    // supervisor: drive the re-exec'd solve-session CHILD into the requested fault.
    // The primary fork-before-threads supervisor fires the same hook in its post-fork
    // child branch (see `fork_supervised_solve_session`), so whichever supervisor
    // runs, the crash gate exercises the real crash path. Gated on the provenance-
    // child env (set only by the re-exec) so a plain (unwrapped) or forked-child
    // invocation never faults here — the fork child has no such env and already
    // handled the hook upstream.
    if env::var_os(SESSION_PROVENANCE_CHILD_ENV).is_some() {
        maybe_inject_test_child_fault();
    }

    // NOTE: the SIGTERM -> "unknown" handler (#8674) is installed inside
    // run_solve(), not here: it synthesizes a solver verdict line on stdout,
    // which must never appear on the stdout of non-solve subcommands.
    let cli = Cli::parse_from(processed);

    match cli.command {
        Some(Command::Solve(args)) => {
            run_solve(&args);
        }
        None => {
            // preprocess_args always injects "solve", so this shouldn't happen.
            // Handle defensively: run interactive mode with defaults.
            let args = SolveArgs::default();
            run_solve(&args);
        }
        Some(Command::Check(cmd)) => {
            if let Err(e) = cmd_check::run(cmd) {
                safe_eprintln!("Error: {e:#}");
                std::process::exit(1);
            }
        }
        Some(Command::Bench(cmd)) => {
            if let Err(e) = cmd_bench::run(cmd) {
                safe_eprintln!("Error: {e:#}");
                std::process::exit(1);
            }
        }
        Some(Command::Corpus(cmd)) => match cmd_corpus::run(cmd) {
            Ok(0) => {}
            Ok(code) => {
                let _ = io::stdout().flush();
                let _ = io::stderr().flush();
                std::process::exit(code);
            }
            Err(e) => {
                safe_eprintln!("Error: {e:#}");
                std::process::exit(1);
            }
        },
        Some(Command::Tool(args)) => match cmd_tool::run(args) {
            Ok(0) => {}
            Ok(code) => {
                let _ = io::stdout().flush();
                let _ = io::stderr().flush();
                std::process::exit(code);
            }
            Err(e) => {
                safe_eprintln!("Error: {e:#}");
                std::process::exit(1);
            }
        },
        Some(Command::Scripts(cmd)) => match cmd_scripts::run(cmd) {
            Ok(0) => {}
            Ok(code) => {
                let _ = io::stdout().flush();
                let _ = io::stderr().flush();
                std::process::exit(code);
            }
            Err(e) => {
                safe_eprintln!("Error: {e:#}");
                std::process::exit(1);
            }
        },
        Some(Command::CompetitionJit(cmd)) => {
            if let Err(e) = cmd_competition_jit::run(cmd) {
                safe_eprintln!("Error: {e:#}");
                std::process::exit(1);
            }
        }
        Some(Command::Gate(cmd)) => match cmd_gate::run(cmd) {
            Ok(0) => {}
            Ok(code) => {
                let _ = io::stdout().flush();
                let _ = io::stderr().flush();
                std::process::exit(code);
            }
            Err(e) => {
                safe_eprintln!("Error: {e:#}");
                std::process::exit(1);
            }
        },
        #[cfg(ay_internal_tools)]
        Some(Command::ConsumerSmoke(cmd)) => match cmd_consumer_smoke::run(cmd) {
            Ok(0) => {}
            Ok(code) => {
                let _ = io::stdout().flush();
                let _ = io::stderr().flush();
                std::process::exit(code);
            }
            Err(e) => {
                safe_eprintln!("Error: {e:#}");
                std::process::exit(1);
            }
        },
        Some(Command::Flatzinc(cmd)) => {
            if let Err(e) = cmd_flatzinc::run(&cmd) {
                safe_eprintln!("Error: {e:#}");
                std::process::exit(1);
            }
        }
        Some(Command::Pb(cmd)) => match cmd_pb::run(&cmd) {
            Ok(status) => {
                let code = cmd_pb::pb_exit_code(status);
                if code != 0 {
                    // Flush before process::exit which skips destructors (#3088).
                    let _ = io::stdout().flush();
                    let _ = io::stderr().flush();
                    std::process::exit(code);
                }
            }
            Err(e) => {
                safe_eprintln!("Error: {e:#}");
                std::process::exit(1);
            }
        },
        Some(Command::Maxsat(cmd)) => match cmd_maxsat::run(&cmd) {
            Ok(code) => {
                let _ = io::stdout().flush();
                let _ = io::stderr().flush();
                if code != 0 {
                    std::process::exit(code);
                }
            }
            Err(e) => {
                safe_eprintln!("Error: {e:#}");
                std::process::exit(1);
            }
        },
        Some(Command::Qbf(cmd)) => match cmd_qbf::run(&cmd) {
            Ok(code) => {
                let _ = io::stdout().flush();
                let _ = io::stderr().flush();
                if code != 0 {
                    std::process::exit(code);
                }
            }
            Err(e) => {
                safe_eprintln!("Error: {e:#}");
                std::process::exit(1);
            }
        },
        Some(Command::Lp(cmd)) => match cmd_lp::run(&cmd) {
            Ok(0) => {}
            Ok(code) => {
                let _ = io::stdout().flush();
                let _ = io::stderr().flush();
                std::process::exit(code);
            }
            Err(e) => {
                safe_eprintln!("Error: {e:#}");
                std::process::exit(1);
            }
        },
        Some(Command::Tutorial(args)) => {
            if let Err(e) = cmd_tutorial::run(&args) {
                safe_eprintln!("Error: {e:#}");
                std::process::exit(1);
            }
        }
        Some(Command::Simplify(args)) => {
            if let Err(e) = cmd_simplify::run(&args) {
                safe_eprintln!("Error: {e:#}");
                std::process::exit(1);
            }
        }
        Some(Command::Bisect(cmd)) => match cmd_bisect::run(&cmd) {
            Ok(0) => {}
            Ok(code) => {
                let _ = io::stdout().flush();
                let _ = io::stderr().flush();
                std::process::exit(code);
            }
            Err(e) => {
                safe_eprintln!("Error: {e:#}");
                std::process::exit(1);
            }
        },
        Some(Command::Allsat(args)) => {
            if let Err(e) = cmd_allsat::run(&args) {
                safe_eprintln!("Error: {e:#}");
                std::process::exit(1);
            }
        }
        Some(Command::ModelCount(args)) => {
            if let Err(e) = cmd_model_count::run(&args) {
                safe_eprintln!("Error: {e:#}");
                std::process::exit(1);
            }
        }
        Some(Command::Diagnose(cmd)) => match cmd_diagnose::run(&cmd) {
            Ok(0) => {}
            Ok(code) => {
                let _ = io::stdout().flush();
                let _ = io::stderr().flush();
                std::process::exit(code);
            }
            Err(e) => {
                safe_eprintln!("Error: {e:#}");
                std::process::exit(1);
            }
        },
        Some(Command::LaunchGate(args)) => match cmd_launch::run(&args) {
            Ok(0) => {}
            Ok(code) => {
                let _ = io::stdout().flush();
                let _ = io::stderr().flush();
                std::process::exit(code);
            }
            Err(e) => {
                safe_eprintln!("Error: {e:#}");
                std::process::exit(1);
            }
        },
        Some(Command::Release(cmd)) => match cmd_release::run(cmd) {
            Ok(0) => {}
            Ok(code) => {
                let _ = io::stdout().flush();
                let _ = io::stderr().flush();
                std::process::exit(code);
            }
            Err(e) => {
                safe_eprintln!("Error: {e:#}");
                std::process::exit(1);
            }
        },
        Some(Command::LaunchPacket(args)) => match cmd_launch_packet::run(&args) {
            Ok(0) => {}
            Ok(code) => {
                let _ = io::stdout().flush();
                let _ = io::stderr().flush();
                std::process::exit(code);
            }
            Err(e) => {
                safe_eprintln!("Error: {e:#}");
                std::process::exit(1);
            }
        },
        Some(Command::Z3Audit(args)) => match cmd_z3_audit::run(&args) {
            Ok(0) => {}
            Ok(code) => {
                let _ = io::stdout().flush();
                let _ = io::stderr().flush();
                std::process::exit(code);
            }
            Err(e) => {
                safe_eprintln!("Error: {e:#}");
                std::process::exit(1);
            }
        },
        Some(Command::Submission(cmd)) => {
            if let Err(e) = cmd_submission::run(cmd) {
                safe_eprintln!("Error: {e:#}");
                std::process::exit(1);
            }
        }
        Some(Command::VerifierAudit(args)) => match cmd_verifier_audit::run(&args) {
            Ok(0) => {}
            Ok(code) => {
                let _ = io::stdout().flush();
                let _ = io::stderr().flush();
                std::process::exit(code);
            }
            Err(e) => {
                safe_eprintln!("Error: {e:#}");
                std::process::exit(1);
            }
        },
    }
}

/// Worker-thread stack for the PB solver: 1 GiB. Reserved address space only —
/// physical pages commit lazily as the stack is used, so unused headroom is free.
/// Large enough for the deepest observed solver recursion on big/wide instances.
const PB_WORKER_STACK_BYTES: usize = 1024 * 1024 * 1024;

/// If this is a `pb` invocation and `RUST_MIN_STACK` is unset, re-exec the process
/// once with it set so every `std`-spawned worker thread (including dependency-
/// internal scoped workers in the SAT backend) gets an ample stack. This is the only
/// reliable way to size those stacks: `std::thread::min_stack()` reads the variable
/// once and caches it, so an in-process `set_var` after startup is too late, and a
/// large parent stack does not propagate to scoped child threads. Scoped to `pb`, so
/// SMT invocations are byte-for-byte unaffected. Best-effort: if `current_exe` or
/// `exec` fails we fall through and run in-process (today's behaviour, a crash only
/// on the rare deepest-recursion instance), so it can never make things worse.
#[cfg(unix)]
fn maybe_reexec_pb_with_large_stack() {
    use std::os::unix::process::CommandExt;
    let args: Vec<std::ffi::OsString> = env::args_os().collect();
    let is_pb = args.get(1).is_some_and(|a| a == "pb");
    if !is_pb || env::var_os("RUST_MIN_STACK").is_some() {
        return;
    }
    let Ok(exe) = env::current_exe() else {
        return;
    };
    // `exec` replaces the current process image (same PID/fds/cwd) and only returns
    // on failure; the re-exec'd process sees `RUST_MIN_STACK` already set and proceeds.
    let _ = std::process::Command::new(exe)
        .args(args.iter().skip(1))
        .env("RUST_MIN_STACK", PB_WORKER_STACK_BYTES.to_string())
        .exec();
}

#[cfg(not(unix))]
fn maybe_reexec_pb_with_large_stack() {}

#[cfg(test)]
#[path = "main_tests.rs"]
mod tests;
