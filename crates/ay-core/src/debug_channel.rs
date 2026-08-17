// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Canonical debug channel and proof format enums for AY.
//!
//! Typed channels replace ad-hoc `AY_DEBUG_*` variables and populate CLI help.

use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::OnceLock;

use crate::kani_compat::{det_hash_set_new, det_hash_set_with_capacity, DetHashSet};

mod sat_ab_switches;
pub use sat_ab_switches::{sat_ab_switches, set_global_sat_ab_switches, SatAbSwitches};

// ---------------------------------------------------------------------------
// Env var deprecation warnings (#8506 CLI migration)
// ---------------------------------------------------------------------------

/// Global debug configuration set by the CLI binary.
///
/// When the `ay` binary parses `--debug <channel>` flags, it populates this
/// global via [`set_global_debug_config`]. Library consumers that cannot go
/// through the CLI (e.g., `bench_dimacs`) leave this unset, and
/// [`debug_channel_active`] falls back to reading `AY_DEBUG_*` env vars.
static GLOBAL_DEBUG_CONFIG: OnceLock<DebugConfig> = OnceLock::new();

/// Set the global debug configuration (called once by the CLI binary).
///
/// Returns `Err` if the config was already set (idempotent — not an error in practice).
pub fn set_global_debug_config(config: DebugConfig) -> Result<(), DebugConfig> {
    GLOBAL_DEBUG_CONFIG.set(config)
}

/// Check whether a debug channel is active.
///
/// Resolution order:
/// 1. If [`set_global_debug_config`] was called (CLI path), check the config.
/// 2. Otherwise, fall back to reading the `AY_DEBUG_*` env var (library path).
///
/// The env-var fallback ensures that library consumers (tests, examples,
/// bench_dimacs) can still use `AY_DEBUG_*=1` without going through the CLI.
pub fn debug_channel_active(ch: DebugChannel) -> bool {
    if let Some(config) = GLOBAL_DEBUG_CONFIG.get() {
        config.enabled(ch)
    } else {
        debug_channel_active_from_env(ch)
    }
}

/// Check whether a debug channel is active by reading its env var.
///
/// Caches the result of all env var checks in a `OnceLock<DebugConfig>`
/// so that subsequent calls avoid per-check syscalls (#8506).
fn debug_channel_active_from_env(ch: DebugChannel) -> bool {
    static ENV_CONFIG: OnceLock<DebugConfig> = OnceLock::new();
    let config = ENV_CONFIG.get_or_init(|| {
        let mut channels = Vec::new();
        let theory_umbrella = false; // B24: umbrella env retired; per-channel flags remain.
                                     // Check each channel's env var
        for &candidate in ALL_DEBUG_CHANNELS {
            let env_name = debug_channel_env_name(candidate);
            if std::env::var_os(&env_name).is_some()
                || (theory_umbrella && DebugChannel::theory_channels().contains(&candidate))
            {
                channels.push(candidate);
            }
        }
        // B72: the pre-`AY_DEBUG_*` legacy alias for `EufFallback` is retired
        // (never set); the channel itself remains reachable per the scan above.
        if theory_umbrella {
            channels.push(DebugChannel::Theory);
        }
        DebugConfig::from_channels(&channels)
    });
    config.enabled(ch)
}

/// All debug channel variants for exhaustive env var scanning.
const ALL_DEBUG_CHANNELS: &[DebugChannel] = &[
    DebugChannel::Theory,
    DebugChannel::Lia,
    DebugChannel::LiaCheck,
    DebugChannel::LiaBranch,
    DebugChannel::LiaNelsonOppen,
    DebugChannel::Gcd,
    DebugChannel::GcdTab,
    DebugChannel::Dioph,
    DebugChannel::Hnf,
    DebugChannel::Mod,
    DebugChannel::Enum,
    DebugChannel::Patch,
    DebugChannel::Lra,
    DebugChannel::LraBounds,
    DebugChannel::LraAssert,
    DebugChannel::LraReset,
    DebugChannel::LraNelsonOppen,
    DebugChannel::LraForced,
    DebugChannel::Intern,
    DebugChannel::FarkasRow,
    DebugChannel::Cube,
    DebugChannel::Gomory,
    DebugChannel::Euf,
    DebugChannel::EufNelsonOppen,
    DebugChannel::NelsonOppen,
    DebugChannel::Nia,
    DebugChannel::Nra,
    DebugChannel::Fp,
    DebugChannel::Dt,
    DebugChannel::BoolIte,
    DebugChannel::StringCore,
    DebugChannel::Dpll,
    DebugChannel::Sync,
    DebugChannel::Model,
    DebugChannel::VarSubst,
    DebugChannel::Verify,
    DebugChannel::IteEq,
    DebugChannel::ConcatEq,
    DebugChannel::Auflia,
    DebugChannel::IteConditions,
    DebugChannel::Linking,
    DebugChannel::Preprocessed,
    DebugChannel::SatCongruence,
    DebugChannel::TransredTrace,
    DebugChannel::TransredClause,
    DebugChannel::Unknown,
    DebugChannel::Prop,
    DebugChannel::ChcSmt,
    DebugChannel::Algebraic,
    DebugChannel::ArrayAxiomSite,
    DebugChannel::AufliaFix,
    DebugChannel::Row2Components,
    DebugChannel::Regex,
    DebugChannel::EufFallback,
    DebugChannel::Pcr,
    DebugChannel::AufliaFixSummary,
];

/// Return the `AY_DEBUG_*` env var name for a channel.
fn debug_channel_env_name(ch: DebugChannel) -> String {
    use DebugChannel::{
        Algebraic, ArrayAxiomSite, Auflia, AufliaFix, AufliaFixSummary, BoolIte, ChcSmt, ConcatEq,
        Cube, Dioph, Dpll, Dt, Enum, Euf, EufFallback, EufNelsonOppen, FarkasRow, Fp, Gcd, GcdTab,
        Gomory, Hnf, Intern, IteConditions, IteEq, Lia, LiaBranch, LiaCheck, LiaNelsonOppen,
        Linking, Lra, LraAssert, LraBounds, LraForced, LraNelsonOppen, LraReset, Mod, Model,
        NelsonOppen, Nia, Nra, Patch, Pcr, Preprocessed, Prop, Regex, Row2Components,
        SatCongruence, StringCore, Sync, Theory, TransredClause, TransredTrace, Unknown, VarSubst,
        Verify,
    };
    let suffix = match ch {
        Theory => "THEORY",
        Lia => "LIA",
        LiaCheck => "LIA_CHECK",
        LiaBranch => "LIA_BRANCH",
        LiaNelsonOppen => "LIA_NELSON_OPPEN",
        Gcd => "GCD",
        GcdTab => "GCD_TAB",
        Dioph => "DIOPH",
        Hnf => "HNF",
        Mod => "MOD",
        Enum => "ENUM",
        Patch => "PATCH",
        Lra => "LRA",
        LraBounds => "LRA_BOUNDS",
        LraAssert => "LRA_ASSERT",
        LraReset => "LRA_RESET",
        LraNelsonOppen => "LRA_NELSON_OPPEN",
        LraForced => "LRA_FORCED",
        Intern => "INTERN",
        FarkasRow => "FARKAS_ROW",
        Cube => "CUBE",
        Gomory => "GOMORY",
        Euf => "EUF",
        EufNelsonOppen => "EUF_NELSON_OPPEN",
        NelsonOppen => "NELSON_OPPEN",
        Nia => "NIA",
        Nra => "NRA",
        Fp => "FP",
        Dt => "DT",
        BoolIte => "BOOL_ITE",
        StringCore => "STRING_CORE",
        Dpll => "DPLL",
        Sync => "SYNC",
        Model => "MODEL",
        VarSubst => "VAR_SUBST",
        Verify => "VERIFY",
        IteEq => "ITE_EQ",
        ConcatEq => "CONCAT_EQ",
        Auflia => "AUFLIA",
        IteConditions => "ITE_CONDITIONS",
        Linking => "LINKING",
        Preprocessed => "PREPROCESSED",
        SatCongruence => "CONGRUENCE",
        TransredTrace => "TRANSRED_TRACE",
        TransredClause => "TRANSRED_CLAUSE",
        Unknown => "UNKNOWN",
        Prop => "PROP",
        ChcSmt => "CHC_SMT",
        Algebraic => "ALGEBRAIC",
        ArrayAxiomSite => "ARRAY_AXIOM_SITE",
        AufliaFix => "AUFLIA_FIX",
        Row2Components => "ROW2_COMPONENTS",
        Regex => "REGEX",
        EufFallback => "EUF_FALLBACK",
        Pcr => "PCR",
        AufliaFixSummary => "AUFLIA_FIX_SUMMARY",
    };
    format!("AY_DEBUG_{suffix}")
}

/// A debug tracing channel that can be selectively enabled.
///
/// Each variant corresponds to a former `AY_DEBUG_*` environment variable.
/// The `Theory` variant is an umbrella that expands to all theory-level
/// channels (LIA, LRA, EUF, NIA, NRA, FP, DT, strings, Nelson-Oppen).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "cli", derive(clap::ValueEnum))]
#[cfg_attr(feature = "cli", clap(rename_all = "kebab-case"))]
pub enum DebugChannel {
    // ---- Umbrella ----
    /// All theory solvers (expands to every theory-level channel)
    Theory,

    // ---- LIA ----
    /// LIA theory: assertions, bounds, conflicts
    Lia,
    /// LIA check() loop details
    LiaCheck,
    /// LIA branch-and-bound decisions
    LiaBranch,
    /// LIA shared equality handling (Nelson-Oppen)
    LiaNelsonOppen,
    /// GCD test reasoning
    Gcd,
    /// GCD tabular details
    GcdTab,
    /// Diophantine solver
    Dioph,
    /// HNF cut generation
    Hnf,
    /// Modular arithmetic reasoning
    Mod,
    /// Enum-sort reasoning
    Enum,
    /// LIA/LRA patch operations
    Patch,

    // ---- LRA ----
    /// LRA simplex solver
    Lra,
    /// LRA bound tracking
    LraBounds,
    /// LRA assertion processing
    LraAssert,
    /// LRA reset/backtrack operations
    LraReset,
    /// LRA shared equality handling (Nelson-Oppen)
    LraNelsonOppen,
    /// LRA forced expression propagation
    LraForced,
    /// LRA variable internalization
    Intern,
    /// Farkas certificate row-level details
    FarkasRow,
    /// Cube-and-conquer / branch cuts
    Cube,
    /// Gomory cut generation
    Gomory,

    // ---- EUF ----
    /// EUF congruence closure solver
    Euf,
    /// EUF shared equality handling (Nelson-Oppen)
    EufNelsonOppen,

    // ---- Other theories ----
    /// Nelson-Oppen combination fixpoint loop
    NelsonOppen,
    /// Nonlinear integer arithmetic
    Nia,
    /// Nonlinear real arithmetic
    Nra,
    /// Floating-point theory solver
    Fp,
    /// Datatype theory solver
    Dt,
    /// Boolean ITE simplification
    BoolIte,
    /// String theory core solver
    StringCore,

    // ---- DPLL(T) ----
    /// DPLL(T) decisions and backtracking
    Dpll,
    /// Theory synchronization operations
    Sync,
    /// Model construction
    Model,
    /// Variable substitution preprocessing
    VarSubst,
    /// Conflict/propagation verification pipeline
    Verify,
    /// ITE equality preprocessing
    IteEq,
    /// Concat equality preprocessing
    ConcatEq,
    /// AUFLIA-specific reasoning
    Auflia,
    /// ITE condition tracking
    IteConditions,
    /// BV-to-SAT linking
    Linking,
    /// Preprocessed formula output
    Preprocessed,

    // ---- SAT ----
    /// SAT congruence closure
    SatCongruence,
    /// Transitive reduction trace
    TransredTrace,
    /// Transitive reduction clause details
    TransredClause,
    /// Unknown/unrecognized result diagnostics
    Unknown,

    // ---- CHC ----
    /// CHC property propagation
    Prop,
    /// CHC SMT sub-queries
    ChcSmt,
    /// CHC algebraic reasoning
    Algebraic,

    // ---- Array axioms / AUFLIA diagnostics (#8726 part 2) ----
    /// Array axiom assertion site tracing (formerly AY_DEBUG_ARRAY_AXIOM_SITE)
    ArrayAxiomSite,
    /// AUFLIA array extensionality fixpoint tracing (formerly AY_DEBUG_AUFLIA_FIX)
    AufliaFix,
    /// ROW2 clause component tracing (formerly AY_DEBUG_ROW2_COMPONENTS)
    Row2Components,

    // ---- String regex (#8726 part 2) ----
    /// Regex membership solver tracing (formerly AY_DEBUG_REGEX)
    Regex,

    // ---- Combiner bridge (#8726 part 2) ----
    /// EUF/LIA bridge fallback tracing (`--debug euf-fallback`)
    EufFallback,

    // ---- Additional env-only migrations (#8834) ----
    /// Polynomial Calculus with Resolution (PCR) saturation tracing
    /// (formerly env-only `AY_DEBUG_PCR`).
    Pcr,
    /// AUFLIA array extensionality fixpoint summary counters
    /// (formerly env-only `AY_DEBUG_AUFLIA_FIX_SUMMARY`).
    AufliaFixSummary,
}

impl DebugChannel {
    /// Returns every channel that the `Theory` umbrella expands to.
    ///
    /// These are the channels that correspond to individual theory solvers
    /// and their Nelson-Oppen integration layers.
    pub fn theory_channels() -> &'static [Self] {
        use DebugChannel::{
            BoolIte, Cube, Dioph, Dt, Enum, Euf, EufNelsonOppen, FarkasRow, Fp, Gcd, GcdTab,
            Gomory, Hnf, Intern, Lia, LiaBranch, LiaCheck, LiaNelsonOppen, Lra, LraAssert,
            LraBounds, LraForced, LraNelsonOppen, LraReset, Mod, NelsonOppen, Nia, Nra, Patch,
            StringCore,
        };
        &[
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
        ]
    }
}

/// Proof certificate format for UNSAT results.
///
/// Selects the format used when writing proof certificates via `--proof`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "cli", derive(clap::ValueEnum))]
#[cfg_attr(feature = "cli", clap(rename_all = "kebab-case"))]
pub enum ProofFormat {
    /// DRAT text/binary proof (Deletion Resolution Asymmetric Tautology)
    Drat,
    /// LRAT text/binary proof (recommended; Linear Resolution Asymmetric Tautology)
    Lrat,
    /// Lean4 LRAT proof export for formal verification
    Lean4,
    /// Alethe SMT proof format
    Alethe,
}

/// Configuration for which debug channels are active.
///
/// Wraps a `HashSet<DebugChannel>` with convenience methods. The `Theory`
/// umbrella is automatically expanded when constructing via
/// [`DebugConfig::from_channels`].
#[derive(Debug, Clone)]
pub struct DebugConfig {
    channels: DetHashSet<DebugChannel>,
}

impl DebugConfig {
    /// Create a `DebugConfig` from a slice of channels.
    ///
    /// If `Theory` is present, all theory-level channels are automatically
    /// enabled (matching the behavior of the old `AY_DEBUG_THEORY` env var).
    #[must_use]
    pub fn from_channels(channels: &[DebugChannel]) -> Self {
        let mut set = det_hash_set_with_capacity(channels.len());
        for &ch in channels {
            set.insert(ch);
            if ch == DebugChannel::Theory {
                for &theory_ch in DebugChannel::theory_channels() {
                    set.insert(theory_ch);
                }
            }
        }
        Self { channels: set }
    }

    /// Returns `true` if the given channel is enabled.
    #[inline]
    #[must_use]
    pub fn enabled(&self, ch: DebugChannel) -> bool {
        self.channels.contains(&ch)
    }

    /// Returns `true` if no channels are enabled.
    #[inline]
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.channels.is_empty()
    }
}

impl Default for DebugConfig {
    fn default() -> Self {
        Self {
            channels: det_hash_set_new(),
        }
    }
}

// ---------------------------------------------------------------------------
// Global singleton: SAT disable flags (#8506)
// ---------------------------------------------------------------------------

/// Centralized SAT-layer disable flags.
///
/// A single struct set once from the CLI `--no-*` / `--disable` flags and
/// cached for the process lifetime, so hot paths like preprocess() and
/// run_restart_inprocessing() avoid per-call `std::env::var()` syscalls.
#[derive(Debug, Clone, Default)]
pub struct SatDisableFlags {
    /// `--no-bve` — disable bounded variable elimination
    pub no_bve: bool,
    /// `--no-probe` — disable failed literal probing
    pub no_probe: bool,
    /// `--no-congruence` — disable congruence closure
    pub no_congruence: bool,
    /// `--disable=decompose` — disable SCC decomposition
    pub no_decompose: bool,
    /// `--disable=sweep` — disable equivalence sweeping
    pub no_sweep: bool,
    /// `--no-subsume` — disable subsumption
    pub no_subsume: bool,
    /// `--no-vivify` — disable vivification
    pub no_vivify: bool,
    /// `--disable=factor` — disable factoring
    pub no_factor: bool,
    /// `--no-bce` — disable blocked clause elimination
    pub no_bce: bool,
    /// `--disable=transred` — disable transitive reduction
    pub no_transred: bool,
    /// `--no-preprocess` — disable all preprocessing
    pub no_preprocess: bool,
    /// `--no-inprocess` — disable all inprocessing
    pub no_inprocess: bool,
    /// `--no-cold-restart` — disable cold restart
    pub no_cold_restart: bool,
    /// `--disable native-code-backend` — disable external code generation backend compilation.
    pub no_external_codegen_backend: bool,
}

/// Global SAT disable flags, initialized once per process.
static GLOBAL_SAT_DISABLE_FLAGS: OnceLock<SatDisableFlags> = OnceLock::new();

/// Set the global SAT disable flags explicitly (from CLI flags).
pub fn set_global_sat_disable_flags(flags: SatDisableFlags) -> Result<(), SatDisableFlags> {
    GLOBAL_SAT_DISABLE_FLAGS.set(flags)
}

/// Returns a reference to the global SAT disable flags.
///
/// The `ay` CLI always sets these from `--no-*` / `--disable` flags before any
/// solve. The default (no techniques disabled) is the fallback for library
/// consumers that never set them. The former `AY_NO_*` env-var fallback was
/// removed (#8506 completed): those deprecated duplicates of the CLI flags were
/// dead for the binary and are gone.
#[inline]
pub fn sat_disable_flags() -> &'static SatDisableFlags {
    GLOBAL_SAT_DISABLE_FLAGS.get_or_init(SatDisableFlags::default)
}

// ---------------------------------------------------------------------------
// Global singleton: theory disable flags (#8331)
// ---------------------------------------------------------------------------

mod theory_disable;
pub use theory_disable::TheoryDisableFlags;

/// Global theory disable flags, initialized once per process.
static GLOBAL_THEORY_DISABLE_FLAGS: OnceLock<TheoryDisableFlags> = OnceLock::new();

/// Set the global theory disable flags explicitly (from CLI flags).
pub fn set_global_theory_disable_flags(
    flags: TheoryDisableFlags,
) -> Result<(), TheoryDisableFlags> {
    GLOBAL_THEORY_DISABLE_FLAGS.set(flags)
}

/// Returns a reference to the global theory disable flags.
///
/// The `ay` CLI always sets these from `--no-*` / `--max-fixpoint-rounds` flags
/// before any solve; the default (nothing disabled) is the library fallback.
/// The former `AY_NO_*` / `AY_MAX_FIXPOINT_ROUNDS` env-var fallback was removed
/// (#8506 completed) — deprecated duplicates of the CLI flags, dead for the
/// binary.
#[inline]
pub fn theory_disable_flags() -> &'static TheoryDisableFlags {
    GLOBAL_THEORY_DISABLE_FLAGS.get_or_init(TheoryDisableFlags::default)
}

/// `--uflia-arith-decisions`: forwards the arithmetic
/// solver's LP-model-guided `suggest_decision_atom` through `LiaSolver` and
/// `TheoryCombiner` to the SAT extension's theory-suggested-decision rank
/// (eager-theory-propagation design 2026-07-20 §2 Inc2). Default OFF: LRA has
/// implemented the suggestion since #8445 but neither adapter ever forwarded
/// it (git-verified never-wired, not deliberate), so the default preserves the
/// historical byte-identical trajectory on every lane. Carried by
/// `--uflia-arith-decisions` (B72); both forwarding sites gate on this one
/// function.
#[inline]
pub fn uflia_arith_decisions_enabled() -> bool {
    misc_cli_flags().uflia_arith_decisions
}

// ---------------------------------------------------------------------------
// Global singleton: SAT debug env flags (#8506)
// ---------------------------------------------------------------------------

/// Centralized SAT-layer debug/trace environment flags.
///
/// Replaces scattered `std::env::var("AY_*")` reads with a single struct that
/// is read once and cached for the process lifetime. These are debug-only
/// flags (not technique disable flags — those are in [`SatDisableFlags`]).
#[derive(Debug, Clone, Default)]
pub struct SatDebugEnvFlags {
    /// `--trace-ext-conflict` — trace external conflict reasons
    pub trace_ext_conflict: bool,
    /// AY_BVE_LIMIT — max variable count for BVE
    pub bve_limit: Option<usize>,
    /// `--bve-trace` — enable BVE tracing
    pub bve_trace: bool,
    /// AY_BVE_MAX_ROUNDS — override BVE round count for bisection (#8133)
    pub bve_max_rounds: Option<usize>,
    /// `--log` — enable SAT logging (cfg(ay_logging))
    pub log_enabled: bool,
    /// `--dump-conflicts` — dump LRA conflict details
    pub dump_conflicts: bool,
    /// `--clause-provenance` — enable clause provenance tracking
    pub clause_provenance: bool,
    /// `--debug-transred-clause` — specific clause ID to trace in transred
    /// (numeric payload; the boolean enable is the `TransredClause` channel)
    pub debug_transred_clause: Option<u32>,
}

/// Global SAT debug env flags, initialized once per process.
static GLOBAL_SAT_DEBUG_ENV_FLAGS: OnceLock<SatDebugEnvFlags> = OnceLock::new();

/// Initialize SAT debug env flags from environment variables.
fn init_sat_debug_env_from_env() -> SatDebugEnvFlags {
    SatDebugEnvFlags {
        // B72: --trace-ext-conflict is the carrier; the never-set env fallback
        // is deleted.
        trace_ext_conflict: false,
        // B16: --bve-limit / --bve-max-rounds are CLI-only now (the ay bin
        // installs them explicitly); the never-set env fallbacks are deleted.
        bve_limit: None,
        // B72: --bve-trace is the carrier; env fallback deleted.
        bve_trace: false,
        bve_max_rounds: None,
        // B45: --log / --clause-provenance are CLI-only now (the ay bin
        // installs them explicitly); the never-set env fallbacks are deleted.
        log_enabled: false,
        // B72: --dump-conflicts is the carrier; env fallback deleted.
        dump_conflicts: false,
        clause_provenance: false,
        // B72: --debug-transred-clause is the carrier; env fallback deleted.
        debug_transred_clause: None,
    }
}

/// Returns a reference to the global SAT debug env flags.
///
/// On first call, initializes from `AY_*` env vars for backward compat.
#[inline]
pub fn sat_debug_env_flags() -> &'static SatDebugEnvFlags {
    GLOBAL_SAT_DEBUG_ENV_FLAGS.get_or_init(init_sat_debug_env_from_env)
}

/// Set the global SAT debug env flags explicitly (e.g., from CLI flags).
///
/// Called by the `ay` CLI binary after parsing `--bve-limit`, `--bve-trace`,
/// `--bve-max-rounds`, `--log`, `--dump-conflicts`, `--trace-ext-conflict`,
/// and `--clause-provenance`. Replaces the env-var IPC round-trip (#8835).
pub fn set_global_sat_debug_env_flags(flags: SatDebugEnvFlags) -> Result<(), SatDebugEnvFlags> {
    GLOBAL_SAT_DEBUG_ENV_FLAGS.set(flags)
}

// ---------------------------------------------------------------------------
// Global singleton: trace config (#8495)
// ---------------------------------------------------------------------------

/// Structured configuration for diagnostic, trace, replay, and dump paths.
///
/// The `ay` CLI populates this directly from parsed flags so downstream crates
/// do not rely on `std::env::set_var` IPC. When a library consumer has not set
/// the global explicitly, the first access falls back to deprecated `AY_*`
/// environment variables for compatibility.
#[derive(Debug, Clone, Default)]
pub struct TraceConfig {
    /// --diagnostic-file, or auto-generated from AY_DIAGNOSTIC=1
    pub diagnostic_path: Option<String>,
    /// AY_DECISION_TRACE_FILE
    pub decision_trace_path: Option<String>,
    /// `--replay-trace`
    pub replay_trace_path: Option<String>,
    /// `--trace-file`
    pub trace_file_path: Option<String>,
    /// `--solution-file`
    pub solution_file_path: Option<String>,
    /// Adaptive-portfolio decision log path (CLI-carried; B24: env retired)
    pub decision_log_path: Option<String>,
    /// Canonical pure-QF_BV CNF export path (`--dump-bv-cnf` / `AY_DUMP_BV_CNF`).
    ///
    /// `AY_DUMP_BV_DIMACS` is accepted as a legacy alias when configuration
    /// is initialized from the environment.
    pub dump_bv_cnf_path: Option<String>,
    /// DRAT proof output path for a single-invocation bit-blasted QF_BV solve
    /// (`--proof X.drat` alongside `--dump-bv-cnf`). When set, the SAME eager
    /// bit-blast that produces the dumped CNF emits a drat-trim-checkable DRAT
    /// beside it, so the CNF and its UNSAT certificate come from one solve.
    /// Only honored for the top-level owning check; never env-driven.
    pub bv_drat_path: Option<String>,
    /// Whether the DRAT proof at `bv_drat_path` is written in binary format.
    pub bv_drat_binary: bool,
    /// Private temp CNF path for `--self-check` BV DRAT self-certification.
    ///
    /// Populated by the CLI ONLY when `--self-check` is set and the user did not
    /// request an explicit `--dump-bv-cnf`. Distinct from `dump_bv_cnf_path` so
    /// that none of the user-facing `--dump-bv-cnf` error/no-verdict handling is
    /// triggered: the emission machinery reaches these paths solely through the
    /// thread-local self-cert arm (see `bv_cnf_dump::configured_path`), which is
    /// set only around an eligible top-level pure-QF_BV `(check-sat)`. Never
    /// env-driven; text DRAT only.
    pub bv_drat_self_cert_cnf_path: Option<String>,
    /// Private temp DRAT path companion to `bv_drat_self_cert_cnf_path`.
    pub bv_drat_self_cert_drat_path: Option<String>,
    /// `--kind-dump-dir` — k-induction TS formula dump directory (#8834)
    pub kind_dump_dir: Option<String>,
    /// AY_DUMP_ENCODING — pre-solve DIMACS encoding dump path (#8834)
    pub dump_encoding_path: Option<String>,
}

/// Backward-compatible alias for the pre-#8495 trace path singleton name.
pub type TracePathCache = TraceConfig;

/// Global trace config, initialized once per process.
static GLOBAL_TRACE_CONFIG: OnceLock<TraceConfig> = OnceLock::new();

/// Read the BV CNF dump path from the environment for compatibility.
///
/// Initialize trace config from environment variables.
fn init_trace_config_from_env() -> TraceConfig {
    // B21/B24: --diagnostic-file is the carrier; both env arms (explicit
    // path, auto temp path) are retired.
    let diagnostic_path = None;
    TraceConfig {
        diagnostic_path,
        // B21: --decision-trace is the carrier; the env fallback is retired.
        decision_trace_path: None,
        // B24: --replay-trace is the carrier; env fallback retired.
        replay_trace_path: None,
        // B72: --trace-file is the carrier; the env fallback (and the stale
        // subprocess-IPC note — no setter survives anywhere) is deleted.
        trace_file_path: None,
        // B45: --solution-file is the carrier; env fallback retired.
        solution_file_path: None,
        // B24: the CLI carrier is the path source; env fallback retired.
        decision_log_path: None,
        // B58: --dump-bv-cnf is the carrier; the env fallback is retired.
        dump_bv_cnf_path: None,
        // DRAT-for-BV is a CLI-only coupling to `--dump-bv-cnf`; no env alias.
        bv_drat_path: None,
        bv_drat_binary: false,
        // Self-cert temp paths are CLI-only (`--self-check`); never env-driven.
        bv_drat_self_cert_cnf_path: None,
        bv_drat_self_cert_drat_path: None,
        // B72: --kind-dump-dir is the carrier; env fallback deleted.
        kind_dump_dir: None,
        // B21: --dump-encoding is the carrier; the env fallback is retired.
        dump_encoding_path: None,
    }
}

/// Returns a reference to the global trace config.
///
/// On first call, initializes from `AY_*` env vars for backward compat.
#[inline]
pub fn trace_config() -> &'static TraceConfig {
    GLOBAL_TRACE_CONFIG.get_or_init(init_trace_config_from_env)
}

/// Set the global trace config explicitly (e.g., from CLI flags).
///
/// Called by the `ay` CLI binary after parsing `--diagnostic-file`,
/// `--decision-trace`, `--replay`, `--trace-file`, `--solution-file`,
/// `--decision-log`, and `--dump-bv-cnf`. Replaces the env-var IPC
/// round-trip (#8835).
pub fn set_global_trace_config(config: TraceConfig) -> Result<(), Box<TraceConfig>> {
    GLOBAL_TRACE_CONFIG.set(config).map_err(Box::new)
}

/// Compatibility accessor for code still using the old `TracePathCache` name.
#[inline]
pub fn trace_path_cache() -> &'static TraceConfig {
    trace_config()
}

/// Compatibility setter for code still using the old `TracePathCache` name.
pub fn set_global_trace_path_cache(config: TraceConfig) -> Result<(), Box<TraceConfig>> {
    set_global_trace_config(config)
}

static TRACE_FILE_CLAIMED: AtomicBool = AtomicBool::new(false);

/// Claim exclusive ownership of the `--trace-file` sink for a higher-level tracer.
///
/// Higher-level tracers include PDR and KindSolver. After this call,
/// `trace_file_available()` returns false, preventing nested SAT/DPLL tracers
/// from opening the same file.
///
/// Idempotent: calling twice is safe and has no additional effect.
///
/// Call [`release_trace_file`] after the trace is finished to allow a
/// subsequent solver invocation in the same process to claim the file again.
pub fn claim_trace_file() {
    TRACE_FILE_CLAIMED.store(true, Ordering::Release);
}

/// Release the trace file claim so that a subsequent solver invocation in the
/// same process can claim the `--trace-file` sink again.
///
/// This is necessary for solver reuse scenarios (e.g., the portfolio runner
/// trying multiple engines sequentially in the same process).
pub fn release_trace_file() {
    TRACE_FILE_CLAIMED.store(false, Ordering::Release);
}

/// Returns true if a `--trace-file` path is configured and unclaimed.
pub fn trace_file_available() -> bool {
    trace_config().trace_file_path.is_some() && !TRACE_FILE_CLAIMED.load(Ordering::Acquire)
}

// ---------------------------------------------------------------------------
// Global singleton: CHC debug env flags (#8506)
// ---------------------------------------------------------------------------

/// Centralized CHC-layer debug environment flags.
///
/// Replaces the scattered per-site `AY_IUC_*` env reads with a single struct
/// cached for the process lifetime.
#[derive(Debug, Clone, Default)]
pub struct ChcDebugEnvFlags {
    /// AY_IUC_TRACE — enable IUC interpolation tracing
    pub iuc_trace: bool,
    /// Hard diagnostic for zero-Farkas fallbacks (B24: env spelling retired)
    pub iuc_require_farkas: bool,
}

/// Global CHC debug env flags, initialized once per process.
static GLOBAL_CHC_DEBUG_ENV_FLAGS: OnceLock<ChcDebugEnvFlags> = OnceLock::new();

/// Initialize CHC debug env flags from environment variables.
fn init_chc_debug_env_from_env() -> ChcDebugEnvFlags {
    ChcDebugEnvFlags {
        // B72: --iuc-trace is the carrier; env fallback deleted.
        iuc_trace: false,
        // B24: the hard-diagnostic env is retired (never set).
        iuc_require_farkas: false,
    }
}

/// Returns a reference to the global CHC debug env flags.
///
/// On first call, initializes from `AY_IUC_*` env vars for backward compat.
#[inline]
pub fn chc_debug_env_flags() -> &'static ChcDebugEnvFlags {
    GLOBAL_CHC_DEBUG_ENV_FLAGS.get_or_init(init_chc_debug_env_from_env)
}

/// Set the global CHC debug env flags explicitly (e.g., from CLI flags).
///
/// Called by the `ay` CLI binary after parsing `--iuc-trace` and
/// `--strict-iuc-farkas`. Replaces the env-var IPC round-trip (#8835).
pub fn set_global_chc_debug_env_flags(flags: ChcDebugEnvFlags) -> Result<(), ChcDebugEnvFlags> {
    GLOBAL_CHC_DEBUG_ENV_FLAGS.set(flags)
}

// ---------------------------------------------------------------------------
// Global singleton: miscellaneous CLI flags (#8835)
// ---------------------------------------------------------------------------

/// Centralized miscellaneous CLI flag storage.
///
/// Holds values that were previously round-tripped through `AY_*` env vars as
/// IPC between the CLI binary and downstream libraries. Populated from CLI
/// flags, except that `sat_variant` retains its documented
/// `AY_SAT_VARIANT` compatibility fallback; downstream readers go through
/// `misc_cli_flags()` instead of re-reading the environment.
///
/// Note: Flags for `--dump-encoding`, `--kind-dump-dir`, and
/// `--debug-transred-clause` live on [`TraceConfig`] and
/// [`SatDebugEnvFlags`] respectively (added by #8834).
#[derive(Debug, Clone, Default)]
pub struct MiscCliFlags {
    /// `--dump-auflia-assertions` — enable AUFLIA assertion dumping.
    pub dump_auflia_assertions: bool,
    /// `--sat-variant=VARIANT` — SAT variant selection for DIMACS input.
    pub sat_variant: Option<String>,
    /// Whether `sat_variant` came from the real CLI rather than the
    /// `AY_SAT_VARIANT` compatibility fallback.
    pub sat_variant_from_cli: bool,
    /// SAT startup-plan gates explicitly disabled by CLI syntax.
    pub disabled_sat_startup_capabilities: Vec<&'static str>,
    /// `--dpll-diagnostic-file=FILE` — explicit DPLL diagnostic JSONL path.
    pub dpll_diagnostic_file: Option<String>,
    /// `--dpll-diagnostic` — enable DPLL diagnostic JSONL at auto temp path.
    pub dpll_diagnostic_enabled: bool,
    /// `--dpll-trace-file=FILE` — explicit DPLL(T) trace JSONL path.
    pub dpll_trace_file: Option<String>,
    /// `--maxsat-no-tot-eqs` — drop totalizer output equalities (A/B; B17).
    pub maxsat_no_tot_eqs: bool,
    /// `--maxsat-no-bce-revert` — keep the preprocessed engine after a
    /// mostly-risky BCE reduction (A/B; B17).
    pub maxsat_no_bce_revert: bool,
    /// `--maxsat-no-am1-maxcover` — restore the shared-only AM1 cover (B32).
    pub maxsat_no_am1_maxcover: bool,
    /// `--maxsat-bce` — arm the opt-in one-shot BCE preprocessing lane (B32;
    /// stays default OFF like the retired env spelling).
    pub maxsat_bce: bool,
    /// `--maxsat-no-bmo` — disable BMO stratified descent (B32).
    pub maxsat_no_bmo: bool,
    /// `--maxsat-no-cold-descent` — disable the cold-descent gate (B32).
    pub maxsat_no_cold_descent: bool,
    /// `--maxsat-no-descent-residual` — disable residual-descent reuse (B32).
    pub maxsat_no_descent_residual: bool,
    /// `--maxsat-no-dpw` — never select the DPW encoding (B32).
    pub maxsat_no_dpw: bool,
    /// `--maxsat-no-early-descent` — disable the early stratified descent
    /// slice (B32).
    pub maxsat_no_early_descent: bool,
    /// `--maxsat-no-preproc` — disable one-shot maxsat preprocessing (B32).
    pub maxsat_no_preproc: bool,
    /// `--maxsat-no-milp-race` — disable the MILP race lane (B32; the race
    /// is correct-by-default, opting out is for contention-free benching).
    pub maxsat_no_milp_race: bool,
    /// `--no-inc-linear-parse` — restore parse-every-line incremental input
    /// handling (B32).
    pub no_inc_linear_parse: bool,
    /// `--no-milp-fastpath` — disable the QF_LRA MILP fastpath route (B32).
    pub no_milp_fastpath: bool,
    /// `--sat-relevancy <0|1|2>` — force the relevancy brancher off/on
    /// (`2` also turns on the engage marker); unset lets the caller decide
    /// (B36; was --sat-relevancy).
    pub sat_relevancy: Option<u8>,
    /// `--fc-global-budget <N>` — explicit FC global pair budget; unset arms
    /// the many-array autoscale (B36).
    pub fc_global_budget: Option<usize>,
    /// `--maxsat-debug` — MILP-race gate diagnostics (B41).
    pub maxsat_debug: bool,
    /// `--proof-self-check <1|2>` — proof self-check mode, warn | strict
    /// (B41; `None` = off).
    pub proof_self_check: Option<u8>,
    /// `--chc-checked-replay <secs>` — opt-in CHECKED replay budget (B41).
    pub chc_checked_replay_secs: Option<u64>,
    /// `--xor-allow-large` — lift the XOR-extension clause cap (B41).
    pub xor_allow_large: bool,
    /// `--xor-allow-residual` — allow residual-dominated XOR routing (B41).
    pub xor_allow_residual: bool,
    /// `--phase-trace` — dpll phase trace lines (B42 diagnostic).
    pub phase_trace: bool,
    /// `--debug-cert` — certificate-path diagnostics (B42).
    pub debug_cert: bool,
    /// `--debug-qmg` — quantified-model-gate diagnostics (B42).
    pub debug_qmg: bool,
    /// `--model-reject-dump` — dump rejected models (B42).
    pub model_reject_dump: bool,
    /// `--debug-strict-oracle` — strict-oracle diagnostics (B42).
    pub debug_strict_oracle: bool,
    /// `--g3-gate-dump` — G3 gate dump (B42).
    pub g3_gate_dump: bool,
    /// `--quiet-soundness-gate` — suppress soundness-gate chatter (B42).
    pub quiet_soundness_gate: bool,
    /// `--rup-fallback-trace` — RUP fallback trace (B42).
    pub rup_fallback_trace: bool,
    /// `--lra-inc-engine-stats` — inc-engine persistence stats (B42).
    pub lra_inc_engine_stats: bool,
    /// `--lra-inc-engine-reverify` — from-scratch disagreement backstop
    /// (B42).
    pub lra_inc_engine_reverify: bool,
    /// `--debug-no-terms i,j` — suppress listed term ids in combiner-check
    /// dumps (B42).
    pub debug_no_terms: Option<String>,
    /// `--proof-introspect <path>` — append proof introspection to a file
    /// (B42).
    pub proof_introspect: Option<String>,
    /// `--proof-introspect-probe <path>` — probe-derivation dump (B42).
    pub proof_introspect_probe: Option<String>,
    /// `--str-w4-work <n>` — W4 work cap (`0` = unbounded; B42).
    pub str_w4_work: Option<u64>,
    /// `--sat-ab-subst-stats` — congruence/substitution stats dumps (B43).
    pub ab_subst_stats: bool,
    /// `--sat-ab-subst-dump-merges` — merge/unit provenance dump (B43).
    pub ab_subst_dump_merges: bool,
    /// `--sat-ab-subst-dump-gates` — gate-extraction dump (B43).
    pub ab_subst_dump_gates: bool,
    /// `--sat-ab-subst-dump-edges` — congruence edge dump (B43).
    pub ab_subst_dump_edges: bool,
    /// `--sat-ab-dump-db` — dump the live clause DB at congruence entry
    /// (B43).
    pub ab_dump_db: bool,
    /// `--sat-factor-probe` — factor candidate-schedule report (B43).
    pub factor_probe: bool,
    /// `--sat-probe-trace-dup` — duplicate-push probe in the clause trace
    /// (B43).
    pub probe_trace_dup: bool,
    /// `--sat-l0-unsat-trace` — level-0 core-failsafe trace (B43).
    pub sat_l0_unsat_trace: bool,
    /// `--sat-symmetry-trace` — symmetry pipeline trace (B43).
    pub sat_symmetry_trace: bool,
    /// `--sat-mem-probe` — per-engine construction footprint report (B43).
    pub sat_mem_probe: bool,
    /// `--sat-ab-triage-clause d1,d2,...` — soundness-triage target clause
    /// in DIMACS lits (B43).
    pub ab_triage_clause: Option<String>,
    /// `--sat-ab-triage-var <dimacs var>` — report every assignment of the
    /// variable (B43).
    pub ab_triage_var: Option<u64>,
    /// `--sat-ab-triage-probe d1,d2,...` — RUP-probe triage target (B43).
    pub ab_triage_probe: Option<String>,
    /// `--chc-accept-profile` — clause-inlining accept profile (B44).
    pub chc_accept_profile: bool,
    /// `--chc-cata-trace` — catamorphism abstraction trace (B44).
    pub chc_cata_trace: bool,
    /// `--chc-houdini-debug` — Houdini lane diagnostics (B44).
    pub chc_houdini_debug: bool,
    /// `--chc-imc-stats` — IMC lane statistics (B44).
    pub chc_imc_stats: bool,
    /// `--chc-proof-itp-stats` — proof-backed interpolation stats (B44).
    pub chc_proof_itp_stats: bool,
    /// `--chc-ice-dt-trace` — ICE datatype learner trace (B44).
    pub chc_ice_dt_trace: bool,
    /// `--chc-dt-bmc-trace` — datatype-BMC trace (B44).
    pub chc_dt_bmc_trace: bool,
    /// `--chc-v2-debug` — BV dual-lane v2 diagnostics (B44).
    pub chc_v2_debug: bool,
    /// `--chc-ground-bt-debug` — ground backtranslation diagnostics (B44).
    pub chc_ground_bt_debug: bool,
    /// `--chc-bmc-nested-debug` — nested-BMC diagnostics (B44).
    pub chc_bmc_nested_debug: bool,
    /// `--chc-debug-marker-dag-verify` — marker-DAG verbose verification
    /// (B44).
    pub chc_debug_marker_dag_verify: bool,
    /// `--chc-array-frontier-telemetry` — array-content frontier telemetry
    /// (B44).
    pub chc_array_frontier_telemetry: bool,
    /// `--chc-cata-dump-abstract <dir>` — dump abstract LIA problems (B44).
    pub chc_cata_dump_abstract: Option<String>,
    /// `--chc-cata-dump-obligations <dir>` — dump undischarged obligations
    /// (B44).
    pub chc_cata_dump_obligations: Option<String>,
    /// `--chc-dump-scalarized <dir>` — dump scalarized problems (B44).
    pub chc_dump_scalarized: Option<String>,
    /// `--chc-dump-failed-replay-obligation <dir>` — write failing replay
    /// obligations as runnable scripts (B44).
    pub chc_dump_failed_replay_obligation: Option<String>,
    /// `--chc-checksat-dump <dir>` — capture timeout-class check scripts
    /// (B44).
    pub chc_checksat_dump: Option<String>,
    /// `--chc-pdr-dump <dir>` — dump PDR executor queries (B44).
    pub chc_pdr_dump: Option<String>,
    /// `--chc-proof-itp-dump <dir>` — dump proof-solve scripts (B44).
    pub chc_proof_itp_dump: Option<String>,
    /// `--chc-checksat-trace <level>` — check-sat trace verbosity (B44).
    pub chc_checksat_trace: Option<u8>,
    /// `--euf-gap-stats` — EUF propagation-gap profiling (B45).
    pub euf_gap_stats: bool,
    /// `--lia-instrument` — LIA instrumentation reporter (B45).
    pub lia_instrument: bool,
    /// `--probe-stats-every <n>` — LIA probe-stats report interval
    /// (default 1000; B45).
    pub probe_stats_every: Option<u64>,
    /// `--str-nf-closures i,j,...` — explicit string NF closure subset
    /// (B45).
    pub str_nf_closures: Option<String>,
    /// `--trace-cegqi-attr` — CEGQI attribution trace (B59).
    pub trace_cegqi_attr: bool,
    /// `--debug-read-pin` — read-pin diagnostics (B59).
    pub debug_read_pin: bool,
    /// `--f1-diag` — F1 combiner diagnostics (B59).
    pub f1_diag: bool,
    /// `--census-trace` — DT model census trace (B59).
    pub census_trace: bool,
    /// `--debug-pigeonhole` — pigeonhole-core diagnostics (B59).
    pub debug_pigeonhole: bool,
    /// `--cert-debug` — PB certificate diagnostics (B59).
    pub cert_debug: bool,
    /// `--count-debug` — model-counting diagnostics (B59).
    pub count_debug: bool,
    /// `--tseitin-trace` — Tseitin derivation trace (B60).
    pub tseitin_trace: bool,
    /// `--debug-subst` — LIA substitution diagnostics (B60).
    pub debug_subst: bool,
    /// `--debug-split-exit` — pipeline split-exit diagnostics (B60).
    pub debug_split_exit: bool,
    /// `--debug-class-merge` — combiner class-merge diagnostics (B60).
    pub debug_class_merge: bool,
    /// `--milp-fastpath-debug` — MILP fastpath diagnostics (B60).
    pub milp_fastpath_debug: bool,
    /// `--demand-debug` — quantifier demand diagnostics (B60).
    pub demand_debug: bool,
    /// `--prop-debug` — extension propagation diagnostics (B60).
    pub prop_debug: bool,
    /// `--quant-stats` — quantifier statistics (B60).
    pub quant_stats: bool,
    /// `--debug-fixup` — combined-theory fixup diagnostics (B60).
    pub debug_fixup: bool,
    /// `--debug-cegar` — CEGAR escalation diagnostics (B60).
    pub debug_cegar: bool,
    /// `--str-prepass-stats` — string prepass statistics (B60).
    pub str_prepass_stats: bool,
    /// `--milp-lane-trace` — PB portfolio MILP-lane trace (B62).
    pub milp_lane_trace: bool,
    /// `--verify-mixed-strings-stats` (B63).
    pub verify_mixed_strings_stats: bool,
    /// `--a5-uf-eq-defer` — A5 UF equality deferral arm (B63).
    pub a5_uf_eq_defer: bool,
    /// `--spike-dump` — interpolation-spike dump (B63).
    pub spike_dump: bool,
    /// `--spike-verbose` — interpolation-spike verbosity (B63).
    pub spike_verbose: bool,
    /// `--qfax-combiner-route` — QF_AX combiner route arm (B63).
    pub qfax_combiner_route: bool,
    /// `--qfax-cegar` — QF_AX CEGAR arm (B63).
    pub qfax_cegar: bool,
    /// `--qfax-lanes-debug` — QF_AX lane diagnostics (B63).
    pub qfax_lanes_debug: bool,
    /// `--probe-strict-check` — strict-check progress probe (B63).
    pub probe_strict_check: bool,
    /// `--probe-cert-reject` — certificate-reject probe (B63).
    pub probe_cert_reject: bool,
    /// `--uflia-witness-debug` (B63).
    pub uflia_witness_debug: bool,
    /// `--pb-sym-debug` — PB symmetry diagnostics (B63).
    pub pb_sym_debug: bool,
    /// `--pb-farkas-cert` — PB Farkas certificate arm (B63).
    pub pb_farkas_cert: bool,
    /// `--qfax-neg-eq-witness` — QF_AX negative-equality witness arm (B63).
    pub qfax_neg_eq_witness: bool,
    /// `--qfax-neg-chain-gate` — QF_AX negative-chain gate arm (B63).
    pub qfax_neg_chain_gate: bool,
    /// `--vsids-decay <f>` — VSIDS decay override in (0, 1) (B64).
    pub vsids_decay: Option<f64>,
    /// `--inprobe-mult <f>` — inprocessing probe interval multiplier (B64).
    pub inprobe_mult: Option<f64>,
    /// `--factor-elim-bound <n>` — factor elimination bound force (B64).
    pub factor_elim_bound: Option<i64>,
    /// `--pb-sls-endgame-threshold <n>` — SLS endgame threshold (B64).
    pub pb_sls_endgame_threshold: Option<usize>,
    /// `--dump-query-dir <dir>` — dump embedded-consumer queries (B64).
    pub dump_query_dir: Option<String>,
    /// `--keep-alethe-artifacts` — keep carcara harness artifacts (B64).
    pub keep_alethe_artifacts: bool,
    /// `--no-quant-unit-authority` — disable P3a derivation authority (B66).
    pub no_quant_unit_authority: bool,
    /// `--no-consequence-replay` — disable authored consequence replay (B66).
    pub no_consequence_replay: bool,
    /// `--vacuous-marker-narrow` — staged marker narrowing (B66).
    pub vacuous_marker_narrow: bool,
    /// `--proj-axiom-budget <n>` — projection axiom cap (default 50000; B66).
    pub proj_axiom_budget: Option<usize>,
    /// `--uflia-witness-complete` (B66).
    pub uflia_witness_complete: bool,
    /// `--uflia-witness-parts fill|chain` (B66).
    pub uflia_witness_parts: Option<String>,
    /// `--uflia-fused-detour` (B66).
    pub uflia_fused_detour: bool,
    /// `--verify-memo` (B66).
    pub verify_memo: bool,
    /// `--pb-eqagg-debug` (B66).
    pub pb_eqagg_debug: bool,
    /// `--pb-bnb` — PB branch-and-bound upgrade arm (B66).
    pub pb_bnb: bool,
    /// `--no-pb-sls-feasfirst` — disable SLS feasibility-first (B66).
    pub no_pb_sls_feasfirst: bool,
    /// `--pb-strict-optimum` (B66).
    pub pb_strict_optimum: bool,
    /// `--pb-sls-unified` — re-enable the unified SLS loop (B66).
    pub pb_sls_unified: bool,
    /// `--pb-proof-tap-soft-cap-mib <n>` (B66).
    pub pb_proof_tap_soft_cap_mib: Option<u64>,
    /// `--sls-planted` / `--sls-sweep` — SLS bench harness gates (B66).
    pub sls_planted: bool,
    /// See `sls_planted`.
    pub sls_sweep: bool,
    /// `--oll-file <path>` — OLL reference-harness instance (B66).
    pub oll_file: Option<String>,
    /// `--oll-expect <n>` — OLL reference-harness expectation (B66).
    pub oll_expect: Option<String>,
    /// `--pb-debug-panic-on-incumbent` — fault-injection assert arm (B66).
    pub pb_debug_panic_on_incumbent: bool,
    /// `--sat-prune-conflict-experiments <bool>` — tri-state force (B66).
    pub sat_prune_conflict_experiments: Option<bool>,
    /// `--debug-lazy-sync` (B67).
    pub debug_lazy_sync: bool,
    /// `--debug-fc-sync` (B67).
    pub debug_fc_sync: bool,
    /// `--lra-warm-stats` (B67).
    pub lra_warm_stats: bool,
    /// `--fuzz-verbose` (B67).
    pub fuzz_verbose: bool,
    /// `--certora-trace` (B67).
    pub certora_trace: bool,
    /// `--debug-abv-finite-array` (B67).
    pub debug_abv_finite_array: bool,
    /// `--debug-abv-packed-lookup` (B67).
    pub debug_abv_packed_lookup: bool,
    /// `--debug-ladder` (B67).
    pub debug_ladder: bool,
    /// `--debug-wgr` (B67).
    pub debug_wgr: bool,
    /// `--debug-completion-merge` (B67).
    pub debug_completion_merge: bool,
    /// `--debug-arith-oracle` (B67).
    pub debug_arith_oracle: bool,
    /// `--debug-unwitnessed` (B67).
    pub debug_unwitnessed: bool,
    /// `--cut-trace` — PB cutting-planes trace (B67).
    pub cut_trace: bool,
    /// `--dump-render` — BV blast-lean render dump (B67).
    pub dump_render: bool,
    /// `--chc-array-tree-refutation` (B68; opt-in arm).
    pub chc_array_tree_refutation: bool,
    /// `--chc-dont-care-filter` (B68).
    pub chc_dont_care_filter: bool,
    /// `--chc-intern` (B68).
    pub chc_intern: bool,
    /// `--chc-array-inv` (B68).
    pub chc_array_inv: bool,
    /// `--chc-dt-recursive-prefix` (B68; experimental scalar-prefix depth).
    pub chc_dt_recursive_prefix: bool,
    /// `--interface-diet on|shadow` (B69; unset = off).
    pub interface_diet: Option<String>,
    /// `--bv-preprocess quick|full` (B69; unset = no preprocessing).
    pub bv_preprocess: Option<String>,
    /// `--fc-cegar-iters <n>` (B69; default 16).
    pub fc_cegar_iters: Option<u32>,
    /// `--int-pigeonhole-enrich-k <n>` (B69; default unbounded).
    pub int_pigeonhole_enrich_k: Option<usize>,
    /// `--ext-row-seed` (B69).
    pub ext_row_seed: bool,
    /// `--debug-row-seed` (B69).
    pub debug_row_seed: bool,
    /// `--dpll-mint-theory-vars` (B69; opt-in).
    pub dpll_mint_theory_vars: bool,
    /// `--dpll-ite-lift` (B69).
    pub dpll_ite_lift: bool,
    /// `--euf-bool-arg-repair` (B69).
    pub euf_bool_arg_repair: bool,
    /// `--lra-warm-theory` (B69).
    pub lra_warm_theory: bool,
    /// `--force-array-euf` (B69).
    pub force_array_euf: bool,
    /// `--ab-maxsat-core-clause` (B70; A/B arm).
    pub ab_maxsat_core_clause: bool,
    /// `--ab-maxsat-descent-organic-slice` (B70).
    pub ab_maxsat_descent_organic_slice: bool,
    /// `--ab-maxsat-kick-gap-abs` (B70).
    pub ab_maxsat_kick_gap_abs: bool,
    /// `--ab-maxsat-descent-kick-scale` (B70).
    pub ab_maxsat_descent_kick_scale: bool,
    /// `--uflia-arith-decisions` (B72): forward UFLIA arith decision hints to
    /// the arith adapters (default off preserves the historical trajectory).
    pub uflia_arith_decisions: bool,
    /// `--no-skolem-witness-sat` — kill switch for the skolem-witness SAT
    /// confirmation arm in quantifier restore (#skolem-witness-sat).
    pub no_skolem_witness_sat: bool,
}

/// Global miscellaneous CLI flags, initialized once per process.
static GLOBAL_MISC_CLI_FLAGS: OnceLock<MiscCliFlags> = OnceLock::new();

/// Initialize miscellaneous CLI flags from environment variables.
///
/// Used as the back-compat fallback when the CLI has not called
/// [`set_global_misc_cli_flags`] (e.g., library consumers, older callers).
fn init_misc_cli_flags_from_env() -> MiscCliFlags {
    // B24: --dpll-diagnostic-file is the carrier; env fallback retired.
    let dpll_diagnostic_file = None;
    let dpll_diagnostic_enabled = false; // B24: --dpll-diagnostic is the carrier; env retired.
                                         // B72: --dpll-trace-file is the carrier; env fallback deleted.
    let dpll_trace_file = None;
    MiscCliFlags {
        // B72: --dump-auflia-assertions is the carrier; env fallback deleted.
        dump_auflia_assertions: false,
        sat_variant: std::env::var("AY_SAT_VARIANT")
            .ok()
            .filter(|s| !s.is_empty()),
        sat_variant_from_cli: false,
        disabled_sat_startup_capabilities: Vec::new(),
        dpll_diagnostic_file,
        dpll_diagnostic_enabled,
        dpll_trace_file,
        // B17/B32: CLI-only; retired A/B env spellings are intentionally ignored.
        maxsat_no_tot_eqs: false,
        maxsat_no_bce_revert: false,
        maxsat_no_am1_maxcover: false,
        maxsat_bce: false,
        maxsat_no_bmo: false,
        maxsat_no_cold_descent: false,
        maxsat_no_descent_residual: false,
        maxsat_no_dpw: false,
        maxsat_no_early_descent: false,
        maxsat_no_preproc: false,
        maxsat_no_milp_race: false,
        no_inc_linear_parse: false,
        no_milp_fastpath: false,
        sat_relevancy: None,
        fc_global_budget: None,
        maxsat_debug: false,
        proof_self_check: None,
        chc_checked_replay_secs: None,
        xor_allow_large: false,
        xor_allow_residual: false,
        // Diagnostic trace, not an A/B lane: keeps its env read like
        // AY_DUMP_*/AY_TRACE_* — the development design notes direct users to AY_PHASE_TRACE=1
        // for the certification funnel's decline reasons.
        phase_trace: std::env::var_os("AY_PHASE_TRACE").is_some(),
        debug_cert: false,
        debug_qmg: false,
        model_reject_dump: false,
        debug_strict_oracle: false,
        g3_gate_dump: false,
        quiet_soundness_gate: false,
        rup_fallback_trace: false,
        lra_inc_engine_stats: false,
        lra_inc_engine_reverify: false,
        debug_no_terms: None,
        proof_introspect: None,
        proof_introspect_probe: None,
        str_w4_work: None,
        ab_subst_stats: false,
        ab_subst_dump_merges: false,
        ab_subst_dump_gates: false,
        ab_subst_dump_edges: false,
        ab_dump_db: false,
        factor_probe: false,
        probe_trace_dup: false,
        sat_l0_unsat_trace: false,
        sat_symmetry_trace: false,
        sat_mem_probe: false,
        ab_triage_clause: None,
        ab_triage_var: None,
        ab_triage_probe: None,
        chc_accept_profile: false,
        chc_cata_trace: false,
        chc_houdini_debug: false,
        chc_imc_stats: false,
        chc_proof_itp_stats: false,
        chc_ice_dt_trace: false,
        chc_dt_bmc_trace: false,
        chc_v2_debug: false,
        chc_ground_bt_debug: false,
        chc_bmc_nested_debug: false,
        chc_debug_marker_dag_verify: false,
        chc_array_frontier_telemetry: false,
        chc_cata_dump_abstract: None,
        chc_cata_dump_obligations: None,
        chc_dump_scalarized: None,
        chc_dump_failed_replay_obligation: None,
        chc_checksat_dump: None,
        chc_pdr_dump: None,
        chc_proof_itp_dump: None,
        chc_checksat_trace: None,
        euf_gap_stats: false,
        lia_instrument: false,
        probe_stats_every: None,
        str_nf_closures: None,
        trace_cegqi_attr: std::env::var_os("AY_TRACE_CEGQI_ATTR").is_some(),
        debug_read_pin: false,
        f1_diag: false,
        census_trace: false,
        debug_pigeonhole: false,
        cert_debug: false,
        count_debug: false,
        tseitin_trace: false,
        debug_subst: false,
        debug_split_exit: false,
        debug_class_merge: false,
        milp_fastpath_debug: false,
        demand_debug: false,
        prop_debug: false,
        quant_stats: false,
        debug_fixup: false,
        debug_cegar: false,
        str_prepass_stats: false,
        milp_lane_trace: false,
        verify_mixed_strings_stats: false,
        a5_uf_eq_defer: false,
        spike_dump: false,
        spike_verbose: false,
        qfax_combiner_route: false,
        qfax_cegar: false,
        qfax_lanes_debug: false,
        // Diagnostic probe, not an A/B lane: keeps its env read like the
        // AY_DUMP_*/AY_TRACE_* family. The strict-check meter's own docs
        // direct users to AY_PROBE_STRICT_CHECK for the refusing limb's
        // numbers; without this read the probe is unreachable from a test run.
        probe_strict_check: std::env::var_os("AY_PROBE_STRICT_CHECK").is_some(),
        probe_cert_reject: false,
        uflia_witness_debug: false,
        pb_sym_debug: false,
        pb_farkas_cert: false,
        qfax_neg_eq_witness: false,
        qfax_neg_chain_gate: false,
        vsids_decay: None,
        inprobe_mult: None,
        factor_elim_bound: None,
        pb_sls_endgame_threshold: None,
        dump_query_dir: None,
        keep_alethe_artifacts: false,
        no_quant_unit_authority: false,
        no_consequence_replay: false,
        vacuous_marker_narrow: false,
        proj_axiom_budget: None,
        uflia_witness_complete: false,
        uflia_witness_parts: None,
        uflia_fused_detour: false,
        verify_memo: false,
        pb_eqagg_debug: false,
        pb_bnb: false,
        no_pb_sls_feasfirst: false,
        pb_strict_optimum: false,
        pb_sls_unified: false,
        pb_proof_tap_soft_cap_mib: None,
        sls_planted: false,
        sls_sweep: false,
        oll_file: None,
        oll_expect: None,
        pb_debug_panic_on_incumbent: false,
        sat_prune_conflict_experiments: None,
        debug_lazy_sync: false,
        debug_fc_sync: false,
        lra_warm_stats: false,
        fuzz_verbose: false,
        certora_trace: false,
        debug_abv_finite_array: false,
        debug_abv_packed_lookup: false,
        debug_ladder: false,
        debug_wgr: false,
        debug_completion_merge: false,
        debug_arith_oracle: false,
        debug_unwitnessed: false,
        cut_trace: false,
        dump_render: false,
        chc_array_tree_refutation: false,
        chc_dont_care_filter: false,
        chc_intern: false,
        chc_array_inv: false,
        chc_dt_recursive_prefix: false,
        interface_diet: None,
        bv_preprocess: None,
        fc_cegar_iters: None,
        int_pigeonhole_enrich_k: None,
        ext_row_seed: false,
        debug_row_seed: false,
        dpll_mint_theory_vars: false,
        dpll_ite_lift: false,
        euf_bool_arg_repair: false,
        lra_warm_theory: false,
        force_array_euf: false,
        ab_maxsat_core_clause: false,
        ab_maxsat_descent_organic_slice: false,
        ab_maxsat_kick_gap_abs: false,
        ab_maxsat_descent_kick_scale: false,
        // B72: --uflia-arith-decisions is the carrier; no env fallback.
        uflia_arith_decisions: false,
        no_skolem_witness_sat: false,
    }
}

/// Returns a reference to the global miscellaneous CLI flags.
///
/// On first call, initializes from `AY_*` env vars for backward compat.
#[inline]
pub fn misc_cli_flags() -> &'static MiscCliFlags {
    if let Some(overridden) = misc_test_override::MISC_TEST_OVERRIDE.with(std::cell::Cell::get) {
        return overridden;
    }
    GLOBAL_MISC_CLI_FLAGS.get_or_init(init_misc_cli_flags_from_env)
}

/// In-process per-test override seam for [`misc_cli_flags`] (B41; the same
/// shape as `ay_pb_core::ab_switches::TestOverride`, but cross-crate — the
/// steering tests live in consumer crates, so `cfg(test)` here cannot serve
/// them). Not a public API.
#[doc(hidden)]
pub mod misc_test_override {
    use super::MiscCliFlags;

    thread_local! {
        pub(super) static MISC_TEST_OVERRIDE: std::cell::Cell<Option<&'static MiscCliFlags>> =
            const { std::cell::Cell::new(None) };
    }

    /// RAII scope for a test's flags override; restores the previous value on
    /// drop. Leaks one `MiscCliFlags` per override — test-only cost.
    pub struct Guard(Option<&'static MiscCliFlags>);

    #[must_use]
    pub fn set(flags: MiscCliFlags) -> Guard {
        let leaked: &'static MiscCliFlags = Box::leak(Box::new(flags));
        let prev = MISC_TEST_OVERRIDE.with(|c| c.replace(Some(leaked)));
        Guard(prev)
    }

    impl Drop for Guard {
        fn drop(&mut self) {
            let prev = self.0;
            MISC_TEST_OVERRIDE.with(|c| c.set(prev));
        }
    }
}

/// Set the global miscellaneous CLI flags explicitly (e.g., from CLI flags).
///
/// Called by the `ay` CLI binary after argument parsing to replace the
/// env-var IPC round-trip (#8835).
pub fn set_global_misc_cli_flags(flags: MiscCliFlags) -> Result<(), MiscCliFlags> {
    GLOBAL_MISC_CLI_FLAGS.set(flags)
}

#[cfg(test)]
mod tests {
    use super::*;
    use serial_test::serial;

    include!("debug_channel/tests.rs");

    #[test]
    #[serial(trace_file_claim)]
    fn test_trace_file_available_false_when_no_env_var() {
        // In the test environment no trace file is configured,
        // so trace_file_available() should return false regardless of claim state.
        release_trace_file();
        assert!(
            !trace_file_available(),
            "trace_file_available should be false when no trace file is configured"
        );
    }

    #[test]
    #[serial(trace_file_claim)]
    fn test_claim_release_cycle() {
        // Simulate a solver reuse scenario: claim -> solve -> release -> claim again
        release_trace_file();

        claim_trace_file();
        assert!(TRACE_FILE_CLAIMED.load(Ordering::Acquire));

        release_trace_file();
        assert!(!TRACE_FILE_CLAIMED.load(Ordering::Acquire));

        // Second solve can claim again
        claim_trace_file();
        assert!(TRACE_FILE_CLAIMED.load(Ordering::Acquire));

        release_trace_file();
    }
}
