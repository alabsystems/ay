// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Canonical debug channel and proof format enums for AY.
//!
//! These enums replace the ad-hoc `AY_DEBUG_*` environment variables with
//! a type-safe, exhaustive set of debug channels. When the `cli` feature is
//! enabled, both enums derive `clap::ValueEnum` so they appear automatically
//! in `ay solve --debug <channel>` help text.

use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::OnceLock;

use crate::kani_compat::{det_hash_set_new, det_hash_set_with_capacity, DetHashSet};

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
        let theory_umbrella = std::env::var_os("AY_DEBUG_THEORY").is_some();
        // Check each channel's env var
        for &candidate in ALL_DEBUG_CHANNELS {
            let env_name = debug_channel_env_name(candidate);
            if std::env::var_os(&env_name).is_some()
                || (theory_umbrella && DebugChannel::theory_channels().contains(&candidate))
            {
                channels.push(candidate);
            }
        }
        // Legacy env var aliases (#8726 part 2): AY_TRACE_EUF_FALLBACK predates
        // the `AY_DEBUG_*` convention but semantically matches `EufFallback`.
        if std::env::var_os("AY_TRACE_EUF_FALLBACK").is_some()
            && !channels.contains(&DebugChannel::EufFallback)
        {
            channels.push(DebugChannel::EufFallback);
        }
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
    /// EUF/LIA bridge fallback tracing (formerly AY_TRACE_EUF_FALLBACK)
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

/// Centralized theory-layer disable flags.
///
/// A single struct set once from the CLI `--no-*` / `--max-fixpoint-rounds`
/// flags and cached for the process lifetime.
#[derive(Debug, Clone, Default)]
pub struct TheoryDisableFlags {
    /// `--no-bound-axioms`
    pub no_bound_axioms: bool,
    /// `--no-theory-propagation`
    pub no_theory_propagation: bool,
    /// `--no-bcp-theory-check`
    pub no_bcp_theory_check: bool,
    /// `--no-ite-deferral`
    pub no_ite_deferral: bool,
    /// `--disable=theory-check`
    pub disable_theory_check: bool,
    /// `--no-inline-lemmas`
    pub no_inline_lemmas: bool,
    /// `--no-implied-bounds`
    pub no_implied_bounds: bool,
    /// `--no-bound-refinement`
    pub no_bound_refinement: bool,
    /// `--no-bcp-implied-restraint` — kill switch for the sat-side-model-search
    /// Fix #2 restraint (single-pass BCP implied bounds on the
    /// propagation-disabled cex lane). When set, BCP-time implied-bounds
    /// computation reverts to the full fixpoint cascade.
    pub no_bcp_implied_restraint: bool,
    /// `--max-fixpoint-rounds=N`
    pub max_fixpoint_rounds: Option<usize>,
}

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
    /// AY_TRACE_EXT_CONFLICT — trace external conflict reasons
    pub trace_ext_conflict: bool,
    /// AY_BVE_LIMIT — max variable count for BVE
    pub bve_limit: Option<usize>,
    /// AY_BVE_TRACE — enable BVE tracing
    pub bve_trace: bool,
    /// AY_BVE_MAX_ROUNDS — override BVE round count for bisection (#8133)
    pub bve_max_rounds: Option<usize>,
    /// AY_LOG — enable SAT logging (cfg(ay_logging))
    pub log_enabled: bool,
    /// AY_DUMP_CONFLICTS — dump LRA conflict details
    pub dump_conflicts: bool,
    /// AY_CLAUSE_PROVENANCE — enable clause provenance tracking
    pub clause_provenance: bool,
    /// AY_DEBUG_TRANSRED_CLAUSE — specific clause ID to trace in transred
    /// (numeric payload; the boolean enable is the `TransredClause` channel)
    pub debug_transred_clause: Option<u32>,
}

/// Global SAT debug env flags, initialized once per process.
static GLOBAL_SAT_DEBUG_ENV_FLAGS: OnceLock<SatDebugEnvFlags> = OnceLock::new();

/// Initialize SAT debug env flags from environment variables.
fn init_sat_debug_env_from_env() -> SatDebugEnvFlags {
    SatDebugEnvFlags {
        trace_ext_conflict: std::env::var_os("AY_TRACE_EXT_CONFLICT").is_some(),
        bve_limit: std::env::var("AY_BVE_LIMIT")
            .ok()
            .and_then(|s| s.parse::<usize>().ok()),
        bve_trace: std::env::var_os("AY_BVE_TRACE").is_some(),
        bve_max_rounds: std::env::var("AY_BVE_MAX_ROUNDS")
            .ok()
            .and_then(|s| s.parse::<usize>().ok()),
        log_enabled: std::env::var("AY_LOG").ok().is_some_and(|v| v == "1"),
        dump_conflicts: std::env::var_os("AY_DUMP_CONFLICTS").is_some(),
        clause_provenance: std::env::var("AY_CLAUSE_PROVENANCE")
            .ok()
            .is_some_and(|v| v == "1" || v.eq_ignore_ascii_case("true")),
        debug_transred_clause: std::env::var("AY_DEBUG_TRANSRED_CLAUSE")
            .ok()
            .and_then(|s| s.parse::<u32>().ok()),
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
    /// AY_DIAGNOSTIC_FILE or auto-generated from AY_DIAGNOSTIC=1
    pub diagnostic_path: Option<String>,
    /// AY_DECISION_TRACE_FILE
    pub decision_trace_path: Option<String>,
    /// AY_REPLAY_TRACE_FILE
    pub replay_trace_path: Option<String>,
    /// AY_TRACE_FILE
    pub trace_file_path: Option<String>,
    /// AY_SOLUTION_FILE
    pub solution_file_path: Option<String>,
    /// AY_DECISION_LOG
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
    /// AY_KIND_DUMP_DIR — k-induction TS formula dump directory (#8834)
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
/// `AY_DUMP_BV_CNF` is the canonical spelling. `AY_DUMP_BV_DIMACS` predates
/// the CLI flag and remains a fallback alias for existing B-cert consumers.
/// Empty and whitespace-only values are ignored, and the canonical spelling
/// wins when both are present.
pub fn bv_cnf_dump_path_from_env() -> Option<String> {
    ["AY_DUMP_BV_CNF", "AY_DUMP_BV_DIMACS"]
        .into_iter()
        .find_map(|name| {
            std::env::var(name)
                .ok()
                .filter(|path| !path.trim().is_empty())
        })
}

/// Initialize trace config from environment variables.
fn init_trace_config_from_env() -> TraceConfig {
    let diagnostic_path = {
        if let Some(path) = std::env::var("AY_DIAGNOSTIC_FILE")
            .ok()
            .map(|s| s.trim().to_string())
            .filter(|s| !s.is_empty())
        {
            Some(path)
        } else if std::env::var("AY_DIAGNOSTIC")
            .ok()
            .is_some_and(|v| v.trim() == "1")
        {
            let pid = std::process::id();
            let path = std::env::temp_dir().join(format!("ay_sat_diagnostic_{pid}.jsonl"));
            Some(path.to_string_lossy().into_owned())
        } else {
            None
        }
    };
    TraceConfig {
        diagnostic_path,
        decision_trace_path: std::env::var("AY_DECISION_TRACE_FILE")
            .ok()
            .map(|s| s.trim().to_string())
            .filter(|s| !s.is_empty()),
        replay_trace_path: std::env::var("AY_REPLAY_TRACE_FILE")
            .ok()
            .map(|s| s.trim().to_string())
            .filter(|s| !s.is_empty()),
        trace_file_path: std::env::var("AY_TRACE_FILE")
            .ok()
            .map(|s| s.trim().to_string())
            .filter(|s| !s.is_empty()),
        solution_file_path: std::env::var("AY_SOLUTION_FILE")
            .ok()
            .map(|s| s.trim().to_string())
            .filter(|s| !s.is_empty()),
        decision_log_path: std::env::var("AY_DECISION_LOG")
            .ok()
            .map(|s| s.trim().to_string())
            .filter(|s| !s.is_empty()),
        dump_bv_cnf_path: bv_cnf_dump_path_from_env(),
        // DRAT-for-BV is a CLI-only coupling to `--dump-bv-cnf`; no env alias.
        bv_drat_path: None,
        bv_drat_binary: false,
        kind_dump_dir: std::env::var("AY_KIND_DUMP_DIR")
            .ok()
            .map(|s| s.trim().to_string())
            .filter(|s| !s.is_empty()),
        dump_encoding_path: std::env::var("AY_DUMP_ENCODING")
            .ok()
            .map(|s| s.trim().to_string())
            .filter(|s| !s.is_empty()),
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

/// Claim exclusive ownership of `AY_TRACE_FILE` for a higher-level tracer.
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
/// same process can claim `AY_TRACE_FILE` again.
///
/// This is necessary for solver reuse scenarios (e.g., the portfolio runner
/// trying multiple engines sequentially in the same process).
pub fn release_trace_file() {
    TRACE_FILE_CLAIMED.store(false, Ordering::Release);
}

/// Returns true if `AY_TRACE_FILE` is set and has not been claimed.
pub fn trace_file_available() -> bool {
    trace_config().trace_file_path.is_some() && !TRACE_FILE_CLAIMED.load(Ordering::Acquire)
}

// ---------------------------------------------------------------------------
// Global singleton: CHC debug env flags (#8506)
// ---------------------------------------------------------------------------

/// Centralized CHC-layer debug environment flags.
///
/// Replaces scattered `std::env::var("AY_IUC_*")` reads with a single struct
/// cached for the process lifetime.
#[derive(Debug, Clone, Default)]
pub struct ChcDebugEnvFlags {
    /// AY_IUC_TRACE — enable IUC interpolation tracing
    pub iuc_trace: bool,
    /// AY_IUC_REQUIRE_FARKAS — hard diagnostic for zero-Farkas fallbacks
    pub iuc_require_farkas: bool,
}

/// Global CHC debug env flags, initialized once per process.
static GLOBAL_CHC_DEBUG_ENV_FLAGS: OnceLock<ChcDebugEnvFlags> = OnceLock::new();

/// Initialize CHC debug env flags from environment variables.
fn init_chc_debug_env_from_env() -> ChcDebugEnvFlags {
    ChcDebugEnvFlags {
        iuc_trace: std::env::var("AY_IUC_TRACE")
            .ok()
            .is_some_and(|v| v == "1" || v.eq_ignore_ascii_case("true")),
        iuc_require_farkas: std::env::var("AY_IUC_REQUIRE_FARKAS")
            .ok()
            .is_some_and(|v| v == "1" || v.eq_ignore_ascii_case("true")),
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
/// flags; downstream readers go through `misc_cli_flags()` instead of
/// `std::env::var`.
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
    /// `--dpll-diagnostic-file=FILE` — explicit DPLL diagnostic JSONL path.
    pub dpll_diagnostic_file: Option<String>,
    /// `--dpll-diagnostic` — enable DPLL diagnostic JSONL at auto temp path.
    pub dpll_diagnostic_enabled: bool,
    /// `--dpll-trace-file=FILE` — explicit DPLL(T) trace JSONL path.
    pub dpll_trace_file: Option<String>,
}

/// Global miscellaneous CLI flags, initialized once per process.
static GLOBAL_MISC_CLI_FLAGS: OnceLock<MiscCliFlags> = OnceLock::new();

/// Initialize miscellaneous CLI flags from environment variables.
///
/// Used as the back-compat fallback when the CLI has not called
/// [`set_global_misc_cli_flags`] (e.g., library consumers, older callers).
fn init_misc_cli_flags_from_env() -> MiscCliFlags {
    let dpll_diagnostic_file = std::env::var("AY_DPLL_DIAGNOSTIC_FILE")
        .ok()
        .map(|s| s.trim().to_string())
        .filter(|s| !s.is_empty());
    let dpll_diagnostic_enabled = std::env::var("AY_DPLL_DIAGNOSTIC")
        .ok()
        .is_some_and(|v| v.trim() == "1");
    let dpll_trace_file = std::env::var("AY_DPLL_TRACE_FILE")
        .ok()
        .map(|s| s.trim().to_string())
        .filter(|s| !s.is_empty());
    MiscCliFlags {
        dump_auflia_assertions: std::env::var_os("AY_DUMP_AUFLIA_ASSERTIONS").is_some(),
        sat_variant: std::env::var("AY_SAT_VARIANT")
            .ok()
            .filter(|s| !s.is_empty()),
        dpll_diagnostic_file,
        dpll_diagnostic_enabled,
        dpll_trace_file,
    }
}

/// Returns a reference to the global miscellaneous CLI flags.
///
/// On first call, initializes from `AY_*` env vars for backward compat.
#[inline]
pub fn misc_cli_flags() -> &'static MiscCliFlags {
    GLOBAL_MISC_CLI_FLAGS.get_or_init(init_misc_cli_flags_from_env)
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

    #[test]
    fn test_debug_config_empty_by_default() {
        let cfg = DebugConfig::default();
        assert!(cfg.is_empty());
        assert!(!cfg.enabled(DebugChannel::Lia));
    }

    #[test]
    fn test_debug_config_explicit_channel() {
        let cfg = DebugConfig::from_channels(&[DebugChannel::Lia, DebugChannel::Dpll]);
        assert!(!cfg.is_empty());
        assert!(cfg.enabled(DebugChannel::Lia));
        assert!(cfg.enabled(DebugChannel::Dpll));
        assert!(!cfg.enabled(DebugChannel::Lra));
    }

    #[test]
    fn test_debug_config_theory_umbrella_expands() {
        let cfg = DebugConfig::from_channels(&[DebugChannel::Theory]);
        assert!(cfg.enabled(DebugChannel::Theory));
        // All theory channels should be enabled
        for &ch in DebugChannel::theory_channels() {
            assert!(cfg.enabled(ch), "Theory umbrella should enable {ch:?}");
        }
        // Non-theory channels should NOT be enabled
        assert!(!cfg.enabled(DebugChannel::Dpll));
        assert!(!cfg.enabled(DebugChannel::SatCongruence));
        assert!(!cfg.enabled(DebugChannel::Prop));
    }

    #[test]
    fn test_debug_config_theory_umbrella_plus_extra() {
        let cfg = DebugConfig::from_channels(&[DebugChannel::Theory, DebugChannel::Dpll]);
        assert!(cfg.enabled(DebugChannel::Lia));
        assert!(cfg.enabled(DebugChannel::Dpll));
    }

    #[test]
    fn test_proof_format_variants() {
        // Ensure all variants are distinct
        let formats = [
            ProofFormat::Drat,
            ProofFormat::Lrat,
            ProofFormat::Lean4,
            ProofFormat::Alethe,
        ];
        for (i, a) in formats.iter().enumerate() {
            for (j, b) in formats.iter().enumerate() {
                if i == j {
                    assert_eq!(a, b);
                } else {
                    assert_ne!(a, b);
                }
            }
        }
    }

    #[test]
    fn test_sat_disable_flags_default_all_false() {
        let flags = SatDisableFlags::default();
        assert!(!flags.no_bve);
        assert!(!flags.no_probe);
        assert!(!flags.no_congruence);
        assert!(!flags.no_decompose);
        assert!(!flags.no_sweep);
        assert!(!flags.no_subsume);
        assert!(!flags.no_vivify);
        assert!(!flags.no_factor);
        assert!(!flags.no_bce);
        assert!(!flags.no_transred);
        assert!(!flags.no_preprocess);
        assert!(!flags.no_inprocess);
        assert!(!flags.no_cold_restart);
        assert!(!flags.no_external_codegen_backend);
    }

    #[test]
    fn test_sat_debug_env_flags_default_all_off() {
        let flags = SatDebugEnvFlags::default();
        assert!(!flags.trace_ext_conflict);
        assert!(flags.bve_limit.is_none());
        assert!(!flags.bve_trace);
        assert!(flags.bve_max_rounds.is_none());
        assert!(!flags.log_enabled);
        assert!(!flags.dump_conflicts);
        assert!(!flags.clause_provenance);
        assert!(flags.debug_transred_clause.is_none());
    }

    #[test]
    fn test_trace_config_default_all_none() {
        let config = TraceConfig::default();
        assert!(config.diagnostic_path.is_none());
        assert!(config.decision_trace_path.is_none());
        assert!(config.replay_trace_path.is_none());
        assert!(config.trace_file_path.is_none());
        assert!(config.solution_file_path.is_none());
        assert!(config.decision_log_path.is_none());
        assert!(config.dump_bv_cnf_path.is_none());
        assert!(config.kind_dump_dir.is_none());
        assert!(config.dump_encoding_path.is_none());
    }

    #[test]
    fn test_chc_debug_env_flags_default_all_off() {
        let flags = ChcDebugEnvFlags::default();
        assert!(!flags.iuc_trace);
        assert!(!flags.iuc_require_farkas);
    }

    #[test]
    #[serial(trace_file_claim)]
    fn test_claim_trace_file_sets_claimed() {
        // Reset state (tests share the process-global atomic)
        release_trace_file();

        // Before claiming, the atomic should be false
        assert!(
            !TRACE_FILE_CLAIMED.load(Ordering::Acquire),
            "TRACE_FILE_CLAIMED should be false before claim"
        );

        claim_trace_file();

        assert!(
            TRACE_FILE_CLAIMED.load(Ordering::Acquire),
            "TRACE_FILE_CLAIMED should be true after claim"
        );

        // Clean up for other tests
        release_trace_file();
    }

    #[test]
    #[serial(trace_file_claim)]
    fn test_release_trace_file_clears_claim() {
        claim_trace_file();
        assert!(TRACE_FILE_CLAIMED.load(Ordering::Acquire));

        release_trace_file();
        assert!(
            !TRACE_FILE_CLAIMED.load(Ordering::Acquire),
            "TRACE_FILE_CLAIMED should be false after release"
        );
    }

    #[test]
    #[serial(trace_file_claim)]
    fn test_claim_trace_file_idempotent() {
        release_trace_file();

        claim_trace_file();
        claim_trace_file(); // double claim should not panic or change state
        assert!(TRACE_FILE_CLAIMED.load(Ordering::Acquire));

        release_trace_file();
    }

    #[test]
    #[serial(trace_file_claim)]
    fn test_trace_file_available_false_when_no_env_var() {
        // In test environment, AY_TRACE_FILE is typically not set,
        // so trace_file_available() should return false regardless of claim state.
        release_trace_file();
        assert!(
            !trace_file_available(),
            "trace_file_available should be false when AY_TRACE_FILE is not set"
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
