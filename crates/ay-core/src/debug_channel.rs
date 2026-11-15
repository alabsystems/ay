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
#[doc(hidden)]
pub use sat_ab_switches::consumer_test_override as sat_ab_test_override;
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
        let theory_umbrella = false; // Umbrella env retired; per-channel flags remain.
                                     // Check each channel's env var
        for &candidate in ALL_DEBUG_CHANNELS {
            let env_name = debug_channel_env_name(candidate);
            if std::env::var_os(&env_name).is_some()
                || (theory_umbrella && DebugChannel::theory_channels().contains(&candidate))
            {
                channels.push(candidate);
            }
        }
        // The pre-`AY_DEBUG_*` legacy alias for `EufFallback` is retired
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

/// The EXTERNAL proof checker the caller declares will verify the emitted
/// certificate.
///
/// This is a CAPABILITY axis that is *paired with* the emitted format rather
/// than implied by it. Of the DRAT-family checkers only `dsr-trim` accepts the
/// DSR substitution-witnessed `a`-lines that AY's SR symmetry routes emit
/// (measured 2026-08-24: php_11_8's orbitope staircase proof is
/// `s VERIFIED UNSAT` under dsr-trim and `s NOT VERIFIED` under both
/// drat-trim and dpr-trim). VeriPB accepts the same witnesses, but only on its
/// own pseudo-Boolean surface. SAT-COMP registrants declare their checker, and
/// a rejected UNSAT proof under the declared checker is disqualifying, so proof
/// routes gate on BOTH [`DeclaredProofChecker::accepts_sr_witnesses`] and
/// [`DeclaredProofChecker::reads_veripb`] (matched against the live proof
/// surface) and fall back to plain-CDCL-checkable emission when the declared
/// checker cannot consume their steps.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "cli", derive(clap::ValueEnum))]
#[cfg_attr(feature = "cli", clap(rename_all = "kebab-case"))]
pub enum DeclaredProofChecker {
    /// `dsr-trim` (the verified SR chain dsr-trim → drat/lsr → cake_lpr).
    /// The DEFAULT for plain local use — SR-witnessed routes stay enabled,
    /// which is exactly the behaviour before this axis existed.
    #[default]
    DsrTrim,
    /// `dpr-trim` — on the SAT-COMP 2026 checker menu; PR witnesses only,
    /// measured to REJECT DSR substitution witnesses.
    DprTrim,
    /// `drat-trim` — RUP/RAT only; measured to reject every witnessed
    /// `a`-line. NOT on the SAT-COMP 2026 checker menu.
    DratTrim,
    /// `gratgen`/`gratchk` — RUP/RAT only; on the 2026 menu.
    Gratgen,
    /// VeriPB — on the 2026 menu, and its `red` (redundance-based
    /// strengthening) rule takes a substitution witness natively, so the SR
    /// symmetry routes ARE representable under this declaration. They must be
    /// written on the pseudo-Boolean surface (`--proof-format veripb`), not as
    /// DSR `a`-lines: VeriPB does not consume DRAT files at all. See
    /// [`Self::reads_veripb`] for the surface half of that gate.
    Veripb,
}

impl DeclaredProofChecker {
    /// Whether the declared checker accepts a substitution witness on a
    /// redundancy step at all — on whichever proof surface that checker reads.
    ///
    /// Fail-closed: `drat-trim`, `dpr-trim` and `gratgen` are RUP/RAT (or
    /// PR-at-most) checkers and are measured to reject them. `dsr-trim` accepts
    /// them as DSR `a`-lines in a DRAT stream; VeriPB accepts them as the
    /// witness argument of `red` in a pseudo-Boolean derivation (measured
    /// 2026-08-24: php_sudoku_p15_h14's 91-step orbitope staircase is
    /// `s VERIFIED UNSATISFIABLE` under the checker `ci/veripb.pin` names —
    /// upstream 4bb10c2c plus the AY soundness patch, NOT stock 3.0.2, which
    /// still accepts five of the nine `ci/veripb-soundness/` fixtures).
    ///
    /// This is only half the question — see [`Self::reads_veripb`] for the
    /// other half, which is whether the emitted FORMAT is the one this checker
    /// can read.
    #[must_use]
    pub const fn accepts_sr_witnesses(self) -> bool {
        matches!(self, Self::DsrTrim | Self::Veripb)
    }

    /// Whether this checker reads the pseudo-Boolean (`.pbp`) surface rather
    /// than a DRAT-family clause stream.
    ///
    /// The two surfaces are not interchangeable in either direction, so an
    /// SR-witnessed step is only checkable when this matches the format being
    /// emitted. `--proof-format drat --proof-checker veripb` and
    /// `--proof-format veripb --proof-checker dsr-trim` are both declarations
    /// under which the witnessed routes must clamp.
    #[must_use]
    pub const fn reads_veripb(self) -> bool {
        matches!(self, Self::Veripb)
    }

    /// Canonical kebab-case checker name for diagnostics.
    #[must_use]
    pub const fn name(self) -> &'static str {
        match self {
            Self::DsrTrim => "dsr-trim",
            Self::DprTrim => "dpr-trim",
            Self::DratTrim => "drat-trim",
            Self::Gratgen => "gratgen",
            Self::Veripb => "veripb",
        }
    }
}

/// Global declared proof checker, installed once by the CLI
/// (`--proof-checker`; the submission run.sh always passes it).
static GLOBAL_DECLARED_PROOF_CHECKER: OnceLock<DeclaredProofChecker> = OnceLock::new();

/// Install the declared proof checker (first caller wins).
///
/// # Errors
///
/// The rejected value when a checker was already installed.
pub fn set_global_declared_proof_checker(
    checker: DeclaredProofChecker,
) -> Result<(), DeclaredProofChecker> {
    GLOBAL_DECLARED_PROOF_CHECKER.set(checker)
}

/// The installed declared proof checker, or the dsr-trim default (SR-witnessed
/// routes allowed — identical to the pre-axis behaviour for library consumers
/// and plain local runs).
#[must_use]
pub fn declared_proof_checker() -> DeclaredProofChecker {
    GLOBAL_DECLARED_PROOF_CHECKER
        .get()
        .copied()
        .unwrap_or_default()
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
/// `--uflia-arith-decisions`; both forwarding sites gate on this one
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
        trace_ext_conflict: false,
        bve_limit: None,
        bve_trace: false,
        bve_max_rounds: None,
        log_enabled: false,
        dump_conflicts: false,
        clause_provenance: false,
        debug_transred_clause: None,
    }
}

/// Returns a reference to the global SAT debug env flags.
///
/// Without a prior `set_global_sat_debug_env_flags`, the first call installs the defaults.
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
    /// Adaptive-portfolio decision log path (CLI-carried; env retired)
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
    let diagnostic_path = None;
    TraceConfig {
        diagnostic_path,
        decision_trace_path: None,
        replay_trace_path: None,
        trace_file_path: None,
        solution_file_path: None,
        decision_log_path: None,
        dump_bv_cnf_path: None,
        // DRAT-for-BV is a CLI-only coupling to `--dump-bv-cnf`; no env alias.
        bv_drat_path: None,
        bv_drat_binary: false,
        // Self-cert temp paths are CLI-only (`--self-check`); never env-driven.
        bv_drat_self_cert_cnf_path: None,
        bv_drat_self_cert_drat_path: None,
        kind_dump_dir: None,
        dump_encoding_path: None,
    }
}

/// Returns a reference to the global trace config.
///
/// Without a prior `set_global_trace_config`, the first call installs the defaults.
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
    /// Hard diagnostic for zero-Farkas fallbacks (env spelling retired)
    pub iuc_require_farkas: bool,
}

/// Global CHC debug env flags, initialized once per process.
static GLOBAL_CHC_DEBUG_ENV_FLAGS: OnceLock<ChcDebugEnvFlags> = OnceLock::new();

/// Initialize CHC debug env flags from environment variables.
fn init_chc_debug_env_from_env() -> ChcDebugEnvFlags {
    ChcDebugEnvFlags {
        iuc_trace: false,
        iuc_require_farkas: false,
    }
}

/// Returns a reference to the global CHC debug env flags.
///
/// Without a prior `set_global_chc_debug_env_flags`, the first call installs the defaults.
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
    /// `--maxsat-no-tot-eqs` — drop totalizer output equalities (A/B).
    pub maxsat_no_tot_eqs: bool,
    /// `--maxsat-no-bce-revert` — keep the preprocessed engine after a
    /// mostly-risky BCE reduction (A/B).
    pub maxsat_no_bce_revert: bool,
    /// `--maxsat-no-am1-maxcover` — restore the shared-only AM1 cover.
    pub maxsat_no_am1_maxcover: bool,
    /// `--maxsat-bce` — arm the opt-in one-shot BCE preprocessing lane
    /// (stays default OFF like the retired env spelling).
    pub maxsat_bce: bool,
    /// `--maxsat-no-bmo` — disable BMO stratified descent.
    pub maxsat_no_bmo: bool,
    /// `--maxsat-no-cold-descent` — disable the cold-descent gate.
    pub maxsat_no_cold_descent: bool,
    /// `--maxsat-no-descent-residual` — disable residual-descent reuse.
    pub maxsat_no_descent_residual: bool,
    /// `--maxsat-no-dpw` — never select the DPW encoding.
    pub maxsat_no_dpw: bool,
    /// `--maxsat-no-early-descent` — disable the early stratified descent
    /// slice.
    pub maxsat_no_early_descent: bool,
    /// `--maxsat-no-preproc` — disable one-shot maxsat preprocessing.
    pub maxsat_no_preproc: bool,
    /// `--maxsat-no-milp-race` — disable the MILP race lane (the race
    /// is correct-by-default, opting out is for contention-free benching).
    pub maxsat_no_milp_race: bool,
    /// `--no-inc-linear-parse` — restore parse-every-line incremental input
    /// handling.
    pub no_inc_linear_parse: bool,
    /// `--no-milp-fastpath` — disable the QF_LRA MILP fastpath route.
    pub no_milp_fastpath: bool,
    /// `--sat-relevancy <0|1|2>` — force the relevancy brancher off/on
    /// (`2` also turns on the engage marker); unset lets the caller decide
    /// (was --sat-relevancy).
    pub sat_relevancy: Option<u8>,
    /// `--fc-global-budget <N>` — explicit FC global pair budget; unset arms
    /// the many-array autoscale.
    pub fc_global_budget: Option<usize>,
    /// `--maxsat-debug` — MILP-race gate diagnostics.
    pub maxsat_debug: bool,
    /// `--proof-self-check <1|2>` — proof self-check mode, warn | strict
    /// (`None` = off).
    pub proof_self_check: Option<u8>,
    /// `--chc-checked-replay <secs>` — opt-in CHECKED replay budget.
    pub chc_checked_replay_secs: Option<u64>,
    /// `--xor-allow-large` — lift the XOR-extension clause cap.
    pub xor_allow_large: bool,
    /// `--xor-allow-residual` — allow residual-dominated XOR routing.
    pub xor_allow_residual: bool,
    /// `--xor-allow-unadmitted` — take the XOR theory route even when almost
    /// none of the detected rows got a Gaussian matrix (#xor-route-entry
    /// kill switch; restores the pre-fix behaviour byte-for-byte).
    pub xor_allow_unadmitted: bool,
    /// `--phase-trace` — dpll phase trace lines (diagnostic).
    pub phase_trace: bool,
    /// `--debug-cert` — certificate-path diagnostics.
    pub debug_cert: bool,
    /// `--debug-qmg` — quantified-model-gate diagnostics.
    pub debug_qmg: bool,
    /// `--model-reject-dump` — dump rejected models.
    pub model_reject_dump: bool,
    /// `--debug-strict-oracle` — strict-oracle diagnostics.
    pub debug_strict_oracle: bool,
    /// `--g3-gate-dump` — G3 gate dump.
    pub g3_gate_dump: bool,
    /// `--quiet-soundness-gate` — suppress soundness-gate chatter.
    pub quiet_soundness_gate: bool,
    /// `--rup-fallback-trace` — RUP fallback trace.
    pub rup_fallback_trace: bool,
    /// `--lra-inc-engine-stats` — inc-engine persistence stats.
    pub lra_inc_engine_stats: bool,
    /// `--lra-inc-engine-reverify` — from-scratch disagreement
    /// backstop.
    pub lra_inc_engine_reverify: bool,
    /// `--debug-no-terms i,j` — suppress listed term ids in combiner-check
    /// dumps.
    pub debug_no_terms: Option<String>,
    /// `--proof-introspect <path>` — append proof introspection to a
    /// file.
    pub proof_introspect: Option<String>,
    /// `--proof-introspect-probe <path>` — probe-derivation dump.
    pub proof_introspect_probe: Option<String>,
    /// `--probe-sat-variable <n>` — observe one zero-based SAT variable's
    /// existing BV provenance under `--probe-cert-reject`; never registers it.
    pub probe_sat_variable: Option<u32>,
    /// `--str-w4-work <n>` — W4 work cap (`0` = unbounded).
    pub str_w4_work: Option<u64>,
    /// `--fmq-lane-budget-ms <n>` — override the finite-model MBQI lane's
    /// per-invocation wall cap (A/B; `None` = the shipped sizing).
    pub fmq_lane_budget_ms: Option<u64>,
    /// `--fmq-probe-ms <n>` — override the finite-model MBQI lane's
    /// per-sub-solve ceiling (A/B; `None` = the shipped constant).
    pub fmq_probe_ms: Option<u64>,
    /// `--fmq-seed-ms <n>` — override the finite-model MBQI lane's session
    /// decline seed (A/B; `None` = the shipped constant).
    pub fmq_seed_ms: Option<u64>,
    /// `--sat-ab-subst-stats` — congruence/substitution stats dumps.
    pub ab_subst_stats: bool,
    /// `--sat-ab-subst-dump-merges` — merge/unit provenance dump.
    pub ab_subst_dump_merges: bool,
    /// `--sat-ab-subst-dump-gates` — gate-extraction dump.
    pub ab_subst_dump_gates: bool,
    /// `--sat-ab-subst-dump-edges` — congruence edge dump.
    pub ab_subst_dump_edges: bool,
    /// `--sat-ab-dump-db` — dump the live clause DB at congruence
    /// entry.
    pub ab_dump_db: bool,
    /// `--sat-factor-probe` — factor candidate-schedule report.
    pub factor_probe: bool,
    /// `--sat-probe-trace-dup` — duplicate-push probe in the clause
    /// trace.
    pub probe_trace_dup: bool,
    /// `--sat-l0-unsat-trace` — level-0 core-failsafe trace.
    pub sat_l0_unsat_trace: bool,
    /// `--sat-symmetry-trace` — symmetry pipeline trace.
    pub sat_symmetry_trace: bool,
    /// `--sat-mem-probe` — per-engine construction footprint report, and the
    /// solver's memory by structure after parsing and after preprocessing.
    pub sat_mem_probe: bool,
    /// `--sat-bve-trace <LEVEL>` — BVE decision trace to stderr: 1 one line
    /// per resolved candidate, 2 also the clauses of every refusal.
    pub sat_bve_trace: u8,
    /// `--sat-ab-triage-clause d1,d2,...` — soundness-triage target clause
    /// in DIMACS lits.
    pub ab_triage_clause: Option<String>,
    /// `--sat-ab-triage-var <dimacs var>` — report every assignment of the
    /// variable.
    pub ab_triage_var: Option<u64>,
    /// `--sat-ab-triage-probe d1,d2,...` — RUP-probe triage target.
    pub ab_triage_probe: Option<String>,
    /// `--chc-accept-profile` — clause-inlining accept profile.
    pub chc_accept_profile: bool,
    /// `--chc-cata-trace` — catamorphism abstraction trace.
    pub chc_cata_trace: bool,
    /// `--chc-houdini-debug` — Houdini lane diagnostics.
    pub chc_houdini_debug: bool,
    /// `--chc-imc-stats` — IMC lane statistics.
    pub chc_imc_stats: bool,
    /// `--chc-proof-itp-stats` — proof-backed interpolation stats.
    pub chc_proof_itp_stats: bool,
    /// `--chc-ice-dt-trace` — ICE datatype learner trace.
    pub chc_ice_dt_trace: bool,
    /// `--chc-dt-bmc-trace` — datatype-BMC trace.
    pub chc_dt_bmc_trace: bool,
    /// `--chc-v2-debug` — BV dual-lane v2 diagnostics.
    pub chc_v2_debug: bool,
    /// `--chc-ground-bt-debug` — ground backtranslation diagnostics.
    pub chc_ground_bt_debug: bool,
    /// `--chc-bmc-nested-debug` — nested-BMC diagnostics.
    pub chc_bmc_nested_debug: bool,
    /// `--chc-debug-marker-dag-verify` — marker-DAG verbose
    /// verification.
    pub chc_debug_marker_dag_verify: bool,
    /// `--chc-array-frontier-telemetry` — array-content frontier
    /// telemetry.
    pub chc_array_frontier_telemetry: bool,
    /// `--chc-cata-dump-abstract <dir>` — dump abstract LIA problems.
    pub chc_cata_dump_abstract: Option<String>,
    /// `--chc-cata-dump-obligations <dir>` — dump undischarged
    /// obligations.
    pub chc_cata_dump_obligations: Option<String>,
    /// `--chc-dump-scalarized <dir>` — dump scalarized problems.
    pub chc_dump_scalarized: Option<String>,
    /// `--chc-dump-failed-replay-obligation <dir>` — write failing replay
    /// obligations as runnable scripts.
    pub chc_dump_failed_replay_obligation: Option<String>,
    /// `--chc-checksat-dump <dir>` — capture timeout-class check
    /// scripts.
    pub chc_checksat_dump: Option<String>,
    /// `--chc-pdr-dump <dir>` — dump PDR executor queries.
    pub chc_pdr_dump: Option<String>,
    /// `--chc-proof-itp-dump <dir>` — dump proof-solve scripts.
    pub chc_proof_itp_dump: Option<String>,
    /// `--chc-checksat-trace <level>` — check-sat trace verbosity.
    pub chc_checksat_trace: Option<u8>,
    /// `--euf-gap-stats` — EUF propagation-gap profiling.
    pub euf_gap_stats: bool,
    /// `--lia-instrument` — LIA instrumentation reporter.
    pub lia_instrument: bool,
    /// `--probe-stats-every <n>` — LIA probe-stats report interval
    /// (default 1000).
    pub probe_stats_every: Option<u64>,
    /// `--str-nf-closures i,j,...` — explicit string NF closure
    /// subset.
    pub str_nf_closures: Option<String>,
    /// `--trace-cegqi-attr` — CEGQI attribution trace.
    pub trace_cegqi_attr: bool,
    /// `--debug-read-pin` — read-pin diagnostics.
    pub debug_read_pin: bool,
    /// `--f1-diag` — F1 combiner diagnostics.
    pub f1_diag: bool,
    /// `--census-trace` — DT model census trace.
    pub census_trace: bool,
    /// `--debug-pigeonhole` — pigeonhole-core diagnostics.
    pub debug_pigeonhole: bool,
    /// `--cert-debug` — PB certificate diagnostics.
    pub cert_debug: bool,
    /// `--count-debug` — model-counting diagnostics.
    pub count_debug: bool,
    /// `--tseitin-trace` — Tseitin derivation trace.
    pub tseitin_trace: bool,
    /// `--debug-subst` — LIA substitution diagnostics.
    pub debug_subst: bool,
    /// `--debug-split-exit` — pipeline split-exit diagnostics.
    pub debug_split_exit: bool,
    /// `--debug-class-merge` — combiner class-merge diagnostics.
    pub debug_class_merge: bool,
    /// `--milp-fastpath-debug` — MILP fastpath diagnostics.
    pub milp_fastpath_debug: bool,
    /// `--demand-debug` — quantifier demand diagnostics.
    pub demand_debug: bool,
    /// `--prop-debug` — extension propagation diagnostics.
    pub prop_debug: bool,
    /// `--quant-stats` — quantifier statistics.
    pub quant_stats: bool,
    /// `--debug-fixup` — combined-theory fixup diagnostics.
    pub debug_fixup: bool,
    /// `--debug-cegar` — CEGAR escalation diagnostics.
    pub debug_cegar: bool,
    /// `--str-prepass-stats` — string prepass statistics.
    pub str_prepass_stats: bool,
    /// `--milp-lane-trace` — PB portfolio MILP-lane trace.
    pub milp_lane_trace: bool,
    /// `--verify-mixed-strings-stats`.
    pub verify_mixed_strings_stats: bool,
    /// `--a5-uf-eq-defer` — A5 UF equality deferral arm.
    pub a5_uf_eq_defer: bool,
    /// `--spike-dump` — interpolation-spike dump.
    pub spike_dump: bool,
    /// `--spike-verbose` — interpolation-spike verbosity.
    pub spike_verbose: bool,
    /// `--qfax-combiner-route` — QF_AX combiner route arm.
    pub qfax_combiner_route: bool,
    /// `--qfax-cegar` — QF_AX CEGAR arm.
    pub qfax_cegar: bool,
    /// `--qfax-lanes-debug` — QF_AX lane diagnostics.
    pub qfax_lanes_debug: bool,
    /// `--probe-strict-check` — strict-check progress probe.
    pub probe_strict_check: bool,
    /// `--probe-cert-reject` — certificate-reject probe.
    pub probe_cert_reject: bool,
    /// `--uflia-witness-debug`.
    pub uflia_witness_debug: bool,
    /// `--pb-sym-debug` — PB symmetry diagnostics.
    pub pb_sym_debug: bool,
    /// `--pb-farkas-cert` — PB Farkas certificate arm.
    pub pb_farkas_cert: bool,
    /// `--qfax-neg-eq-witness` — QF_AX negative-equality witness arm.
    pub qfax_neg_eq_witness: bool,
    /// `--qfax-neg-chain-gate` — QF_AX negative-chain gate arm.
    pub qfax_neg_chain_gate: bool,
    /// `--vsids-decay <f>` — VSIDS decay override in (0, 1).
    pub vsids_decay: Option<f64>,
    /// `--inprobe-mult <f>` — inprocessing probe interval multiplier.
    pub inprobe_mult: Option<f64>,
    /// `--factor-elim-bound <n>` — factor elimination bound force.
    pub factor_elim_bound: Option<i64>,
    /// `--pb-sls-endgame-threshold <n>` — SLS endgame threshold.
    pub pb_sls_endgame_threshold: Option<usize>,
    /// `--dump-query-dir <dir>` — dump embedded-consumer queries.
    pub dump_query_dir: Option<String>,
    /// `--keep-alethe-artifacts` — keep carcara harness artifacts.
    pub keep_alethe_artifacts: bool,
    /// `--no-quant-unit-authority` — disable P3a derivation authority.
    pub no_quant_unit_authority: bool,
    /// `--no-consequence-replay` — disable authored consequence replay.
    pub no_consequence_replay: bool,
    /// `--no-quantified-shedding-yield` — restore proof shedding on QUANTIFIED
    /// public queries (#quantified-shedding-yield). Default off, i.e. shedding
    /// yields. Setting this reinstates the measured non-monotone rigor ladder
    /// where `--rigor fast` publishes strictly fewer answers than `--rigor
    /// standard` on quantified problems; it exists only so the barrier can be
    /// mutation-tested.
    pub no_quantified_shedding_yield: bool,
    /// `--no-negated-exists-ground-inst` — disable the negated-existential
    /// ground-instantiation artifact-firewall translation
    /// (#inc-fparith-negated-exists-inst). UNSAT-only; disabling restores the
    /// baseline fail-closed `unknown` byte-for-byte.
    pub no_negated_exists_ground_inst: bool,
    /// `--no-qlra-cegqi` — disable the nested-CEGQI quantified-LRA lane
    /// (#qlra-nested-cegqi). The lane is a probe, never a pre-empt; disabling
    /// it restores the legacy quantifier path byte-for-byte.
    pub no_qlra_cegqi: bool,
    /// `--no-eq-qe-lane` — disable the SAT-only equality-QE lane (#eq-qe-lane).
    pub no_eq_qe_lane: bool,
    /// `--no-qsat` — disable the QSAT route (roadmap component QS) for
    /// quantified linear arithmetic; the nested-CEGQI lane and the deep-QE
    /// `Unknown` retry it replaces run again.
    pub no_qsat: bool,
    /// `--no-qlra-nested` — disable the nested-CEGQI search (Fig. 8
    /// recursion, #qlra-nested-cegqi) for quantified-LRA problems the depth-1
    /// lane declines. The search is ON by default: its `unsat` publishes only
    /// through the M3a expansion certificate (strict installation boundary)
    /// and its `sat` only through the quantified model gate (M3b
    /// confirm-only expansion route); disabling it restores the depth-1-only
    /// lane.
    pub no_qlra_nested: bool,
    /// `--no-authored-skeleton-refutation` — disable the authored
    /// BOOLEAN-SKELETON refutation artifact-firewall translation
    /// (#authored-skeleton-refutation). UNSAT-only; disabling restores the
    /// baseline fail-closed `unknown` byte-for-byte.
    pub no_authored_skeleton_refutation: bool,
    /// `--no-authored-fold-identity` — disable the authored fold-identity
    /// refutation (#authored-fold-identity): the derivation recorded for a
    /// preprocessor fold-to-`false` whose argument is a normalization
    /// identity between two operands of an authored disequality, or a
    /// conjunct and its negation. UNSAT-only; disabling restores the
    /// bare-hole erasure byte-for-byte.
    pub no_authored_fold_identity: bool,
    /// `--no-probe-ite-lift-promoter` — disable the consequence-replay
    /// LIFTED-ASSERTION trust-leaf promoter (#probe-ite-lift-promoter).
    /// UNSAT-only; disabling restores the baseline byte-for-byte: a probe
    /// whose only residual trust leaf is the arithmetic-ITE lift of one of
    /// its own assertions declines its strict check exactly as before.
    pub no_probe_ite_lift_promoter: bool,
    /// `--no-alpha-quantifier-sharing` — disable ALPHA-EQUIVALENCE sharing of
    /// authored quantifiers (#alpha-quantifier-sharing). With it set, every
    /// quantifier occurrence keeps the globally unique binder names the
    /// elaborator mints for it, so two syntactically identical authored
    /// assertions elaborate to different terms exactly as before.
    pub no_alpha_quantifier_sharing: bool,
    /// `--no-quantifier-proxy-abstraction` — disable the quantifier proxy
    /// abstraction (#quantifier-proxy-abstraction). With it set,
    /// `flatten_and_strip_quantifiers` DELETES every assertion that mentions a
    /// quantifier, exactly as before the stage landed, so the ground solver
    /// loses the ground disjuncts of a disjunct-position `forall` goal.
    /// Disabling restores the baseline assertion vector byte-for-byte.
    pub no_quantifier_proxy_abstraction: bool,
    /// `--no-skolem-guarded-proxy-instances` — disable the Skolem-witness
    /// guarded instantiation of proxied quantifiers
    /// (#skolem-guarded-proxy-instances). UNSAT-only: with it set no guarded
    /// clause is built and the abstracted assertion vector is byte-for-byte
    /// what `purify_quantifier_atoms` left behind.
    pub no_skolem_guarded_proxy_instances: bool,
    /// `--no-quantifier-guarded-instances` — disable GUARDED instance clauses
    /// from the E-matcher (#quantifier-guarded-instances). With it set, the
    /// matcher takes the same `continue` it took before the stage landed for
    /// every `forall` the assertion set does not entail, so no
    /// `(or (not qproxy) body[t])` clause is ever built. Disabling restores the
    /// baseline assertion vector byte-for-byte.
    pub no_quantifier_guarded_instances: bool,
    /// `--quantifier-guarded-enumerative` — force guarded instance clauses
    /// from the triggerless ENUMERATIVE lane on for EVERY solve
    /// (#quantifier-guarded-enumerative), overriding the structural trigger.
    ///
    /// The lane's default is neither "on" nor "off": it fires when the
    /// E-matcher produced no instance in the solve, which is the measured
    /// separator between the family it helps and the family it hurts (see
    /// `quant_unit_authority::quantifier_guarded_enumerative_enabled`). This
    /// flag removes that condition, which is the arm the corpus-wide
    /// always-on measurement used and the way to reproduce it.
    pub quantifier_guarded_enumerative: bool,
    /// `--no-quantifier-guarded-enumerative` — kill switch for the same lane.
    /// With it set no enumerative guarded clause is built whatever the
    /// structure says, restoring the pre-gate assertion vector byte-for-byte.
    /// It also outranks `--quantifier-guarded-enumerative`.
    pub no_quantifier_guarded_enumerative: bool,
    /// `--no-quantifier-ce-free-resolve` — kill switch for the counterexample-free
    /// consequence re-solve (#quantifier-ce-free-resolve): stage 4
    /// of the quantifier-instantiation plan. With it set, a CEGQI-forall
    /// refutation the disambiguation apparatus cannot attribute fails closed
    /// exactly as before the stage landed: no guard literal is minted, no
    /// re-solve runs, and the published `unknown` is byte-identical.
    pub no_quantifier_ce_free_resolve: bool,
    /// `--no-quantifier-guard-seeds` — kill switch for the guard-bound seed
    /// instances of entailed single-binder `Real` universals
    /// (#nra-guard-seed-instances). With it set no seed instance is asserted
    /// and the quantifier pipeline's assertion vector is byte-identical to the
    /// pre-pass one. For A/B measurement.
    pub no_quantifier_guard_seeds: bool,
    /// `--no-ground-first` — kill switch for ground-first scheduling of
    /// quantified check-sat (#qe-ground-first): the query without its
    /// top-level universal axioms is no longer decided before the quantifier
    /// pipeline, which then runs exactly as it did before the pass landed.
    /// For A/B measurement and for guards pinning a lane the pass preempts.
    pub no_ground_first: bool,
    /// `--no-ground-conflict-decomp` — disable the ground-conflict
    /// decomposition arms of the proof builder (#ground-conflict-decomp):
    /// the EUF-chain + Farkas-bridge split, and the array read-over-write
    /// chain-under-equality split. UNSAT-only producer surgery; disabling
    /// restores the baseline Generic/trust lemmas byte-for-byte.
    pub no_ground_conflict_decomp: bool,
    /// `--no-fp-incremental` — persistent incremental FP lane kill switch.
    ///
    /// With it set, every `check-sat` runs the stateless FP pipeline that
    /// predates the lane: a fresh `Tseitin`, `FpSolver` and `SatSolver` per
    /// call. It exists for two reasons. It is the A/B control — the primary
    /// metric is check-sats per CPU-second measured INTERLEAVED, which two
    /// separate builds cannot give honestly — and it is the operational escape
    /// hatch for a change whose failure mode is a silent wrong answer.
    pub no_fp_incremental: bool,
    /// `--vacuous-marker-narrow` — staged marker narrowing.
    pub vacuous_marker_narrow: bool,
    /// `--proj-axiom-budget <n>` — projection axiom cap (default 50000).
    pub proj_axiom_budget: Option<usize>,
    /// `--uflia-witness-complete`.
    pub uflia_witness_complete: bool,
    /// `--uflia-witness-parts fill|chain`.
    pub uflia_witness_parts: Option<String>,
    /// `--uflia-fused-detour`.
    pub uflia_fused_detour: bool,
    /// `--verify-memo`.
    pub verify_memo: bool,
    /// `--pb-eqagg-debug`.
    pub pb_eqagg_debug: bool,
    /// `--pb-bnb` — PB branch-and-bound upgrade arm.
    pub pb_bnb: bool,
    /// `--no-pb-sls-feasfirst` — disable SLS feasibility-first.
    pub no_pb_sls_feasfirst: bool,
    /// `--pb-strict-optimum`.
    pub pb_strict_optimum: bool,
    /// `--pb-sls-unified` — re-enable the unified SLS loop.
    pub pb_sls_unified: bool,
    /// `--pb-proof-tap-soft-cap-mib <n>`.
    pub pb_proof_tap_soft_cap_mib: Option<u64>,
    /// `--sls-planted` / `--sls-sweep` — SLS bench harness gates.
    pub sls_planted: bool,
    /// See `sls_planted`.
    pub sls_sweep: bool,
    /// `--oll-file <path>` — OLL reference-harness instance.
    pub oll_file: Option<String>,
    /// `--oll-expect <n>` — OLL reference-harness expectation.
    pub oll_expect: Option<String>,
    /// `--pb-debug-panic-on-incumbent` — fault-injection assert arm.
    pub pb_debug_panic_on_incumbent: bool,
    /// `--sat-prune-conflict-experiments <bool>` — tri-state force.
    pub sat_prune_conflict_experiments: Option<bool>,
    /// `--debug-lazy-sync`.
    pub debug_lazy_sync: bool,
    /// `--debug-fc-sync`.
    pub debug_fc_sync: bool,
    /// `--lra-warm-stats`.
    pub lra_warm_stats: bool,
    /// `--fuzz-verbose`.
    pub fuzz_verbose: bool,
    /// `--certora-trace`.
    pub certora_trace: bool,
    /// `--debug-abv-finite-array`.
    pub debug_abv_finite_array: bool,
    /// `--debug-abv-packed-lookup`.
    pub debug_abv_packed_lookup: bool,
    /// `--debug-ladder`.
    pub debug_ladder: bool,
    /// `--debug-wgr`.
    pub debug_wgr: bool,
    /// `--debug-completion-merge`.
    pub debug_completion_merge: bool,
    /// `--debug-arith-oracle`.
    pub debug_arith_oracle: bool,
    /// `--debug-unwitnessed`.
    pub debug_unwitnessed: bool,
    /// `--cut-trace` — PB cutting-planes trace.
    pub cut_trace: bool,
    /// `--dump-render` — BV blast-lean render dump.
    pub dump_render: bool,
    /// `--chc-array-tree-refutation` (opt-in arm).
    pub chc_array_tree_refutation: bool,
    /// `--chc-dont-care-filter`.
    pub chc_dont_care_filter: bool,
    /// `--chc-intern`.
    pub chc_intern: bool,
    /// `--chc-session <0|1|2>` — the `HornSmt` persistent session for the CHC
    /// engines' Search-lane queries (CHC-COMP 2026 Rung 1). 0 = off (default
    /// until Rung 4), 1 = session with legacy fall-through on
    /// unsupported/incomplete queries, 2 = session only.
    pub chc_session: Option<u8>,
    /// `--chc-session-strict <l2|full>` — `HornSmt` session harness posture.
    /// `full` panics on any non-Budget Unknown, any audit disagreement and
    /// any routing under verification mode; `l2` panics only on the lock-L2
    /// tripwire (`constructions_in_verification`). Unset = no panics.
    pub chc_session_strict: Option<String>,
    /// `--chc-session-audit <n>` — every N-th `HornSmt` session UNSAT is
    /// re-solved on a fresh `Verification`-lane context; a disagreement is
    /// counted and the query answers `Unknown`. Unset/0 = off.
    pub chc_session_audit: Option<u64>,
    /// `--chc-session-stats` — print the `HornSmt` session's process totals
    /// (`[CHC-SESSION] ...`) to stderr at the end of the CLI run.
    pub chc_session_stats: bool,
    /// `--chc-session-coverage` — emit the Rung-4 `[CHC-SESSION-COVERAGE]`
    /// census lines.
    pub chc_session_coverage: bool,
    /// `--chc-session-trace` — one `[CHC-SESSION-DEMOTION]` stderr line per
    /// query the router's strict evaluation demoted from the session's Sat.
    pub chc_session_trace: bool,
    /// `--chc-session-dump <dir>` — record every routed `HornSmt` session
    /// query as a self-contained SMT-LIB script plus an `index.tsv` (design
    /// §10.1).
    pub chc_session_dump: Option<String>,
    /// `--chc-session-dump-max <n>` — cap the number of script files
    /// `--chc-session-dump` writes (default 5000; index rows keep flowing
    /// past the cap).
    pub chc_session_dump_max: Option<u64>,
    /// `--chc-array-inv`.
    pub chc_array_inv: bool,
    /// `--chc-dt-recursive-prefix` (experimental scalar-prefix depth).
    pub chc_dt_recursive_prefix: bool,
    /// `--interface-diet on|shadow` (unset = off).
    pub interface_diet: Option<String>,
    /// `--bv-preprocess quick|full` (unset = no preprocessing).
    pub bv_preprocess: Option<String>,
    /// `--fc-cegar-iters <n>` (default 16).
    pub fc_cegar_iters: Option<u32>,
    /// `--int-pigeonhole-enrich-k <n>` (default unbounded).
    pub int_pigeonhole_enrich_k: Option<usize>,
    /// `--ext-row-seed`.
    pub ext_row_seed: bool,
    /// `--debug-row-seed`.
    pub debug_row_seed: bool,
    /// `--dpll-mint-theory-vars` (opt-in).
    pub dpll_mint_theory_vars: bool,
    /// `--dpll-ite-lift`.
    pub dpll_ite_lift: bool,
    /// `--euf-bool-arg-repair`.
    pub euf_bool_arg_repair: bool,
    /// `--lra-warm-theory`.
    pub lra_warm_theory: bool,
    /// `--force-array-euf`.
    pub force_array_euf: bool,
    /// `--ab-maxsat-core-clause` (A/B arm).
    pub ab_maxsat_core_clause: bool,
    /// `--ab-maxsat-descent-organic-slice`.
    pub ab_maxsat_descent_organic_slice: bool,
    /// `--ab-maxsat-kick-gap-abs`.
    pub ab_maxsat_kick_gap_abs: bool,
    /// `--ab-maxsat-descent-kick-scale`.
    pub ab_maxsat_descent_kick_scale: bool,
    /// `--uflia-arith-decisions`: forward UFLIA arith decision hints to
    /// the arith adapters (default off preserves the historical trajectory).
    pub uflia_arith_decisions: bool,
    /// `--no-skolem-witness-sat` — kill switch for the skolem-witness SAT
    /// confirmation arm in quantifier restore (#skolem-witness-sat).
    pub no_skolem_witness_sat: bool,
    /// `--no-singleton-carrier-mint` — kill switch for the empty-universe
    /// singleton carrier mint in the EPR singleton SAT chain
    /// (#eu-carrier-mint).
    pub no_singleton_carrier_mint: bool,
    /// `--lra-float-layer`: opt in to the LRA float pre-solve layer.
    pub lra_float_layer: bool,
    /// `--str-nf`: string-theory normal-form debug gate.
    pub str_nf: bool,
    /// `--debug-euf-init`: EUF e-graph construction tracing.
    pub debug_euf_init: bool,
    /// `--euf-cong-undo-debug`: EUF congruence-undo tracing.
    pub euf_cong_undo_debug: bool,
    /// `--euf-diseq-undo-debug`: EUF disequality-undo tracing.
    pub euf_diseq_undo_debug: bool,
    /// `--probe-prescreen`: arm the LIA probe batch prescreen.
    pub probe_prescreen: bool,
    /// `--lia-probe-qx`: probe minimization mode
    /// (`quickxplain` | `gallop`; default scan).
    pub lia_probe_qx: Option<String>,
    /// `--probe-stats`: LIA probe statistics to stderr.
    pub probe_stats: bool,
    /// `--debug-fixed-eqs`: LIA fixed-equality tracing.
    pub debug_fixed_eqs: bool,
    /// `--algebraic-stats`: Nelson-Oppen algebraic statistics.
    pub algebraic_stats: bool,
    /// `--debug-arr-extract`: array model extraction tracing.
    pub debug_arr_extract: bool,
    /// `--weq5-shadow-dump`: weak-equivalence shadow differential dump.
    pub weq5_shadow_dump: bool,
    /// `--ic3-lane-debug`: TRUST ic3-lane stderr tracing.
    pub ic3_lane_debug: bool,
    /// `--ic3-lane-dump`: append ic3-lane traffic to this path.
    pub ic3_lane_dump: Option<String>,
    /// `--ic3-lane-noslice`: disable the COI slice (A/B; slice is sound).
    pub ic3_lane_noslice: bool,
    /// `--reve-debug`: REVE invariant-sampling stderr tracing.
    pub reve_debug: bool,
    /// `--max-propagate-rounds`: extension spin guard override (default 50M).
    pub max_propagate_rounds: Option<u64>,
    /// `--lra-cond-trail`: experimental LRA conditional bound trail.
    pub lra_cond_trail: bool,
    /// `--lra-unit-pivot-pref` (#lra-unit-pivot-pref): experimental simplex
    /// entering-variable tie-break preferring ±1 coefficients. Changes pivot
    /// paths (models/certificates), never verdicts; default OFF until a
    /// corpus diff clears it.
    pub lra_unit_pivot_pref: bool,
    /// `--euf-inc-neg-pop`: opt-in; 2026-08-20 A/B was not a win.
    /// (+2/314 limit-edge runs; median unchanged; see the dated EUF A/B report.)
    pub euf_inc_neg_pop: bool,
    /// `--nra-diag`: NRA ICP diagnostics.
    pub nra_diag: bool,
    /// `--nra-grid-probe`: NRA ICP grid probe diagnostics.
    pub nra_grid_probe: bool,
    /// `--nra-witness <ASSIGNMENTS>`: inline rationals such as `x=1/2,y=-3`.
    pub nra_witness: Option<String>,
    /// `--quant-relevance <bool>`: e-matching relevance admission layer
    /// (measured 2026-08-19: real flood control, no verdict conversions yet —
    /// default OFF; see ematching/relevance.rs).
    pub quant_relevance: Option<bool>,
    /// `--quant-relevance-k <n>`: per-round admission budget.
    pub quant_relevance_k: Option<usize>,
    /// `--quant-relevance-min <n>`: flood threshold.
    pub quant_relevance_min: Option<usize>,
    /// `--quant-relevance-model <bool>`: model-signal ranking.
    pub quant_relevance_model: Option<bool>,
    /// `--quant-relevance-debug`: per-round admission trace.
    pub quant_relevance_debug: bool,
    /// The proof-cycle-shedding posture the CLI's own executor EFFECTIVELY
    /// runs with (T8, the development design notes): `--competition` /
    /// `AY_COMPETITION`, `--no-proof` or `--z3-mode` selected shedding AND no
    /// proof or certificate demand is in scope (`--proof`, `--strict-proofs`,
    /// `--self-check`, `--verify-firewall`, `--emit-firewall-lean`,
    /// `--verify-proof`, `--chc-checked-replay`). Library engines that build
    /// executors for their own SEARCH queries — the CHC engines' SMT queries,
    /// whose verdicts only guide the search and are re-verified at the CHC
    /// level before anything is printed — read it so their per-query posture
    /// matches the CLI executor's (`Executor::set_competition_mode`) instead
    /// of paying the certified cycle on verdicts nothing publishes. `false`
    /// for a plain solve, for every certificate-demanding lane, and for every
    /// library consumer that never installs CLI flags.
    pub search_executor_sheds_proof_cycle: bool,
    /// `--z3-mode`: stderr stays as empty as z3's, so the library's own
    /// stderr diagnostics (`MODEL-UNCONFIRMED`, the partial-model note, the
    /// `[AY SOUNDNESS GATE]` banner) are not written. No verdict or search
    /// changes.
    pub z3_transcript: bool,
    /// `--engine=shadow` — measurement only (design `cdclt-engine.md` §10.1):
    /// after each top-level QF_LRA / QF_RDL / QF_IDL / QF_LIA check-sat, run the
    /// CDCL(T) kernel (`ay-cdclt`) on the lane's dispatch window with its own
    /// budget and record both verdicts. The kernel's answer is never printed.
    pub engine_shadow: bool,
    /// `--engine-shadow-log=FILE` — append one JSON row per shadowed
    /// check-sat to FILE.
    pub engine_shadow_log: Option<String>,
    /// `--engine=shadow:theory-branching` — the shadow kernel with
    /// theory-aware branching on (design §3.8, measured off by default).
    pub engine_shadow_theory_branching: bool,
    /// `--engine=shadow:simplex` — the shadow kernel without its
    /// difference-logic sub-module: every arithmetic check runs the simplex
    /// (the control arm for measuring that sub-module).
    pub engine_shadow_simplex_only: bool,
    /// `--engine=shadow:lia-bcp-implied` — the shadow kernel's integer
    /// simplex derives implied bounds during BCP-time checks too (the
    /// control arm; off by default).
    pub engine_shadow_lia_bcp_implied: bool,
    /// `--engine=shadow:sat-default` — the shadow kernel with its own search
    /// profile (ay-sat's default, KC25) instead of the lane-parity profile
    /// the shadow uses to compare the kernel with the lanes.
    pub engine_shadow_sat_default: bool,
    /// `--engine=shadow:hub-relevancy` — the shadow kernel runs its relevancy
    /// service (KC21) and hands the search only relevant hub propagations.
    pub engine_shadow_hub_relevancy: bool,
    /// The kernel's own budget per shadowed check-sat, in milliseconds: the
    /// CLI's `--timeout`, so the kernel gets what the lane got.
    pub engine_shadow_budget_ms: Option<u64>,
    /// `--engine-shadow-proofs=DIR` — the shadow kernel records its proof
    /// while it searches (design D3): it runs on the authored assertions, and
    /// every `unsat` answer's refutation is assembled, checked by AY's strict
    /// checker and written to DIR as an Alethe document. Measurement only.
    pub engine_shadow_proofs: Option<String>,
    /// `--engine-shadow-authored` — the shadow kernel runs on the authored
    /// assertions (as `--engine-shadow-proofs` does) without recording: the
    /// control that prices the recording. Measurement only.
    pub engine_shadow_authored: bool,
    /// `--engine=lane` — measurement only: every family keeps its lane, as
    /// before the kernel took QF_LRA in the `--z3-mode` posture
    /// (`executor/engine_route.rs`). `--engine=shadow` implies it, since the
    /// shadow compares the kernel with the lane.
    pub engine_lanes: bool,
}

/// Global miscellaneous CLI flags, initialized once per process.
static GLOBAL_MISC_CLI_FLAGS: OnceLock<MiscCliFlags> = OnceLock::new();

/// Initialize miscellaneous CLI flags from environment variables.
///
/// Used as the back-compat fallback when the CLI has not called
/// [`set_global_misc_cli_flags`] (e.g., library consumers, older callers).
fn init_misc_cli_flags_from_env() -> MiscCliFlags {
    let dpll_diagnostic_file = None;
    let dpll_diagnostic_enabled = false;
    let dpll_trace_file = None;
    MiscCliFlags {
        dump_auflia_assertions: false,
        sat_variant: std::env::var("AY_SAT_VARIANT")
            .ok()
            .filter(|s| !s.is_empty()),
        sat_variant_from_cli: false,
        disabled_sat_startup_capabilities: Vec::new(),
        dpll_diagnostic_file,
        dpll_diagnostic_enabled,
        dpll_trace_file,
        // CLI-only; retired A/B env spellings are intentionally ignored.
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
        xor_allow_unadmitted: false,
        phase_trace: false,
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
        probe_sat_variable: None,
        str_w4_work: None,
        fmq_lane_budget_ms: None,
        fmq_probe_ms: None,
        fmq_seed_ms: None,
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
        sat_bve_trace: 0,
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
        trace_cegqi_attr: false,
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
        // Test runs install --probe-strict-check via `misc_test_override`.
        probe_strict_check: false,
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
        no_quantified_shedding_yield: false,
        no_negated_exists_ground_inst: false,
        no_qlra_cegqi: false,
        no_eq_qe_lane: false,
        no_qsat: false,
        no_qlra_nested: false,
        no_authored_skeleton_refutation: false,
        no_authored_fold_identity: false,
        no_probe_ite_lift_promoter: false,
        no_alpha_quantifier_sharing: false,
        no_quantifier_proxy_abstraction: false,
        no_skolem_guarded_proxy_instances: false,
        no_quantifier_guarded_instances: false,
        quantifier_guarded_enumerative: false,
        no_quantifier_guarded_enumerative: false,
        no_quantifier_ce_free_resolve: false,
        no_quantifier_guard_seeds: false,
        no_ground_first: false,
        no_ground_conflict_decomp: false,
        no_fp_incremental: false,
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
        chc_session: None,
        chc_session_strict: None,
        chc_session_audit: None,
        chc_session_stats: false,
        chc_session_coverage: false,
        chc_session_trace: false,
        chc_session_dump: None,
        chc_session_dump_max: None,
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
        uflia_arith_decisions: false,
        no_skolem_witness_sat: false,
        no_singleton_carrier_mint: false,
        // The theory-crate diagnostics are CLI-carried; no env fallbacks.
        lra_float_layer: false,
        str_nf: false,
        debug_euf_init: false,
        euf_cong_undo_debug: false,
        euf_diseq_undo_debug: false,
        probe_prescreen: false,
        lia_probe_qx: None,
        probe_stats: false,
        debug_fixed_eqs: false,
        algebraic_stats: false,
        debug_arr_extract: false,
        weq5_shadow_dump: false,
        // The chc/dpll research diagnostics are CLI-carried.
        ic3_lane_debug: false,
        ic3_lane_dump: None,
        ic3_lane_noslice: false,
        reve_debug: false,
        max_propagate_rounds: None,
        lra_cond_trail: false,
        lra_unit_pivot_pref: false,
        // The euf/nra experiment and diagnostic flags.
        euf_inc_neg_pop: false,
        nra_diag: false,
        nra_grid_probe: false,
        nra_witness: None,
        quant_relevance: None,
        quant_relevance_k: None,
        quant_relevance_min: None,
        quant_relevance_model: None,
        quant_relevance_debug: false,
        search_executor_sheds_proof_cycle: false,
        z3_transcript: false,
        engine_shadow: false,
        engine_shadow_log: None,
        engine_shadow_budget_ms: None,
        engine_shadow_theory_branching: false,
        engine_shadow_simplex_only: false,
        engine_shadow_lia_bcp_implied: false,
        engine_shadow_sat_default: false,
        engine_shadow_hub_relevancy: false,
        engine_shadow_proofs: None,
        engine_shadow_authored: false,
        engine_lanes: false,
    }
}

/// Returns a reference to the global miscellaneous CLI flags.
///
/// Without a prior `set_global_misc_cli_flags`, the first call uses defaults + `AY_SAT_VARIANT`.
#[inline]
pub fn misc_cli_flags() -> &'static MiscCliFlags {
    if let Some(overridden) = misc_test_override::MISC_TEST_OVERRIDE.with(std::cell::Cell::get) {
        return overridden;
    }
    GLOBAL_MISC_CLI_FLAGS.get_or_init(init_misc_cli_flags_from_env)
}

/// Read already captured process configuration without initializing it.
///
/// Bounded query constructors use this to refuse before a first-use environment
/// read could allocate unmetered input. The command layer may capture these
/// flags with `misc_cli_flags` or a setter before it creates a query owner.
#[inline]
pub fn captured_misc_cli_flags() -> Option<&'static MiscCliFlags> {
    misc_test_override::MISC_TEST_OVERRIDE
        .with(std::cell::Cell::get)
        .or_else(|| GLOBAL_MISC_CLI_FLAGS.get())
}

/// In-process per-test override seam for [`misc_cli_flags`] (the same
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

/// Set the global miscellaneous CLI flags after parsing, without env-var IPC (#8835).
/// Returns the rejected flags when another value is already installed.
#[expect(clippy::result_large_err, reason = "duplicate-set ownership")]
pub fn set_global_misc_cli_flags(flags: MiscCliFlags) -> Result<(), MiscCliFlags> {
    GLOBAL_MISC_CLI_FLAGS.set(flags)
}

/// The flag set [`misc_cli_flags`] would install on first use, with `configure`
/// applied on top. Pure: installs nothing.
///
/// This exists because `MiscCliFlags` has ~120 fields and no `Default`, so a
/// consumer outside this crate cannot in practice build one to hand to
/// [`set_global_misc_cli_flags`] — the setter was public but unusable.
#[must_use]
pub fn misc_cli_flags_with(configure: impl FnOnce(&mut MiscCliFlags)) -> MiscCliFlags {
    let mut flags = init_misc_cli_flags_from_env();
    configure(&mut flags);
    flags
}

/// Install a diagnostic configuration process-wide from a Rust-API consumer.
///
/// # Why this exists (the measurement gap)
///
/// The diagnostic carriers — `probe_cert_reject`, `phase_trace`, `debug_cert`,
/// `trace_cegqi_attr`, the `--f1-diag` family — were migrated to typed
/// `MiscCliFlags` and `init_misc_cli_flags_from_env` deliberately keeps no
/// `AY_*` fallback for them. That is right for a CLI, and it is not to be
/// undone by re-adding an environment read.
///
/// But it left every *library* consumer with no supported way to turn a channel
/// on at all:
///
///  * the Rust API and the integration-test binaries never parse a CLI, so a
///    strict-certification refusal records its reason and is never printed;
///  * downstream embedders (`deductive-checks`) surface only the opaque
///    `(incomplete self-check-rejected)` reason code and cannot ask which gate
///    refused, or on which Alethe rule/step/clause;
///  * the only seam was [`misc_test_override`], which is **thread-local** — it
///    cannot instrument a solve that runs on a worker thread, and cannot be
///    applied to a whole test binary.
///
/// This is that seam: process-wide, typed, no environment variable, and
/// therefore no new entry in the exact-set environment-flag audit.
///
/// # Authority
///
/// Exactly [`set_global_misc_cli_flags`]'s — no more, no less. It is *not*
/// restricted to diagnostic fields, because `MiscCliFlags` draws no such line;
/// callers get the same first-writer-wins global the CLI writes. Returns
/// `false` if the flags were already initialized (the CLI already parsed its
/// arguments, or an earlier caller installed a set, or something already called
/// [`misc_cli_flags`]), in which case nothing was changed.
pub fn set_global_misc_cli_flags_with(configure: impl FnOnce(&mut MiscCliFlags)) -> bool {
    set_global_misc_cli_flags(misc_cli_flags_with(configure)).is_ok()
}

#[cfg(test)]
mod tests;
