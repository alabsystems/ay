// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by the binary root to preserve private CLI item DefPaths.

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
    /// VeriPB pseudo-Boolean derivation (`.pbp`), checked against the DIMACS
    /// CNF directly: `veripb --cnf instance.cnf proof.pbp` (no OPB companion
    /// file; `--cnf` is named rather than left to extension sniffing). The only
    /// DIMACS format that can carry the SR-witnessed symmetry routes under a
    /// checker on the official SAT-COMP 2026 menu, and what the SAT-COMP 2026
    /// submission declares.
    Veripb,
}

impl From<CliProofFormat> for ProofFormat {
    fn from(cli: CliProofFormat) -> Self {
        match cli {
            CliProofFormat::Drat => Self::Drat,
            CliProofFormat::Lrat => Self::Lrat,
            CliProofFormat::Lean4 => Self::Lean4,
            CliProofFormat::Alethe => Self::Alethe,
            CliProofFormat::Veripb => Self::Veripb,
        }
    }
}

/// CLI wrapper for [`ay_core::DeclaredProofChecker`] (`--proof-checker`).
///
/// A capability declaration paired with the format: `dsr-trim` verifies the DSR
/// substitution-witnessed symmetry steps inside `--proof-format drat`, and
/// `veripb` verifies the same steps inside `--proof-format veripb`. Any other
/// declaration — or a checker/format mismatch — makes the solver clamp those
/// routes to plain-CDCL-checkable emission.
#[derive(Debug, Clone, Copy, clap::ValueEnum)]
#[clap(rename_all = "kebab-case")]
enum CliProofChecker {
    DsrTrim,
    DprTrim,
    DratTrim,
    Gratgen,
    Veripb,
}

impl From<CliProofChecker> for ay_core::DeclaredProofChecker {
    fn from(cli: CliProofChecker) -> Self {
        match cli {
            CliProofChecker::DsrTrim => Self::DsrTrim,
            CliProofChecker::DprTrim => Self::DprTrim,
            CliProofChecker::DratTrim => Self::DratTrim,
            CliProofChecker::Gratgen => Self::Gratgen,
            CliProofChecker::Veripb => Self::Veripb,
        }
    }
}

/// The single assurance dial (`--assurance`): how hard AY works to justify the
/// answer it prints, arranged on one mutually-exclusive ladder from fastest to
/// safest. This is the primary, self-documenting surface; each level is exactly
/// equivalent to a legacy flag that stays accepted as a hidden alias:
///
///   fast      == --competition
///   standard  == (default; no flag)
///   strict    == --strict-proofs
///   certified == --self-check
///
/// Soundness defaults never move between levels: every solver technique, the
/// automatic engine selection, and the always-on independent model gate are
/// identical at every level. Only the optional overhead "batteries" (runtime
/// result validation, default proof emission, and the post-solve proof
/// re-check) differ. `--assurance` resolves onto the same internal switches the
/// legacy flags set, so the two spellings are byte-for-byte equivalent.
#[derive(Debug, Clone, Copy, PartialEq, Eq, clap::ValueEnum)]
#[clap(rename_all = "kebab-case")]
enum CliAssuranceLevel {
    /// Batteries off for raw speed (== --competition). No default runtime
    /// validation, no post-solve proof re-check, and no default proof emission
    /// (an explicit --proof still wins). Capability/soundness defaults -- all
    /// solver techniques, the always-on independent model gate, automatic
    /// engine selection -- are UNCHANGED. Also forced automatically when a
    /// SAT-competition wrapper env signal is present.
    Fast,
    /// The default. Batteries included: runtime result validation is ON,
    /// default proof-certificate emission is ON, and the emitted proof is
    /// re-checked afterward (the built-in --verify-proof re-check).
    Standard,
    /// Strict proof diagnostic and terminal-trust screen (== --strict-proofs).
    /// Uses AY's strict semantic checker while constructing proofs and
    /// downgrades a terminal Trust-backed `unsat` to `unknown`. Other checker
    /// failures remain diagnostics.
    Strict,
    /// Fail-closed self-check (== --self-check). AY emits only an answer it can
    /// verify itself -- model evaluation for `sat`, a strict same-problem
    /// refutation for `unsat` -- and reports `unknown` for anything it cannot
    /// self-check.
    Certified,
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
