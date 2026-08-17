// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::allow_unknown_env_is_set;

/// What a knob is for.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Bucket {
    /// Product surface: promote to a CLI flag / typed option.
    Product,
    /// `AY_MILP_NO_*` kill switch for a shipped default.
    KillSwitch,
    /// Numeric measurement scaffolding.
    Tuning,
    /// Trace / profile / census output.
    Diagnostic,
    /// Experiment arm selector.
    Arm,
    /// Mentioned in source but never read.
    Dead,
}

impl Bucket {
    /// The bucket's short name.
    #[must_use]
    pub fn name(self) -> &'static str {
        match self {
            Self::Product => "product",
            Self::KillSwitch => "kill-switch",
            Self::Tuning => "tuning",
            Self::Diagnostic => "diagnostic",
            Self::Arm => "arm",
            Self::Dead => "dead",
        }
    }
}

/// One environment knob.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Knob {
    /// The environment variable name.
    pub name: &'static str,
    /// What it is for.
    pub bucket: Bucket,
    /// Literal `env::var`/`env::var_os` call sites naming this knob, in `src/`
    /// and `examples/`.
    ///
    /// # This number is DERIVED, not declared
    ///
    /// It was hand-typed until `tests/env_ledger.rs::read_site_counts_are_derived`
    /// began deriving it, and by then **23 of 353 entries disagreed with the
    /// source**. That mattered because the number is quoted as evidence: a debt
    /// census written off this column reported "404 read sites" for a table whose
    /// column summed to 432 and whose true literal count was 423.
    ///
    /// The drift was not random, which is the interesting part. Twelve of the
    /// twenty-three are exactly the knobs `EngineEconomics` migrated to
    /// [`crate::tune`]: their literal reads were deleted and the ledger still
    /// claimed one apiece. Three more were read by **nothing at all** and are now
    /// [`Bucket::Dead`] — see [`super::ROUTED`] for the ones that legitimately read zero.
    ///
    /// A zero here means "no literal call site", which is *not* the same as dead:
    /// check [`super::ROUTED`] before concluding anything.
    pub read_sites: u32,
}

/// Why a live knob has **zero** literal `env::var` sites.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Route {
    /// Resolved through [`crate::tune`]'s accessors, which hold the only copy of
    /// the name (`tune::Knob::env`). The call site names the typed knob, not the
    /// variable.
    Tune,
    /// Read through a named constant rather than a literal. A grep of the call
    /// sites cannot see these, which is the reason this table is hand-maintained
    /// and the derivation needs an exception list at all.
    Indirect {
        /// The constant that holds the name.
        via: &'static str,
    },
}

/// A live knob with no literal `env::var` site, and why.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Routed {
    /// The environment variable.
    pub env: &'static str,
    /// How it is reached instead.
    pub route: Route,
}

/// What a scan of the process environment found.
#[derive(Debug, Clone, Default)]
pub struct EnvAudit {
    /// `AY_*` names set in the environment and present in [`super::KNOBS`].
    pub known: Vec<(String, String)>,
    /// `AY_*` names set in the environment that NO read site consumes. A typo
    /// here silently measures the wrong arm — the single highest-value item in
    /// this whole area.
    pub unknown: Vec<String>,
    /// `AY_*` names set that are in the table but marked [`Bucket::Dead`] —
    /// also no-ops, for a different reason.
    pub dead: Vec<String>,
    /// Set names a CLI flag now supersedes, with the flag to use.
    pub deprecated: Vec<(String, &'static str)>,
}

impl EnvAudit {
    /// Does this environment invalidate the run?
    ///
    /// # Why a warning was not enough
    ///
    /// `AY_MILP_NO_CUTZ=1` is a no-op, so a campaign that sets it measures the
    /// default arm and writes the result down as a finding. That is a correctness
    /// defect in the measurement record, and the response to it was a `WARNING`
    /// line on stderr — inside a harness that produces hundreds of lines per
    /// instance and is read by a script. A warning nobody reads is not a guard.
    ///
    /// Both classes are fatal and for the same reason: the operator asked for a
    /// configuration, and the run is not going to deliver it. An [`unknown`] name
    /// is usually a typo; a [`dead`] one is usually a recipe that outlived its
    /// knob (the retired cond-tighten arm is the worked example — documented in
    /// `presolve.rs` as *"kept as the explicit-on A/B arm"*, read by nothing).
    /// Neither run measures what it claims to.
    ///
    /// [`unknown`]: Self::unknown
    /// [`dead`]: Self::dead
    #[must_use]
    pub fn is_fatal(&self) -> bool {
        (!self.unknown.is_empty() || !self.dead.is_empty()) && !allow_unknown_env_is_set()
    }
}
