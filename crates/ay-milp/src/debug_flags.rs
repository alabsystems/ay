// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Process-constant MILP diagnostic switches, installed once by the CLI.
//!
//! B46 of the env-flag retirement: these were never-set `AY_MILP_*`
//! diagnostic env vars. Every switch defaults OFF (the quiet engine);
//! enabling one turns on a stderr diagnostic stream, never a behavior
//! change.

use std::sync::OnceLock;

/// The diagnostic switch set. Every field defaults to OFF.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct MilpDebugFlags {
    /// `--trace` — main solver/presolve trace stream.
    pub trace: bool,
    /// `--ms-dive-trace` — multi-start dive trace.
    pub ms_dive_trace: bool,
    /// `--coef-tighten-debug` — coefficient-tightening presolve diagnostics.
    pub coef_tighten_debug: bool,
    /// `--sym-debug` — symmetry generator probe.
    pub sym_debug: bool,
    /// `--shape-census` — LP peel census (with `trace`).
    pub shape_census: bool,
    /// `--sep-screen-audit` — separator screen claims checked against the
    /// exact kernel.
    pub sep_screen_audit: bool,
    /// `--lnp-probe <path>` — LNP probe MPS input (B64; leaked once at
    /// install, process-constant).
    pub lnp_probe: Option<&'static str>,
    /// `--kernel-scan-dir <dir>` — kernel-reformulation corpus census input
    /// (B71; dev harness).
    pub kernel_scan_dir: Option<&'static str>,
}

static GLOBAL_MILP_DEBUG_FLAGS: OnceLock<MilpDebugFlags> = OnceLock::new();

/// Install the diagnostic switches (first caller wins).
///
/// # Errors
///
/// The rejected value when a set was already installed.
pub fn set_milp_debug_flags(flags: MilpDebugFlags) -> Result<(), MilpDebugFlags> {
    GLOBAL_MILP_DEBUG_FLAGS.set(flags).map_err(|_| flags)
}

/// The installed diagnostic switches, or the all-quiet default.
#[must_use]
pub fn milp_debug_flags() -> MilpDebugFlags {
    GLOBAL_MILP_DEBUG_FLAGS.get().copied().unwrap_or_default()
}

/// Consumer-test seam (B66): force the tri-crash-all knob for the guard's
/// scope. Doc-hidden — external LU tests are the only intended caller.
#[doc(hidden)]
pub struct TriCrashAllGuard(crate::tune::Active);

#[doc(hidden)]
#[must_use]
pub fn force_tri_crash_all_for_test() -> TriCrashAllGuard {
    TriCrashAllGuard(crate::tune::activate_caller(
        crate::tune::Profile::EMPTY.with(
            crate::tune::Knob::TriCrashAll,
            crate::tune::Setting::Flag(true),
        ),
    ))
}

/// Consumer-test seam (B71): the bump-LU harness pins the bump floor and the
/// refactorization cadence to 1 alongside the tri-crash force.
#[doc(hidden)]
#[must_use]
pub fn force_bump_lu_for_test() -> TriCrashAllGuard {
    TriCrashAllGuard(crate::tune::activate_caller(
        crate::tune::Profile::EMPTY
            .with(
                crate::tune::Knob::TriCrashAll,
                crate::tune::Setting::Flag(true),
            )
            .with(crate::tune::Knob::BumpLuMin, crate::tune::Setting::Count(1))
            .with(
                crate::tune::Knob::RefactorEvery,
                crate::tune::Setting::Count(1),
            ),
    ))
}
