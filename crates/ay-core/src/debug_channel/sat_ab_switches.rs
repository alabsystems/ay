// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Process-constant SAT A/B switches installed by the CLI.

use std::sync::OnceLock;

/// SAT-engine A/B opt-outs, CLI-owned (B26: these replace never-set
/// default-on `AY_AB_*`/`AY_SAT_*` kill-switch env vars). Every field
/// defaults FALSE = the shipped engine; each true disables one
/// sound-alternative lane for measurement.
#[derive(Debug, Clone, Copy, Default, PartialEq)]
pub struct SatAbSwitches {
    /// `--sat-no-bve-inst-gate`
    pub no_bve_inst_gate: bool,
    /// `--sat-no-bve-sparse-deep`
    pub no_bve_sparse_deep: bool,
    /// `--sat-no-dense-skip-lift`
    pub no_dense_skip_lift: bool,
    /// `--sat-no-factor-bin-fastpath`
    pub no_factor_bin_fastpath: bool,
    /// `--sat-no-factor-dense`
    pub no_factor_dense: bool,
    /// `--sat-no-factor-dense-init` (B33)
    pub no_factor_dense_init: bool,
    /// `--sat-no-lucky`
    pub no_lucky: bool,
    /// `--sat-no-midband-deep-restart`
    pub no_midband_deep_restart: bool,
    /// `--sat-no-orbitope`
    pub no_orbitope: bool,
    /// `--sat-no-orbitope-alo-columns`
    pub no_orbitope_alo_columns: bool,
    /// `--sat-no-symmetry-sr-auxfree`
    pub no_symmetry_sr_auxfree: bool,
    /// `--sat-no-probe-route` (B34; was the AY_AB_PROBE_ROUTE=0 shim)
    pub no_probe_route: bool,
    /// `--sat-no-aggressive-route` (B34)
    pub no_aggressive_route: bool,
    /// `--sat-no-bve-sparse` (B34)
    pub no_bve_sparse: bool,
    /// `--sat-no-bve-post-collapse` (B34)
    pub no_bve_post_collapse: bool,
    /// `--sat-no-subst-auto` (B34; restores the pre-flip opt-in profile)
    pub no_subst_auto: bool,
    /// `--sat-subst-auto-uncapped` (B34; the historical `=1` UNCAPPED
    /// measurement semantics — disarms the dense-band guard rails)
    pub subst_auto_uncapped: bool,
    /// `--sat-no-drat-subst` (B34; force-clamp Decompose+Congruence on DRAT
    /// — the pre-2026-07-09 behavior. The old `=1` force-allow arm was
    /// registry-redundant and is gone.)
    pub no_drat_subst: bool,
    /// `--sat-bve-additive-fastelim` (B36; force the banded additive
    /// fast-elim ON past its band auto decision)
    pub bve_additive_fastelim: bool,
    /// `--sat-no-bve-additive-fastelim` (B36; force it OFF)
    pub no_bve_additive_fastelim: bool,
    /// `--sat-mode-equiticks <true|false>` (B43; was the
    /// `AY_AB_MODE_EQUITICKS` 1/0 tri-state — `Some(true)` forces the
    /// equal-effort stable budgeting ON everywhere, `Some(false)` forces it
    /// OFF, `None` = the shipped default-off resolution)
    pub mode_equiticks: Option<bool>,
    /// `--sat-eqt-progress <N>` (B43; `1` = the default progress-gate
    /// window, `N > 1` sets the window directly; `None`/other = gate inert)
    pub eqt_progress: Option<u64>,
    /// `--sat-congruence-memory-bound` (B43; re-arm the retired congruence
    /// fixpoint memory guard without re-deriving it)
    pub congruence_memory_bound: bool,
    /// `--sat-circuit-equiv-throughput-profile` (B43; opt in to the
    /// multiplier-equivalence throughput profile lane)
    pub circuit_equiv_throughput_profile: bool,
    /// `--sat-signed-symmetry` (B61; opt in to the signed lex-leader route —
    /// measured LOSING on the full 400 at 300s, kept as a sweepable arm)
    pub signed_symmetry: bool,
    /// `--sat-signed-symmetry-sr` (B61)
    pub signed_symmetry_sr: bool,
    /// `--sat-composite-symmetry` (B61; certificates may be REJECTED by
    /// external checkers — the proof-mode refusal gate names this flag)
    pub composite_symmetry: bool,
    /// `--sat-symmetry-sr` (B61)
    pub symmetry_sr: bool,
    /// `--sat-symmetry-hhw` (B61)
    pub symmetry_hhw: bool,
    /// `--sat-bve-sparse-max-vars <n>` (B65; raises/lowers the sparse-BVE
    /// variable ceiling — was `AY_BVE_SPARSE_MAX_VARS`)
    pub bve_sparse_max_vars: Option<usize>,
    /// `--sat-bve-sparse-max-density <f>` (B65)
    pub bve_sparse_max_density: Option<f64>,
    /// `--sat-deterministic-inproc <bool>` (B70; tri-state force of the
    /// default-ON deterministic inprocessing budget)
    pub deterministic_inproc: Option<bool>,
    /// `--sat-congruence-parity-trust` (B70; default-off trust arm)
    pub congruence_parity_trust: bool,
}

static GLOBAL_SAT_AB_SWITCHES: OnceLock<SatAbSwitches> = OnceLock::new();

/// Install the SAT A/B opt-outs (first caller wins).
///
/// # Errors
///
/// The rejected value when a set was already installed.
pub fn set_global_sat_ab_switches(switches: SatAbSwitches) -> Result<(), SatAbSwitches> {
    GLOBAL_SAT_AB_SWITCHES.set(switches).map_err(|_| switches)
}

/// The installed SAT A/B opt-outs, or the all-shipped default.
#[must_use]
pub fn sat_ab_switches() -> SatAbSwitches {
    if let Some(overridden) = consumer_test_override::CONSUMER_OVERRIDE.with(std::cell::Cell::get) {
        return overridden;
    }
    GLOBAL_SAT_AB_SWITCHES.get().copied().unwrap_or_default()
}

/// Consumer-crate test seam (B61; same shape as
/// `ay_pb_core::ab_switches::consumer_test_override`): always compiled so a
/// consumer crate's own tests can scope switch values. Production code must
/// never touch it.
#[doc(hidden)]
pub mod consumer_test_override {
    use super::SatAbSwitches;

    thread_local! {
        pub(super) static CONSUMER_OVERRIDE: std::cell::Cell<Option<SatAbSwitches>> =
            const { std::cell::Cell::new(None) };
    }

    /// RAII guard restoring the previous override on drop.
    pub struct Guard(Option<SatAbSwitches>);

    impl Drop for Guard {
        fn drop(&mut self) {
            let prev = self.0;
            CONSUMER_OVERRIDE.with(|c| c.set(prev));
        }
    }

    /// Install a thread-scoped override for the current test.
    #[must_use]
    pub fn set(switches: SatAbSwitches) -> Guard {
        let prev = CONSUMER_OVERRIDE.with(|c| c.replace(Some(switches)));
        Guard(prev)
    }
}
