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
    // B75: the dimacs env-lever block becomes typed switches. Opt-in bools
    // default false = the shipped engine; tri-states default None = the
    // compiled default named at the read site.
    /// `--sat-bcp-telemetry` (B75; was `AY_BCP_TELEMETRY`)
    pub bcp_telemetry: bool,
    /// `--sat-bcp-lean` (B75; was `AY_SAT_BCP_LEAN`)
    pub bcp_lean: bool,
    /// `--sat-bcp-disable-trail-lookahead-prefetch` (B75; was `AY_SAT_BCP_DISABLE_TRAIL_LOOKAHEAD_PREFETCH`)
    pub bcp_disable_trail_lookahead_prefetch: bool,
    /// `--sat-bcp-advance-saved-pos` (B75; was `AY_SAT_BCP_ADVANCE_SAVED_POS`)
    pub bcp_advance_saved_pos: bool,
    /// `--sat-bcp-learned-1963-false-saved-pos-reset` (B75; was `AY_SAT_BCP_LEARNED_1963_FALSE_SAVED_POS_RESET`)
    pub bcp_learned_1963_false_saved_pos_reset: bool,
    /// `--sat-bcp-learned-1963-true-tail-relocation` (B75; was `AY_SAT_BCP_LEARNED_1963_TRUE_TAIL_RELOCATION`)
    pub bcp_learned_1963_true_tail_relocation: bool,
    /// `--sat-bcp-learned-618-true-tail-relocation` (B75; was `AY_SAT_BCP_LEARNED_618_TRUE_TAIL_RELOCATION`)
    pub bcp_learned_618_true_tail_relocation: bool,
    /// `--sat-bcp-learned-617-tail-reorder` (B75; was `AY_SAT_BCP_LEARNED_617_TAIL_REORDER`)
    pub bcp_learned_617_tail_reorder: bool,
    /// `--sat-bcp-learned-18-tail-reorder` (B75; was `AY_SAT_BCP_LEARNED_18_TAIL_REORDER`)
    pub bcp_learned_18_tail_reorder: bool,
    /// `--sat-bcp-learned-1963-tail-reorder` (B75; was `AY_SAT_BCP_LEARNED_1963_TAIL_REORDER`)
    pub bcp_learned_1963_tail_reorder: bool,
    /// `--sat-bve-occ-delta-validation` (B75; was `AY_SAT_BVE_OCC_DELTA_VALIDATION`)
    pub bve_occ_delta_validation: bool,
    /// `--sat-bve-occ-saved-state-reuse` (B75; was `AY_SAT_BVE_OCC_SAVED_STATE_REUSE`)
    pub bve_occ_saved_state_reuse: bool,
    /// `--sat-dense-mutex-focused-restart-gate` (B75; was `AY_SAT_DENSE_MUTEX_FOCUSED_RESTART_GATE`)
    pub dense_mutex_focused_restart_gate: bool,
    /// `--sat-dense-clique-mab-branch` (B75; was `AY_SAT_DENSE_CLIQUE_MAB_BRANCH`)
    pub dense_clique_mab_branch: bool,
    /// `--sat-bve-lrat-scout-route` (B75; was `AY_SAT_BVE_LRAT_SCOUT_ROUTE`)
    pub bve_lrat_scout_route: bool,
    /// `--sat-fmla-decompose-lrat-preflight-route` (B75; was `AY_SAT_FMLA_DECOMPOSE_LRAT_PREFLIGHT_ROUTE`)
    pub fmla_decompose_lrat_preflight_route: bool,
    /// `--sat-dense-clique-scout` (B75; was `AY_SAT_DENSE_CLIQUE_SCOUT`)
    pub dense_clique_scout: bool,
    /// `--sat-multiplier-equiv-conservation-scout` (B75; was `AY_SAT_MULTIPLIER_EQUIV_CONSERVATION_SCOUT`)
    pub multiplier_equiv_conservation_scout: bool,
    /// `--sat-bcp-learned-1963-used5-fsw-saved-pos-reset` (B75; was `AY_SAT_BCP_LEARNED_1963_USED5_FSW_SAVED_POS_RESET`)
    pub bcp_learned_1963_used5_fsw_saved_pos_reset: bool,
    /// `--sat-bcp-learned-1963-fsw-conflict-saved-pos-reset` (B75; was `AY_SAT_BCP_LEARNED_1963_FSW_CONFLICT_SAVED_POS_RESET`)
    pub bcp_learned_1963_fsw_conflict_saved_pos_reset: bool,
    /// `--sat-bcp-learned-no-replacement-saved-pos-update` (B75; was `AY_SAT_BCP_LEARNED_NO_REPLACEMENT_SAVED_POS_UPDATE`)
    pub bcp_learned_no_replacement_saved_pos_update: bool,
    /// `--sat-bcp-learned-1963-fsw-gent-skip` (B75; was `AY_SAT_BCP_LEARNED_1963_FSW_GENT_SKIP`)
    pub bcp_learned_1963_fsw_gent_skip: bool,
    /// `--sat-bcp-learned-no-replacement-scan-pressure` (B75; was `AY_SAT_BCP_LEARNED_NO_REPLACEMENT_SCAN_PRESSURE`)
    pub bcp_learned_no_replacement_scan_pressure: bool,
    /// `--sat-bcp-learned-1963-identity` (B75; was `AY_SAT_BCP_LEARNED_1963_IDENTITY`)
    pub bcp_learned_1963_identity: bool,
    /// `--sat-bcp-learned-1963-pressure-reduction` (B75; was `AY_SAT_BCP_LEARNED_1963_PRESSURE_REDUCTION`)
    pub bcp_learned_1963_pressure_reduction: bool,
    /// `--sat-bcp-learned-1963-pressure-retention` (B75; was `AY_SAT_BCP_LEARNED_1963_PRESSURE_RETENTION`)
    pub bcp_learned_1963_pressure_retention: bool,
    /// `--sat-bcp-disable-learned-1963-no-replacement-unit-blocker-refresh` (B75; was `AY_SAT_BCP_DISABLE_LEARNED_1963_NO_REPLACEMENT_UNIT_BLOCKER_REFRESH`)
    pub bcp_disable_learned_1963_no_replacement_unit_blocker_refresh: bool,
    /// `--sat-inprocessing-yield-productivity-rescue` (B75; was `AY_SAT_INPROCESSING_YIELD_PRODUCTIVITY_RESCUE`)
    pub inprocessing_yield_productivity_rescue: bool,
    /// M2 FLIP (2026-08-19): default ON — paired full-400 300s proof-mode
    /// lost 0 / gained 2 with median 0.0s delta on the common set, and the
    /// 900s boundary confirmation was clean (ab_lrat_clamp_rescue_300s.json,
    /// ab_lrat_clamp_confirm_900s.json). `--sat-lrat-proof-clamp-probe-rescue
    /// false` is the opt-out; None = ON.
    pub lrat_proof_clamp_probe_rescue: Option<bool>,
    /// M3 FLIP (2026-08-19): default ON — paired full-400 300s proof-mode
    /// lost 0 / gained 1, and the 900s confirmation held the gain (arm 430s
    /// vs base timeout at 900s) with zero regressions
    /// (ab_backbone_cooldown_300s.json + _confirm_900s.json).
    /// `--sat-yield-rescue-backbone-cooldown false` is the opt-out; None = ON.
    pub yield_rescue_backbone_cooldown: Option<bool>,
    /// `--sat-bounded-backbone-zero-decompose-backoff` (B75; was `AY_SAT_BOUNDED_BACKBONE_ZERO_DECOMPOSE_BACKOFF`)
    pub bounded_backbone_zero_decompose_backoff: bool,
    /// `--sat-bcp-learned-1963-blocker-cert-shadow` (B75; was `AY_SAT_BCP_LEARNED_1963_BLOCKER_CERT_SHADOW`)
    pub bcp_learned_1963_blocker_cert_shadow: bool,
    /// `--sat-bcp-search-inplace-watch-scan <bool>` (B75; tri-state, was `AY_SAT_BCP_SEARCH_INPLACE_WATCH_SCAN`; None = default ON)
    pub bcp_search_inplace_watch_scan: Option<bool>,
    /// `--sat-backbone-post-vivify-binary-admission <bool>` (B75; tri-state, was `AY_SAT_BACKBONE_POST_VIVIFY_BINARY_ADMISSION`; None = default ON)
    pub backbone_post_vivify_binary_admission: Option<bool>,
    /// `--sat-finalize-rescue <bool>` (B75; tri-state, was `AY_AB_FINALIZE_RESCUE`; None = default ON)
    pub finalize_rescue: Option<bool>,
    /// `--sat-bcp-learned-1963-tail-reorder-swap-budget <n>` (B75; was `AY_SAT_BCP_LEARNED_1963_TAIL_REORDER_SWAP_BUDGET`)
    pub bcp_learned_1963_tail_reorder_swap_budget: Option<u64>,
    /// `--sat-bcp-learned-1963-blocker-cert-elision` (B76; the run.sh
    /// profile pair travels as CLI args now — was env-exported)
    pub bcp_learned_1963_blocker_cert_elision: bool,
    /// `--sat-bcp-learned-1963-blocker-cert-false-reject-demote` (B76)
    pub bcp_learned_1963_blocker_cert_false_reject_demote: bool,
    /// `--sat-dense-clique-php-proof-route` (B76)
    pub dense_clique_php_proof_route: bool,
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
