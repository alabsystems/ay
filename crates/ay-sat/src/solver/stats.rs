// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Solver statistics, queries, debug diagnostics, and clause database access.

use super::solver_stats::{
    BcpLearned1963IdentityRecord, InprocessingPassAccounting, RephaseAttribution,
    RestartAttribution, BCP_LEARNED_1963_IDENTITY_ACTIVITY_BUCKETS,
    BCP_LEARNED_1963_IDENTITY_AGE_BUCKETS, BCP_LEARNED_1963_PRESSURE_LBD_BUCKETS,
    BCP_LEARNED_1963_PRESSURE_REPEAT_BUCKETS, BCP_LEARNED_1963_PRESSURE_USED_BUCKETS,
    BCP_LONG_SCAN_BUCKET_LABELS, INPROCESS_ACCOUNTING_LABELS, INPROCESS_TIMING_LABELS,
};
use super::*;
use crate::guidance::{SatGuidanceFingerprint, SatGuidanceImportDecision};

/// Restart decisions attributed to their primary trigger and current mode.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct RestartAttributionStats {
    /// Geometric restart schedule fired.
    pub geometric: u64,
    /// Theory-heavy dedicated Luby restart fired.
    pub theory_luby: u64,
    /// Stable-mode reluctant doubling fired.
    pub stable_reluctant: u64,
    /// Stable-mode Glucose EMA fired.
    pub stable_ema: u64,
    /// Focused-mode Glucose EMA fired.
    pub focused_ema: u64,
    /// Focused-mode Luby fallback fired.
    pub focused_luby: u64,
    /// Restart decisions made while in focused mode.
    pub focused_mode: u64,
    /// Restart decisions made while in stable mode.
    pub stable_mode: u64,
}

/// Rephase operations attributed to strategy, mode, and observable effects.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct RephaseAttributionStats {
    /// Original-phase rephases.
    pub original: u64,
    /// Inverted-phase rephases.
    pub inverted: u64,
    /// Best-phase rephases.
    pub best: u64,
    /// Random-phase rephases.
    pub random: u64,
    /// Flip-phase rephases.
    pub flip: u64,
    /// Walk-phase rephases.
    pub walk: u64,
    /// Rephase operations made while in focused mode.
    pub focused_mode: u64,
    /// Rephase operations made while in stable mode.
    pub stable_mode: u64,
    /// Phase entries changed by strategies with direct change accounting.
    ///
    /// Walk and greedy flip-search can mutate phases through local-search
    /// helpers that do not expose per-entry deltas, so they contribute to the
    /// strategy counters but not this direct-change total.
    pub direct_changed_phases: u64,
    /// Non-zero saved phases copied into target phase after rephasing.
    pub target_phase_updates: u64,
    /// Best-trail resets caused by Best rephases.
    pub best_resets: u64,
}

/// Backbone scheduler/backoff state exported for SAT Main diagnostics.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct BackboneScheduleStats {
    /// Whether the shared backbone scheduler row is enabled.
    pub enabled: bool,
    /// Completed bounded-CDCL backbone phases.
    pub phases: u32,
    /// Maximum bounded-CDCL backbone phases allowed for one instance.
    pub max_rounds: u32,
    /// Consecutive shared backbone rounds with zero unit yield.
    pub consecutive_empty: u32,
    /// Empty-streak limit that blocks bounded-CDCL backbone.
    pub stall_limit: u32,
    /// Conflict count at which the shared backbone row next becomes due.
    pub next_conflict: u64,
    /// Conflicts remaining until the shared backbone row is due.
    pub conflicts_until_next: u64,
    /// Internal growing-backoff interval used for the next empty reschedule.
    pub backoff_interval: u64,
    /// Base shared backbone cadence.
    pub base_interval: u64,
    /// Maximum shared backbone cadence after empty backoff growth.
    pub max_interval: u64,
    /// Whether the default-off yield-rescue backbone cooldown is enabled.
    pub yield_rescue_cooldown_enabled: bool,
    /// Yield-rescued rounds where the cooldown pushed out the backbone row.
    pub yield_rescue_cooldown_rounds: u64,
    /// Cooldown interval applied to the shared backbone row.
    pub yield_rescue_cooldown_interval: u64,
    /// Whether the default-off bounded-CDCL-only backoff is enabled.
    pub bounded_zero_decompose_backoff_enabled: bool,
    /// Conflict target for the bounded-CDCL-only cooldown.
    pub bounded_next_conflict: u64,
    /// Conflicts remaining until the bounded-CDCL-only cooldown allows a run.
    pub bounded_conflicts_until_next: u64,
    /// Bounded-CDCL-only backoff trigger count.
    pub bounded_backoff_triggers: u64,
    /// Bounded-CDCL backbone runs, excluding binary backbone.
    pub bounded_runs: u64,
    /// Bounded-CDCL backbone runs with pass-local yield.
    pub bounded_yields: u64,
    /// Bounded-CDCL backbone wall time in milliseconds.
    pub bounded_ms: u64,
    /// Binary-backbone suppressions caused by bounded-only cooldown.
    pub bounded_binary_suppressed: u64,
    /// Whether the shared backbone row is due at the current conflict count.
    pub due: bool,
    /// Whether the empty-streak guard currently blocks bounded-CDCL backbone.
    pub stalled_by_empty: bool,
    /// Whether the bounded-CDCL backbone phase cap has been reached.
    pub rounds_exhausted: bool,
}

/// BCP saved-position replacement-scan telemetry for long clauses.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct BcpSavedPosStats {
    /// Long-clause replacement scans using saved position.
    pub long_scans: u64,
    /// Long scans whose normalized saved position starts on a false literal.
    pub long_start_false: u64,
    /// Long scans that found a satisfied replacement.
    pub long_found_true: u64,
    /// Long scans that found an unassigned replacement.
    pub long_found_unassigned: u64,
    /// Long scans that found no replacement.
    pub long_no_replacement: u64,
    /// Length-18 replacement scans using saved position.
    pub len18_scans: u64,
    /// Length-18 scans whose normalized saved position starts on a false literal.
    pub len18_start_false: u64,
    /// Length-18 scans that found a satisfied replacement.
    pub len18_found_true: u64,
    /// Length-18 scans that found an unassigned replacement.
    pub len18_found_unassigned: u64,
    /// Length-18 scans that found no replacement.
    pub len18_no_replacement: u64,
}

/// Sequential Main BCP long-clause replacement-scan diagnostics.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct BcpLongScanStats {
    /// Bucket labels for every length-indexed array below.
    pub bucket_labels: [&'static str; 5],
    /// Existing blocker fast-path hits across BCP paths.
    pub blocker_fastpath_hits: u64,
    /// Sequential Main long-suffix blocker short-circuits.
    pub long_blocker_fastpath_hits: u64,
    /// Replacement scan steps attributed to binary clauses.
    pub scan_steps_binary: u64,
    /// Replacement scan steps attributed to non-binary clauses.
    pub scan_steps_non_binary: u64,
    /// Replacement scan steps in learned non-binary clauses.
    pub scan_steps_learned: u64,
    /// Replacement scan steps in original non-binary clauses.
    pub scan_steps_original: u64,
    /// Long replacement scan steps by clause-length bucket.
    pub scan_steps_by_len: [u64; 5],
    /// Learned long replacement scan steps by clause-length bucket.
    pub learned_scan_steps_by_len: [u64; 5],
    /// Original long replacement scan steps by clause-length bucket.
    pub original_scan_steps_by_len: [u64; 5],
    /// Long replacement scans by clause-length bucket.
    pub scans_by_len: [u64; 5],
    /// Long scans that found any replacement.
    pub found_replacement_by_len: [u64; 5],
    /// Long scans that found a true replacement.
    pub found_true_by_len: [u64; 5],
    /// Long scans that found an unassigned replacement.
    pub found_unassigned_by_len: [u64; 5],
    /// Long scans that found no replacement and therefore full-scanned.
    pub no_replacement_by_len: [u64; 5],
    /// No-replacement long scans ending in unit propagation.
    pub unit_by_len: [u64; 5],
    /// No-replacement long scans ending in conflict.
    pub conflict_by_len: [u64; 5],
    /// Learned-clause scans by length bucket.
    pub learned_scans_by_len: [u64; 5],
    /// Learned-clause scans that found any replacement.
    pub learned_found_replacement_by_len: [u64; 5],
    /// Learned-clause scans that found no replacement and full-scanned.
    pub learned_no_replacement_by_len: [u64; 5],
    /// Learned no-replacement scans ending in unit propagation.
    pub learned_unit_by_len: [u64; 5],
    /// Learned no-replacement scans ending in conflict.
    pub learned_conflict_by_len: [u64; 5],
    /// Whether the default-off learned 19-63 true-tail relocation gate is enabled.
    pub learned_1963_true_tail_relocation_enabled: bool,
    /// Eligible replacement candidates observed while telemetry and the gate are active.
    pub learned_1963_true_tail_relocation_attempts: u64,
    /// True-tail replacements that moved a watch while telemetry and the gate are active.
    pub learned_1963_true_tail_relocation_moves: u64,
    /// Whether the learned 19-63 used>=5 FSW saved-position reset gate is enabled.
    pub learned_1963_used5_fsw_saved_pos_reset_enabled: bool,
    /// Eligible learned 19-63 used>=5 false-start-wrap no-replacement scans.
    pub learned_1963_used5_fsw_saved_pos_reset_eligible: u64,
    /// Header writes made by the used>=5 FSW saved-position reset.
    pub learned_1963_used5_fsw_saved_pos_reset_writes: u64,
    /// Eligible used>=5 FSW reset scans ending in unit propagation.
    pub learned_1963_used5_fsw_saved_pos_reset_unit: u64,
    /// Eligible used>=5 FSW reset scans ending in conflict.
    pub learned_1963_used5_fsw_saved_pos_reset_conflict: u64,
    /// Whether the learned 19-63 FSW conflict-only reset gate is enabled.
    pub learned_1963_fsw_conflict_saved_pos_reset_enabled: bool,
    /// Eligible learned 19-63 FSW no-replacement conflict scans.
    pub learned_1963_fsw_conflict_saved_pos_reset_eligible: u64,
    /// Header writes made by the conflict-only FSW saved-position reset.
    pub learned_1963_fsw_conflict_saved_pos_reset_writes: u64,
    /// Eligible conflict-only FSW reset scans ending in conflict.
    pub learned_1963_fsw_conflict_saved_pos_reset_conflict: u64,
    /// Whether the default-off learned 6-18 true-tail relocation gate is enabled.
    pub learned_618_true_tail_relocation_enabled: bool,
    /// Eligible replacement candidates observed while telemetry and the gate are active.
    pub learned_618_true_tail_relocation_attempts: u64,
    /// True-tail replacements that moved a watch while telemetry and the gate are active.
    pub learned_618_true_tail_relocation_moves: u64,
    /// Whether the default-off learned no-replacement saved-position update is enabled.
    pub learned_no_replacement_saved_pos_update_enabled: bool,
    /// Eligible learned no-replacement scans by length bucket.
    pub learned_no_replacement_saved_pos_eligible_by_len: [u64; 5],
    /// Header writes made by the learned no-replacement saved-position update.
    pub learned_no_replacement_saved_pos_writes_by_len: [u64; 5],
    /// Eligible scans skipped because saved_pos was already at the tail head.
    pub learned_no_replacement_saved_pos_skipped_current_by_len: [u64; 5],
    /// Eligible learned no-replacement scans ending in unit propagation.
    pub learned_no_replacement_saved_pos_unit_by_len: [u64; 5],
    /// Eligible learned no-replacement scans ending in conflict.
    pub learned_no_replacement_saved_pos_conflict_by_len: [u64; 5],
    /// Whether the default-off learned 19-63 FSW Gent-order skip is enabled.
    pub learned_1963_fsw_gent_skip_enabled: bool,
    /// Learned 19-63 FSW Gent-order skip candidates.
    pub learned_1963_fsw_gent_skip_candidates: u64,
    /// Learned 19-63 FSW Gent-order skip applications.
    pub learned_1963_fsw_gent_skip_applied: u64,
    /// Saved-start slots skipped by the Gent-order FSW gate.
    pub learned_1963_fsw_gent_skip_saved_slots: u64,
    /// Gent-order FSW skips that found a satisfied suffix replacement.
    pub learned_1963_fsw_gent_skip_found_true_suffix: u64,
    /// Gent-order FSW skips that found an unassigned suffix replacement.
    pub learned_1963_fsw_gent_skip_found_unassigned_suffix: u64,
    /// Gent-order FSW skips that found a satisfied prefix replacement.
    pub learned_1963_fsw_gent_skip_found_true_prefix: u64,
    /// Gent-order FSW skips that found an unassigned prefix replacement.
    pub learned_1963_fsw_gent_skip_found_unassigned_prefix: u64,
    /// Gent-order FSW no-replacement unit outcomes.
    pub learned_1963_fsw_gent_skip_no_replacement_unit: u64,
    /// Gent-order FSW no-replacement conflict outcomes.
    pub learned_1963_fsw_gent_skip_no_replacement_conflict: u64,
    /// Whether gated learned no-replacement scan-pressure instrumentation is enabled.
    pub learned_no_replacement_scan_pressure_enabled: bool,
    /// Whether learned 19-63 no-replacement unit blocker refresh is disabled.
    pub disable_learned_1963_no_replacement_unit_blocker_refresh_enabled: bool,
    /// Gated learned no-replacement scans by length bucket.
    pub learned_no_replacement_scan_pressure_scans_by_len: [u64; 5],
    /// Scan steps spent in gated learned no-replacement scans by length bucket.
    pub learned_no_replacement_scan_pressure_steps_by_len: [u64; 5],
    /// Gated learned no-replacement scans whose saved start was false.
    pub learned_no_replacement_scan_pressure_start_false_by_len: [u64; 5],
    /// Gated learned no-replacement scans that wrapped from saved_pos.
    pub learned_no_replacement_scan_pressure_wrapped_by_len: [u64; 5],
    /// Gated learned no-replacement scans ending in unit propagation.
    pub learned_no_replacement_scan_pressure_unit_by_len: [u64; 5],
    /// Gated learned no-replacement scans ending in conflict.
    pub learned_no_replacement_scan_pressure_conflict_by_len: [u64; 5],
    /// Learned 19-63 false-start-wrap unit scans by LBD bucket: 0-2, 3-6, 7-10, 11-20, 21+.
    pub learned_1963_fsw_unit_by_lbd: [u64; BCP_LEARNED_1963_PRESSURE_LBD_BUCKETS],
    /// Learned 19-63 false-start-wrap conflict scans by LBD bucket.
    pub learned_1963_fsw_conflict_by_lbd: [u64; BCP_LEARNED_1963_PRESSURE_LBD_BUCKETS],
    /// Learned 19-63 false-start-wrap unit scan steps by LBD bucket.
    pub learned_1963_fsw_unit_steps_by_lbd: [u64; BCP_LEARNED_1963_PRESSURE_LBD_BUCKETS],
    /// Learned 19-63 false-start-wrap conflict scan steps by LBD bucket.
    pub learned_1963_fsw_conflict_steps_by_lbd: [u64; BCP_LEARNED_1963_PRESSURE_LBD_BUCKETS],
    /// Learned 19-63 false-start-wrap unit scans by used bucket: 0, 1, 2-4, 5+.
    pub learned_1963_fsw_unit_by_used: [u64; BCP_LEARNED_1963_PRESSURE_USED_BUCKETS],
    /// Learned 19-63 false-start-wrap conflict scans by used bucket.
    pub learned_1963_fsw_conflict_by_used: [u64; BCP_LEARNED_1963_PRESSURE_USED_BUCKETS],
    /// Learned 19-63 false-start-wrap unit scan steps by used bucket.
    pub learned_1963_fsw_unit_steps_by_used: [u64; BCP_LEARNED_1963_PRESSURE_USED_BUCKETS],
    /// Learned 19-63 false-start-wrap conflict scan steps by used bucket.
    pub learned_1963_fsw_conflict_steps_by_used: [u64; BCP_LEARNED_1963_PRESSURE_USED_BUCKETS],
    /// Learned 19-63 false-start-wrap counts by fixed clause-offset sketch bucket.
    pub learned_1963_fsw_repeat_by_bucket: [u64; BCP_LEARNED_1963_PRESSURE_REPEAT_BUCKETS],
    /// Learned 19-63 false-start-wrap steps by fixed clause-offset sketch bucket.
    pub learned_1963_fsw_repeat_steps_by_bucket: [u64; BCP_LEARNED_1963_PRESSURE_REPEAT_BUCKETS],
    /// Maximum count observed in one fixed clause-offset sketch bucket.
    pub learned_1963_fsw_repeat_bucket_max: u64,
    /// Whether learned 19-63 blocker-certified scan elision is enabled.
    pub learned_1963_blocker_cert_elision_enabled: bool,
    /// Whether learned 19-63 blocker-certificate shadow probing is enabled.
    pub learned_1963_blocker_cert_shadow_enabled: bool,
    /// Whether false-rejected learned 19-63 blocker certificates are demoted.
    pub learned_1963_blocker_cert_false_reject_demote_enabled: bool,
    /// Learned 19-63 blocker-certificate lookup candidates.
    pub learned_1963_blocker_cert_candidates: u64,
    /// Learned 19-63 replacement scans elided by a validated true certificate.
    pub learned_1963_blocker_cert_elisions: u64,
    /// Learned 19-63 shadow probes whose certificate would have elided.
    pub learned_1963_blocker_cert_shadow_hits: u64,
    /// Shadow probes where the normal scan selected a different replacement.
    pub learned_1963_blocker_cert_shadow_mismatches: u64,
    /// Mismatched learned 19-63 blocker certificates cleared by demotion.
    pub learned_1963_blocker_cert_mismatch_demotions: u64,
    /// Learned 19-63 blocker certificates populated/refreshed.
    pub learned_1963_blocker_cert_populates: u64,
    /// Learned 19-63 blocker certificates rejected as stale.
    pub learned_1963_blocker_cert_stale_rejects: u64,
    /// Learned 19-63 blocker certificates rejected because the literal was not true.
    pub learned_1963_blocker_cert_false_rejects: u64,
    /// False-rejected learned 19-63 blocker certificates cleared by demotion.
    pub learned_1963_blocker_cert_false_reject_demotions: u64,
    /// Learned 19-63 blocker certificates rejected by repeat guard.
    pub learned_1963_blocker_cert_repeat_rejects: u64,
    /// Suffix slots elided after blocker-certificate prefix validation.
    pub learned_1963_blocker_cert_elided_suffix_slots: u64,
    /// Suffix slots shadow hits would have elided after prefix validation.
    pub learned_1963_blocker_cert_shadow_elided_suffix_slots: u64,
    /// Certificate/elision events seeded from false-start-wrap scans.
    pub learned_1963_blocker_cert_affected_fsw_rows: u64,
    /// Shadow hits seeded from false-start-wrap scans.
    pub learned_1963_blocker_cert_shadow_affected_fsw_rows: u64,
    /// Whether the default-off learned 6-17 creation-time tail reorder gate is enabled.
    pub learned_617_tail_reorder_enabled: bool,
    /// Eligible learned 6-17 clauses observed while the creation-time tail reorder is active.
    pub learned_617_tail_reorder_candidates: u64,
    /// Eligible learned 6-17 clauses whose tail reorder ran.
    pub learned_617_tail_reorder_exercised: u64,
    /// Eligible learned 6-17 clauses whose tail order changed.
    pub learned_617_tail_reorder_changed: u64,
    /// Adjacent swaps made while reordering learned 6-17 tails.
    pub learned_617_tail_reorder_swaps: u64,
    /// Whether the default-off learned length-18 creation-time tail reorder gate is enabled.
    pub learned_18_tail_reorder_enabled: bool,
    /// Eligible learned length-18 clauses observed while the creation-time tail reorder is active.
    pub learned_18_tail_reorder_candidates: u64,
    /// Eligible learned length-18 clauses whose tail reorder ran.
    pub learned_18_tail_reorder_exercised: u64,
    /// Eligible learned length-18 clauses whose tail order changed.
    pub learned_18_tail_reorder_changed: u64,
    /// Adjacent swaps made while reordering learned length-18 tails.
    pub learned_18_tail_reorder_swaps: u64,
    /// Whether the default-off learned 19-63 creation-time tail reorder gate is enabled.
    pub learned_1963_tail_reorder_enabled: bool,
    /// Eligible learned clauses observed while the creation-time tail reorder is active.
    pub learned_1963_tail_reorder_candidates: u64,
    /// Eligible learned clauses whose tail order changed.
    pub learned_1963_tail_reorder_changed: u64,
    /// Adjacent swaps made while reordering learned 19-63 tails.
    pub learned_1963_tail_reorder_swaps: u64,
    /// Optional budget for learned 19-63 creation-time tail reorder.
    pub learned_1963_tail_reorder_swap_budget: Option<u64>,
    /// Eligible learned 19-63 clauses seen by the budgeted tail reorder.
    pub learned_1963_tail_reorder_budget_candidates: u64,
    /// Budgeted learned 19-63 tail reorders applied.
    pub learned_1963_tail_reorder_budget_applied: u64,
    /// Budgeted learned 19-63 tail reorders skipped because swaps exceeded budget.
    pub learned_1963_tail_reorder_budget_skipped_over_budget: u64,
    /// Adjacent swaps applied by budgeted learned 19-63 tail reorder.
    pub learned_1963_tail_reorder_budget_swaps_applied: u64,
    /// Adjacent swaps skipped by budgeted learned 19-63 tail reorder.
    pub learned_1963_tail_reorder_budget_swaps_skipped: u64,
}

/// Top learned 19-63 clause identity pressure row.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct BcpLearned1963IdentityRow {
    pub clause_id: u64,
    pub clause_offset: u64,
    pub clause_len: u64,
    pub birth_conflict: u64,
    pub last_conflict: u64,
    pub age_conflicts: u64,
    pub lbd: u64,
    pub used: u64,
    pub activity_milli: u64,
    pub scans: u64,
    pub scan_steps: u64,
    pub replacement_scans: u64,
    pub replacement_steps: u64,
    pub true_replacements: u64,
    pub unassigned_replacements: u64,
    pub no_replacement_scans: u64,
    pub no_replacement_steps: u64,
    pub unit: u64,
    pub conflict: u64,
    pub saved_start_false: u64,
    pub wrapped: u64,
    pub fsw: u64,
    pub fsw_steps: u64,
    pub fsw_unit_steps: u64,
    pub fsw_conflict_steps: u64,
    pub repeat_scans: u64,
    pub repeat_steps: u64,
    pub fsw_repeat_steps: u64,
    pub max_scan_steps: u64,
}

fn bcp_learned_1963_identity_row_from_record(
    record: BcpLearned1963IdentityRecord,
) -> BcpLearned1963IdentityRow {
    BcpLearned1963IdentityRow {
        clause_id: record.clause_id,
        clause_offset: record.clause_offset,
        clause_len: record.clause_len,
        birth_conflict: record.birth_conflict,
        last_conflict: record.last_conflict,
        age_conflicts: record.age_conflicts,
        lbd: record.lbd,
        used: record.used,
        activity_milli: record.activity_milli,
        scans: record.scans,
        scan_steps: record.scan_steps,
        replacement_scans: record.replacement_scans,
        replacement_steps: record.replacement_steps,
        true_replacements: record.true_replacements,
        unassigned_replacements: record.unassigned_replacements,
        no_replacement_scans: record.no_replacement_scans,
        no_replacement_steps: record.no_replacement_steps,
        unit: record.unit,
        conflict: record.conflict,
        saved_start_false: record.saved_start_false,
        wrapped: record.wrapped,
        fsw: record.fsw,
        fsw_steps: record.fsw_steps,
        fsw_unit_steps: record.fsw_unit_steps,
        fsw_conflict_steps: record.fsw_conflict_steps,
        repeat_scans: record.repeat_scans,
        repeat_steps: record.repeat_steps,
        fsw_repeat_steps: record.fsw_repeat_steps,
        max_scan_steps: record.max_scan_steps,
    }
}

/// Exact learned 19-63 clause identity pressure diagnostics.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct BcpLearned1963IdentityStats {
    pub enabled: bool,
    pub exact_identity_rows: u64,
    pub row_limit: u64,
    pub total_scans: u64,
    pub total_scan_steps: u64,
    pub replacement_scans: u64,
    pub replacement_steps: u64,
    pub true_replacements: u64,
    pub unassigned_replacements: u64,
    pub no_replacement_scans: u64,
    pub no_replacement_steps: u64,
    pub unit: u64,
    pub conflict: u64,
    pub fsw_scans: u64,
    pub fsw_steps: u64,
    pub repeat_scans: u64,
    pub repeat_steps: u64,
    pub fsw_repeat_steps: u64,
    pub topk_scan_steps: u64,
    pub topk_pressure_share_ppm: u64,
    pub topk_fsw_steps: u64,
    pub topk_fsw_pressure_share_ppm: u64,
    pub scans_per_conflict_x1000: u64,
    pub steps_per_conflict_x1000: u64,
    pub age_steps_by_bucket: [u64; BCP_LEARNED_1963_IDENTITY_AGE_BUCKETS],
    pub fsw_age_steps_by_bucket: [u64; BCP_LEARNED_1963_IDENTITY_AGE_BUCKETS],
    pub lbd_steps_by_bucket: [u64; BCP_LEARNED_1963_PRESSURE_LBD_BUCKETS],
    pub used_steps_by_bucket: [u64; BCP_LEARNED_1963_PRESSURE_USED_BUCKETS],
    pub activity_steps_by_bucket: [u64; BCP_LEARNED_1963_IDENTITY_ACTIVITY_BUCKETS],
    pub rows: Vec<BcpLearned1963IdentityRow>,
    pub fsw_rows: Vec<BcpLearned1963IdentityRow>,
}

/// Default-off learned 19-63 pressure-aware reduce_db diagnostics.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Learned1963PressureReductionStats {
    pub enabled: bool,
    pub candidates: u64,
    pub pressure_candidates: u64,
    pub ranked: u64,
    pub rank_bias_total: u64,
    pub selected: u64,
    pub selected_steps: u64,
    pub deleted: u64,
    pub deleted_steps: u64,
    pub kept: u64,
    pub kept_steps: u64,
    pub skipped_no_pressure: u64,
    pub lrat_retained_delete_skips: u64,
}

/// Default-off learned 19-63 pressure-aware reduce_db retention diagnostics.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Learned1963PressureRetentionStats {
    pub enabled: bool,
    pub candidates: u64,
    pub pressure_candidates: u64,
    pub ranked: u64,
    pub rank_bias_total: u64,
    pub selected: u64,
    pub selected_steps: u64,
    pub deleted: u64,
    pub deleted_steps: u64,
    pub kept: u64,
    pub kept_steps: u64,
    pub skipped_no_pressure: u64,
    pub lrat_retained_delete_skips: u64,
}

/// LRAT level-0 unit materialization and unit-chain diagnostics.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct LratMaterializationStats {
    /// Standard materialization calls.
    pub materialize_calls: u64,
    /// Minimize-chain materialization calls.
    pub materialize_minimize_calls: u64,
    /// Root-trail entries scanned by standard materialization.
    pub materialize_root_trail_entries: u64,
    /// Root-trail entries scanned by minimize-chain materialization.
    pub materialize_minimize_root_trail_entries: u64,
    /// Visible derived unit proof lines emitted by standard materialization.
    pub materialize_emitted_unit_lines: u64,
    /// Visible derived unit proof lines emitted by minimize-chain materialization.
    pub materialize_minimize_emitted_unit_lines: u64,
    /// LRAT hint IDs used by visible standard materialized unit lines.
    pub materialize_unit_hints: u64,
    /// LRAT hint IDs used by visible minimize-chain materialized unit lines.
    pub materialize_minimize_unit_hints: u64,
    /// Maximum hint count on one visible standard materialized unit line.
    pub materialize_unit_max_hints: u64,
    /// Maximum hint count on one visible minimize-chain materialized unit line.
    pub materialize_minimize_unit_max_hints: u64,
    /// Standard materialization attempts skipped because the hint chain was incomplete.
    pub materialize_incomplete_chains: u64,
    /// Minimize materialization attempts skipped because the hint chain was incomplete.
    pub materialize_minimize_incomplete_chains: u64,
    /// Standard materialization fallbacks emitted as hidden TrustedTransform units.
    pub materialize_hidden_trusted_units: u64,
    /// Unit-chain collection calls.
    pub unit_chain_calls: u64,
    /// Root-trail entries scanned by unit-chain collection.
    pub unit_chain_root_trail_entries: u64,
    /// LRAT hint IDs emitted by unit-chain collection.
    pub unit_chain_hints: u64,
    /// Maximum hint count emitted by one unit-chain collection.
    pub unit_chain_max_hints: u64,
    /// Unit-chain candidates that lacked an externally visible LRAT hint ID.
    pub unit_chain_missing_hints: u64,
}

impl Solver {
    /// Return the number of user-visible variables.
    pub fn user_num_vars(&self) -> usize {
        self.user_num_vars
    }

    /// Return the total number of variables, including internal scope selectors.
    pub fn total_num_vars(&self) -> usize {
        self.num_vars
    }

    /// Get the number of conflicts encountered during solving
    pub fn num_conflicts(&self) -> u64 {
        self.num_conflicts
    }

    /// #lra-inc-engine (S1): incremental-reset hits in the incremental QF_LRA
    /// engine lane — the objective proof that SAT state persisted across
    /// check-sats. See `SolverStats::ext_incremental_reset_hits`.
    pub fn ext_incremental_reset_hits(&self) -> u64 {
        self.stats.ext_incremental_reset_hits
    }

    /// #lra-inc-engine (S1): full-reset fallbacks in the incremental QF_LRA
    /// engine lane. See `SolverStats::ext_full_reset_hits`.
    pub fn ext_full_reset_hits(&self) -> u64 {
        self.stats.ext_full_reset_hits
    }

    /// IC3/assumption-cache hits (#8443): incremental resets taken on the
    /// assumption-based solve path (used by the inc-engine lane's scoped
    /// push/pop check-sats to confirm state persistence).
    pub fn assumption_cache_hits(&self) -> u64 {
        self.stats.assumption_cache_hits
    }

    /// IC3/assumption-cache misses (#8443): full resets on the assumption-based
    /// solve path.
    pub fn assumption_cache_misses(&self) -> u64 {
        self.stats.assumption_cache_misses
    }

    /// Cumulative conflict count across all incremental solve calls (#8208).
    ///
    /// Returns `lifetime_conflicts + num_conflicts` where `lifetime_conflicts`
    /// accumulates prior solves' conflict counts and `num_conflicts` is the
    /// current solve's count. Used for inprocessing scheduling so thresholds
    /// progress across IC3/PDR's many tiny incremental solves.
    #[inline]
    pub(super) fn total_conflicts(&self) -> u64 {
        self.cold
            .lifetime_conflicts
            .saturating_add(self.num_conflicts)
    }

    #[inline(always)]
    pub(super) fn bcp_learned_1963_blocker_cert_elision_enabled_internal(&self) -> bool {
        cold::bcp_learned_1963_blocker_cert_elision_env_enabled()
            || self
                .stats
                .bcp_learned_1963_blocker_cert_elision_test_enabled()
    }

    #[inline(always)]
    pub(super) fn bcp_learned_1963_blocker_cert_shadow_enabled_internal(&self) -> bool {
        cold::bcp_learned_1963_blocker_cert_shadow_env_enabled()
            || self
                .stats
                .bcp_learned_1963_blocker_cert_shadow_test_enabled()
    }

    #[inline(always)]
    pub(super) fn bcp_learned_1963_blocker_cert_false_reject_demote_enabled_internal(
        &self,
    ) -> bool {
        cold::bcp_learned_1963_blocker_cert_false_reject_demote_env_enabled()
            || self
                .stats
                .bcp_learned_1963_blocker_cert_false_reject_demote_test_enabled()
    }

    /// Get the number of restarts performed during solving
    pub fn num_restarts(&self) -> u64 {
        self.cold.restarts
    }

    /// Lifetime-inclusive counters (#qfuflia-stats): the incremental split
    /// loop calls `reset_search_state` every round, zeroing the per-solve
    /// counters — so end-of-solve reporting through `num_*` reflected ONLY the
    /// last round (observed: "decisions: 550, restarts: 0" for a 10s
    /// hash_sat run whose true totals were ~138k decisions / 46 restarts).
    /// These return `lifetime + current`.
    pub fn total_num_conflicts(&self) -> u64 {
        self.cold
            .lifetime_conflicts
            .saturating_add(self.num_conflicts)
    }

    /// Lifetime-inclusive decision count (see [`Self::total_num_conflicts`]).
    pub fn total_num_decisions(&self) -> u64 {
        self.cold
            .lifetime_decisions
            .saturating_add(self.num_decisions)
    }

    /// Lifetime-inclusive propagation count (see [`Self::total_num_conflicts`]).
    pub fn total_num_propagations(&self) -> u64 {
        self.cold
            .lifetime_propagations
            .saturating_add(self.num_propagations)
    }

    /// Lifetime-inclusive restart count (see [`Self::total_num_conflicts`]).
    pub fn total_num_restarts(&self) -> u64 {
        self.cold
            .lifetime_restarts
            .saturating_add(self.cold.restarts)
    }

    /// Get the number of cold restarts performed (Zhang et al. 2024).
    pub fn num_cold_restarts(&self) -> u64 {
        self.stats.cold_restarts
    }

    /// Restart decision attribution by primary trigger and current mode.
    pub fn restart_attribution_stats(&self) -> RestartAttributionStats {
        let cause = self.stats.restart_attribution;
        let mode = self.stats.restart_attribution_modes;
        RestartAttributionStats {
            geometric: cause[RestartAttribution::Geometric.index()],
            theory_luby: cause[RestartAttribution::TheoryLuby.index()],
            stable_reluctant: cause[RestartAttribution::StableReluctant.index()],
            stable_ema: cause[RestartAttribution::StableEma.index()],
            focused_ema: cause[RestartAttribution::FocusedEma.index()],
            focused_luby: cause[RestartAttribution::FocusedLuby.index()],
            focused_mode: mode[0],
            stable_mode: mode[1],
        }
    }

    /// Rephase attribution by selected strategy, mode, and observable effects.
    pub fn rephase_attribution_stats(&self) -> RephaseAttributionStats {
        let kind = self.stats.rephase_attribution;
        let mode = self.stats.rephase_attribution_modes;
        RephaseAttributionStats {
            original: kind[RephaseAttribution::Original.index()],
            inverted: kind[RephaseAttribution::Inverted.index()],
            best: kind[RephaseAttribution::Best.index()],
            random: kind[RephaseAttribution::Random.index()],
            flip: kind[RephaseAttribution::Flip.index()],
            walk: kind[RephaseAttribution::Walk.index()],
            focused_mode: mode[0],
            stable_mode: mode[1],
            direct_changed_phases: self.stats.rephase_direct_changed_phases,
            target_phase_updates: self.stats.rephase_target_phase_updates,
            best_resets: self.stats.rephase_best_resets,
        }
    }

    /// Get the number of decisions made during solving
    pub fn num_decisions(&self) -> u64 {
        self.num_decisions
    }

    /// Get the currently active branching heuristic.
    pub fn active_branch_heuristic(&self) -> BranchHeuristic {
        self.active_branch_heuristic
    }

    /// Get the branch-selector policy currently controlling heuristic choice.
    pub fn branch_selector_mode(&self) -> BranchSelectorMode {
        self.cold.branch_selector_mode
    }

    /// Get per-arm heuristic reward statistics in `[EVSIDS, VMTF]` order.
    pub fn branch_heuristic_epoch_stats(
        &self,
    ) -> [BranchHeuristicStats; crate::mab::NUM_BRANCH_HEURISTIC_ARMS] {
        self.cold.branch_mab.arm_stats()
    }

    /// Get total search ticks (focused + stable modes combined).
    ///
    /// Search ticks approximate memory-access cost and drive all
    /// effort-proportional scheduling (vivify, walk, backbone, sweep).
    pub fn total_search_ticks(&self) -> u64 {
        self.search_ticks[0] + self.search_ticks[1]
    }

    /// Get the number of propagations performed during solving
    pub fn num_propagations(&self) -> u64 {
        self.num_propagations
    }

    /// Get the number of chronological backtracks performed during solving
    pub fn num_chrono_backtracks(&self) -> u64 {
        self.stats.chrono_backtracks
    }

    /// Approximate-BCP filter (#8789 Phase 2): number of active clauses the
    /// filter correctly classified as `NoopLikely` on the current trail.
    /// Divided by total filter invocations, this is the Phase 3 skip-rate
    /// upper bound. Always `0` when the `approx-bcp-filter` feature is off.
    pub fn approx_bcp_noop_matched(&self) -> u64 {
        self.stats.approx_bcp_noop_matched
    }

    /// Approximate-BCP filter (#8789 Phase 2): number of active clauses the
    /// filter correctly classified as "maybe unit or falsified" (the exact
    /// trail check confirmed unit/falsified). Always `0` when the
    /// `approx-bcp-filter` feature is off.
    pub fn approx_bcp_conflict_matched(&self) -> u64 {
        self.stats.approx_bcp_conflict_matched
    }

    /// Approximate-BCP filter (#8789 Phase 2): **soundness alarm counter**.
    /// Any nonzero value indicates the filter said "skip" for a clause that
    /// was actually unit or falsified — a correctness bug. Always `0` when
    /// the `approx-bcp-filter` feature is off.
    pub fn approx_bcp_mismatch_detected(&self) -> u64 {
        self.stats.approx_bcp_mismatch_detected
    }

    /// Get the number of block-UIP shrink attempts during conflict analysis.
    pub fn shrink_block_attempts(&self) -> u64 {
        self.stats.shrink_block_attempts
    }

    /// Get the number of successful block-UIP replacements.
    pub fn shrink_block_successes(&self) -> u64 {
        self.stats.shrink_block_successes
    }

    /// Get learned-clause shrink/LRAT snapshot diagnostics (#9102):
    /// (singleton fast-path skips, LRAT removed-literal snapshot copies, copied literals,
    /// LRAT singleton-guard snapshot skips, removed-literal chain calls).
    pub fn learned_lrat_snapshot_stats(&self) -> (u64, u64, u64, u64, u64) {
        (
            self.stats.shrink_singleton_fast_path_skips,
            self.stats.lrat_original_learned_snapshot_copies,
            self.stats.lrat_original_learned_snapshot_literals,
            self.stats.lrat_original_learned_snapshot_singleton_skips,
            self.stats.lrat_removed_literal_chain_calls,
        )
    }

    /// Get the number of random decisions made during solving
    pub fn num_random_decisions(&self) -> u64 {
        self.stats.random_decisions
    }

    /// Get the number of forced-literal early returns (skip 1UIP).
    pub fn num_forced_backtracks(&self) -> u64 {
        self.stats.forced_backtracks
    }

    /// LSCB (#8442) missed lower implication statistics.
    /// Returns (detected, reimplied, used_in_analysis).
    pub fn mli_stats(&self) -> (u64, u64, u64) {
        (
            self.stats.mli_detected,
            self.stats.mli_reimplied,
            self.stats.mli_used_in_analysis,
        )
    }

    /// Get focused-mode EMA restart check/fire counts (diagnostic).
    pub fn focused_ema_stats(&self) -> (u64, u64) {
        (self.stats.focused_ema_checks, self.stats.focused_ema_fires)
    }

    /// Get stable-mode reluctant fire count (diagnostic).
    pub fn stable_reluctant_fires(&self) -> u64 {
        self.stats.stable_reluctant_fires
    }

    /// Get stable-mode Glucose EMA fire count (diagnostic, #7998).
    pub fn stable_ema_fires(&self) -> u64 {
        self.stats.stable_ema_fires
    }

    /// Get current LBD EMA values (diagnostic).
    pub fn lbd_ema_values(&self) -> (f64, f64) {
        (self.cold.lbd_ema_fast, self.cold.lbd_ema_slow)
    }

    /// Get the number of MAB arm switches (branch heuristic changes via UCB1).
    pub fn mab_arm_switches(&self) -> u64 {
        self.stats.mab_arm_switches
    }

    /// Get the number of focused/stable mode switches (diagnostic).
    pub fn mode_switch_count(&self) -> u64 {
        self.cold.mode_switch_count
    }

    /// Get the number of focused-mode EMA restart blocked by conflict gate.
    pub fn focused_ema_blocked_by_conflict_gate(&self) -> u64 {
        self.stats.focused_ema_blocked_by_conflict_gate
    }

    /// Get the current focused-mode conflict gate.
    pub fn focused_restart_gate(&self) -> u64 {
        self.cold.focused_restart_gate
    }

    /// Get dense-mutex focused restart gate update count.
    pub fn dense_mutex_focused_restart_gate_updates(&self) -> u64 {
        self.stats.dense_mutex_focused_restart_gate_updates
    }

    /// Get dense-mutex focused restart runtime check count.
    pub fn dense_mutex_focused_restart_runtime_checked(&self) -> u64 {
        self.stats.dense_mutex_focused_restart_runtime_checked
    }

    /// Get active variables at the dense-mutex focused restart runtime check.
    pub fn dense_mutex_focused_restart_active_vars(&self) -> u64 {
        self.stats.dense_mutex_focused_restart_active_vars
    }

    /// Get active clauses at the dense-mutex focused restart runtime check.
    pub fn dense_mutex_focused_restart_active_clauses(&self) -> u64 {
        self.stats.dense_mutex_focused_restart_active_clauses
    }

    /// Get active binary clauses at the dense-mutex focused restart runtime check.
    pub fn dense_mutex_focused_restart_active_binary_clauses(&self) -> u64 {
        self.stats.dense_mutex_focused_restart_active_binary_clauses
    }

    /// Get whether the runtime dense-mutex focused restart candidate predicate held.
    pub fn dense_mutex_focused_restart_runtime_candidate(&self) -> bool {
        self.stats.dense_mutex_focused_restart_runtime_candidate != 0
    }

    /// Get focused restart gate before the dense-mutex runtime check.
    pub fn dense_mutex_focused_restart_previous_gate(&self) -> u64 {
        self.stats.dense_mutex_focused_restart_previous_gate
    }

    /// Get computed dense-mutex focused restart gate, or zero if not a candidate.
    pub fn dense_mutex_focused_restart_computed_gate(&self) -> u64 {
        self.stats.dense_mutex_focused_restart_computed_gate
    }

    /// Return whether variant routing enabled the dense-clique MAB branch route.
    pub fn dense_clique_mab_branch_route_enabled(&self) -> bool {
        self.stats.dense_clique_mab_branch_route_enabled != 0
    }

    /// Return the number of branch decisions made under the dense-clique MAB route.
    pub fn dense_clique_mab_branch_route_exercise_count(&self) -> u64 {
        self.stats.dense_clique_mab_branch_route_exercised
    }

    /// Return whether the dense-clique MAB branch route was exercised at least once.
    pub fn dense_clique_mab_branch_route_exercised(&self) -> bool {
        self.dense_clique_mab_branch_route_exercise_count() != 0
    }

    /// Get the number of restarts blocked by trail-length heuristic (#8449).
    pub fn trail_blocked_restarts(&self) -> u64 {
        self.stats.trail_blocked_restarts
    }

    /// Return whether Glucose-style EMA restarts are enabled.
    pub fn glucose_restarts_enabled(&self) -> bool {
        self.cold.glucose_restarts
    }

    /// Return the configured Luby restart base interval.
    pub fn restart_base(&self) -> u64 {
        self.cold.restart_base
    }

    /// Get the per-decision random variable frequency.
    pub fn random_var_freq(&self) -> f64 {
        self.cold.random_var_freq
    }

    /// Get the active geometric restart schedule, if enabled.
    pub fn geometric_restart_config(&self) -> Option<(f64, f64)> {
        self.cold
            .geometric_restarts
            .then_some((self.cold.geometric_initial, self.cold.geometric_factor))
    }

    /// Get the number of clauses removed by per-conflict eager subsumption.
    pub fn num_eager_subsumptions(&self) -> u64 {
        self.cold.num_eager_subsumptions
    }

    /// Get the number of OTFS trigger events during conflict analysis.
    pub fn otfs_subsumed(&self) -> u64 {
        self.stats.otfs_subsumed
    }

    /// Get the number of reason clauses strengthened by OTFS.
    pub fn otfs_strengthened(&self) -> u64 {
        self.stats.otfs_strengthened
    }

    /// OTFS diagnostic: number of OTFS candidates (resolvent < antecedent).
    pub fn otfs_candidates(&self) -> u64 {
        self.stats.otfs_candidates
    }

    /// OTFS diagnostic: blocked by open==0.
    pub fn otfs_blocked_open0(&self) -> u64 {
        self.stats.otfs_blocked_open0
    }

    /// OTFS diagnostic: blocked by watch invariant.
    pub fn otfs_blocked_watch(&self) -> u64 {
        self.stats.otfs_blocked_watch
    }

    /// OTFS diagnostic: blocked by otfs_strengthen returning false.
    pub fn otfs_blocked_strengthen(&self) -> u64 {
        self.stats.otfs_blocked_strengthen
    }

    /// OTFS Branch B: strengthened clause was asserting (skip learning).
    pub fn otfs_branch_b(&self) -> u64 {
        self.stats.otfs_branch_b
    }

    /// OTFS Branch C: analysis restarted from strengthened clause.
    pub fn otfs_branch_c(&self) -> u64 {
        self.stats.otfs_branch_c
    }

    /// OTFS on-the-fly subsumption: conflict clause subsumed by strengthened reason.
    pub fn otfs_clause_subsumed(&self) -> u64 {
        self.stats.otfs_clause_subsumed
    }

    /// Get the number of aggressive clause flushes performed (CaDiCaL flush).
    pub fn num_flushes(&self) -> u64 {
        self.cold.num_flushes
    }

    /// Get the number of arena locality compactions performed.
    ///
    /// Arena compaction reorders clauses in VMTF decision-queue order for
    /// cache locality (CaDiCaL arenatype=3). Triggered after reduce_db when
    /// dead space exceeds the adaptive threshold.
    pub fn num_arena_compactions(&self) -> u64 {
        self.cold.num_arena_compactions
    }

    /// Get the number of reduce_db calls performed.
    pub fn num_reductions(&self) -> u64 {
        self.cold.num_reductions
    }

    /// Get the number of learned clauses eagerly subsumed per-conflict.
    pub fn eager_subsumed(&self) -> u64 {
        self.cold.eager_subsumed
    }

    /// Unified total subsumption count aggregating all sources (#8368, #8502).
    ///
    /// CaDiCaL's `stats.subsumed` aggregates subsumptions from 7+ sources.
    /// AY previously only reported forward subsumption in `--stats` output,
    /// making it appear that AY does far less subsumption than CaDiCaL.
    ///
    /// Sources:
    /// - Forward subsumption (`subsume_stats().forward_subsumed`)
    /// - Backward BVE subsumption (`bve_stats().backward_subsumed`)
    /// - OTFS clause subsumption (`otfs_clause_subsumed` in solver_stats)
    /// - Eager subsumption (`eager_subsumed` in cold)
    /// - Vivification inline + analysis subsumption (`vivify_stats()`)
    /// - Congruence forward subsumption (`congruence_stats().congruence_subsumed`)
    /// - Deduplication (`dedup_deleted` in solver_stats)
    pub fn total_subsumed(&self) -> u64 {
        let fwd = self.inproc.subsumer.stats().forward_subsumed;
        let bve_bw = self.inproc.bve.stats().backward_subsumed;
        let otfs = self.stats.otfs_clause_subsumed;
        let eager = self.cold.eager_subsumed;
        let vivify_inline = self.inproc.vivifier.stats().inline_subsumed;
        let vivify_analysis = self.inproc.vivifier.stats().analysis_subsumed;
        let congruence = self.inproc.congruence.stats().congruence_subsumed;
        let dedup = self.stats.dedup_deleted;
        fwd + bve_bw + otfs + eager + vivify_inline + vivify_analysis + congruence + dedup
    }

    /// Get default-off exact learned 19-63 clause-identity pressure counters.
    pub fn bcp_learned_1963_identity_stats(&self, top_k: usize) -> BcpLearned1963IdentityStats {
        let Some(table) = self.stats.bcp_learned_1963_identity_table() else {
            return BcpLearned1963IdentityStats {
                enabled: self.cold.bcp_learned_1963_identity_profile,
                row_limit: top_k as u64,
                ..BcpLearned1963IdentityStats::default()
            };
        };
        let rows: Vec<_> = table
            .top_rows(top_k)
            .into_iter()
            .map(bcp_learned_1963_identity_row_from_record)
            .collect();
        let fsw_rows: Vec<_> = table
            .top_fsw_rows(top_k)
            .into_iter()
            .map(bcp_learned_1963_identity_row_from_record)
            .collect();
        let topk_scan_steps = rows.iter().map(|row| row.scan_steps).sum::<u64>();
        let topk_pressure_share_ppm = topk_scan_steps
            .saturating_mul(1_000_000)
            .checked_div(table.total_scan_steps)
            .unwrap_or(0);
        let topk_fsw_steps = table.top_fsw_scan_steps(top_k);
        let topk_fsw_pressure_share_ppm = topk_fsw_steps
            .saturating_mul(1_000_000)
            .checked_div(table.fsw_steps)
            .unwrap_or(0);
        let conflicts = self.num_conflicts.max(1);
        BcpLearned1963IdentityStats {
            enabled: self.cold.bcp_learned_1963_identity_profile,
            exact_identity_rows: table.exact_identity_rows(),
            row_limit: top_k as u64,
            total_scans: table.total_scans,
            total_scan_steps: table.total_scan_steps,
            replacement_scans: table.replacement_scans,
            replacement_steps: table.replacement_steps,
            true_replacements: table.true_replacements,
            unassigned_replacements: table.unassigned_replacements,
            no_replacement_scans: table.no_replacement_scans,
            no_replacement_steps: table.no_replacement_steps,
            unit: table.unit,
            conflict: table.conflict,
            fsw_scans: table.fsw_scans,
            fsw_steps: table.fsw_steps,
            repeat_scans: table.repeat_scans,
            repeat_steps: table.repeat_steps,
            fsw_repeat_steps: table.fsw_repeat_steps,
            topk_scan_steps,
            topk_pressure_share_ppm,
            topk_fsw_steps,
            topk_fsw_pressure_share_ppm,
            scans_per_conflict_x1000: table.total_scans.saturating_mul(1000) / conflicts,
            steps_per_conflict_x1000: table.total_scan_steps.saturating_mul(1000) / conflicts,
            age_steps_by_bucket: table.age_steps_by_bucket,
            fsw_age_steps_by_bucket: table.fsw_age_steps_by_bucket,
            lbd_steps_by_bucket: table.lbd_steps_by_bucket,
            used_steps_by_bucket: table.used_steps_by_bucket,
            activity_steps_by_bucket: table.activity_steps_by_bucket,
            rows,
            fsw_rows,
        }
    }

    /// Get default-off learned 19-63 pressure-aware reduce_db counters.
    pub fn learned_1963_pressure_reduction_stats(&self) -> Learned1963PressureReductionStats {
        Learned1963PressureReductionStats {
            enabled: self.cold.bcp_learned_1963_pressure_reduction,
            candidates: self.stats.learned_1963_pressure_reduction_candidates,
            pressure_candidates: self
                .stats
                .learned_1963_pressure_reduction_pressure_candidates,
            ranked: self.stats.learned_1963_pressure_reduction_ranked,
            rank_bias_total: self.stats.learned_1963_pressure_reduction_rank_bias_total,
            selected: self.stats.learned_1963_pressure_reduction_selected,
            selected_steps: self.stats.learned_1963_pressure_reduction_selected_steps,
            deleted: self.stats.learned_1963_pressure_reduction_deleted,
            deleted_steps: self.stats.learned_1963_pressure_reduction_deleted_steps,
            kept: self.stats.learned_1963_pressure_reduction_kept,
            kept_steps: self.stats.learned_1963_pressure_reduction_kept_steps,
            skipped_no_pressure: self
                .stats
                .learned_1963_pressure_reduction_skipped_no_pressure,
            lrat_retained_delete_skips: self
                .stats
                .learned_1963_pressure_reduction_lrat_retained_delete_skips,
        }
    }

    /// Get default-off learned 19-63 pressure-aware reduce_db retention counters.
    pub fn learned_1963_pressure_retention_stats(&self) -> Learned1963PressureRetentionStats {
        Learned1963PressureRetentionStats {
            enabled: self.cold.bcp_learned_1963_pressure_retention,
            candidates: self.stats.learned_1963_pressure_retention_candidates,
            pressure_candidates: self
                .stats
                .learned_1963_pressure_retention_pressure_candidates,
            ranked: self.stats.learned_1963_pressure_retention_ranked,
            rank_bias_total: self.stats.learned_1963_pressure_retention_rank_bias_total,
            selected: self.stats.learned_1963_pressure_retention_selected,
            selected_steps: self.stats.learned_1963_pressure_retention_selected_steps,
            deleted: self.stats.learned_1963_pressure_retention_deleted,
            deleted_steps: self.stats.learned_1963_pressure_retention_deleted_steps,
            kept: self.stats.learned_1963_pressure_retention_kept,
            kept_steps: self.stats.learned_1963_pressure_retention_kept_steps,
            skipped_no_pressure: self
                .stats
                .learned_1963_pressure_retention_skipped_no_pressure,
            lrat_retained_delete_skips: self
                .stats
                .learned_1963_pressure_retention_lrat_retained_delete_skips,
        }
    }

    /// Get the number of duplicate binary clauses deleted by deduplication (#8502).
    pub fn dedup_deleted(&self) -> u64 {
        self.stats.dedup_deleted
    }

    /// Get the number of completed inprocessing (inprobe) phases.
    pub fn inprobe_phases(&self) -> u64 {
        self.cold.inprobe_phases
    }

    /// Get cumulative per-pass inprocessing timings in nanoseconds.
    pub fn inprocessing_pass_times_ns(&self) -> Vec<(&'static str, u64)> {
        INPROCESS_TIMING_LABELS
            .iter()
            .copied()
            .zip(self.stats.inprocessing_time_ns)
            .collect()
    }

    /// Get cumulative per-pass inprocessing timings in milliseconds.
    pub fn inprocessing_pass_times_ms(&self) -> Vec<(&'static str, u64)> {
        self.inprocessing_pass_times_ns()
            .into_iter()
            .map(|(label, nanos)| (label, nanos / 1_000_000))
            .collect()
    }

    /// Get cumulative per-pass inprocessing attempt/run/yield counters.
    pub fn inprocessing_pass_accounting(&self) -> Vec<(&'static str, InprocessingPassAccounting)> {
        INPROCESS_ACCOUNTING_LABELS
            .iter()
            .copied()
            .enumerate()
            .map(|(index, label)| {
                (
                    label,
                    InprocessingPassAccounting {
                        attempts: self.stats.inprocessing_pass_attempts[index],
                        runs: self.stats.inprocessing_pass_runs[index],
                        yields: self.stats.inprocessing_pass_yields[index],
                    },
                )
            })
            .collect()
    }

    /// Get LRAT proof-clamped inprocessing eligibility counters.
    ///
    /// Returns `(bve_due_rounds, factor_due_rounds, probe_rescue_rounds)`.
    pub fn inprocessing_lrat_clamp_stats(&self) -> (u64, u64, u64) {
        (
            self.stats.inprocessing_lrat_clamped_bve_due_rounds,
            self.stats.inprocessing_lrat_clamped_factor_due_rounds,
            self.stats.inprocessing_lrat_probe_rescue_rounds,
        )
    }

    /// Get shared backbone scheduler/backoff state for SAT Main diagnostics.
    pub fn backbone_schedule_stats(&self) -> BackboneScheduleStats {
        let control = &self.inproc_ctrl.backbone;
        BackboneScheduleStats {
            enabled: control.enabled,
            phases: self.cold.backbone_phases,
            max_rounds: BACKBONE_MAX_ROUNDS,
            consecutive_empty: self.cold.backbone_consecutive_empty,
            stall_limit: BACKBONE_STALL_LIMIT,
            next_conflict: control.next_conflict,
            conflicts_until_next: control.next_conflict.saturating_sub(self.num_conflicts),
            backoff_interval: control.interval_used(),
            base_interval: BACKBONE_INTERVAL,
            max_interval: BACKBONE_MAX_INTERVAL,
            yield_rescue_cooldown_enabled: self.inprocessing_yield_rescue_backbone_cooldown_enabled,
            yield_rescue_cooldown_rounds: self
                .stats
                .inprocessing_yield_rescue_backbone_cooldown_rounds,
            yield_rescue_cooldown_interval: YIELD_RESCUE_BACKBONE_COOLDOWN_INTERVAL,
            bounded_zero_decompose_backoff_enabled: self
                .bounded_backbone_zero_decompose_backoff_enabled,
            bounded_next_conflict: self.cold.next_bounded_backbone_conflict,
            bounded_conflicts_until_next: self
                .cold
                .next_bounded_backbone_conflict
                .saturating_sub(self.num_conflicts),
            bounded_backoff_triggers: self.stats.bounded_backbone_backoff_triggers,
            bounded_runs: self.stats.bounded_backbone_runs,
            bounded_yields: self.stats.bounded_backbone_yields,
            bounded_ms: self.stats.bounded_backbone_ms,
            bounded_binary_suppressed: self.stats.bounded_backbone_binary_suppressed,
            due: control.should_fire(self.num_conflicts),
            stalled_by_empty: self.cold.backbone_consecutive_empty >= BACKBONE_STALL_LIMIT,
            rounds_exhausted: self.cold.backbone_phases >= BACKBONE_MAX_ROUNDS,
        }
    }

    /// Get GPU BVE telemetry counters.
    /// Returns (dispatches, ordered_pairs, tautological_resolvents).
    pub fn gpu_bve_stats(&self) -> (u64, u64, u64) {
        (
            self.stats.gpu_bve_dispatches,
            self.stats.gpu_bve_pairs,
            self.stats.gpu_bve_tautologies,
        )
    }

    /// Get the number of propagations performed via dense (occ-list) mode (#8088).
    pub fn dense_propagations(&self) -> u64 {
        self.stats.dense_propagations
    }

    /// Get the number of conflicts found via dense propagation (#8088).
    pub fn dense_conflicts(&self) -> u64 {
        self.stats.dense_conflicts
    }

    /// Get the number of satisfied clauses deleted during dense propagation (#8088).
    pub fn dense_satisfied_deleted(&self) -> u64 {
        self.stats.dense_satisfied_deleted
    }

    /// Get reduction L0-satisfied prepass stats.
    /// Returns (occ_scans, full_scans, no_occ_skips, deleted).
    pub fn reduction_l0_satisfied_prepass_stats(&self) -> (u64, u64, u64, u64) {
        (
            self.stats.reduction_l0_satisfied_occ_scans,
            self.stats.reduction_l0_satisfied_full_scans,
            self.stats.reduction_l0_satisfied_no_occ_skips,
            self.stats.reduction_l0_satisfied_deleted,
        )
    }

    /// Get learned clause reduction telemetry.
    /// Returns (considered, deleted, reason_protected, ic3_protected,
    /// low_lbd_protected, usage_protected, target_kept,
    /// lrat_retained_delete_skips, hyper_deleted, hyper_kept).
    pub fn learned_reduction_telemetry_stats(
        &self,
    ) -> (u64, u64, u64, u64, u64, u64, u64, u64, u64, u64) {
        (
            self.stats.learned_reduction_considered,
            self.stats.learned_reduction_deleted,
            self.stats.learned_reduction_reason_protected,
            self.stats.learned_reduction_ic3_protected,
            self.stats.learned_reduction_low_lbd_protected,
            self.stats.learned_reduction_usage_protected,
            self.stats.learned_reduction_target_kept,
            self.stats.learned_reduction_lrat_retained_delete_skips,
            self.stats.learned_reduction_hyper_deleted,
            self.stats.learned_reduction_hyper_kept,
        )
    }

    /// Get learned reduction delete skips where LRAT retained the active clause.
    pub fn learned_reduction_lrat_retained_delete_skips(&self) -> u64 {
        self.stats.learned_reduction_lrat_retained_delete_skips
    }

    /// Get the number of dirty literals processed by flush_watches (#8101).
    pub fn flush_dirty_lits(&self) -> u64 {
        self.stats.flush_dirty_lits
    }

    /// Get the number of stale watch entries removed by flush_watches (#8101).
    pub fn flush_watches_removed(&self) -> u64 {
        self.stats.flush_watches_removed
    }

    /// Get the number of watch lists shrunk after reduce_db (#8031).
    pub fn watches_shrunk(&self) -> u64 {
        self.stats.watches_shrunk
    }

    /// Minimal trail rewind stats (#8095): rewinds where nothing was affected.
    pub fn trail_rewind_skipped(&self) -> u64 {
        self.stats.trail_rewind_skipped
    }

    /// Minimal trail rewind stats (#8095): partial rewinds (position > 0).
    pub fn trail_rewind_partial(&self) -> u64 {
        self.stats.trail_rewind_partial
    }

    /// Minimal trail rewind stats (#8095): full rewinds to position 0.
    pub fn trail_rewind_full(&self) -> u64 {
        self.stats.trail_rewind_full
    }

    /// Minimal trail rewind stats (#8095): cumulative trail entries saved.
    pub fn trail_rewind_saved_entries(&self) -> u64 {
        self.stats.trail_rewind_saved_entries
    }

    /// Get the number of propagations discovered by JIT-compiled BCP.
    pub fn jit_propagations(&self) -> u64 {
        self.stats.jit_propagations
    }

    /// Get the number of conflicts found by JIT-compiled BCP.
    pub fn jit_conflicts(&self) -> u64 {
        self.stats.jit_conflicts
    }

    /// Get the number of JIT function calls skipped by blocker pre-check (#8520).
    pub fn jit_blocker_skips(&self) -> u64 {
        self.stats.jit_blocker_skips
    }

    /// Get the number of trail literals dispatched to JIT path in hybrid BCP (#8517).
    pub fn jit_hybrid_jit_literals(&self) -> u64 {
        self.stats.jit_hybrid_jit_literals
    }

    /// Get the number of trail literals dispatched to 2WL path in hybrid BCP (#8517).
    pub fn jit_hybrid_2wl_literals(&self) -> u64 {
        self.stats.jit_hybrid_2wl_literals
    }

    /// Get the JIT compile time in microseconds.
    pub fn jit_compile_time_us(&self) -> u64 {
        self.stats.jit_compile_time_us
    }

    /// Get the number of clauses compiled into native JIT code.
    pub fn jit_clauses_compiled(&self) -> u64 {
        self.stats.jit_clauses_compiled
    }

    /// Get the number of learned clauses compiled into native JIT code (#8229).
    pub fn jit_learned_clauses_compiled(&self) -> u64 {
        self.stats.jit_learned_clauses_compiled
    }

    /// Get the number of 2WL watch entries detached for JIT-compiled clauses (#8005).
    pub fn jit_watches_detached(&self) -> u64 {
        self.stats.jit_watches_detached
    }

    /// Get the number of 2WL watch entries reattached after JIT invalidation (#8005).
    pub fn jit_watches_reattached(&self) -> u64 {
        self.stats.jit_watches_reattached
    }

    /// Get the number of inprocessing rounds where JIT recompilation was
    /// skipped because only deletion-only passes ran (#8128).
    pub fn jit_recompilations_skipped(&self) -> u64 {
        self.stats.jit_recompilations_skipped
    }

    /// Get the number of full JIT recompilations after structural inprocessing.
    pub fn jit_recompilations(&self) -> u64 {
        self.stats.jit_recompilations
    }

    /// Get the number of delta recompilations (reusing code for clean vars, #8228).
    pub fn jit_delta_recompilations(&self) -> u64 {
        self.stats.jit_delta_recompilations
    }

    /// Get the number of clause deletions handled by guard bits (#8202).
    pub fn jit_guard_deletions(&self) -> u64 {
        self.stats.jit_guard_deletions
    }

    /// Get the number of lazy JIT incremental compilation rounds (#8227).
    pub fn jit_incremental_compilations(&self) -> u64 {
        self.stats.jit_incremental_compilations
    }

    /// Get the total number of pairs compiled incrementally (#8227).
    pub fn jit_incremental_pairs(&self) -> u64 {
        self.stats.jit_incremental_pairs
    }

    /// Whether the most recent JIT compilation used rayon parallel codegen (#8224).
    pub fn jit_parallel_compiled(&self) -> bool {
        self.stats.jit_parallel_compiled
    }

    /// JIT incremental cache hits across solve() calls (#8225).
    pub fn jit_cache_hits(&self) -> u64 {
        self.stats.jit_cache_hits
    }

    /// JIT incremental cache misses across solve() calls (#8225).
    pub fn jit_cache_misses(&self) -> u64 {
        self.stats.jit_cache_misses
    }

    /// JIT: number of scoped clauses skipped during compilation (#8392).
    pub fn jit_scope_skipped_clauses(&self) -> u64 {
        self.stats.jit_scope_skipped_clauses
    }

    /// Canonical competition-gate evidence for SAT learned-clause candidates.
    ///
    /// The current learned-clause artifact is profile-only: it can extract and
    /// describe candidates, but no learned-clause native dispatch is installed in
    /// the SAT solver. Keep this flat application counter at zero until a real
    /// dispatch path exists so the competition gate does not mistake profile
    /// metadata for native-code execution.
    pub fn sat_learned_clause_candidate_applications(&self) -> u64 {
        0
    }

    /// Canonical competition-gate evidence for existing SAT native helpers.
    ///
    /// Count only live native-helper outcomes that did useful solver work, not
    /// merely enabled flags, compile attempts, or retired propagation telemetry.
    /// Live non-BCP helpers currently include subsumption checks and
    /// conflict-analysis literal processing.
    pub fn sat_native_code_helper_applications(&self) -> u64 {
        self.stats
            .sat_conflict_analysis_native_applications
            .saturating_add(self.inproc.subsumer.stats().native_applications)
    }

    /// Native subsumption checks applied by the SAT subsumption helper.
    pub fn sat_subsumption_native_applications(&self) -> u64 {
        self.inproc.subsumer.stats().native_applications
    }

    /// Native conflict-analysis helper applications.
    pub fn sat_conflict_analysis_native_applications(&self) -> u64 {
        self.stats.sat_conflict_analysis_native_applications
    }

    /// Solver-start SAT whole-loop guard artifacts retained after a successful
    /// native runtime guard application.
    pub fn sat_whole_loop_guard_installs(&self) -> u64 {
        self.stats.sat_whole_loop_guard_installs
    }

    /// Solver-start SAT whole-loop guard applications after runtime guards pass.
    pub fn sat_whole_loop_guard_applications(&self) -> u64 {
        self.stats.sat_whole_loop_guard_applications
    }

    /// Whether ghost literal guards are active in conflict analysis (#8489).
    ///
    /// Returns true when either chrono-BT can produce ghost literals
    /// (num_vars > CHRONO_LEVEL_LIMIT) or incremental mode has been used
    /// (has_ever_scoped). Used by tests to verify the incremental-mode
    /// ghost guard fix.
    pub fn ghost_guard_needed(&self) -> bool {
        self.ghost_guard_needed
    }

    /// Whether SAT native-code helper compilation is enabled for this solve.
    ///
    /// The retired SAT propagation compiler telemetry used a legacy enabled key; the
    /// current flag gates non-BCP native helpers.
    pub fn native_code_helpers_enabled(&self) -> bool {
        !self.cold.jit_disabled
    }

    /// Whether native SAT propagation telemetry is active.
    ///
    /// The current production path keeps this false after the retired
    /// propagation compiler was removed in #8517.
    pub fn sat_propagation_native_active(&self) -> bool {
        self.stats.sat_propagation_native_active
    }

    /// Number of clauses covered by native SAT propagation telemetry.
    pub fn sat_propagation_native_clauses(&self) -> u64 {
        self.stats.sat_propagation_native_clauses
    }

    /// Number of propagation rounds covered by native SAT propagation telemetry.
    pub fn sat_propagation_native_rounds(&self) -> u64 {
        self.stats.sat_propagation_native_rounds
    }

    /// Propagations discovered by native SAT propagation telemetry.
    pub fn sat_propagation_native_propagations(&self) -> u64 {
        self.stats.sat_propagation_native_propagations
    }

    /// Conflicts discovered by native SAT propagation telemetry.
    pub fn sat_propagation_native_conflicts(&self) -> u64 {
        self.stats.sat_propagation_native_conflicts
    }

    /// Native SAT propagation compile time in microseconds.
    pub fn sat_propagation_native_compile_time_us(&self) -> u64 {
        self.stats.sat_propagation_native_compile_time_us
    }

    /// Current compilation tier as a human-readable string (e.g. "T0:interpret").
    pub fn compilation_tier(&self) -> &'static str {
        self.stats.compilation_tier
    }

    /// Number of tier promotions executed by the tier controller.
    pub fn tier_controller_promotions(&self) -> u64 {
        self.stats.tier_controller_promotions
    }

    /// Code cache: total mmap'd executable bytes across all JIT allocations (#8394).
    pub fn code_cache_total_bytes(&self) -> usize {
        self.stats.code_cache_total_bytes
    }

    /// Code cache: peak total allocation observed (#8394).
    pub fn code_cache_peak_bytes(&self) -> usize {
        self.stats.code_cache_peak_bytes
    }

    /// Code cache: number of LRU evictions performed (#8394).
    pub fn code_cache_evictions(&self) -> u64 {
        self.stats.code_cache_evictions
    }

    /// Code cache: total bytes freed by eviction (#8394).
    pub fn code_cache_bytes_evicted(&self) -> u64 {
        self.stats.code_cache_bytes_evicted
    }

    /// Get clause arena memory usage in 32-bit words (#8131).
    pub fn arena_words(&self) -> usize {
        self.arena.len()
    }

    /// Get the number of currently active clauses (excludes deleted) (#8131).
    pub fn active_clause_count(&self) -> usize {
        self.arena.active_clause_count()
    }

    /// Get phase timing: preprocess wall-clock nanoseconds.
    pub fn preprocess_time_ns(&self) -> u64 {
        self.stats.preprocess_time_ns
    }

    /// Get phase timing: CDCL search loop wall-clock nanoseconds.
    pub fn search_time_ns(&self) -> u64 {
        self.stats.search_time_ns
    }

    /// Get phase timing: lucky-phase probing wall-clock nanoseconds.
    pub fn lucky_time_ns(&self) -> u64 {
        self.stats.lucky_time_ns
    }

    /// Get phase timing: walk-based phase init wall-clock nanoseconds.
    pub fn walk_time_ns(&self) -> u64 {
        self.stats.walk_time_ns
    }

    /// Get cumulative LBD sum and count for average LBD computation.
    pub fn lbd_sum_count(&self) -> (u64, u64) {
        (self.stats.lbd_sum, self.stats.lbd_count)
    }

    /// Get learned clause LBD distribution buckets (#8131).
    /// Returns `[lbd_1, lbd_2, lbd_3to5, lbd_6to10, lbd_11plus]`.
    pub fn lbd_buckets(&self) -> [u64; 5] {
        self.stats.lbd_buckets
    }

    /// Get peak decision level observed during solving.
    pub fn peak_decision_level(&self) -> u32 {
        self.stats.peak_decision_level
    }

    /// Get average decision level (sum / count).
    pub fn avg_decision_level(&self) -> f64 {
        if self.stats.decision_level_count > 0 {
            self.stats.decision_level_sum as f64 / self.stats.decision_level_count as f64
        } else {
            0.0
        }
    }

    /// Get lookahead statistics: (rounds, failed_literals, decisions_used).
    pub fn lookahead_stats(&self) -> (u64, u64, u64) {
        (
            self.stats.lookahead_rounds,
            self.stats.lookahead_failed_literals,
            self.stats.lookahead_decisions_used,
        )
    }

    /// Get BCP telemetry counters: (blocker_fastpath_hits, binary_path_hits, replacement_scan_steps).
    pub fn bcp_stats(&self) -> (u64, u64, u64) {
        (
            self.stats.bcp_blocker_fastpath_hits,
            self.stats.bcp_binary_path_hits,
            self.stats.bcp_replacement_scan_steps,
        )
    }

    /// Return SEARCH in-place watch scan route invocations.
    pub fn bcp_search_inplace_watch_scan_exercise_count(&self) -> u64 {
        self.stats.bcp_search_inplace_watch_scan_exercised
    }

    /// Return whether SEARCH in-place watch scan route was exercised at least once.
    pub fn bcp_search_inplace_watch_scan_exercised(&self) -> bool {
        self.bcp_search_inplace_watch_scan_exercise_count() != 0
    }

    /// Get BCP saved-position replacement-scan telemetry.
    pub fn bcp_saved_pos_stats(&self) -> BcpSavedPosStats {
        BcpSavedPosStats {
            long_scans: self.stats.bcp_long_saved_pos_scans,
            long_start_false: self.stats.bcp_long_saved_pos_start_false,
            long_found_true: self.stats.bcp_long_saved_pos_found_true,
            long_found_unassigned: self.stats.bcp_long_saved_pos_found_unassigned,
            long_no_replacement: self.stats.bcp_long_saved_pos_no_replacement,
            len18_scans: self.stats.bcp_len18_saved_pos_scans,
            len18_start_false: self.stats.bcp_len18_saved_pos_start_false,
            len18_found_true: self.stats.bcp_len18_saved_pos_found_true,
            len18_found_unassigned: self.stats.bcp_len18_saved_pos_found_unassigned,
            len18_no_replacement: self.stats.bcp_len18_saved_pos_no_replacement,
        }
    }

    /// Get default-on Sequential Main BCP long-clause replacement-scan diagnostics.
    pub fn bcp_long_scan_stats(&self) -> BcpLongScanStats {
        BcpLongScanStats {
            bucket_labels: BCP_LONG_SCAN_BUCKET_LABELS,
            blocker_fastpath_hits: self.stats.bcp_blocker_fastpath_hits,
            long_blocker_fastpath_hits: self.stats.bcp_long_blocker_fastpath_hits,
            scan_steps_binary: self.stats.bcp_replacement_scan_steps_binary,
            scan_steps_non_binary: self.stats.bcp_replacement_scan_steps_non_binary,
            scan_steps_learned: self.stats.bcp_replacement_scan_steps_learned,
            scan_steps_original: self.stats.bcp_replacement_scan_steps_original,
            scan_steps_by_len: self.stats.bcp_long_scan_steps_by_len,
            learned_scan_steps_by_len: self.stats.bcp_long_scan_steps_learned_by_len,
            original_scan_steps_by_len: self.stats.bcp_long_scan_steps_original_by_len,
            scans_by_len: self.stats.bcp_long_scan_by_len,
            found_replacement_by_len: self.stats.bcp_long_scan_found_replacement_by_len,
            found_true_by_len: self.stats.bcp_long_scan_found_true_by_len,
            found_unassigned_by_len: self.stats.bcp_long_scan_found_unassigned_by_len,
            no_replacement_by_len: self.stats.bcp_long_scan_no_replacement_by_len,
            unit_by_len: self.stats.bcp_long_scan_unit_by_len,
            conflict_by_len: self.stats.bcp_long_scan_conflict_by_len,
            learned_scans_by_len: self.stats.bcp_long_scan_learned_by_len,
            learned_found_replacement_by_len: self
                .stats
                .bcp_long_scan_learned_found_replacement_by_len,
            learned_no_replacement_by_len: self.stats.bcp_long_scan_learned_no_replacement_by_len,
            learned_unit_by_len: self.stats.bcp_long_scan_learned_unit_by_len,
            learned_conflict_by_len: self.stats.bcp_long_scan_learned_conflict_by_len,
            learned_1963_true_tail_relocation_enabled: self
                .cold
                .bcp_learned_1963_true_tail_relocation,
            learned_1963_true_tail_relocation_attempts: self
                .stats
                .bcp_learned_1963_true_tail_relocation_attempts,
            learned_1963_true_tail_relocation_moves: self
                .stats
                .bcp_learned_1963_true_tail_relocation_moves,
            learned_1963_used5_fsw_saved_pos_reset_enabled: self
                .cold
                .bcp_learned_1963_used5_fsw_saved_pos_reset,
            learned_1963_used5_fsw_saved_pos_reset_eligible: self
                .stats
                .bcp_learned_1963_used5_fsw_saved_pos_reset_eligible,
            learned_1963_used5_fsw_saved_pos_reset_writes: self
                .stats
                .bcp_learned_1963_used5_fsw_saved_pos_reset_writes,
            learned_1963_used5_fsw_saved_pos_reset_unit: self
                .stats
                .bcp_learned_1963_used5_fsw_saved_pos_reset_unit,
            learned_1963_used5_fsw_saved_pos_reset_conflict: self
                .stats
                .bcp_learned_1963_used5_fsw_saved_pos_reset_conflict,
            learned_1963_fsw_conflict_saved_pos_reset_enabled: self
                .cold
                .bcp_learned_1963_fsw_conflict_saved_pos_reset,
            learned_1963_fsw_conflict_saved_pos_reset_eligible: self
                .stats
                .bcp_learned_1963_fsw_conflict_saved_pos_reset_eligible,
            learned_1963_fsw_conflict_saved_pos_reset_writes: self
                .stats
                .bcp_learned_1963_fsw_conflict_saved_pos_reset_writes,
            learned_1963_fsw_conflict_saved_pos_reset_conflict: self
                .stats
                .bcp_learned_1963_fsw_conflict_saved_pos_reset_conflict,
            learned_618_true_tail_relocation_enabled: self
                .cold
                .bcp_learned_618_true_tail_relocation,
            learned_618_true_tail_relocation_attempts: self
                .stats
                .bcp_learned_618_true_tail_relocation_attempts,
            learned_618_true_tail_relocation_moves: self
                .stats
                .bcp_learned_618_true_tail_relocation_moves,
            learned_no_replacement_saved_pos_update_enabled: self
                .cold
                .bcp_learned_no_replacement_saved_pos_update,
            learned_no_replacement_saved_pos_eligible_by_len: self
                .stats
                .bcp_learned_no_replacement_saved_pos_eligible_by_len,
            learned_no_replacement_saved_pos_writes_by_len: self
                .stats
                .bcp_learned_no_replacement_saved_pos_writes_by_len,
            learned_no_replacement_saved_pos_skipped_current_by_len: self
                .stats
                .bcp_learned_no_replacement_saved_pos_skipped_current_by_len,
            learned_no_replacement_saved_pos_unit_by_len: self
                .stats
                .bcp_learned_no_replacement_saved_pos_unit_by_len,
            learned_no_replacement_saved_pos_conflict_by_len: self
                .stats
                .bcp_learned_no_replacement_saved_pos_conflict_by_len,
            learned_1963_fsw_gent_skip_enabled: self.cold.bcp_learned_1963_fsw_gent_skip,
            learned_1963_fsw_gent_skip_candidates: self
                .stats
                .bcp_learned_1963_fsw_gent_skip_candidates,
            learned_1963_fsw_gent_skip_applied: self.stats.bcp_learned_1963_fsw_gent_skip_applied,
            learned_1963_fsw_gent_skip_saved_slots: self
                .stats
                .bcp_learned_1963_fsw_gent_skip_saved_slots,
            learned_1963_fsw_gent_skip_found_true_suffix: self
                .stats
                .bcp_learned_1963_fsw_gent_skip_found_true_suffix,
            learned_1963_fsw_gent_skip_found_unassigned_suffix: self
                .stats
                .bcp_learned_1963_fsw_gent_skip_found_unassigned_suffix,
            learned_1963_fsw_gent_skip_found_true_prefix: self
                .stats
                .bcp_learned_1963_fsw_gent_skip_found_true_prefix,
            learned_1963_fsw_gent_skip_found_unassigned_prefix: self
                .stats
                .bcp_learned_1963_fsw_gent_skip_found_unassigned_prefix,
            learned_1963_fsw_gent_skip_no_replacement_unit: self
                .stats
                .bcp_learned_1963_fsw_gent_skip_no_replacement_unit,
            learned_1963_fsw_gent_skip_no_replacement_conflict: self
                .stats
                .bcp_learned_1963_fsw_gent_skip_no_replacement_conflict,
            learned_no_replacement_scan_pressure_enabled: self
                .cold
                .bcp_learned_no_replacement_scan_pressure,
            disable_learned_1963_no_replacement_unit_blocker_refresh_enabled: self
                .cold
                .bcp_disable_learned_1963_no_replacement_unit_blocker_refresh,
            learned_no_replacement_scan_pressure_scans_by_len: self
                .stats
                .bcp_learned_no_replacement_scan_pressure_scans_by_len,
            learned_no_replacement_scan_pressure_steps_by_len: self
                .stats
                .bcp_learned_no_replacement_scan_pressure_steps_by_len,
            learned_no_replacement_scan_pressure_start_false_by_len: self
                .stats
                .bcp_learned_no_replacement_scan_pressure_start_false_by_len,
            learned_no_replacement_scan_pressure_wrapped_by_len: self
                .stats
                .bcp_learned_no_replacement_scan_pressure_wrapped_by_len,
            learned_no_replacement_scan_pressure_unit_by_len: self
                .stats
                .bcp_learned_no_replacement_scan_pressure_unit_by_len,
            learned_no_replacement_scan_pressure_conflict_by_len: self
                .stats
                .bcp_learned_no_replacement_scan_pressure_conflict_by_len,
            learned_1963_fsw_unit_by_lbd: self.stats.bcp_learned_1963_fsw_unit_by_lbd,
            learned_1963_fsw_conflict_by_lbd: self.stats.bcp_learned_1963_fsw_conflict_by_lbd,
            learned_1963_fsw_unit_steps_by_lbd: self.stats.bcp_learned_1963_fsw_unit_steps_by_lbd,
            learned_1963_fsw_conflict_steps_by_lbd: self
                .stats
                .bcp_learned_1963_fsw_conflict_steps_by_lbd,
            learned_1963_fsw_unit_by_used: self.stats.bcp_learned_1963_fsw_unit_by_used,
            learned_1963_fsw_conflict_by_used: self.stats.bcp_learned_1963_fsw_conflict_by_used,
            learned_1963_fsw_unit_steps_by_used: self.stats.bcp_learned_1963_fsw_unit_steps_by_used,
            learned_1963_fsw_conflict_steps_by_used: self
                .stats
                .bcp_learned_1963_fsw_conflict_steps_by_used,
            learned_1963_fsw_repeat_by_bucket: self.stats.bcp_learned_1963_fsw_repeat_by_bucket,
            learned_1963_fsw_repeat_steps_by_bucket: self
                .stats
                .bcp_learned_1963_fsw_repeat_steps_by_bucket,
            learned_1963_fsw_repeat_bucket_max: self.stats.bcp_learned_1963_fsw_repeat_bucket_max,
            learned_1963_blocker_cert_elision_enabled: self
                .bcp_learned_1963_blocker_cert_elision_enabled_internal(),
            learned_1963_blocker_cert_shadow_enabled: self
                .bcp_learned_1963_blocker_cert_shadow_enabled_internal(),
            learned_1963_blocker_cert_false_reject_demote_enabled: self
                .bcp_learned_1963_blocker_cert_false_reject_demote_enabled_internal(),
            learned_1963_blocker_cert_candidates: self
                .stats
                .bcp_learned_1963_blocker_cert_candidates,
            learned_1963_blocker_cert_elisions: self.stats.bcp_learned_1963_blocker_cert_elisions,
            learned_1963_blocker_cert_shadow_hits: self
                .stats
                .bcp_learned_1963_blocker_cert_shadow_hits,
            learned_1963_blocker_cert_shadow_mismatches: self
                .stats
                .bcp_learned_1963_blocker_cert_shadow_mismatches,
            learned_1963_blocker_cert_mismatch_demotions: self
                .stats
                .bcp_learned_1963_blocker_cert_mismatch_demotions,
            learned_1963_blocker_cert_populates: self.stats.bcp_learned_1963_blocker_cert_populates,
            learned_1963_blocker_cert_stale_rejects: self
                .stats
                .bcp_learned_1963_blocker_cert_stale_rejects,
            learned_1963_blocker_cert_false_rejects: self
                .stats
                .bcp_learned_1963_blocker_cert_false_rejects,
            learned_1963_blocker_cert_false_reject_demotions: self
                .stats
                .bcp_learned_1963_blocker_cert_false_reject_demotions,
            learned_1963_blocker_cert_repeat_rejects: self
                .stats
                .bcp_learned_1963_blocker_cert_repeat_rejects,
            learned_1963_blocker_cert_elided_suffix_slots: self
                .stats
                .bcp_learned_1963_blocker_cert_elided_suffix_slots,
            learned_1963_blocker_cert_shadow_elided_suffix_slots: self
                .stats
                .bcp_learned_1963_blocker_cert_shadow_elided_suffix_slots,
            learned_1963_blocker_cert_affected_fsw_rows: self
                .stats
                .bcp_learned_1963_blocker_cert_affected_fsw_rows,
            learned_1963_blocker_cert_shadow_affected_fsw_rows: self
                .stats
                .bcp_learned_1963_blocker_cert_shadow_affected_fsw_rows,
            learned_617_tail_reorder_enabled: self.cold.bcp_learned_617_tail_reorder,
            learned_617_tail_reorder_candidates: self.stats.bcp_learned_617_tail_reorder_candidates,
            learned_617_tail_reorder_exercised: self.stats.bcp_learned_617_tail_reorder_exercised,
            learned_617_tail_reorder_changed: self.stats.bcp_learned_617_tail_reorder_changed,
            learned_617_tail_reorder_swaps: self.stats.bcp_learned_617_tail_reorder_swaps,
            learned_18_tail_reorder_enabled: self.cold.bcp_learned_18_tail_reorder,
            learned_18_tail_reorder_candidates: self.stats.bcp_learned_18_tail_reorder_candidates,
            learned_18_tail_reorder_exercised: self.stats.bcp_learned_18_tail_reorder_exercised,
            learned_18_tail_reorder_changed: self.stats.bcp_learned_18_tail_reorder_changed,
            learned_18_tail_reorder_swaps: self.stats.bcp_learned_18_tail_reorder_swaps,
            learned_1963_tail_reorder_enabled: self.cold.bcp_learned_1963_tail_reorder
                || self
                    .cold
                    .bcp_learned_1963_tail_reorder_swap_budget
                    .is_some(),
            learned_1963_tail_reorder_candidates: self
                .stats
                .bcp_learned_1963_tail_reorder_candidates,
            learned_1963_tail_reorder_changed: self.stats.bcp_learned_1963_tail_reorder_changed,
            learned_1963_tail_reorder_swaps: self.stats.bcp_learned_1963_tail_reorder_swaps,
            learned_1963_tail_reorder_swap_budget: self
                .cold
                .bcp_learned_1963_tail_reorder_swap_budget,
            learned_1963_tail_reorder_budget_candidates: self
                .stats
                .bcp_learned_1963_tail_reorder_budget_candidates,
            learned_1963_tail_reorder_budget_applied: self
                .stats
                .bcp_learned_1963_tail_reorder_budget_applied,
            learned_1963_tail_reorder_budget_skipped_over_budget: self
                .stats
                .bcp_learned_1963_tail_reorder_budget_skipped_over_budget,
            learned_1963_tail_reorder_budget_swaps_applied: self
                .stats
                .bcp_learned_1963_tail_reorder_budget_swaps_applied,
            learned_1963_tail_reorder_budget_swaps_skipped: self
                .stats
                .bcp_learned_1963_tail_reorder_budget_swaps_skipped,
        }
    }

    /// Get LRAT level-0 unit materialization and unit-chain diagnostics.
    pub fn lrat_materialization_stats(&self) -> LratMaterializationStats {
        LratMaterializationStats {
            materialize_calls: self.stats.lrat_materialize_calls,
            materialize_minimize_calls: self.stats.lrat_materialize_minimize_calls,
            materialize_root_trail_entries: self.stats.lrat_materialize_root_trail_entries,
            materialize_minimize_root_trail_entries: self
                .stats
                .lrat_materialize_minimize_root_trail_entries,
            materialize_emitted_unit_lines: self.stats.lrat_materialize_emitted_unit_lines,
            materialize_minimize_emitted_unit_lines: self
                .stats
                .lrat_materialize_minimize_emitted_unit_lines,
            materialize_unit_hints: self.stats.lrat_materialize_unit_hints,
            materialize_minimize_unit_hints: self.stats.lrat_materialize_minimize_unit_hints,
            materialize_unit_max_hints: self.stats.lrat_materialize_unit_max_hints,
            materialize_minimize_unit_max_hints: self
                .stats
                .lrat_materialize_minimize_unit_max_hints,
            materialize_incomplete_chains: self.stats.lrat_materialize_incomplete_chains,
            materialize_minimize_incomplete_chains: self
                .stats
                .lrat_materialize_minimize_incomplete_chains,
            materialize_hidden_trusted_units: self.stats.lrat_materialize_hidden_trusted_units,
            unit_chain_calls: self.stats.lrat_unit_chain_calls,
            unit_chain_root_trail_entries: self.stats.lrat_unit_chain_root_trail_entries,
            unit_chain_hints: self.stats.lrat_unit_chain_hints,
            unit_chain_max_hints: self.stats.lrat_unit_chain_max_hints,
            unit_chain_missing_hints: self.stats.lrat_unit_chain_missing_hints,
        }
    }

    /// Get jumped reasons count (binary reason chains compressed, Kissat #8034).
    pub fn jumped_reasons(&self) -> u64 {
        self.stats.jumped_reasons
    }

    /// Get stale enqueue skip count (#8359, #8382).
    /// Non-zero values indicate a bug in JIT/compaction/arena GC producing
    /// out-of-bounds variable indices. Zero is expected in correct operation.
    pub fn stale_enqueue_skips(&self) -> u64 {
        self.stats.stale_enqueue_skips
    }

    /// Get stale BCP watch skip count (#8547).
    /// Non-zero values indicate stale watch entries from prior arena GC or
    /// variable compaction. Zero is expected in correct operation.
    pub fn stale_bcp_watch_skips(&self) -> u64 {
        self.stats.stale_bcp_watch_skips
    }

    /// Get OTFS (on-the-fly self-subsumption) stats: (candidates, subsumed, strengthened).
    pub fn otfs_stats(&self) -> (u64, u64, u64) {
        (
            self.stats.otfs_candidates,
            self.stats.otfs_subsumed,
            self.stats.otfs_strengthened,
        )
    }

    /// Get focused-mode and stable-mode decision counts.
    pub fn mode_decisions(&self) -> (u64, u64) {
        (self.stats.focused_decisions, self.stats.stable_decisions)
    }

    /// Get the number of completed inprocessing rounds.
    pub fn inprocessing_rounds(&self) -> u64 {
        self.stats.inprocessing_rounds
    }

    /// Get the number of completed incremental inprocessing rounds (#8208).
    pub fn incremental_inprocessing_rounds(&self) -> u64 {
        self.stats.incremental_inprocessing_rounds
    }

    /// Get total inprocessing simplifications across all rounds.
    pub fn inprocessing_simplifications(&self) -> u64 {
        self.stats.inprocessing_simplifications
    }

    /// Get cumulative rebuild_watches time in microseconds (#8103).
    /// Combined total for both full and incremental paths.
    pub fn rebuild_watches_us(&self) -> u64 {
        self.stats.rebuild_watches_us
    }

    /// Get number of rebuild_watches calls (#8103).
    /// Combined total for both full and incremental paths.
    pub fn rebuild_watches_calls(&self) -> u64 {
        self.stats.rebuild_watches_calls
    }

    /// Get full rebuild_watches time in microseconds (#8103).
    pub fn full_rebuild_watches_us(&self) -> u64 {
        self.stats.full_rebuild_watches_us
    }

    /// Get number of full rebuild_watches calls (#8103).
    pub fn full_rebuild_watches_calls(&self) -> u64 {
        self.stats.full_rebuild_watches_calls
    }

    /// Get incremental reconnect_bve_watches time in microseconds (#8103).
    pub fn incremental_reconnect_watches_us(&self) -> u64 {
        self.stats.incremental_reconnect_watches_us
    }

    /// Get number of incremental reconnect_bve_watches calls (#8103).
    pub fn incremental_reconnect_watches_calls(&self) -> u64 {
        self.stats.incremental_reconnect_watches_calls
    }

    /// Get post-rebuild BCP cache behavior stats (#8103).
    /// Returns (nanoseconds, propagations) during re-propagation after rebuild_watches.
    /// Compare propagations/ns here vs overall BCP to assess cache efficiency.
    pub fn post_rebuild_bcp_stats(&self) -> (u64, u64) {
        (
            self.stats.post_rebuild_bcp_ns,
            self.stats.post_rebuild_bcp_propagations,
        )
    }

    /// Get post-rebuild BCP stats for full rebuild path only (#8103).
    pub fn post_full_rebuild_bcp_stats(&self) -> (u64, u64) {
        (
            self.stats.post_full_rebuild_bcp_ns,
            self.stats.post_full_rebuild_bcp_propagations,
        )
    }

    /// Get post-rebuild BCP stats for incremental reconnect path only (#8103).
    pub fn post_incremental_reconnect_bcp_stats(&self) -> (u64, u64) {
        (
            self.stats.post_incremental_reconnect_bcp_ns,
            self.stats.post_incremental_reconnect_bcp_propagations,
        )
    }

    /// Get IBCL (interpolation-based clause learning) stats (#8269):
    /// (attempts, improvements, skipped_short_chain).
    pub fn ibcl_stats(&self) -> (u64, u64, u64) {
        (
            self.stats.ibcl_attempts,
            self.stats.ibcl_improvements,
            self.stats.ibcl_skipped_short_chain,
        )
    }

    /// Get IBCL proof-readiness skips caused by missing pivot metadata (#8269).
    pub fn ibcl_skipped_missing_pivots(&self) -> u64 {
        self.stats.ibcl_skipped_missing_pivots
    }

    /// Get BCP-theory fixed-point loop stats (#8003).
    pub fn bcp_theory_fixpoint_stats(&self) -> (u64, u64, u32, u64) {
        (
            self.stats.bcp_theory_fixpoint_entries,
            self.stats.bcp_theory_fixpoint_iterations,
            self.stats.bcp_theory_fixpoint_max_depth,
            self.stats.bcp_theory_fixpoint_saturated,
        )
    }

    /// Get Phase C BCP-interleaved theory-propagation stats (#4919).
    ///
    /// Returns `(force_calls, force_hits)`:
    /// - `force_calls`: number of extra `propagate_force` calls made because
    ///   BCP propagated atoms after a `Continue` from the initial theory call.
    /// - `force_hits`: subset of those that surfaced new theory work. A high
    ///   ratio indicates BCP-interleaved propagation is paying off.
    pub fn bcp_theory_interleaved_stats(&self) -> (u64, u64) {
        (
            self.stats.bcp_theory_interleaved_force_calls,
            self.stats.bcp_theory_interleaved_force_hits,
        )
    }

    /// Get clause provenance summary (#8321).
    ///
    /// Returns a map from provenance category to count. Empty when provenance
    /// tracking is disabled (`AY_CLAUSE_PROVENANCE` env var not set).
    pub fn provenance_summary(
        &self,
    ) -> std::collections::BTreeMap<crate::clause_provenance::ClauseProvenance, usize> {
        self.provenance.summary()
    }

    /// Get the total number of tracked clauses with provenance (#8321).
    pub fn provenance_tracked_count(&self) -> usize {
        self.provenance.tracked_count()
    }

    /// Whether clause provenance tracking is enabled (#8321).
    pub fn provenance_enabled(&self) -> bool {
        self.provenance.is_enabled()
    }

    /// Compute UNSAT core provenance breakdown (#8322).
    ///
    /// Returns `Some(summary)` when provenance tracking is enabled AND the
    /// proof certificate contains a non-empty minimal core. The summary
    /// reports which categories of clauses participated in the proof of
    /// unsatisfiability.
    ///
    /// Returns `None` when provenance tracking is disabled or the core is
    /// empty.
    pub fn core_provenance_summary(
        &self,
        certificate: &ProofCertificate,
    ) -> Option<crate::clause_provenance::CoreProvenanceSummary> {
        if !self.provenance.is_enabled() {
            return None;
        }
        let core_ids = certificate.minimal_core();
        if core_ids.is_empty() {
            return None;
        }
        // Build reverse map: clause_id -> arena_index.
        // cold.clause_ids[arena_idx] = clause_id (1-based LRAT IDs).
        let clause_ids = &self.cold.clause_ids;
        let mut id_to_arena: crate::kani_compat::DetHashMap<u64, usize> = Default::default();
        for (arena_idx, &cid) in clause_ids.iter().enumerate() {
            if cid > 0 {
                id_to_arena.insert(cid, arena_idx);
            }
        }
        let arena_indices: Vec<usize> = core_ids
            .iter()
            .filter_map(|&cid| id_to_arena.get(&cid).copied())
            .collect();
        let breakdown = self.provenance.breakdown_for_indices(&arena_indices);
        let total_clauses = self.provenance.tracked_count();
        Some(crate::clause_provenance::CoreProvenanceSummary {
            total_clauses,
            core_clauses: arena_indices.len(),
            breakdown,
        })
    }

    /// Get backbone binary units count (#3274): units found via binary-only propagation.
    pub fn backbone_binary_units(&self) -> u64 {
        self.stats.backbone_binary_units
    }

    /// Get occ list incremental refresh count (#8403).
    pub fn occ_incremental_refreshes(&self) -> u64 {
        self.stats.occ_incremental_refreshes
    }

    /// Get occ list full rebuild count (#8403).
    pub fn occ_full_rebuilds(&self) -> u64 {
        self.stats.occ_full_rebuilds
    }

    /// Get between-solve learned clause reduction stats (#8435).
    /// Returns (reductions, clauses_deleted, used_decays).
    pub fn between_solve_stats(&self) -> (u64, u64, u64) {
        (
            self.stats.between_solve_reductions,
            self.stats.between_solve_clauses_deleted,
            self.stats.between_solve_used_decays,
        )
    }

    /// Get domain-restricted BCP stats (#8475).
    /// Returns (skips, calls).
    pub fn domain_bcp_stats(&self) -> (u64, u64) {
        (self.stats.domain_bcp_skips, self.stats.domain_bcp_calls)
    }

    /// Get intree probing stats: (rounds, failed_literals, vars_set).
    pub fn intree_stats(&self) -> (u64, u64, u64) {
        (
            self.cold.intree_rounds,
            self.cold.intree_failed,
            self.cold.intree_vars_set,
        )
    }

    /// Get DIP-ERCL statistics (#8440):
    /// (attempts, found, extensions_created, gc_deleted, skipped, reuses).
    pub fn dip_stats(&self) -> (u64, u64, u64, u64, u64, u64) {
        (
            self.stats.dip_attempts,
            self.stats.dip_found,
            self.stats.dip_extensions_created,
            self.stats.dip_gc_deleted,
            self.stats.dip_skipped,
            self.stats.dip_reuses,
        )
    }

    /// Get the number of fixed (unit-propagated at level 0) variables
    pub fn num_fixed(&self) -> i64 {
        self.fixed_count
    }

    /// Get the number of active clauses currently stored in the clause database.
    pub fn num_clauses(&self) -> usize {
        self.arena.num_clauses()
    }

    /// Check if the solver has derived an empty clause (UNSAT indicator).
    pub fn has_empty_clause(&self) -> bool {
        self.has_empty_clause
    }

    /// Pop the oldest pending theory conflict, if any (#6262).
    ///
    /// Returns `Some(clause_ref)` for immediately false clauses and mandatory
    /// non-root unit work queued by `add_theory_lemma`. BCP cannot rediscover
    /// an all-false watched conflict through a future watch event, and units
    /// must be installed at root before they can be considered consumed. A
    /// callback may queue multiple entries in one batch, so callers must
    /// continue draining until the queue is empty.
    pub fn take_pending_theory_conflict(&mut self) -> Option<ClauseRef> {
        self.pending_theory_conflicts.pop_front()
    }

    /// Whether the pending-conflict queue still owns this arena reference.
    ///
    /// Queue entries are short-lived, so a linear scan avoids another
    /// allocation in the solver state. The empty-queue common case is O(1).
    #[inline]
    pub(super) fn is_pending_theory_conflict_clause(&self, clause_idx: usize) -> bool {
        self.pending_theory_conflicts
            .iter()
            .any(|conflict_ref| conflict_ref.index() == clause_idx)
    }

    /// Consume any proof-manager ID retained for a queued theory unit.
    ///
    /// LRAT `TrustedTransform` additions reserve a hidden ID that intentionally
    /// differs from the arena clause ID. Other modes have no distinct emitted
    /// ID, so the arena ID is the correct clause-trace provenance.
    fn record_theory_unit_proof_id(&mut self, unit_ref: ClauseRef, unit: Literal) {
        let retained_id = self
            .pending_theory_unit_proof_ids
            .iter()
            .position(|(pending_ref, _)| *pending_ref == unit_ref)
            .map(|position| self.pending_theory_unit_proof_ids.swap_remove(position).1);
        let var_idx = unit.variable().index();
        let existing_id = self.unit_proof_id.get(var_idx).copied().unwrap_or(0);
        let existing_sign = self.unit_proof_sign.get(var_idx).copied().unwrap_or(0);
        let proof_id = retained_id
            .or_else(|| {
                (existing_id != 0 && existing_sign == unit.sign_i8()).then_some(existing_id)
            })
            .unwrap_or_else(|| self.clause_id(unit_ref));
        if proof_id != 0 {
            self.record_unit_proof_id_for_lit(unit, proof_id);
        }
    }

    fn discard_theory_unit_proof_id(&mut self, unit_ref: ClauseRef) {
        if let Some(position) = self
            .pending_theory_unit_proof_ids
            .iter()
            .position(|(pending_ref, _)| *pending_ref == unit_ref)
        {
            self.pending_theory_unit_proof_ids.swap_remove(position);
        }
    }

    /// Install an active length-1 theory clause as a root fact.
    ///
    /// Requires decision level 0. Returns `false` only when the unit is
    /// contradicted by an existing root assignment; callers must then process
    /// the ClauseRef as a genuine level-0 conflict. A successful installation
    /// also preserves the arena clause ID for LRAT/clause-trace unit chains.
    pub(super) fn install_theory_unit_at_root(&mut self, unit_ref: ClauseRef) -> bool {
        debug_assert_eq!(
            self.decision_level, 0,
            "install_theory_unit_at_root requires decision level 0",
        );
        let unit_idx = unit_ref.index();
        debug_assert_eq!(self.arena.len_of(unit_idx), 1);
        let unit = self.arena.literal(unit_idx, 0);
        if self.lit_val(unit) < 0 {
            return false;
        }

        let var_idx = unit.variable().index();
        if self.lit_val(unit) == 0 {
            self.enqueue(unit, None);
        } else {
            debug_assert_eq!(
                self.var_data[var_idx].level, 0,
                "true theory unit must already be assigned at root",
            );
        }
        if !self.var_lifecycle.is_inactive(var_idx) && !self.var_lifecycle.is_fixed(var_idx) {
            self.fixed_count += 1;
            self.var_lifecycle.mark_fixed(var_idx);
            self.l0_gc_dirty[var_idx] = true;
        }
        self.record_theory_unit_proof_id(unit_ref, unit);
        true
    }

    /// Pop the oldest theory conflict that is still live under the current
    /// assignment, discarding every stale queue head first (#8480).
    ///
    /// Backtracking after an earlier queued conflict may make later clauses
    /// non-conflicting. Conversely, a stale head must never hide a later live
    /// conflict long enough for BCP or a new decision to run. Centralizing the
    /// drain loop keeps all solve entry points on that invariant.
    pub(crate) fn take_live_pending_theory_conflict(&mut self) -> Option<ClauseRef> {
        while let Some(conflict_ref) = self.take_pending_theory_conflict() {
            let conflict_idx = conflict_ref.index();
            // Deleted entries have a zero literal length, for which `all`
            // would be vacuously true. Garbage-kept husks retain literals but
            // are no longer clauses in the live formula. Neither can be
            // handed to conflict analysis.
            if !self.arena.is_active(conflict_idx) || self.arena.is_garbage_any(conflict_idx) {
                self.discard_theory_unit_proof_id(conflict_ref);
                continue;
            }
            if self.arena.len_of(conflict_idx) == 1 {
                let unit = self.arena.literal(conflict_idx, 0);
                let unit_is_root_fact =
                    self.lit_val(unit) > 0 && self.var_data[unit.variable().index()].level == 0;
                if unit_is_root_fact {
                    self.record_theory_unit_proof_id(conflict_ref, unit);
                    continue;
                }
                if self.decision_level == 0 {
                    if self.install_theory_unit_at_root(conflict_ref) {
                        continue;
                    }
                    // Only a genuinely false root unit is a conflict.
                    return Some(conflict_ref);
                }
                // A unit may become unassigned (or true only above root) while
                // an earlier queued conflict is analyzed. It remains mandatory
                // callback-aware root work and must not be discarded as stale.
                return Some(conflict_ref);
            }
            let still_conflict = self
                .arena
                .literals(conflict_idx)
                .iter()
                .all(|&lit| self.lit_val(lit) < 0);
            if still_conflict {
                return Some(conflict_ref);
            }
        }
        None
    }

    /// Debug: dump all unit clauses in the arena as DIMACS literals.
    pub fn debug_dump_unit_clauses(&self) -> Vec<(usize, i32)> {
        let mut result = Vec::new();
        for idx in self.arena.indices() {
            if self.arena.is_active(idx) && self.arena.len_of(idx) == 1 {
                let lit = self.arena.literal(idx, 0);
                result.push((idx, lit.to_dimacs()));
            }
        }
        result
    }

    /// Count learned vs original clauses in the arena (debug diagnostic).
    pub fn debug_clause_counts(&self) -> (usize, usize) {
        let mut original = 0;
        let mut learned = 0;
        for idx in self.arena.indices() {
            if self.arena.is_active(idx) {
                if self.arena.is_learned(idx) {
                    learned += 1;
                } else {
                    original += 1;
                }
            }
        }
        (original, learned)
    }

    /// Remove all learned clauses from the arena.
    ///
    /// This is a drastic measure for debugging incremental optimization.
    /// It discards all learned clauses and theory lemmas, keeping only originals.
    pub fn clear_learned_clauses(&mut self) {
        let indices: Vec<usize> = self
            .arena
            .indices()
            .filter(|&idx| self.arena.is_active(idx) && self.arena.is_learned(idx))
            .collect();
        for idx in indices {
            // #5910: Must eagerly unlink binary watches before arena deletion.
            // Binary watcher lifecycle (#4924) requires eager removal so BCP's
            // hot path can skip liveness checks. Without this, stale binary
            // watches from deleted theory lemmas would cause incorrect
            // propagation in subsequent incremental solves.
            self.delete_binary_clause_watches(idx);
            // Mark watched literals dirty for targeted flush (#8101).
            let clause_len = self.arena.len_of(idx);
            if clause_len > 2 {
                let (w0, w1) = self.arena.watched_literals(idx);
                if w0.index() < self.dirty_watches.len() {
                    self.dirty_watches[w0.index()] = true;
                    self.dirty_watch_list.push(w0.index() as u32);
                }
                if w1.index() < self.dirty_watches.len() {
                    self.dirty_watches[w1.index()] = true;
                    self.dirty_watch_list.push(w1.index() as u32);
                }
            }
            if let Some(ref mut gc_occ) = self.gc_occ {
                let lits = self.arena.literals(idx);
                gc_occ.remove_clause(idx, lits);
            }
            self.stats.clear_bcp_learned_1963_blocker_cert(idx);
            self.arena.delete(idx);
        }
    }

    /// Clear the `has_empty_clause` flag for incremental solving.
    ///
    /// In incremental optimization (e.g., CP-SAT), a previous solve may have
    /// derived the empty clause (UNSAT) due to bound-tightening constraints.
    /// After clearing learned clauses and adding new constraints, the empty
    /// clause derivation is no longer valid — the new constraint set may be
    /// satisfiable. Without clearing this flag, all subsequent solves would
    /// immediately return UNSAT (#5910).
    ///
    /// Must be called AFTER `clear_learned_clauses()` to ensure the clauses
    /// that led to the empty clause derivation have been removed.
    pub fn clear_empty_clause(&mut self) {
        self.has_empty_clause = false;
        self.cold.empty_clause_in_proof = false;
        self.cold.empty_clause_lrat_id = None;
        self.pending_theory_conflicts.clear();
        self.pending_theory_unit_proof_ids.clear();
    }

    /// Dump all active clauses in DIMACS format to a file (debug only).
    pub fn dump_dimacs(&self, path: &str) -> std::io::Result<()> {
        use std::io::Write;
        let mut f = std::fs::File::create(path)?;
        let nc = self.arena.active_indices().count();
        writeln!(f, "p cnf {} {}", self.num_vars, nc)?;
        for idx in self.arena.indices() {
            if !self.arena.is_active(idx) {
                continue;
            }
            let len = self.arena.len_of(idx);
            let mut line = String::new();
            for j in 0..len {
                let lit = self.arena.literal(idx, j);
                let v = lit.variable().index() as i32 + 1;
                if lit.is_positive() {
                    line.push_str(&format!("{v} "));
                } else {
                    line.push_str(&format!("-{v} "));
                }
            }
            line.push('0');
            writeln!(f, "{line}")?;
        }
        Ok(())
    }

    /// Get the number of original (non-learned) clauses
    pub fn num_original_clauses(&self) -> usize {
        self.num_original_clauses
    }

    /// Convert an internal literal to its stable external representation.
    ///
    /// External indices are assigned at variable creation time and never
    /// change, even across compaction rounds. This is O(1): a single array
    /// lookup into `i2e`.
    ///
    /// Called at reconstruction stack push sites during inprocessing.
    /// Reference: CaDiCaL `internal.hpp:1628-1637`.
    #[inline]
    pub(crate) fn externalize(&self, lit: Literal) -> Literal {
        let int_var = lit.variable().index();
        debug_assert!(
            int_var < self.cold.i2e.len(),
            "BUG: externalize: internal var {} >= i2e.len() ({})",
            int_var,
            self.cold.i2e.len(),
        );
        let ext_var = self.cold.i2e[int_var];
        if lit.is_positive() {
            Literal::positive(Variable(ext_var))
        } else {
            Literal::negative(Variable(ext_var))
        }
    }

    /// Convert a slice of internal literals to external representation.
    ///
    /// Convenience wrapper for `externalize()` on each literal in a clause
    /// or witness. Used at reconstruction stack push sites.
    #[inline]
    pub(crate) fn externalize_lits(&self, lits: &[Literal]) -> Vec<Literal> {
        lits.iter().map(|&lit| self.externalize(lit)).collect()
    }

    /// Compute the SAT guidance v2 formula fingerprint for this solver.
    ///
    /// The fingerprint covers the original-clause ledger, not learned clauses.
    /// Learned-clause replay is only exact-replay compatible when this value
    /// matches between producer and consumer.
    #[must_use]
    pub fn guidance_fingerprint(&self) -> SatGuidanceFingerprint {
        SatGuidanceFingerprint::from_clause_iter(
            self.user_num_vars,
            self.cold.original_ledger.iter_clauses(),
        )
    }

    /// Classify a SAT guidance payload against this solver's current formula.
    ///
    /// Legacy guidance without a v2 fingerprint is still accepted for heuristic
    /// hints, but it cannot import learned clauses.
    #[must_use]
    pub fn classify_guidance_import(
        &self,
        source: Option<&SatGuidanceFingerprint>,
    ) -> SatGuidanceImportDecision {
        let Some(source) = source else {
            return SatGuidanceImportDecision::legacy_v1();
        };
        source.classify_import(&self.guidance_fingerprint())
    }

    /// Get the number of learned (non-original) clauses currently retained.
    pub fn num_learned_clauses(&self) -> u64 {
        let mut count: u64 = 0;
        for idx in self.arena.active_indices() {
            if self.arena.is_learned(idx) {
                count += 1;
            }
        }
        count
    }

    /// Extract all learned (non-original) clauses from the clause database.
    ///
    /// This is useful for preserving learned clauses when recreating the solver,
    /// such as in branch-and-bound algorithms for LIA.
    pub fn get_learned_clauses(&self) -> Vec<Vec<Literal>> {
        let mut learned = Vec::new();
        for idx in self.arena.active_indices() {
            if self.arena.is_learned(idx) {
                let lits = self.arena.literals(idx);
                // Skip clauses referencing internal variables (scope selectors,
                // factoring extension vars) that won't exist in a fresh solver.
                // Only preserve clauses whose variables are all within the
                // user-visible range. (#4716 soundness fix)
                if lits
                    .iter()
                    .all(|l| l.variable().index() < self.user_num_vars)
                {
                    learned.push(lits.to_vec());
                }
            }
        }
        learned
    }

    /// Extract high-quality learned clauses filtered by LBD threshold (#3762).
    ///
    /// Returns only learned clauses with LBD <= `max_lbd`. Low-LBD clauses
    /// (especially LBD 1-2, called "glue clauses" in CaDiCaL/Glucose) are
    /// high-quality: they encode relationships between few decision levels
    /// and are unlikely to become irrelevant. Preserving these across CEGAR
    /// iterations avoids re-deriving expensive lemmas.
    ///
    /// Also caps the total number of preserved clauses at `max_clauses` to
    /// prevent memory bloat in long CEGAR runs.
    pub fn get_learned_clauses_by_quality(
        &self,
        max_lbd: u32,
        max_clauses: usize,
    ) -> Vec<Vec<Literal>> {
        let mut learned = Vec::new();
        for idx in self.arena.active_indices() {
            if learned.len() >= max_clauses {
                break;
            }
            if self.arena.is_learned(idx) {
                let lbd = self.arena.lbd(idx);
                if lbd > max_lbd {
                    continue;
                }
                let lits = self.arena.literals(idx);
                // Same user-visible range guard as get_learned_clauses (#4716).
                if lits
                    .iter()
                    .all(|l| l.variable().index() < self.user_num_vars)
                {
                    learned.push(lits.to_vec());
                }
            }
        }
        learned
    }

    /// Export VSIDS activity scores for all user-visible variables (#3762).
    ///
    /// Returns a vec of `(variable_index, activity)` pairs for variables
    /// with non-zero activity. This can be used to seed a fresh solver's
    /// decision heuristic with prior search knowledge, avoiding cold-start
    /// in CEGAR iterations.
    pub fn export_variable_activities(&self) -> Vec<(usize, f64)> {
        let mut activities = Vec::new();
        for i in 0..self.user_num_vars {
            let var = Variable::new(i as u32);
            let act = self.vsids.activity(var);
            if act > 0.0 {
                activities.push((i, act));
            }
        }
        activities
    }

    /// Import VSIDS activity scores from a previous solve session (#3762).
    ///
    /// For each `(variable_index, activity)` pair, bumps the variable's
    /// activity proportionally to the prior score. This seeds the decision
    /// heuristic with knowledge from prior CEGAR iterations so the solver
    /// prioritizes variables that were contentious before.
    ///
    /// Variables beyond the current solver's range are silently skipped.
    pub fn import_variable_activities(&mut self, activities: &[(usize, f64)]) {
        for &(var_idx, _activity) in activities {
            if var_idx < self.num_vars {
                let var = Variable::new(var_idx as u32);
                // Bump the variable once to increase its priority. We don't
                // try to replicate exact scores (which depend on the decay
                // schedule) — a single bump is enough to differentiate
                // previously-active variables from cold ones.
                self.vsids.bump(var, &self.vals, true);
            }
        }
    }

    /// Export phase (polarity) hints for all user-visible variables (#3762).
    ///
    /// Returns pairs of `(variable_index, phase)` where phase is the last
    /// assignment polarity. Seeding a fresh solver with these hints helps
    /// it converge to similar assignments faster across CEGAR iterations.
    pub fn export_phase_hints(&self) -> Vec<(usize, bool)> {
        let mut hints = Vec::new();
        for i in 0..self.user_num_vars {
            // phase[i]: 1 = positive, -1 = negative, 0 = unset
            if i < self.phase.len() && self.phase[i] != 0 {
                hints.push((i, self.phase[i] > 0));
            }
        }
        hints
    }

    /// Import phase (polarity) hints from a previous solve session (#3762).
    ///
    /// Sets initial phase hints so the solver starts by trying the same
    /// polarities as the prior session. Phase saving is a standard SAT
    /// technique (Pipatsrisawat & Darwiche, 2007); seeding across CEGAR
    /// iterations extends it.
    pub fn import_phase_hints(&mut self, hints: &[(usize, bool)]) {
        for &(var_idx, positive) in hints {
            if var_idx < self.num_vars {
                let var = Variable::new(var_idx as u32);
                self.set_var_phase(var, positive);
            }
        }
    }

    /// Add a clause that was learned from a previous solve session.
    ///
    /// Unlike regular learned clauses, these are added without proof logging
    /// since they were already proven in the previous session.
    ///
    /// Automatically expands the solver's variable count if the clause
    /// references variables beyond the current `num_vars` (#4797). This can
    /// happen in branch-and-bound when the previous solver instance allocated
    /// extra SAT variables (e.g., from split atoms applied during solving)
    /// that don't yet exist in the fresh solver.
    #[allow(clippy::needless_pass_by_value)]
    pub fn add_preserved_learned(&mut self, mut literals: Vec<Literal>) -> bool {
        // Grow solver to accommodate out-of-range variables (#4797).
        let max_var = literals.iter().map(|l| l.variable().index()).max();
        if let Some(max_var) = max_var {
            if max_var >= self.num_vars {
                self.ensure_num_vars(max_var + 1);
            }
        }
        self.add_preserved_learned_watched(&mut literals)
    }

    // ── Progress reporting ──────────────────────────────────────────────

    /// Minimum interval between progress line emissions.
    const PROGRESS_INTERVAL_SECS: f64 = 5.0;

    /// Format a compact one-line progress summary for SAT solving.
    ///
    /// Uses the DIMACS `c` comment prefix for compatibility with SAT
    /// competition tooling. Includes conflicts, decisions, propagations,
    /// restarts, learned clause count, current search mode, and RSS.
    /// When a process memory limit is set and RSS exceeds 80% of it,
    /// shows `rss=USED/LIMIT(PCT%)` instead of bare `rss=MB`.
    pub(crate) fn format_progress_line(&self, elapsed_secs: f64) -> String {
        let mode = if self.stable_mode {
            "stable"
        } else {
            "focused"
        };
        let learned = self.num_learned_clauses();
        let props_per_sec = if elapsed_secs > 0.001 {
            self.num_propagations as f64 / elapsed_secs
        } else {
            0.0
        };
        let confs_per_sec = if elapsed_secs > 0.001 {
            self.num_conflicts as f64 / elapsed_secs
        } else {
            0.0
        };
        let rss_str = format_rss_field();
        format!(
            "c [{:.1}s] conflicts={} decisions={} props={} restarts={} learned={} mode={} props/s={:.0} confs/s={:.0} {rss_str}",
            elapsed_secs,
            self.num_conflicts,
            self.num_decisions,
            self.num_propagations,
            self.cold.restarts,
            learned,
            mode,
            props_per_sec,
            confs_per_sec,
        )
    }

    /// Check elapsed time and emit a progress line to stderr if due.
    ///
    /// Called from the CDCL loop on conflicts (high frequency). The actual
    /// emission is gated by a wall-clock check so overhead when progress is
    /// disabled is a single bool branch. When enabled, the `Instant::now()`
    /// call runs at most once per conflict; the 5-second gate ensures actual
    /// formatting + I/O happens rarely.
    #[inline]
    pub(crate) fn maybe_emit_progress(&mut self) {
        // Skip entirely if neither stderr progress nor observer is active.
        if !self.cold.progress_enabled && !self.has_observer() {
            return;
        }
        let now = ay_core::time::Instant::now();
        let should_emit = match self.cold.last_progress_time {
            Some(last) => now.duration_since(last).as_secs_f64() >= Self::PROGRESS_INTERVAL_SECS,
            None => {
                // First check: emit if at least PROGRESS_INTERVAL_SECS from solve start.
                self.cold.solve_start_time.is_some_and(|start| {
                    now.duration_since(start).as_secs_f64() >= Self::PROGRESS_INTERVAL_SECS
                })
            }
        };
        if should_emit {
            if self.cold.progress_enabled {
                let elapsed = self
                    .cold
                    .solve_start_time
                    .map_or(0.0, |start| now.duration_since(start).as_secs_f64());
                let line = self.format_progress_line(elapsed);
                // Use write! to stderr to avoid panic on broken pipe.
                let _ = Write::write_all(&mut std::io::stderr(), line.as_bytes());
                let _ = Write::write_all(&mut std::io::stderr(), b"\n");
            }
            self.cold.last_progress_time = Some(now);
            // Notify programmatic observer of periodic progress (#8155).
            self.notify_observer_progress();
        }
    }
}

/// Format the RSS field for progress line output (#8641).
///
/// Returns `rss=<N>MB` normally. When a process memory limit is configured
/// and current RSS exceeds 80% of it, returns `rss=<USED>/<LIMIT>(<PCT>%)`
/// with human-friendly GB/MB units.
fn format_rss_field() -> String {
    let rss_bytes = ay_sys::current_rss_bytes();
    let limit = ay_sys::get_process_memory_limit();
    if limit > 0 {
        let pct = (rss_bytes as u64 * 100) / limit as u64;
        if pct > 80 {
            return format!(
                "rss={:.1}GB/{:.1}GB({}%)",
                rss_bytes as f64 / (1024.0 * 1024.0 * 1024.0),
                limit as f64 / (1024.0 * 1024.0 * 1024.0),
                pct,
            );
        }
    }
    let rss_mb = rss_bytes / (1024 * 1024);
    format!("rss={rss_mb}MB")
}
