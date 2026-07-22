// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Pure telemetry counters sub-struct for hot/cold field separation (#5090).
//!
//! Groups write-only telemetry counters into a single struct so the
//! Solver's hot BCP fields are not intermixed with cold diagnostic state.
//! All fields are incremented in hot paths but never read for scheduling
//! decisions — only for stats display and diagnostic traces.

use crate::diagnostic_trace::DiagnosticPass;
use crate::kani_compat::DetHashMap as HashMap;

pub(crate) const INPROCESS_TIMING_LABELS: [&str; 16] = [
    "inproc_decompose_ms",
    "inproc_htr_ms",
    "inproc_subsume_ms",
    "inproc_probe_ms",
    "inproc_backbone_ms",
    "inproc_congruence_ms",
    "inproc_bve_ms",
    "inproc_factor_ms",
    "inproc_sbva_ms",
    "inproc_bce_ms",
    "inproc_cce_ms",
    "inproc_condition_ms",
    "inproc_transred_ms",
    "inproc_sweep_ms",
    "inproc_vivify_ms",
    "inproc_reorder_ms",
];

pub(crate) const INPROCESS_ACCOUNTING_LABELS: [&str; INPROCESS_TIMING_LABELS.len()] =
    INPROCESS_TIMING_LABELS;

pub(crate) fn inprocessing_timing_index(pass: DiagnosticPass) -> Option<usize> {
    match pass {
        DiagnosticPass::Decompose => Some(0),
        DiagnosticPass::HTR => Some(1),
        DiagnosticPass::Subsume => Some(2),
        DiagnosticPass::Probe => Some(3),
        DiagnosticPass::Backbone => Some(4),
        DiagnosticPass::Congruence => Some(5),
        DiagnosticPass::BVE => Some(6),
        DiagnosticPass::Factor => Some(7),
        DiagnosticPass::Sbva => Some(8),
        DiagnosticPass::BCE => Some(9),
        DiagnosticPass::CCE => Some(10),
        DiagnosticPass::Condition => Some(11),
        DiagnosticPass::TransRed => Some(12),
        DiagnosticPass::Sweep => Some(13),
        DiagnosticPass::Vivify => Some(14),
        DiagnosticPass::Reorder => Some(15),
        _ => None,
    }
}

pub(crate) const RESTART_ATTRIBUTION_BUCKETS: usize = 6;
pub(crate) const RESTART_MODE_BUCKETS: usize = 2;
pub(crate) const REPHASE_ATTRIBUTION_BUCKETS: usize = 6;
pub(crate) const REPHASE_MODE_BUCKETS: usize = 2;
pub(crate) const BCP_LONG_SCAN_BUCKETS: usize = 5;
pub(crate) const BCP_LONG_SCAN_BUCKET_LABELS: [&str; BCP_LONG_SCAN_BUCKETS] =
    ["6-8", "9-17", "18", "19-63", "64+"];
pub(crate) const BCP_LEARNED_1963_PRESSURE_LBD_BUCKETS: usize = 5;
pub(crate) const BCP_LEARNED_1963_PRESSURE_USED_BUCKETS: usize = 4;
pub(crate) const BCP_LEARNED_1963_PRESSURE_REPEAT_BUCKETS: usize = 32;
pub(crate) const BCP_LEARNED_1963_IDENTITY_AGE_BUCKETS: usize = 5;
pub(crate) const BCP_LEARNED_1963_IDENTITY_ACTIVITY_BUCKETS: usize = 4;

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) struct BcpLearned1963BlockerCert {
    pub(crate) clause_offset: usize,
    pub(crate) literal_raw: u32,
    pub(crate) position: usize,
    pub(crate) repeat_count: u8,
    pub(crate) fsw_seed: bool,
}

pub(crate) const BCP_LEARNED_1963_BLOCKER_CERT_MIN_REPEATS: u8 = 3;

#[inline(always)]
pub(crate) const fn bcp_long_scan_bucket(clause_len: usize) -> usize {
    match clause_len {
        0..=8 => 0,
        9..=17 => 1,
        18 => 2,
        19..=63 => 3,
        _ => 4,
    }
}

#[inline(always)]
pub(crate) const fn bcp_learned_1963_pressure_lbd_bucket(lbd: u32) -> usize {
    match lbd {
        0..=2 => 0,
        3..=6 => 1,
        7..=10 => 2,
        11..=20 => 3,
        _ => 4,
    }
}

#[inline(always)]
pub(crate) const fn bcp_learned_1963_pressure_used_bucket(used: u8) -> usize {
    match used {
        0 => 0,
        1 => 1,
        2..=4 => 2,
        _ => 3,
    }
}

#[inline(always)]
pub(crate) const fn bcp_learned_1963_identity_age_bucket(age_conflicts: u64) -> usize {
    match age_conflicts {
        0..=99 => 0,
        100..=999 => 1,
        1_000..=9_999 => 2,
        10_000..=99_999 => 3,
        _ => 4,
    }
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct BcpLearned1963IdentityRecord {
    pub(crate) clause_id: u64,
    pub(crate) clause_offset: u64,
    pub(crate) clause_len: u64,
    pub(crate) birth_conflict: u64,
    pub(crate) last_conflict: u64,
    pub(crate) age_conflicts: u64,
    pub(crate) lbd: u64,
    pub(crate) used: u64,
    pub(crate) activity_milli: u64,
    pub(crate) scans: u64,
    pub(crate) scan_steps: u64,
    pub(crate) replacement_scans: u64,
    pub(crate) replacement_steps: u64,
    pub(crate) true_replacements: u64,
    pub(crate) unassigned_replacements: u64,
    pub(crate) no_replacement_scans: u64,
    pub(crate) no_replacement_steps: u64,
    pub(crate) unit: u64,
    pub(crate) conflict: u64,
    pub(crate) saved_start_false: u64,
    pub(crate) wrapped: u64,
    pub(crate) fsw: u64,
    pub(crate) fsw_steps: u64,
    pub(crate) fsw_unit_steps: u64,
    pub(crate) fsw_conflict_steps: u64,
    pub(crate) repeat_scans: u64,
    pub(crate) repeat_steps: u64,
    pub(crate) fsw_repeat_steps: u64,
    pub(crate) max_scan_steps: u64,
}

#[derive(Clone, Debug, Default)]
pub(crate) struct BcpLearned1963IdentityTable {
    records: HashMap<u64, BcpLearned1963IdentityRecord>,
    pub(crate) total_scans: u64,
    pub(crate) total_scan_steps: u64,
    pub(crate) replacement_scans: u64,
    pub(crate) replacement_steps: u64,
    pub(crate) true_replacements: u64,
    pub(crate) unassigned_replacements: u64,
    pub(crate) no_replacement_scans: u64,
    pub(crate) no_replacement_steps: u64,
    pub(crate) unit: u64,
    pub(crate) conflict: u64,
    pub(crate) fsw_scans: u64,
    pub(crate) fsw_steps: u64,
    pub(crate) repeat_scans: u64,
    pub(crate) repeat_steps: u64,
    pub(crate) fsw_repeat_steps: u64,
    pub(crate) age_steps_by_bucket: [u64; BCP_LEARNED_1963_IDENTITY_AGE_BUCKETS],
    pub(crate) fsw_age_steps_by_bucket: [u64; BCP_LEARNED_1963_IDENTITY_AGE_BUCKETS],
    pub(crate) lbd_steps_by_bucket: [u64; BCP_LEARNED_1963_PRESSURE_LBD_BUCKETS],
    pub(crate) used_steps_by_bucket: [u64; BCP_LEARNED_1963_PRESSURE_USED_BUCKETS],
    pub(crate) activity_steps_by_bucket: [u64; BCP_LEARNED_1963_IDENTITY_ACTIVITY_BUCKETS],
}

impl BcpLearned1963IdentityTable {
    #[inline(always)]
    fn record(
        &mut self,
        clause_id: u64,
        clause_offset: usize,
        clause_len: usize,
        current_conflict: u64,
        birth_conflict: u64,
        scan_steps: u64,
        replacement_val: i8,
        first_val: i8,
        saved_start_false: bool,
        wrapped_from_saved_pos: bool,
        lbd: u32,
        used: u8,
    ) {
        let identity = if clause_id != 0 {
            clause_id
        } else {
            (1u64 << 63) | (clause_offset as u64)
        };
        let age_conflicts = current_conflict.saturating_sub(birth_conflict);
        let found_replacement = replacement_val >= 0;
        let no_replacement = !found_replacement;
        let unit = no_replacement && first_val == 0;
        let conflict = no_replacement && first_val < 0;
        let fsw = no_replacement && saved_start_false && wrapped_from_saved_pos;

        self.total_scans += 1;
        self.total_scan_steps += scan_steps;
        if found_replacement {
            self.replacement_scans += 1;
            self.replacement_steps += scan_steps;
            if replacement_val > 0 {
                self.true_replacements += 1;
            } else {
                self.unassigned_replacements += 1;
            }
        } else {
            self.no_replacement_scans += 1;
            self.no_replacement_steps += scan_steps;
            if unit {
                self.unit += 1;
            }
            if conflict {
                self.conflict += 1;
            }
        }
        if fsw {
            self.fsw_scans += 1;
            self.fsw_steps += scan_steps;
            self.fsw_age_steps_by_bucket[bcp_learned_1963_identity_age_bucket(age_conflicts)] +=
                scan_steps;
        }
        self.age_steps_by_bucket[bcp_learned_1963_identity_age_bucket(age_conflicts)] += scan_steps;
        self.lbd_steps_by_bucket[bcp_learned_1963_pressure_lbd_bucket(lbd)] += scan_steps;
        self.used_steps_by_bucket[bcp_learned_1963_pressure_used_bucket(used)] += scan_steps;
        self.activity_steps_by_bucket[0] += scan_steps;

        let record = self
            .records
            .entry(identity)
            .or_insert_with(|| BcpLearned1963IdentityRecord {
                clause_id,
                clause_offset: clause_offset as u64,
                clause_len: clause_len as u64,
                birth_conflict,
                lbd: u64::from(lbd),
                used: u64::from(used),
                ..BcpLearned1963IdentityRecord::default()
            });
        let repeated = record.scans > 0;
        if repeated {
            record.repeat_scans += 1;
            record.repeat_steps += scan_steps;
            self.repeat_scans += 1;
            self.repeat_steps += scan_steps;
        }
        record.clause_offset = clause_offset as u64;
        record.clause_len = clause_len as u64;
        record.last_conflict = current_conflict;
        record.age_conflicts = age_conflicts;
        record.lbd = u64::from(lbd);
        record.used = u64::from(used);
        record.activity_milli = 0;
        record.scans += 1;
        record.scan_steps += scan_steps;
        record.max_scan_steps = record.max_scan_steps.max(scan_steps);
        if found_replacement {
            record.replacement_scans += 1;
            record.replacement_steps += scan_steps;
            if replacement_val > 0 {
                record.true_replacements += 1;
            } else {
                record.unassigned_replacements += 1;
            }
        } else {
            record.no_replacement_scans += 1;
            record.no_replacement_steps += scan_steps;
            if unit {
                record.unit += 1;
            }
            if conflict {
                record.conflict += 1;
            }
        }
        if saved_start_false {
            record.saved_start_false += 1;
        }
        if wrapped_from_saved_pos {
            record.wrapped += 1;
        }
        if fsw {
            record.fsw += 1;
            record.fsw_steps += scan_steps;
            if unit {
                record.fsw_unit_steps += scan_steps;
            }
            if conflict {
                record.fsw_conflict_steps += scan_steps;
            }
            if repeated {
                record.fsw_repeat_steps += scan_steps;
                self.fsw_repeat_steps += scan_steps;
            }
        }
    }

    pub(crate) fn exact_identity_rows(&self) -> u64 {
        self.records
            .iter()
            .map(|(_, record)| record)
            .filter(|record| record.clause_id != 0)
            .count() as u64
    }

    #[inline]
    pub(crate) fn exact_clause_record(
        &self,
        clause_id: u64,
    ) -> Option<&BcpLearned1963IdentityRecord> {
        if clause_id == 0 {
            return None;
        }
        self.records
            .get(&clause_id)
            .filter(|record| record.clause_id == clause_id)
    }

    pub(crate) fn top_rows(&self, limit: usize) -> Vec<BcpLearned1963IdentityRecord> {
        let mut rows: Vec<_> = self
            .records
            .iter()
            .map(|(_, record)| record.clone())
            .collect();
        rows.sort_by(|left, right| {
            right
                .scan_steps
                .cmp(&left.scan_steps)
                .then_with(|| right.scans.cmp(&left.scans))
                .then_with(|| left.clause_id.cmp(&right.clause_id))
                .then_with(|| left.clause_offset.cmp(&right.clause_offset))
        });
        rows.truncate(limit);
        rows
    }

    pub(crate) fn top_fsw_scan_steps(&self, limit: usize) -> u64 {
        self.top_fsw_rows(limit)
            .into_iter()
            .map(|row| row.fsw_steps)
            .sum()
    }

    pub(crate) fn top_fsw_rows(&self, limit: usize) -> Vec<BcpLearned1963IdentityRecord> {
        let mut rows: Vec<_> = self
            .records
            .iter()
            .map(|(_, record)| record)
            .filter(|record| record.fsw_steps > 0)
            .cloned()
            .collect();
        rows.sort_by(|left, right| {
            right
                .fsw_steps
                .cmp(&left.fsw_steps)
                .then_with(|| right.fsw.cmp(&left.fsw))
                .then_with(|| left.clause_id.cmp(&right.clause_id))
                .then_with(|| left.clause_offset.cmp(&right.clause_offset))
        });
        rows.truncate(limit);
        rows
    }
}

#[derive(Clone, Copy)]
pub(crate) enum RestartAttribution {
    Geometric,
    TheoryLuby,
    StableReluctant,
    StableEma,
    FocusedEma,
    FocusedLuby,
}

impl RestartAttribution {
    #[inline]
    pub(crate) const fn index(self) -> usize {
        match self {
            Self::Geometric => 0,
            Self::TheoryLuby => 1,
            Self::StableReluctant => 2,
            Self::StableEma => 3,
            Self::FocusedEma => 4,
            Self::FocusedLuby => 5,
        }
    }
}

#[derive(Clone, Copy)]
pub(crate) enum RephaseAttribution {
    Original,
    Inverted,
    Best,
    Random,
    Flip,
    Walk,
}

impl RephaseAttribution {
    #[inline]
    pub(crate) const fn index(self) -> usize {
        match self {
            Self::Original => 0,
            Self::Inverted => 1,
            Self::Best => 2,
            Self::Random => 3,
            Self::Flip => 4,
            Self::Walk => 5,
        }
    }
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct InprocessingPassAccounting {
    pub attempts: u64,
    pub runs: u64,
    pub yields: u64,
}

/// Pure telemetry counters (incremented in hot paths, read only for stats display).
///
/// These counters are never consulted for scheduling decisions (restart,
/// reduce_db, inprocessing). They exist purely for performance diagnostics
/// and user-facing statistics. Grouping them reduces the Solver's direct
/// field count and clarifies the hot/cold boundary.
///
/// Reference: CaDiCaL `Stats` struct groups all counters separately from
/// solver state.
#[derive(Clone)]
pub(crate) struct SolverStats {
    /// Chronological backtrack count.
    pub chrono_backtracks: u64,
    /// Number of same-level blocks considered for block-UIP shrinking.
    pub shrink_block_attempts: u64,
    /// Number of block-UIP searches that found a replacement literal.
    pub shrink_block_successes: u64,
    /// #9102: learned clauses whose shrink path was skipped because every
    /// non-UIP literal was on a distinct decision level.
    pub shrink_singleton_fast_path_skips: u64,
    /// #9102: LRAT removed-literal snapshots collected after shrink/minimize.
    pub lrat_original_learned_snapshot_copies: u64,
    /// #9102: literals copied into LRAT removed-literal snapshots.
    pub lrat_original_learned_snapshot_literals: u64,
    /// #9102: LRAT snapshots skipped by the singleton-level shrink guard.
    pub lrat_original_learned_snapshot_singleton_skips: u64,
    /// #9102: removed-literal LRAT chain computations.
    pub lrat_removed_literal_chain_calls: u64,
    /// BCP telemetry: blocker-fastpath hits (`blocker_val > 0`).
    pub bcp_blocker_fastpath_hits: u64,
    /// BCP telemetry: binary watcher path hits.
    pub bcp_binary_path_hits: u64,
    /// SEARCH BCP route telemetry: in-place watch scan route invocations.
    pub bcp_search_inplace_watch_scan_exercised: u64,
    /// Jump reasons (#8034): binary reason chains compressed (Kissat INC(jumped_reasons)).
    pub jumped_reasons: u64,
    /// BCP telemetry: literals examined in replacement scans.
    pub bcp_replacement_scan_steps: u64,
    /// BCP telemetry: replacement scan steps attributed to binary clauses.
    ///
    /// Binary clauses do not run replacement scans; this stays zero and makes
    /// the binary/non-binary attribution explicit in stats output.
    pub bcp_replacement_scan_steps_binary: u64,
    /// BCP telemetry: replacement scan steps attributed to non-binary clauses.
    pub bcp_replacement_scan_steps_non_binary: u64,
    /// BCP telemetry: replacement scan steps in learned non-binary clauses.
    pub bcp_replacement_scan_steps_learned: u64,
    /// BCP telemetry: replacement scan steps in original non-binary clauses.
    pub bcp_replacement_scan_steps_original: u64,
    /// Sequential Main BCP: long-clause blocker short-circuits.
    pub bcp_long_blocker_fastpath_hits: u64,
    /// Sequential Main BCP: long replacement scan steps by clause-length bucket.
    pub bcp_long_scan_steps_by_len: [u64; BCP_LONG_SCAN_BUCKETS],
    /// Sequential Main BCP: learned long replacement scan steps by length bucket.
    pub bcp_long_scan_steps_learned_by_len: [u64; BCP_LONG_SCAN_BUCKETS],
    /// Sequential Main BCP: original long replacement scan steps by length bucket.
    pub bcp_long_scan_steps_original_by_len: [u64; BCP_LONG_SCAN_BUCKETS],
    /// Sequential Main BCP: long replacement scans by clause-length bucket.
    pub bcp_long_scan_by_len: [u64; BCP_LONG_SCAN_BUCKETS],
    /// Sequential Main BCP: long scans that found any replacement.
    pub bcp_long_scan_found_replacement_by_len: [u64; BCP_LONG_SCAN_BUCKETS],
    /// Sequential Main BCP: long scans that found a true replacement.
    pub bcp_long_scan_found_true_by_len: [u64; BCP_LONG_SCAN_BUCKETS],
    /// Sequential Main BCP: long scans that found an unassigned replacement.
    pub bcp_long_scan_found_unassigned_by_len: [u64; BCP_LONG_SCAN_BUCKETS],
    /// Sequential Main BCP: long scans that found no replacement/full-scanned.
    pub bcp_long_scan_no_replacement_by_len: [u64; BCP_LONG_SCAN_BUCKETS],
    /// Sequential Main BCP: long no-replacement scans ending in unit propagation.
    pub bcp_long_scan_unit_by_len: [u64; BCP_LONG_SCAN_BUCKETS],
    /// Sequential Main BCP: long no-replacement scans ending in conflict.
    pub bcp_long_scan_conflict_by_len: [u64; BCP_LONG_SCAN_BUCKETS],
    /// Sequential Main BCP: learned long replacement scans by length bucket.
    pub bcp_long_scan_learned_by_len: [u64; BCP_LONG_SCAN_BUCKETS],
    /// Sequential Main BCP: learned long scans that found any replacement.
    pub bcp_long_scan_learned_found_replacement_by_len: [u64; BCP_LONG_SCAN_BUCKETS],
    /// Sequential Main BCP: learned long no-replacement/full-scan outcomes.
    pub bcp_long_scan_learned_no_replacement_by_len: [u64; BCP_LONG_SCAN_BUCKETS],
    /// Sequential Main BCP: learned long no-replacement unit outcomes.
    pub bcp_long_scan_learned_unit_by_len: [u64; BCP_LONG_SCAN_BUCKETS],
    /// Sequential Main BCP: learned long no-replacement conflict outcomes.
    pub bcp_long_scan_learned_conflict_by_len: [u64; BCP_LONG_SCAN_BUCKETS],
    /// BCP telemetry: learned 19-63 true-tail relocation candidates.
    pub bcp_learned_1963_true_tail_relocation_attempts: u64,
    /// BCP telemetry: learned 19-63 true-tail relocations that moved a watch.
    pub bcp_learned_1963_true_tail_relocation_moves: u64,
    /// BCP telemetry: learned 19-63 used>=5 FSW reset eligible scans.
    pub bcp_learned_1963_used5_fsw_saved_pos_reset_eligible: u64,
    /// BCP telemetry: learned 19-63 used>=5 FSW reset header writes.
    pub bcp_learned_1963_used5_fsw_saved_pos_reset_writes: u64,
    /// BCP telemetry: learned 19-63 used>=5 FSW reset unit outcomes.
    pub bcp_learned_1963_used5_fsw_saved_pos_reset_unit: u64,
    /// BCP telemetry: learned 19-63 used>=5 FSW reset conflict outcomes.
    pub bcp_learned_1963_used5_fsw_saved_pos_reset_conflict: u64,
    /// BCP telemetry: learned 19-63 FSW conflict-only reset eligible scans.
    pub bcp_learned_1963_fsw_conflict_saved_pos_reset_eligible: u64,
    /// BCP telemetry: learned 19-63 FSW conflict-only reset header writes.
    pub bcp_learned_1963_fsw_conflict_saved_pos_reset_writes: u64,
    /// BCP telemetry: learned 19-63 FSW conflict-only reset conflict outcomes.
    pub bcp_learned_1963_fsw_conflict_saved_pos_reset_conflict: u64,
    /// BCP telemetry: learned 6-18 true-tail relocation candidates.
    pub bcp_learned_618_true_tail_relocation_attempts: u64,
    /// BCP telemetry: learned 6-18 true-tail relocations that moved a watch.
    pub bcp_learned_618_true_tail_relocation_moves: u64,
    /// BCP telemetry: learned no-replacement saved-position eligible scans.
    pub bcp_learned_no_replacement_saved_pos_eligible_by_len: [u64; BCP_LONG_SCAN_BUCKETS],
    /// BCP telemetry: learned no-replacement saved-position header writes.
    pub bcp_learned_no_replacement_saved_pos_writes_by_len: [u64; BCP_LONG_SCAN_BUCKETS],
    /// BCP telemetry: learned no-replacement saved-position skips already at tail head.
    pub bcp_learned_no_replacement_saved_pos_skipped_current_by_len: [u64; BCP_LONG_SCAN_BUCKETS],
    /// BCP telemetry: learned no-replacement saved-position unit outcomes.
    pub bcp_learned_no_replacement_saved_pos_unit_by_len: [u64; BCP_LONG_SCAN_BUCKETS],
    /// BCP telemetry: learned no-replacement saved-position conflict outcomes.
    pub bcp_learned_no_replacement_saved_pos_conflict_by_len: [u64; BCP_LONG_SCAN_BUCKETS],
    /// BCP telemetry: learned 19-63 FSW Gent-order skip candidates.
    pub bcp_learned_1963_fsw_gent_skip_candidates: u64,
    /// BCP telemetry: learned 19-63 FSW Gent-order skip applications.
    pub bcp_learned_1963_fsw_gent_skip_applied: u64,
    /// BCP telemetry: saved-start slots skipped by the FSW Gent-order gate.
    pub bcp_learned_1963_fsw_gent_skip_saved_slots: u64,
    /// BCP telemetry: FSW Gent-order skips that found a satisfied suffix replacement.
    pub bcp_learned_1963_fsw_gent_skip_found_true_suffix: u64,
    /// BCP telemetry: FSW Gent-order skips that found an unassigned suffix replacement.
    pub bcp_learned_1963_fsw_gent_skip_found_unassigned_suffix: u64,
    /// BCP telemetry: FSW Gent-order skips that found a satisfied prefix replacement.
    pub bcp_learned_1963_fsw_gent_skip_found_true_prefix: u64,
    /// BCP telemetry: FSW Gent-order skips that found an unassigned prefix replacement.
    pub bcp_learned_1963_fsw_gent_skip_found_unassigned_prefix: u64,
    /// BCP telemetry: FSW Gent-order no-replacement unit outcomes.
    pub bcp_learned_1963_fsw_gent_skip_no_replacement_unit: u64,
    /// BCP telemetry: FSW Gent-order no-replacement conflict outcomes.
    pub bcp_learned_1963_fsw_gent_skip_no_replacement_conflict: u64,
    /// BCP telemetry: gated learned no-replacement pressure scans.
    pub bcp_learned_no_replacement_scan_pressure_scans_by_len: [u64; BCP_LONG_SCAN_BUCKETS],
    /// BCP telemetry: gated scan steps spent in learned no-replacement scans.
    pub bcp_learned_no_replacement_scan_pressure_steps_by_len: [u64; BCP_LONG_SCAN_BUCKETS],
    /// BCP telemetry: gated learned no-replacement scans whose saved start was false.
    pub bcp_learned_no_replacement_scan_pressure_start_false_by_len: [u64; BCP_LONG_SCAN_BUCKETS],
    /// BCP telemetry: gated learned no-replacement scans that wrapped from saved_pos.
    pub bcp_learned_no_replacement_scan_pressure_wrapped_by_len: [u64; BCP_LONG_SCAN_BUCKETS],
    /// BCP telemetry: gated learned no-replacement scans ending in unit propagation.
    pub bcp_learned_no_replacement_scan_pressure_unit_by_len: [u64; BCP_LONG_SCAN_BUCKETS],
    /// BCP telemetry: gated learned no-replacement scans ending in conflict.
    pub bcp_learned_no_replacement_scan_pressure_conflict_by_len: [u64; BCP_LONG_SCAN_BUCKETS],
    /// BCP telemetry: learned 19-63 false-start-wrap unit scans by LBD bucket.
    pub bcp_learned_1963_fsw_unit_by_lbd: [u64; BCP_LEARNED_1963_PRESSURE_LBD_BUCKETS],
    /// BCP telemetry: learned 19-63 false-start-wrap conflict scans by LBD bucket.
    pub bcp_learned_1963_fsw_conflict_by_lbd: [u64; BCP_LEARNED_1963_PRESSURE_LBD_BUCKETS],
    /// BCP telemetry: learned 19-63 false-start-wrap unit scan steps by LBD bucket.
    pub bcp_learned_1963_fsw_unit_steps_by_lbd: [u64; BCP_LEARNED_1963_PRESSURE_LBD_BUCKETS],
    /// BCP telemetry: learned 19-63 false-start-wrap conflict scan steps by LBD bucket.
    pub bcp_learned_1963_fsw_conflict_steps_by_lbd: [u64; BCP_LEARNED_1963_PRESSURE_LBD_BUCKETS],
    /// BCP telemetry: learned 19-63 false-start-wrap unit scans by used bucket.
    pub bcp_learned_1963_fsw_unit_by_used: [u64; BCP_LEARNED_1963_PRESSURE_USED_BUCKETS],
    /// BCP telemetry: learned 19-63 false-start-wrap conflict scans by used bucket.
    pub bcp_learned_1963_fsw_conflict_by_used: [u64; BCP_LEARNED_1963_PRESSURE_USED_BUCKETS],
    /// BCP telemetry: learned 19-63 false-start-wrap unit scan steps by used bucket.
    pub bcp_learned_1963_fsw_unit_steps_by_used: [u64; BCP_LEARNED_1963_PRESSURE_USED_BUCKETS],
    /// BCP telemetry: learned 19-63 false-start-wrap conflict scan steps by used bucket.
    pub bcp_learned_1963_fsw_conflict_steps_by_used: [u64; BCP_LEARNED_1963_PRESSURE_USED_BUCKETS],
    /// BCP telemetry: learned 19-63 false-start-wrap events by clause-offset sketch bucket.
    pub bcp_learned_1963_fsw_repeat_by_bucket: [u64; BCP_LEARNED_1963_PRESSURE_REPEAT_BUCKETS],
    /// BCP telemetry: learned 19-63 false-start-wrap scan steps by clause-offset sketch bucket.
    pub bcp_learned_1963_fsw_repeat_steps_by_bucket:
        [u64; BCP_LEARNED_1963_PRESSURE_REPEAT_BUCKETS],
    /// BCP telemetry: maximum learned 19-63 false-start-wrap repeat bucket count.
    pub bcp_learned_1963_fsw_repeat_bucket_max: u64,
    /// Default-off exact learned 19-63 clause-identity pressure table.
    pub(crate) bcp_learned_1963_identity: Option<BcpLearned1963IdentityTable>,
    /// Default-off learned 19-63 secondary blocker certificates by arena offset.
    pub(crate) bcp_learned_1963_blocker_certs: Vec<Option<BcpLearned1963BlockerCert>>,
    /// BCP telemetry: learned 19-63 blocker-certificate lookup candidates.
    pub bcp_learned_1963_blocker_cert_candidates: u64,
    /// BCP telemetry: learned 19-63 blocker-certified replacement-scan elisions.
    pub bcp_learned_1963_blocker_cert_elisions: u64,
    /// BCP telemetry: shadow probes where a true certificate would have elided.
    pub bcp_learned_1963_blocker_cert_shadow_hits: u64,
    /// BCP telemetry: shadow probes whose normal scan chose a different replacement.
    pub bcp_learned_1963_blocker_cert_shadow_mismatches: u64,
    /// BCP telemetry: mismatched blocker certificates cleared by demotion.
    pub bcp_learned_1963_blocker_cert_mismatch_demotions: u64,
    /// BCP telemetry: learned 19-63 blocker certificates populated/refreshed.
    pub bcp_learned_1963_blocker_cert_populates: u64,
    /// BCP telemetry: learned 19-63 blocker certificates rejected as stale.
    pub bcp_learned_1963_blocker_cert_stale_rejects: u64,
    /// BCP telemetry: learned 19-63 blocker certificates rejected as non-true.
    pub bcp_learned_1963_blocker_cert_false_rejects: u64,
    /// BCP telemetry: false-rejected blocker certificates cleared by demotion.
    pub bcp_learned_1963_blocker_cert_false_reject_demotions: u64,
    /// BCP telemetry: learned 19-63 blocker certificates rejected by repeat guard.
    pub bcp_learned_1963_blocker_cert_repeat_rejects: u64,
    /// BCP telemetry: suffix slots elided after prefix validation by cert elision.
    pub bcp_learned_1963_blocker_cert_elided_suffix_slots: u64,
    /// BCP telemetry: suffix slots shadow hits would elide after prefix validation.
    pub bcp_learned_1963_blocker_cert_shadow_elided_suffix_slots: u64,
    /// BCP telemetry: certificates/elisions seeded from false-start-wrap scans.
    pub bcp_learned_1963_blocker_cert_affected_fsw_rows: u64,
    /// BCP telemetry: shadow hits seeded from false-start-wrap scans.
    pub bcp_learned_1963_blocker_cert_shadow_affected_fsw_rows: u64,
    #[cfg(test)]
    pub(crate) bcp_learned_1963_blocker_cert_elision_test_enabled: bool,
    #[cfg(test)]
    pub(crate) bcp_learned_1963_blocker_cert_shadow_test_enabled: bool,
    #[cfg(test)]
    pub(crate) bcp_learned_1963_blocker_cert_false_reject_demote_test_enabled: bool,
    /// BCP telemetry: learned 6-17 creation-time tail reorder candidates.
    pub bcp_learned_617_tail_reorder_candidates: u64,
    /// BCP telemetry: learned 6-17 creation-time tail reorders exercised.
    pub bcp_learned_617_tail_reorder_exercised: u64,
    /// BCP telemetry: learned 6-17 creation-time tail reorders that changed order.
    pub bcp_learned_617_tail_reorder_changed: u64,
    /// BCP telemetry: adjacent swaps made by learned 6-17 tail reorder.
    pub bcp_learned_617_tail_reorder_swaps: u64,
    /// BCP telemetry: learned length-18 creation-time tail reorder candidates.
    pub bcp_learned_18_tail_reorder_candidates: u64,
    /// BCP telemetry: learned length-18 creation-time tail reorders exercised.
    pub bcp_learned_18_tail_reorder_exercised: u64,
    /// BCP telemetry: learned length-18 creation-time tail reorders that changed order.
    pub bcp_learned_18_tail_reorder_changed: u64,
    /// BCP telemetry: adjacent swaps made by learned length-18 tail reorder.
    pub bcp_learned_18_tail_reorder_swaps: u64,
    /// BCP telemetry: learned 19-63 creation-time tail reorder candidates.
    pub bcp_learned_1963_tail_reorder_candidates: u64,
    /// BCP telemetry: learned 19-63 creation-time tail reorders that changed order.
    pub bcp_learned_1963_tail_reorder_changed: u64,
    /// BCP telemetry: adjacent swaps made by learned 19-63 tail reorder.
    pub bcp_learned_1963_tail_reorder_swaps: u64,
    /// BCP telemetry: budgeted learned 19-63 tail reorder candidates.
    pub bcp_learned_1963_tail_reorder_budget_candidates: u64,
    /// BCP telemetry: budgeted learned 19-63 tail reorders applied.
    pub bcp_learned_1963_tail_reorder_budget_applied: u64,
    /// BCP telemetry: budgeted learned 19-63 tail reorders skipped over budget.
    pub bcp_learned_1963_tail_reorder_budget_skipped_over_budget: u64,
    /// BCP telemetry: adjacent swaps applied by budgeted learned 19-63 tail reorder.
    pub bcp_learned_1963_tail_reorder_budget_swaps_applied: u64,
    /// BCP telemetry: adjacent swaps skipped by budgeted learned 19-63 tail reorder.
    pub bcp_learned_1963_tail_reorder_budget_swaps_skipped: u64,
    /// BCP telemetry: long-clause saved-position replacement scans.
    pub bcp_long_saved_pos_scans: u64,
    /// BCP telemetry: long scans whose normalized saved position starts false.
    pub bcp_long_saved_pos_start_false: u64,
    /// BCP telemetry: long scans that found a satisfied replacement.
    pub bcp_long_saved_pos_found_true: u64,
    /// BCP telemetry: long scans that found an unassigned replacement.
    pub bcp_long_saved_pos_found_unassigned: u64,
    /// BCP telemetry: long scans that found no replacement.
    pub bcp_long_saved_pos_no_replacement: u64,
    /// BCP telemetry: length-18 saved-position replacement scans.
    pub bcp_len18_saved_pos_scans: u64,
    /// BCP telemetry: length-18 scans whose normalized saved position starts false.
    pub bcp_len18_saved_pos_start_false: u64,
    /// BCP telemetry: length-18 scans that found a satisfied replacement.
    pub bcp_len18_saved_pos_found_true: u64,
    /// BCP telemetry: length-18 scans that found an unassigned replacement.
    pub bcp_len18_saved_pos_found_unassigned: u64,
    /// BCP telemetry: length-18 scans that found no replacement.
    pub bcp_len18_saved_pos_no_replacement: u64,
    /// LRAT level-0 unit materialization calls for deletion/conflict hints.
    pub lrat_materialize_calls: u64,
    /// LRAT minimize-chain level-0 unit materialization calls.
    pub lrat_materialize_minimize_calls: u64,
    /// Root-trail entries scanned by standard LRAT unit materialization.
    pub lrat_materialize_root_trail_entries: u64,
    /// Root-trail entries scanned by minimize-chain LRAT unit materialization.
    pub lrat_materialize_minimize_root_trail_entries: u64,
    /// Visible derived unit proof lines emitted by standard materialization.
    pub lrat_materialize_emitted_unit_lines: u64,
    /// Visible derived unit proof lines emitted by minimize-chain materialization.
    pub lrat_materialize_minimize_emitted_unit_lines: u64,
    /// LRAT hint IDs used by visible standard materialized unit lines.
    pub lrat_materialize_unit_hints: u64,
    /// LRAT hint IDs used by visible minimize-chain materialized unit lines.
    pub lrat_materialize_minimize_unit_hints: u64,
    /// Maximum hint count on one visible standard materialized unit line.
    pub lrat_materialize_unit_max_hints: u64,
    /// Maximum hint count on one visible minimize-chain materialized unit line.
    pub lrat_materialize_minimize_unit_max_hints: u64,
    /// Standard materialization attempts skipped because the hint chain was incomplete.
    pub lrat_materialize_incomplete_chains: u64,
    /// Minimize materialization attempts skipped because the hint chain was incomplete.
    pub lrat_materialize_minimize_incomplete_chains: u64,
    /// Standard materialization fallbacks emitted as hidden TrustedTransform units.
    pub lrat_materialize_hidden_trusted_units: u64,
    /// LRAT level-0 unit-chain collection calls.
    pub lrat_unit_chain_calls: u64,
    /// Root-trail entries scanned by LRAT unit-chain collection.
    pub lrat_unit_chain_root_trail_entries: u64,
    /// LRAT hint IDs emitted by unit-chain collection.
    pub lrat_unit_chain_hints: u64,
    /// Maximum hint count emitted by one LRAT unit-chain collection.
    pub lrat_unit_chain_max_hints: u64,
    /// Unit-chain candidates that lacked an externally visible LRAT hint ID.
    pub lrat_unit_chain_missing_hints: u64,
    /// Level-0 preprocess telemetry: literals removed as root-false.
    pub preprocess_level0_literals_removed: u64,
    /// Level-0 preprocess telemetry: satisfied clauses deleted.
    pub preprocess_level0_satisfied_deleted: u64,
    /// Total random decisions made.
    pub random_decisions: u64,
    /// OTFS (on-the-fly self-subsumption) strengthening count.
    pub otfs_strengthened: u64,
    /// OTFS (on-the-fly self-subsumption) trigger count.
    pub otfs_subsumed: u64,
    /// OTFS diagnostic: candidate count (resolvent_size < antecedent_size).
    pub otfs_candidates: u64,
    /// OTFS diagnostic: blocked by open==0.
    pub otfs_blocked_open0: u64,
    /// OTFS diagnostic: blocked by watch invariant.
    pub otfs_blocked_watch: u64,
    /// OTFS diagnostic: blocked by otfs_strengthen returning false.
    pub otfs_blocked_strengthen: u64,
    /// OTFS Branch B: strengthened clause was asserting (skip learning).
    pub otfs_branch_b: u64,
    /// OTFS Branch C: analysis restarted from strengthened clause.
    pub otfs_branch_c: u64,
    /// OTFS on-the-fly subsumption: conflict clause subsumed by strengthened reason.
    pub otfs_clause_subsumed: u64,
    /// Forced-literal early return count (CaDiCaL analyze.cpp:977-1004).
    /// Single literal at conflict level → skip 1UIP, use clause as driver.
    pub forced_backtracks: u64,
    /// Focused-mode Glucose EMA checks (number of times condition was evaluated).
    pub focused_ema_checks: u64,
    /// Focused-mode Glucose EMA fires (condition was true → restart).
    pub focused_ema_fires: u64,
    /// Stable-mode reluctant doubling fires (countdown reached 0 → restart).
    pub stable_reluctant_fires: u64,
    /// Stable-mode Glucose EMA fires (fast > 1.25 * slow → restart).
    pub stable_ema_fires: u64,
    /// Cumulative sum of LBD values fed to EMA updates.
    pub lbd_sum: u64,
    /// Count of LBD values fed to EMA updates.
    pub lbd_count: u64,
    /// Focused-mode: EMA condition true but blocked by conflict gate.
    pub focused_ema_blocked_by_conflict_gate: u64,
    /// Dense-mutex focused restart route raised the focused conflict gate.
    pub dense_mutex_focused_restart_gate_updates: u64,
    /// Dense-mutex focused restart runtime predicate snapshots taken.
    pub dense_mutex_focused_restart_runtime_checked: u64,
    /// Active variables at the dense-mutex focused restart runtime check.
    pub dense_mutex_focused_restart_active_vars: u64,
    /// Active clauses at the dense-mutex focused restart runtime check.
    pub dense_mutex_focused_restart_active_clauses: u64,
    /// Active binary clauses at the dense-mutex focused restart runtime check.
    pub dense_mutex_focused_restart_active_binary_clauses: u64,
    /// Whether the runtime dense-mutex focused restart candidate predicate held.
    pub dense_mutex_focused_restart_runtime_candidate: u64,
    /// Focused restart gate before the runtime dense-mutex focused restart check.
    pub dense_mutex_focused_restart_previous_gate: u64,
    /// Computed dense-mutex focused restart gate, or zero if not a candidate.
    pub dense_mutex_focused_restart_computed_gate: u64,
    /// Dense-clique MAB branch route was enabled by variant/profile planning.
    pub dense_clique_mab_branch_route_enabled: u64,
    /// Branch decisions made while the dense-clique MAB branch route was enabled.
    pub dense_clique_mab_branch_route_exercised: u64,
    /// Focused-mode: restart blocked by trail-length heuristic (#8449).
    /// Glucose trail blocking (Audemard & Simon, CP 2012): suppresses restarts
    /// when the current trail is longer than the slow-moving average.
    pub trail_blocked_restarts: u64,
    /// Restart decisions attributed to their primary cause.
    pub restart_attribution: [u64; RESTART_ATTRIBUTION_BUCKETS],
    /// Restart decisions by current mode: [focused, stable].
    pub restart_attribution_modes: [u64; RESTART_MODE_BUCKETS],
    /// Candidate restart attribution from the most recent true restart predicate.
    ///
    /// This is committed only after all restart blockers allow an actual restart.
    pub(crate) pending_restart_attribution: Option<(RestartAttribution, bool)>,
    /// Rephase operations attributed to the selected strategy.
    pub rephase_attribution: [u64; REPHASE_ATTRIBUTION_BUCKETS],
    /// Rephase operations by current mode: [focused, stable].
    pub rephase_attribution_modes: [u64; REPHASE_MODE_BUCKETS],
    /// Phase entries changed by directly counted rephase strategies.
    pub rephase_direct_changed_phases: u64,
    /// Non-zero saved phases copied into target phase during rephase.
    pub rephase_target_phase_updates: u64,
    /// Best-trail resets caused by Best rephases.
    pub rephase_best_resets: u64,
    /// Cold restarts performed (Zhang et al. 2024, arXiv:2404.16387).
    pub cold_restarts: u64,
    /// Focused-mode decisions (for computing focused dec/confl).
    pub focused_decisions: u64,
    /// Stable-mode decisions.
    pub stable_decisions: u64,
    /// Cumulative per-pass inprocessing wall time in nanoseconds.
    pub inprocessing_time_ns: [u64; INPROCESS_TIMING_LABELS.len()],
    /// Per-pass attempt/run/yield counters for policy tuning.
    pub inprocessing_pass_attempts: [u64; INPROCESS_ACCOUNTING_LABELS.len()],
    pub inprocessing_pass_runs: [u64; INPROCESS_ACCOUNTING_LABELS.len()],
    pub inprocessing_pass_yields: [u64; INPROCESS_ACCOUNTING_LABELS.len()],
    /// LRAT rounds where BVE would be due by cadence/fixpoint gates but is
    /// proof-clamped.
    pub inprocessing_lrat_clamped_bve_due_rounds: u64,
    /// LRAT rounds where factor would be due by cadence/mark gates but is
    /// proof-clamped.
    pub inprocessing_lrat_clamped_factor_due_rounds: u64,
    /// Default-off LRAT-safe probe rescue rounds scheduled from proof-clamped
    /// BVE/factor eligibility.
    pub inprocessing_lrat_probe_rescue_rounds: u64,
    /// Default-off yield-rescue rounds where the shared backbone row was pushed
    /// out by the bounded cooldown experiment.
    pub inprocessing_yield_rescue_backbone_cooldown_rounds: u64,
    /// Default-off bounded-CDCL-only backbone backoff triggers.
    pub bounded_backbone_backoff_triggers: u64,
    /// Bounded-CDCL backbone calls, excluding binary-backbone calls.
    pub bounded_backbone_runs: u64,
    /// Bounded-CDCL backbone calls that produced a pass-local yield.
    pub bounded_backbone_yields: u64,
    /// Bounded-CDCL backbone wall time, excluding binary-backbone calls.
    pub bounded_backbone_ms: u64,
    /// Binary-backbone suppressions caused by the bounded-only cooldown.
    ///
    /// This counter should remain zero; it is exported to make the #9084 kill
    /// threshold mechanically visible in A/B packets.
    pub bounded_backbone_binary_suppressed: u64,
    /// Number of completed inprocessing rounds (#8099).
    pub inprocessing_rounds: u64,
    /// Number of completed incremental inprocessing rounds (#8208).
    /// These run between solve_with_assumptions() calls in incremental mode,
    /// using only safe techniques (subsumption, vivification, transred).
    pub incremental_inprocessing_rounds: u64,
    /// Cumulative time in rebuild_watches (microseconds) (#8103).
    /// This is the combined total for both full and incremental paths.
    pub rebuild_watches_us: u64,
    /// Number of rebuild_watches calls (#8103).
    /// Combined total for both full and incremental paths.
    pub rebuild_watches_calls: u64,
    /// Cumulative time in full rebuild_watches only (microseconds) (#8103).
    pub full_rebuild_watches_us: u64,
    /// Number of full rebuild_watches calls (#8103).
    pub full_rebuild_watches_calls: u64,
    /// Cumulative time in reconnect_bve_watches only (microseconds) (#8103).
    pub incremental_reconnect_watches_us: u64,
    /// Number of reconnect_bve_watches calls (#8103).
    pub incremental_reconnect_watches_calls: u64,
    /// Total simplifications across all inprocessing rounds (#8099).
    /// Counts clauses removed + literals strengthened per round.
    pub inprocessing_simplifications: u64,
    /// GPU BVE: completed GPU resolvent dispatches.
    pub gpu_bve_dispatches: u64,
    /// GPU BVE: ordered positive/negative clause pairs processed.
    pub gpu_bve_pairs: u64,
    /// GPU BVE: tautological resolvents skipped after GPU generation.
    pub gpu_bve_tautologies: u64,
    /// Wall-clock time spent in preprocessing phase (nanoseconds).
    pub preprocess_time_ns: u64,
    /// Wall-clock time spent in CDCL search loop (nanoseconds).
    pub search_time_ns: u64,
    /// Wall-clock time spent in lucky-phase probing (nanoseconds).
    pub lucky_time_ns: u64,
    /// Wall-clock time spent in walk-based phase initialization (nanoseconds).
    pub walk_time_ns: u64,
    /// Number of MAB arm switches (branch heuristic changes via UCB1).
    pub mab_arm_switches: u64,
    /// Retired SAT propagation compiler: propagations discovered by native code.
    /// Retained as zeroed telemetry after production removal in #8517.
    pub jit_propagations: u64,
    /// Retired SAT propagation compiler: conflicts found by native code.
    /// Retained as zeroed telemetry after production removal in #8517.
    pub jit_conflicts: u64,
    /// Retired SAT propagation compiler: calls skipped by blocker-literal pre-check (#8520).
    /// When a blocker literal is satisfied, the entire JIT function call
    /// can be skipped (1 load + 1 branch vs ~50-500 instructions).
    pub jit_blocker_skips: u64,
    /// Retired SAT propagation compiler: trail literals dispatched to native code (#8517).
    pub jit_hybrid_jit_literals: u64,
    /// Retired SAT propagation compiler: trail literals dispatched to 2WL (#8517).
    pub jit_hybrid_2wl_literals: u64,
    /// Retired SAT propagation compiler: compile time in microseconds.
    pub jit_compile_time_us: u64,
    /// Retired SAT propagation compiler: number of clauses compiled into native code.
    pub jit_clauses_compiled: u64,
    /// Retired SAT propagation compiler: learned clauses compiled (subset of jit_clauses_compiled, #8229).
    pub jit_learned_clauses_compiled: u64,
    /// Retired SAT propagation compiler: total 2WL watch entries detached for native clauses (#8005).
    pub jit_watches_detached: u64,
    /// Retired SAT propagation compiler: total 2WL watch entries reattached after invalidation (#8005).
    pub jit_watches_reattached: u64,
    /// JIT: number of inprocessing rounds where recompilation was skipped
    /// because only deletion-only passes ran (guard bits handle deletion).
    pub jit_recompilations_skipped: u64,
    /// JIT: number of full recompilations after structural inprocessing passes.
    pub jit_recompilations: u64,
    /// JIT: delta recompilations (reusing code for clean variables, #8228).
    pub jit_delta_recompilations: u64,
    /// JIT: incremental compilations from lazy deferred pairs (#8227).
    pub jit_incremental_compilations: u64,
    /// JIT: total pairs compiled incrementally (#8227).
    pub jit_incremental_pairs: u64,
    /// JIT: guard-based clause deletions (clauses marked deleted via guard bits
    /// instead of full recompilation).
    pub jit_guard_deletions: u64,
    /// JIT: whether the most recent compilation used rayon parallel codegen.
    pub jit_parallel_compiled: bool,
    /// JIT: incremental cache hits across solve() calls (#8225).
    /// A cache hit means the previous JIT compilation was reused via
    /// delta recompilation instead of a full recompile.
    pub jit_cache_hits: u64,
    /// JIT: incremental cache misses across solve() calls (#8225).
    /// A cache miss means a full recompile was needed (formula changed
    /// too much or no cache was available).
    pub jit_cache_misses: u64,
    /// JIT PGO: number of PGO recompilations performed (#8266).
    pub jit_pgo_recompilations: u64,
    /// JIT PGO: number of hot functions recompiled with prefetch (#8266).
    pub jit_pgo_hot_functions: u64,
    /// JIT PGO: number of cold functions removed (#8266).
    pub jit_pgo_cold_removed: u64,
    /// JIT: learned clauses promoted to tier-1 and marked for recompilation (#8177).
    pub jit_tier_promotions: u64,
    /// JIT: recompilations triggered by accumulated tier-1 promotions (#8177).
    pub jit_tier_promotion_recompilations: u64,
    /// JIT: number of scoped clauses skipped during compilation (#8392).
    /// Counted when scope-aware JIT filtering excludes clauses containing
    /// scope selector variables from the compiled formula.
    pub jit_scope_skipped_clauses: u64,
    /// Code cache: total mmap'd executable bytes across all JIT allocations (#8394).
    pub code_cache_total_bytes: usize,
    /// Code cache: peak total allocation observed (#8394).
    pub code_cache_peak_bytes: usize,
    /// Code cache: number of LRU evictions performed (#8394).
    pub code_cache_evictions: u64,
    /// Code cache: total bytes freed by eviction (#8394).
    pub code_cache_bytes_evicted: u64,
    /// Whether SAT native-code helper compilation is enabled for this solve.
    pub native_code_helpers_enabled: bool,
    /// Current compilation tier (T0-T4) as reported by the tier controller.
    pub compilation_tier: &'static str,
    /// Number of tier promotions executed by the tier controller.
    pub tier_controller_promotions: u64,
    /// SAT whole-loop guard artifacts installed at solver-start boundaries.
    pub sat_whole_loop_guard_installs: u64,
    /// SAT whole-loop guard artifacts applied after runtime profile guards pass.
    pub sat_whole_loop_guard_applications: u64,
    /// SAT propagation native telemetry: whether a native propagation artifact is active.
    /// The current production path keeps this false after #8517.
    pub sat_propagation_native_active: bool,
    /// SAT propagation native telemetry: number of compiled irredundant clauses.
    pub sat_propagation_native_clauses: u64,
    /// SAT propagation native telemetry: number of propagation rounds using native code.
    pub sat_propagation_native_rounds: u64,
    /// SAT propagation native telemetry: total propagations from native code.
    pub sat_propagation_native_propagations: u64,
    /// SAT propagation native telemetry: conflicts found by native code.
    pub sat_propagation_native_conflicts: u64,
    /// SAT propagation native telemetry: compilation time in microseconds.
    pub sat_propagation_native_compile_time_us: u64,
    /// SAT conflict-analysis native helper applications.
    ///
    /// Counts successful dispatches through the non-BCP 1UIP conflict-analysis
    /// processor, not compile attempts.
    pub sat_conflict_analysis_native_applications: u64,
    /// Dense propagation: total propagations during elimination phases (#8088).
    pub dense_propagations: u64,
    /// Dense propagation: conflicts found via dense propagation (#8088).
    pub dense_conflicts: u64,
    /// Dense propagation: satisfied clauses deleted during dense propagation (#8088).
    pub dense_satisfied_deleted: u64,
    /// Reduction L0-satisfied prepass: occ-guided scans.
    pub reduction_l0_satisfied_occ_scans: u64,
    /// Reduction L0-satisfied prepass: full arena fallback scans.
    pub reduction_l0_satisfied_full_scans: u64,
    /// Reduction L0-satisfied prepass: no-gc_occ full scans skipped.
    pub reduction_l0_satisfied_no_occ_skips: u64,
    /// Reduction L0-satisfied prepass: clauses deleted.
    pub reduction_l0_satisfied_deleted: u64,
    /// Learned clause reduction telemetry: active learned clauses considered.
    pub learned_reduction_considered: u64,
    /// Learned clause reduction telemetry: learned clauses deleted.
    pub learned_reduction_deleted: u64,
    /// Learned clause reduction telemetry: clauses protected because they are reasons.
    pub learned_reduction_reason_protected: u64,
    /// Learned clause reduction telemetry: IC3 lemmas protected from deletion.
    pub learned_reduction_ic3_protected: u64,
    /// Learned clause reduction telemetry: low-LBD clauses protected from deletion.
    pub learned_reduction_low_lbd_protected: u64,
    /// Learned clause reduction telemetry: recently-used clauses protected by tier policy.
    pub learned_reduction_usage_protected: u64,
    /// Learned clause reduction telemetry: candidates kept by the reduce target quota.
    pub learned_reduction_target_kept: u64,
    /// Learned clause reduction telemetry: delete attempts skipped because LRAT retained an active clause.
    pub learned_reduction_lrat_retained_delete_skips: u64,
    /// Learned clause reduction telemetry: unused hyper clauses deleted.
    pub learned_reduction_hyper_deleted: u64,
    /// Learned clause reduction telemetry: recently-used hyper clauses kept.
    pub learned_reduction_hyper_kept: u64,
    /// Learned 19-63 pressure reduction: eligible already-deletable candidates seen.
    pub learned_1963_pressure_reduction_candidates: u64,
    /// Learned 19-63 pressure reduction: candidates with exact pressure rows.
    pub learned_1963_pressure_reduction_pressure_candidates: u64,
    /// Learned 19-63 pressure reduction: candidates whose rank was biased.
    pub learned_1963_pressure_reduction_ranked: u64,
    /// Learned 19-63 pressure reduction: total low-word rank bias applied.
    pub learned_1963_pressure_reduction_rank_bias_total: u64,
    /// Learned 19-63 pressure reduction: biased candidates selected by the delete quota.
    pub learned_1963_pressure_reduction_selected: u64,
    /// Learned 19-63 pressure reduction: pressure steps selected by the delete quota.
    pub learned_1963_pressure_reduction_selected_steps: u64,
    /// Learned 19-63 pressure reduction: biased candidates actually deleted.
    pub learned_1963_pressure_reduction_deleted: u64,
    /// Learned 19-63 pressure reduction: pressure steps actually deleted.
    pub learned_1963_pressure_reduction_deleted_steps: u64,
    /// Learned 19-63 pressure reduction: biased candidates kept by the quota.
    pub learned_1963_pressure_reduction_kept: u64,
    /// Learned 19-63 pressure reduction: pressure steps kept by the quota.
    pub learned_1963_pressure_reduction_kept_steps: u64,
    /// Learned 19-63 pressure reduction: eligible candidates without usable pressure.
    pub learned_1963_pressure_reduction_skipped_no_pressure: u64,
    /// Learned 19-63 pressure reduction: selected biased candidates retained by LRAT.
    pub learned_1963_pressure_reduction_lrat_retained_delete_skips: u64,
    /// Learned 19-63 pressure retention: eligible already-deletable candidates seen.
    pub learned_1963_pressure_retention_candidates: u64,
    /// Learned 19-63 pressure retention: candidates with exact pressure rows.
    pub learned_1963_pressure_retention_pressure_candidates: u64,
    /// Learned 19-63 pressure retention: candidates whose rank was biased.
    pub learned_1963_pressure_retention_ranked: u64,
    /// Learned 19-63 pressure retention: total low-word rank bias applied.
    pub learned_1963_pressure_retention_rank_bias_total: u64,
    /// Learned 19-63 pressure retention: biased candidates selected by the delete quota.
    pub learned_1963_pressure_retention_selected: u64,
    /// Learned 19-63 pressure retention: pressure steps selected by the delete quota.
    pub learned_1963_pressure_retention_selected_steps: u64,
    /// Learned 19-63 pressure retention: biased candidates actually deleted.
    pub learned_1963_pressure_retention_deleted: u64,
    /// Learned 19-63 pressure retention: pressure steps actually deleted.
    pub learned_1963_pressure_retention_deleted_steps: u64,
    /// Learned 19-63 pressure retention: biased candidates kept by the quota.
    pub learned_1963_pressure_retention_kept: u64,
    /// Learned 19-63 pressure retention: pressure steps kept by the quota.
    pub learned_1963_pressure_retention_kept_steps: u64,
    /// Learned 19-63 pressure retention: eligible candidates without usable pressure.
    pub learned_1963_pressure_retention_skipped_no_pressure: u64,
    /// Learned 19-63 pressure retention: selected biased candidates retained by LRAT.
    pub learned_1963_pressure_retention_lrat_retained_delete_skips: u64,
    /// Learned clause LBD distribution buckets (#8131).
    /// [0]=LBD 1, [1]=LBD 2, [2]=LBD 3-5, [3]=LBD 6-10, [4]=LBD 11+
    pub lbd_buckets: [u64; 5],
    /// Lookahead rounds completed (#8087).
    pub lookahead_rounds: u64,
    /// Failed literals discovered during lookahead probing (#8087).
    pub lookahead_failed_literals: u64,
    /// Lookahead decisions actually used (not stale) (#8087).
    pub lookahead_decisions_used: u64,
    /// Peak decision level observed during solving.
    pub peak_decision_level: u32,
    /// Cumulative decision level sum (for computing average decision level).
    pub decision_level_sum: u64,
    /// Count of decisions for average decision level computation.
    pub decision_level_count: u64,
    /// Dirty-literal flush: total dirty literals processed (#8101).
    pub flush_dirty_lits: u64,
    /// Dirty-literal flush: total stale watch entries removed (#8101).
    pub flush_watches_removed: u64,
    /// Watch lists shrunk after reduce_db (over-provisioned capacity reclaimed, #8031).
    pub watches_shrunk: u64,
    /// Minimal trail rewind (#8095): rewinds where no position was affected.
    pub trail_rewind_skipped: u64,
    /// Minimal trail rewind (#8095): rewinds to a position > 0.
    pub trail_rewind_partial: u64,
    /// Minimal trail rewind (#8095): full rewinds to position 0.
    pub trail_rewind_full: u64,
    /// Minimal trail rewind (#8095): cumulative trail entries saved.
    pub trail_rewind_saved_entries: u64,
    /// Cumulative nanoseconds of BCP re-propagation after rebuild_watches (#8103).
    /// Measures the wall time of the first propagate() call after each rebuild.
    /// Comparing propagations/ns here vs overall quantifies cache behavior.
    pub post_rebuild_bcp_ns: u64,
    /// Propagations during re-propagation after rebuild_watches (#8103).
    pub post_rebuild_bcp_propagations: u64,
    /// Post-rebuild BCP ns for full rebuild path only (#8103).
    pub post_full_rebuild_bcp_ns: u64,
    /// Post-rebuild BCP propagations for full rebuild path only (#8103).
    pub post_full_rebuild_bcp_propagations: u64,
    /// Post-rebuild BCP ns for incremental reconnect path only (#8103).
    pub post_incremental_reconnect_bcp_ns: u64,
    /// Post-rebuild BCP propagations for incremental reconnect path only (#8103).
    pub post_incremental_reconnect_bcp_propagations: u64,
    /// IBCL (#8269): number of times the interpolation-based clause learning
    /// pass was attempted (requires LRAT/proof mode active).
    pub ibcl_attempts: u64,
    /// IBCL (#8269): number of times the interpolant clause was strictly shorter
    /// than the 1UIP clause and replaced it.
    pub ibcl_improvements: u64,
    /// IBCL (#8269): number of times the IBCL pass was skipped because the
    /// resolution chain was too short for meaningful interpolation (< 3 steps).
    pub ibcl_skipped_short_chain: u64,
    /// IBCL (#8269): number of long proof chains skipped because the
    /// resolution skeleton lacks pivot metadata required for interpolation.
    pub ibcl_skipped_missing_pivots: u64,
    /// BCP-theory fixed-point (#8003): number of times the inner loop was entered.
    pub bcp_theory_fixpoint_entries: u64,
    /// BCP-theory fixed-point (#8003): total iterations across all entries.
    pub bcp_theory_fixpoint_iterations: u64,
    /// BCP-theory fixed-point (#8003): maximum depth reached in any single entry.
    pub bcp_theory_fixpoint_max_depth: u32,
    /// BCP-theory fixed-point (#8003): times MAX_FIXPOINT_ITERS was reached.
    pub bcp_theory_fixpoint_saturated: u64,
    /// Phase C (#4919): number of interleaved `propagate_force` calls made
    /// because the initial theory call returned `Continue` but BCP propagated
    /// SAT atoms — matching Z3's `propagate_core` pattern.
    pub bcp_theory_interleaved_force_calls: u64,
    /// Phase C (#4919): number of interleaved `propagate_force` calls that
    /// found new theory work (returned non-`Continue`). High ratio indicates
    /// BCP-interleaved propagation is paying off on this benchmark.
    pub bcp_theory_interleaved_force_hits: u64,
    /// Binary-clause backbone detection (#3274): backbone units found via
    /// binary-only propagation (CaDiCaL backbone_propagate2 + backbone_analyze).
    pub backbone_binary_units: u64,
    /// Occ list incremental refreshes (#8403): times the O(mutation) incremental
    /// path was used instead of a full O(formula) rebuild.
    pub occ_incremental_refreshes: u64,
    /// Occ list full rebuilds (#8403): times the O(formula) full rebuild path
    /// was used (first round of each BVE phase, or when occ lists not populated).
    pub occ_full_rebuilds: u64,
    /// Between-solve learned clause reductions triggered (#8435).
    /// Counts how many times `between_solve_reduce` ran during incremental
    /// sessions to prune accumulated learned clauses.
    pub between_solve_reductions: u64,
    /// Between-solve: total learned clauses deleted across all reductions (#8435).
    pub between_solve_clauses_deleted: u64,
    /// Between-solve: total `used` flag decrements across all decay passes (#8435).
    pub between_solve_used_decays: u64,
    /// IC3 memory pressure reduces: arena exceeded threshold factor of baseline (#8673).
    pub ic3_memory_pressure_reduces: u64,
    /// Domain-restricted BCP (#8475): watchers skipped because watched
    /// literal's variable was outside the active domain.
    pub domain_bcp_skips: u64,
    /// Domain-restricted BCP (#8475): total propagation calls using domain BCP.
    pub domain_bcp_calls: u64,
    /// IC3 assumption cache (#8443): solve calls where the common assumption
    /// prefix was reused, avoiding full `reset_search_state`.
    pub assumption_cache_hits: u64,
    /// IC3 assumption cache (#8443): solve calls that required full reset
    /// (no valid cache or no common prefix).
    pub assumption_cache_misses: u64,
    /// IC3 assumption cache (#8443): cumulative assumption levels reused
    /// across all cache hits. Higher = more BCP work saved.
    pub assumption_cache_levels_reused: u64,
    /// #lra-inc-engine (S1): per-check-sat solves in the incremental QF_LRA
    /// engine lane (ic3_mode + eager theory extension) that took the
    /// state-preserving incremental reset (`reset_search_state_incremental`)
    /// instead of the full `reset_search_state`. This is the OBJECTIVE proof
    /// that SAT state persisted across check-sats: a value near
    /// (num_check_sats - 1) means the level-0 trail / watches / learned clauses
    /// were kept; 0 means the integration did not persist (S1 NO-GO).
    pub ext_incremental_reset_hits: u64,
    /// #lra-inc-engine (S1): per-check-sat solves in the incremental QF_LRA
    /// engine lane that fell back to the full `reset_search_state` (first
    /// check-sat, or `can_use_incremental_reset` failed closed on a destructive
    /// arena op). Should stay small/constant, not scale with num_check_sats.
    pub ext_full_reset_hits: u64,
    /// IC3 lazy lemma removal (#8662 Gap 7): clauses marked as pending-garbage
    /// by the IC3 caller via `mark_clause_garbage_lazy()`.
    pub ic3_lazy_removed: u64,
    /// Learned clauses removed by the push/pop hermeticity sweep (Z3 PR #9221).
    /// Incremented by `gc_leaked_learned_clauses()` after every `pop()` that
    /// reduces the user-scope depth. A non-zero value means CDCL derived
    /// resolvents inside the popped scope that had no scope-selector guard;
    /// without this sweep those clauses would persist across scope boundaries,
    /// skewing VSIDS and reusing watch-list capacity for stale reasoning.
    pub leaked_learned_clauses_gc_removed: u64,
    /// IC3 domain expansion cache hits (#8569 Gap 1): queries where the
    /// expanded domain bitmap was reused from the previous call.
    pub ic3_domain_cache_hits: u64,
    /// IC3 domain expansion cache misses (#8569 Gap 1): queries where
    /// the domain expansion BFS had to be recomputed.
    pub ic3_domain_cache_misses: u64,
    /// Stale literal safety net (#8359, #8382): number of enqueue calls
    /// that were skipped because var.index() >= num_vars. These indicate
    /// a bug upstream (JIT, compaction, or arena GC producing stale
    /// literal indices). Zero is expected in a correct implementation.
    pub stale_enqueue_skips: u64,
    /// Stale BCP watch skips (#8547): number of watch entries skipped during
    /// unsafe BCP because blocker, arena offset, or literal index was
    /// out of bounds. These indicate stale watch entries from a prior arena
    /// GC or variable compaction. Zero is expected in a correct implementation.
    pub stale_bcp_watch_skips: u64,

    /// Trail exhaustion bailouts (#8479): backward trail scan failed to find
    /// a current-level seen literal. Analysis returns None and the caller
    /// backtracks to level 0. Indicates stale trail_pos under chrono-BT.
    pub trail_exhaustion_bailouts: u64,
    /// DIP-ERCL (#8440): number of DIP detection attempts.
    pub dip_attempts: u64,
    /// DIP-ERCL (#8440): number of valid DIPs found.
    pub dip_found: u64,
    /// DIP-ERCL (#8440): number of extension variables created.
    pub dip_extensions_created: u64,
    /// DIP-ERCL (#8440): number of extension variables garbage collected.
    pub dip_gc_deleted: u64,
    /// DIP-ERCL (#8440): number of times DIP was skipped (clause too short, etc.).
    pub dip_skipped: u64,
    /// DIP-ERCL (#8440): number of DIP pair reuses (existing extension var matched).
    pub dip_reuses: u64,
    /// LSCB (#8442): MLIs detected during BCP replacement scan.
    pub mli_detected: u64,
    /// LSCB (#8442): literals reimplied at a lower level during backtracking.
    pub mli_reimplied: u64,
    /// LSCB (#8442): lambda reasons used in conflict analysis.
    pub mli_used_in_analysis: u64,

    /// Compact stale clause cleanup (#8464): clauses deleted during
    /// compaction Phase 0 because they referenced eliminated/substituted
    /// variables. Nonzero values indicate that inprocessing passes between
    /// BVE's post-elimination GC and compaction introduced stale references.
    pub compact_stale_clauses_deleted: u64,

    /// Duplicate binary clauses deleted by deduplication (#8502).
    /// Deduplication is a form of subsumption (exact duplicate = trivially
    /// subsumed). Tracked separately for per-source breakdown.
    pub dedup_deleted: u64,

    /// Approximate-BCP filter (#8789 Phase 2): number of active clauses the
    /// filter classified as `NoopLikely` (≥2 surviving signature bits,
    /// i.e., the clause is definitely not unit and definitely not
    /// falsified) where the exact BCP view agreed — the clause was
    /// neither unit nor falsified on the real trail. A high ratio of
    /// `approx_bcp_noop_matched` to total filter invocations quantifies
    /// the Phase 3 BCP-skip potential. Always zero when the
    /// `approx-bcp-filter` feature is off.
    pub approx_bcp_noop_matched: u64,
    /// Approximate-BCP filter (#8789 Phase 2): number of active clauses the
    /// filter classified as `ConflictLikely` (≤1 surviving signature bit,
    /// i.e., "maybe unit or falsified") where the exact BCP view also
    /// saw the clause as unit or falsified under the current trail.
    /// This is the true-positive column of the filter's confusion
    /// matrix. Always zero when the `approx-bcp-filter` feature is off.
    pub approx_bcp_conflict_matched: u64,
    /// Approximate-BCP filter (#8789 Phase 2): number of active clauses
    /// where the filter returned `NoopLikely` ("≥2 literals not
    /// falsified, safe to skip") but the exact trail-based check found
    /// the clause was actually unit or falsified. This counter **must
    /// stay at zero** for the filter to be sound — a nonzero value
    /// means the soundness property in `filter::may_be_unit_or_falsified`
    /// is violated on real solver state. Phase 2 integration flags this
    /// as a hard correctness bug. Always zero when the
    /// `approx-bcp-filter` feature is off.
    pub approx_bcp_mismatch_detected: u64,
}

impl SolverStats {
    #[inline(always)]
    pub(crate) fn record_bcp_replacement_scan_step(&mut self, clause_len: usize, learned: bool) {
        self.bcp_replacement_scan_steps += 1;
        self.bcp_replacement_scan_steps_non_binary += 1;
        if learned {
            self.bcp_replacement_scan_steps_learned += 1;
        } else {
            self.bcp_replacement_scan_steps_original += 1;
        }
        if clause_len >= 6 {
            let bucket = bcp_long_scan_bucket(clause_len);
            self.bcp_long_scan_steps_by_len[bucket] += 1;
            if learned {
                self.bcp_long_scan_steps_learned_by_len[bucket] += 1;
            } else {
                self.bcp_long_scan_steps_original_by_len[bucket] += 1;
            }
        }
    }

    #[inline(always)]
    pub(crate) fn record_bcp_long_scan(&mut self, clause_len: usize, learned: bool) -> usize {
        let bucket = bcp_long_scan_bucket(clause_len);
        self.bcp_long_scan_by_len[bucket] += 1;
        if learned {
            self.bcp_long_scan_learned_by_len[bucket] += 1;
        }
        bucket
    }

    #[inline(always)]
    pub(crate) fn record_bcp_long_found_replacement(
        &mut self,
        bucket: usize,
        learned: bool,
        replacement_val: i8,
    ) {
        self.bcp_long_scan_found_replacement_by_len[bucket] += 1;
        if replacement_val > 0 {
            self.bcp_long_scan_found_true_by_len[bucket] += 1;
        } else {
            debug_assert_eq!(
                replacement_val, 0,
                "long replacement outcome must be true or unassigned"
            );
            self.bcp_long_scan_found_unassigned_by_len[bucket] += 1;
        }
        if learned {
            self.bcp_long_scan_learned_found_replacement_by_len[bucket] += 1;
        }
    }

    #[inline(always)]
    pub(crate) fn record_bcp_long_no_replacement(
        &mut self,
        bucket: usize,
        learned: bool,
        first_val: i8,
    ) {
        self.bcp_long_scan_no_replacement_by_len[bucket] += 1;
        if first_val < 0 {
            self.bcp_long_scan_conflict_by_len[bucket] += 1;
            if learned {
                self.bcp_long_scan_learned_conflict_by_len[bucket] += 1;
            }
        } else {
            debug_assert_eq!(
                first_val, 0,
                "no-replacement long scan should end in unit or conflict"
            );
            self.bcp_long_scan_unit_by_len[bucket] += 1;
            if learned {
                self.bcp_long_scan_learned_unit_by_len[bucket] += 1;
            }
        }
        if learned {
            self.bcp_long_scan_learned_no_replacement_by_len[bucket] += 1;
        }
    }

    #[inline(always)]
    pub(crate) fn record_bcp_learned_1963_true_tail_relocation_attempt(
        &mut self,
        replacement_val: i8,
    ) {
        self.bcp_learned_1963_true_tail_relocation_attempts += 1;
        if replacement_val > 0 {
            self.bcp_learned_1963_true_tail_relocation_moves += 1;
        }
    }

    #[inline(always)]
    pub(crate) fn record_bcp_learned_1963_used5_fsw_saved_pos_reset(
        &mut self,
        first_val: i8,
        wrote: bool,
    ) {
        self.bcp_learned_1963_used5_fsw_saved_pos_reset_eligible += 1;
        if wrote {
            self.bcp_learned_1963_used5_fsw_saved_pos_reset_writes += 1;
        }
        if first_val < 0 {
            self.bcp_learned_1963_used5_fsw_saved_pos_reset_conflict += 1;
        } else {
            debug_assert_eq!(
                first_val, 0,
                "used5 FSW saved-pos reset should end in unit or conflict"
            );
            self.bcp_learned_1963_used5_fsw_saved_pos_reset_unit += 1;
        }
    }

    #[inline(always)]
    pub(crate) fn record_bcp_learned_1963_fsw_conflict_saved_pos_reset(&mut self, wrote: bool) {
        self.bcp_learned_1963_fsw_conflict_saved_pos_reset_eligible += 1;
        self.bcp_learned_1963_fsw_conflict_saved_pos_reset_conflict += 1;
        if wrote {
            self.bcp_learned_1963_fsw_conflict_saved_pos_reset_writes += 1;
        }
    }

    #[inline(always)]
    pub(crate) fn record_bcp_learned_618_true_tail_relocation_attempt(
        &mut self,
        replacement_val: i8,
    ) {
        self.bcp_learned_618_true_tail_relocation_attempts += 1;
        if replacement_val > 0 {
            self.bcp_learned_618_true_tail_relocation_moves += 1;
        }
    }

    #[inline(always)]
    pub(crate) fn record_bcp_learned_no_replacement_saved_pos_update(
        &mut self,
        bucket: usize,
        first_val: i8,
        wrote: bool,
    ) {
        self.bcp_learned_no_replacement_saved_pos_eligible_by_len[bucket] += 1;
        if wrote {
            self.bcp_learned_no_replacement_saved_pos_writes_by_len[bucket] += 1;
        } else {
            self.bcp_learned_no_replacement_saved_pos_skipped_current_by_len[bucket] += 1;
        }
        if first_val < 0 {
            self.bcp_learned_no_replacement_saved_pos_conflict_by_len[bucket] += 1;
        } else {
            debug_assert_eq!(
                first_val, 0,
                "no-replacement saved-pos update should end in unit or conflict"
            );
            self.bcp_learned_no_replacement_saved_pos_unit_by_len[bucket] += 1;
        }
    }

    #[inline(always)]
    pub(crate) fn record_bcp_learned_1963_fsw_gent_skip(
        &mut self,
        replacement_val: i8,
        replacement_k: usize,
        saved_start: usize,
        first_val: i8,
    ) {
        self.bcp_learned_1963_fsw_gent_skip_candidates += 1;
        self.bcp_learned_1963_fsw_gent_skip_applied += 1;
        self.bcp_learned_1963_fsw_gent_skip_saved_slots += 1;
        if replacement_val > 0 {
            if replacement_k > saved_start {
                self.bcp_learned_1963_fsw_gent_skip_found_true_suffix += 1;
            } else {
                self.bcp_learned_1963_fsw_gent_skip_found_true_prefix += 1;
            }
        } else if replacement_val == 0 {
            if replacement_k > saved_start {
                self.bcp_learned_1963_fsw_gent_skip_found_unassigned_suffix += 1;
            } else {
                self.bcp_learned_1963_fsw_gent_skip_found_unassigned_prefix += 1;
            }
        } else if first_val < 0 {
            self.bcp_learned_1963_fsw_gent_skip_no_replacement_conflict += 1;
        } else {
            debug_assert_eq!(
                first_val, 0,
                "FSW Gent-order skip should end in replacement, unit, or conflict"
            );
            self.bcp_learned_1963_fsw_gent_skip_no_replacement_unit += 1;
        }
    }

    #[inline(always)]
    pub(crate) fn record_bcp_learned_no_replacement_scan_pressure(
        &mut self,
        bucket: usize,
        scan_steps: u64,
        first_val: i8,
        saved_start_false: bool,
        wrapped_from_saved_pos: bool,
        lbd: u32,
        used: u8,
        clause_offset: usize,
    ) {
        self.bcp_learned_no_replacement_scan_pressure_scans_by_len[bucket] += 1;
        self.bcp_learned_no_replacement_scan_pressure_steps_by_len[bucket] += scan_steps;
        if saved_start_false {
            self.bcp_learned_no_replacement_scan_pressure_start_false_by_len[bucket] += 1;
        }
        if wrapped_from_saved_pos {
            self.bcp_learned_no_replacement_scan_pressure_wrapped_by_len[bucket] += 1;
        }
        if first_val < 0 {
            self.bcp_learned_no_replacement_scan_pressure_conflict_by_len[bucket] += 1;
        } else {
            debug_assert_eq!(
                first_val, 0,
                "no-replacement scan-pressure profile should end in unit or conflict"
            );
            self.bcp_learned_no_replacement_scan_pressure_unit_by_len[bucket] += 1;
        }
        if bucket == 3 && saved_start_false && wrapped_from_saved_pos {
            let lbd_bucket = bcp_learned_1963_pressure_lbd_bucket(lbd);
            let used_bucket = bcp_learned_1963_pressure_used_bucket(used);
            let repeat_bucket = clause_offset & (BCP_LEARNED_1963_PRESSURE_REPEAT_BUCKETS - 1);
            if first_val < 0 {
                self.bcp_learned_1963_fsw_conflict_by_lbd[lbd_bucket] += 1;
                self.bcp_learned_1963_fsw_conflict_steps_by_lbd[lbd_bucket] += scan_steps;
                self.bcp_learned_1963_fsw_conflict_by_used[used_bucket] += 1;
                self.bcp_learned_1963_fsw_conflict_steps_by_used[used_bucket] += scan_steps;
            } else {
                self.bcp_learned_1963_fsw_unit_by_lbd[lbd_bucket] += 1;
                self.bcp_learned_1963_fsw_unit_steps_by_lbd[lbd_bucket] += scan_steps;
                self.bcp_learned_1963_fsw_unit_by_used[used_bucket] += 1;
                self.bcp_learned_1963_fsw_unit_steps_by_used[used_bucket] += scan_steps;
            }
            self.bcp_learned_1963_fsw_repeat_by_bucket[repeat_bucket] += 1;
            self.bcp_learned_1963_fsw_repeat_steps_by_bucket[repeat_bucket] += scan_steps;
            self.bcp_learned_1963_fsw_repeat_bucket_max = self
                .bcp_learned_1963_fsw_repeat_bucket_max
                .max(self.bcp_learned_1963_fsw_repeat_by_bucket[repeat_bucket]);
        }
    }

    #[inline]
    pub(crate) fn enable_bcp_learned_1963_identity(&mut self) {
        if self.bcp_learned_1963_identity.is_none() {
            self.bcp_learned_1963_identity = Some(BcpLearned1963IdentityTable::default());
        }
    }

    #[allow(clippy::too_many_arguments)]
    #[inline(always)]
    pub(crate) fn record_bcp_learned_1963_identity(
        &mut self,
        clause_id: u64,
        clause_offset: usize,
        clause_len: usize,
        current_conflict: u64,
        birth_conflict: u64,
        scan_steps: u64,
        replacement_val: i8,
        first_val: i8,
        saved_start_false: bool,
        wrapped_from_saved_pos: bool,
        lbd: u32,
        used: u8,
    ) {
        let table = self
            .bcp_learned_1963_identity
            .get_or_insert_with(BcpLearned1963IdentityTable::default);
        table.record(
            clause_id,
            clause_offset,
            clause_len,
            current_conflict,
            birth_conflict,
            scan_steps,
            replacement_val,
            first_val,
            saved_start_false,
            wrapped_from_saved_pos,
            lbd,
            used,
        );
    }

    pub(crate) fn bcp_learned_1963_identity_table(&self) -> Option<&BcpLearned1963IdentityTable> {
        self.bcp_learned_1963_identity.as_ref()
    }

    pub(crate) fn bcp_learned_1963_identity_record(
        &self,
        clause_id: u64,
    ) -> Option<&BcpLearned1963IdentityRecord> {
        self.bcp_learned_1963_identity
            .as_ref()
            .and_then(|table| table.exact_clause_record(clause_id))
    }

    #[cfg(test)]
    pub(crate) fn set_bcp_learned_1963_blocker_cert_elision_test_enabled(&mut self, enabled: bool) {
        self.bcp_learned_1963_blocker_cert_elision_test_enabled = enabled;
    }

    #[inline(always)]
    pub(crate) fn bcp_learned_1963_blocker_cert_elision_test_enabled(&self) -> bool {
        #[cfg(test)]
        {
            self.bcp_learned_1963_blocker_cert_elision_test_enabled
        }
        #[cfg(not(test))]
        {
            false
        }
    }

    #[cfg(test)]
    pub(crate) fn set_bcp_learned_1963_blocker_cert_shadow_test_enabled(&mut self, enabled: bool) {
        self.bcp_learned_1963_blocker_cert_shadow_test_enabled = enabled;
    }

    #[inline(always)]
    pub(crate) fn bcp_learned_1963_blocker_cert_shadow_test_enabled(&self) -> bool {
        #[cfg(test)]
        {
            self.bcp_learned_1963_blocker_cert_shadow_test_enabled
        }
        #[cfg(not(test))]
        {
            false
        }
    }

    #[cfg(test)]
    pub(crate) fn set_bcp_learned_1963_blocker_cert_false_reject_demote_test_enabled(
        &mut self,
        enabled: bool,
    ) {
        self.bcp_learned_1963_blocker_cert_false_reject_demote_test_enabled = enabled;
    }

    #[inline(always)]
    pub(crate) fn bcp_learned_1963_blocker_cert_false_reject_demote_test_enabled(&self) -> bool {
        #[cfg(test)]
        {
            self.bcp_learned_1963_blocker_cert_false_reject_demote_test_enabled
        }
        #[cfg(not(test))]
        {
            false
        }
    }

    #[inline(always)]
    pub(crate) fn bcp_learned_1963_blocker_cert(
        &self,
        clause_offset: usize,
    ) -> Option<BcpLearned1963BlockerCert> {
        self.bcp_learned_1963_blocker_certs
            .get(clause_offset)
            .copied()
            .flatten()
    }

    #[inline(always)]
    pub(crate) fn clear_bcp_learned_1963_blocker_cert(&mut self, clause_offset: usize) {
        if let Some(slot) = self.bcp_learned_1963_blocker_certs.get_mut(clause_offset) {
            *slot = None;
        }
    }

    #[inline]
    pub(crate) fn clear_bcp_learned_1963_blocker_certs(&mut self) {
        self.bcp_learned_1963_blocker_certs.clear();
    }

    #[inline]
    pub(crate) fn remap_bcp_learned_1963_blocker_certs(&mut self, remap: &[u32]) {
        if self.bcp_learned_1963_blocker_certs.is_empty() {
            return;
        }
        let old_certs = std::mem::take(&mut self.bcp_learned_1963_blocker_certs);
        let mut new_certs: Vec<Option<BcpLearned1963BlockerCert>> = Vec::new();
        for (old_offset, cert) in old_certs.into_iter().enumerate() {
            let Some(mut cert) = cert else {
                continue;
            };
            if cert.clause_offset != old_offset {
                continue;
            }
            let Some(&new_offset) = remap.get(old_offset) else {
                continue;
            };
            if new_offset == u32::MAX {
                continue;
            }
            let new_offset = new_offset as usize;
            if new_certs.len() <= new_offset {
                new_certs.resize(new_offset + 1, None);
            }
            cert.clause_offset = new_offset;
            new_certs[new_offset] = Some(cert);
        }
        self.bcp_learned_1963_blocker_certs = new_certs;
    }

    #[inline(always)]
    pub(crate) fn record_bcp_learned_1963_blocker_cert_candidate(&mut self) {
        self.bcp_learned_1963_blocker_cert_candidates += 1;
    }

    #[inline(always)]
    pub(crate) fn record_bcp_learned_1963_blocker_cert_elision(
        &mut self,
        elided_suffix_slots: u64,
        fsw_seed: bool,
    ) {
        self.bcp_learned_1963_blocker_cert_elisions += 1;
        self.bcp_learned_1963_blocker_cert_elided_suffix_slots += elided_suffix_slots;
        if fsw_seed {
            self.bcp_learned_1963_blocker_cert_affected_fsw_rows += 1;
        }
    }

    #[inline(always)]
    pub(crate) fn record_bcp_learned_1963_blocker_cert_shadow_hit(
        &mut self,
        elided_suffix_slots: u64,
        fsw_seed: bool,
    ) {
        self.bcp_learned_1963_blocker_cert_shadow_hits += 1;
        self.bcp_learned_1963_blocker_cert_shadow_elided_suffix_slots += elided_suffix_slots;
        if fsw_seed {
            self.bcp_learned_1963_blocker_cert_shadow_affected_fsw_rows += 1;
        }
    }

    #[inline(always)]
    pub(crate) fn record_bcp_learned_1963_blocker_cert_shadow_mismatch(&mut self) {
        self.bcp_learned_1963_blocker_cert_shadow_mismatches += 1;
    }

    #[inline(always)]
    pub(crate) fn record_bcp_learned_1963_blocker_cert_mismatch_demotion(&mut self) {
        self.bcp_learned_1963_blocker_cert_mismatch_demotions += 1;
    }

    #[inline(always)]
    pub(crate) fn record_bcp_learned_1963_blocker_cert_stale_reject(&mut self) {
        self.bcp_learned_1963_blocker_cert_stale_rejects += 1;
    }

    #[inline(always)]
    pub(crate) fn record_bcp_learned_1963_blocker_cert_false_reject(&mut self) {
        self.bcp_learned_1963_blocker_cert_false_rejects += 1;
    }

    #[inline(always)]
    pub(crate) fn record_bcp_learned_1963_blocker_cert_false_reject_demotion(&mut self) {
        self.bcp_learned_1963_blocker_cert_false_reject_demotions += 1;
    }

    #[inline(always)]
    pub(crate) fn record_bcp_learned_1963_blocker_cert_repeat_reject(&mut self) {
        self.bcp_learned_1963_blocker_cert_repeat_rejects += 1;
    }

    #[inline(always)]
    pub(crate) fn record_bcp_learned_1963_blocker_cert_populate(
        &mut self,
        clause_offset: usize,
        position: usize,
        literal_raw: u32,
        fsw_seed: bool,
    ) {
        if self.bcp_learned_1963_blocker_certs.len() <= clause_offset {
            self.bcp_learned_1963_blocker_certs
                .resize(clause_offset + 1, None);
        }
        let repeat_count = self.bcp_learned_1963_blocker_certs[clause_offset]
            .filter(|cert| {
                cert.clause_offset == clause_offset
                    && cert.position == position
                    && cert.literal_raw == literal_raw
            })
            .map_or(1, |cert| cert.repeat_count.saturating_add(1).max(1));
        self.bcp_learned_1963_blocker_certs[clause_offset] = Some(BcpLearned1963BlockerCert {
            clause_offset,
            literal_raw,
            position,
            repeat_count,
            fsw_seed,
        });
        self.bcp_learned_1963_blocker_cert_populates += 1;
    }

    #[inline(always)]
    pub(crate) fn record_dense_clique_mab_branch_route_exercised(&mut self) {
        self.dense_clique_mab_branch_route_exercised += 1;
    }

    #[inline(always)]
    pub(crate) fn record_bcp_search_inplace_watch_scan_exercised(&mut self) {
        self.bcp_search_inplace_watch_scan_exercised += 1;
    }

    #[inline(always)]
    pub(crate) fn record_bcp_learned_617_tail_reorder(&mut self, swaps: u64) {
        self.bcp_learned_617_tail_reorder_candidates += 1;
        self.bcp_learned_617_tail_reorder_exercised += 1;
        if swaps != 0 {
            self.bcp_learned_617_tail_reorder_changed += 1;
            self.bcp_learned_617_tail_reorder_swaps += swaps;
        }
    }

    #[inline(always)]
    pub(crate) fn record_bcp_learned_18_tail_reorder(&mut self, swaps: u64) {
        self.bcp_learned_18_tail_reorder_candidates += 1;
        self.bcp_learned_18_tail_reorder_exercised += 1;
        if swaps != 0 {
            self.bcp_learned_18_tail_reorder_changed += 1;
            self.bcp_learned_18_tail_reorder_swaps += swaps;
        }
    }

    #[inline(always)]
    pub(crate) fn record_bcp_learned_1963_tail_reorder(&mut self, swaps: u64) {
        self.bcp_learned_1963_tail_reorder_candidates += 1;
        if swaps != 0 {
            self.bcp_learned_1963_tail_reorder_changed += 1;
            self.bcp_learned_1963_tail_reorder_swaps += swaps;
        }
    }

    #[inline(always)]
    pub(crate) fn record_bcp_learned_1963_tail_reorder_budget_applied(&mut self, swaps: u64) {
        self.bcp_learned_1963_tail_reorder_candidates += 1;
        self.bcp_learned_1963_tail_reorder_budget_candidates += 1;
        self.bcp_learned_1963_tail_reorder_budget_applied += 1;
        self.bcp_learned_1963_tail_reorder_budget_swaps_applied += swaps;
        if swaps != 0 {
            self.bcp_learned_1963_tail_reorder_changed += 1;
            self.bcp_learned_1963_tail_reorder_swaps += swaps;
        }
    }

    #[inline(always)]
    pub(crate) fn record_bcp_learned_1963_tail_reorder_budget_skipped(&mut self, swaps: u64) {
        self.bcp_learned_1963_tail_reorder_candidates += 1;
        self.bcp_learned_1963_tail_reorder_budget_candidates += 1;
        self.bcp_learned_1963_tail_reorder_budget_skipped_over_budget += 1;
        self.bcp_learned_1963_tail_reorder_budget_swaps_skipped += swaps;
    }

    /// Create zeroed telemetry counters.
    pub(crate) fn new() -> Self {
        Self {
            chrono_backtracks: 0,
            shrink_block_attempts: 0,
            shrink_block_successes: 0,
            shrink_singleton_fast_path_skips: 0,
            lrat_original_learned_snapshot_copies: 0,
            lrat_original_learned_snapshot_literals: 0,
            lrat_original_learned_snapshot_singleton_skips: 0,
            lrat_removed_literal_chain_calls: 0,
            bcp_blocker_fastpath_hits: 0,
            bcp_binary_path_hits: 0,
            bcp_search_inplace_watch_scan_exercised: 0,
            jumped_reasons: 0,
            bcp_replacement_scan_steps: 0,
            bcp_replacement_scan_steps_binary: 0,
            bcp_replacement_scan_steps_non_binary: 0,
            bcp_replacement_scan_steps_learned: 0,
            bcp_replacement_scan_steps_original: 0,
            bcp_long_blocker_fastpath_hits: 0,
            bcp_long_scan_steps_by_len: [0; BCP_LONG_SCAN_BUCKETS],
            bcp_long_scan_steps_learned_by_len: [0; BCP_LONG_SCAN_BUCKETS],
            bcp_long_scan_steps_original_by_len: [0; BCP_LONG_SCAN_BUCKETS],
            bcp_long_scan_by_len: [0; BCP_LONG_SCAN_BUCKETS],
            bcp_long_scan_found_replacement_by_len: [0; BCP_LONG_SCAN_BUCKETS],
            bcp_long_scan_found_true_by_len: [0; BCP_LONG_SCAN_BUCKETS],
            bcp_long_scan_found_unassigned_by_len: [0; BCP_LONG_SCAN_BUCKETS],
            bcp_long_scan_no_replacement_by_len: [0; BCP_LONG_SCAN_BUCKETS],
            bcp_long_scan_unit_by_len: [0; BCP_LONG_SCAN_BUCKETS],
            bcp_long_scan_conflict_by_len: [0; BCP_LONG_SCAN_BUCKETS],
            bcp_long_scan_learned_by_len: [0; BCP_LONG_SCAN_BUCKETS],
            bcp_long_scan_learned_found_replacement_by_len: [0; BCP_LONG_SCAN_BUCKETS],
            bcp_long_scan_learned_no_replacement_by_len: [0; BCP_LONG_SCAN_BUCKETS],
            bcp_long_scan_learned_unit_by_len: [0; BCP_LONG_SCAN_BUCKETS],
            bcp_long_scan_learned_conflict_by_len: [0; BCP_LONG_SCAN_BUCKETS],
            bcp_learned_1963_true_tail_relocation_attempts: 0,
            bcp_learned_1963_true_tail_relocation_moves: 0,
            bcp_learned_1963_used5_fsw_saved_pos_reset_eligible: 0,
            bcp_learned_1963_used5_fsw_saved_pos_reset_writes: 0,
            bcp_learned_1963_used5_fsw_saved_pos_reset_unit: 0,
            bcp_learned_1963_used5_fsw_saved_pos_reset_conflict: 0,
            bcp_learned_1963_fsw_conflict_saved_pos_reset_eligible: 0,
            bcp_learned_1963_fsw_conflict_saved_pos_reset_writes: 0,
            bcp_learned_1963_fsw_conflict_saved_pos_reset_conflict: 0,
            bcp_learned_618_true_tail_relocation_attempts: 0,
            bcp_learned_618_true_tail_relocation_moves: 0,
            bcp_learned_no_replacement_saved_pos_eligible_by_len: [0; BCP_LONG_SCAN_BUCKETS],
            bcp_learned_no_replacement_saved_pos_writes_by_len: [0; BCP_LONG_SCAN_BUCKETS],
            bcp_learned_no_replacement_saved_pos_skipped_current_by_len: [0; BCP_LONG_SCAN_BUCKETS],
            bcp_learned_no_replacement_saved_pos_unit_by_len: [0; BCP_LONG_SCAN_BUCKETS],
            bcp_learned_no_replacement_saved_pos_conflict_by_len: [0; BCP_LONG_SCAN_BUCKETS],
            bcp_learned_1963_fsw_gent_skip_candidates: 0,
            bcp_learned_1963_fsw_gent_skip_applied: 0,
            bcp_learned_1963_fsw_gent_skip_saved_slots: 0,
            bcp_learned_1963_fsw_gent_skip_found_true_suffix: 0,
            bcp_learned_1963_fsw_gent_skip_found_unassigned_suffix: 0,
            bcp_learned_1963_fsw_gent_skip_found_true_prefix: 0,
            bcp_learned_1963_fsw_gent_skip_found_unassigned_prefix: 0,
            bcp_learned_1963_fsw_gent_skip_no_replacement_unit: 0,
            bcp_learned_1963_fsw_gent_skip_no_replacement_conflict: 0,
            bcp_learned_no_replacement_scan_pressure_scans_by_len: [0; BCP_LONG_SCAN_BUCKETS],
            bcp_learned_no_replacement_scan_pressure_steps_by_len: [0; BCP_LONG_SCAN_BUCKETS],
            bcp_learned_no_replacement_scan_pressure_start_false_by_len: [0; BCP_LONG_SCAN_BUCKETS],
            bcp_learned_no_replacement_scan_pressure_wrapped_by_len: [0; BCP_LONG_SCAN_BUCKETS],
            bcp_learned_no_replacement_scan_pressure_unit_by_len: [0; BCP_LONG_SCAN_BUCKETS],
            bcp_learned_no_replacement_scan_pressure_conflict_by_len: [0; BCP_LONG_SCAN_BUCKETS],
            bcp_learned_1963_fsw_unit_by_lbd: [0; BCP_LEARNED_1963_PRESSURE_LBD_BUCKETS],
            bcp_learned_1963_fsw_conflict_by_lbd: [0; BCP_LEARNED_1963_PRESSURE_LBD_BUCKETS],
            bcp_learned_1963_fsw_unit_steps_by_lbd: [0; BCP_LEARNED_1963_PRESSURE_LBD_BUCKETS],
            bcp_learned_1963_fsw_conflict_steps_by_lbd: [0; BCP_LEARNED_1963_PRESSURE_LBD_BUCKETS],
            bcp_learned_1963_fsw_unit_by_used: [0; BCP_LEARNED_1963_PRESSURE_USED_BUCKETS],
            bcp_learned_1963_fsw_conflict_by_used: [0; BCP_LEARNED_1963_PRESSURE_USED_BUCKETS],
            bcp_learned_1963_fsw_unit_steps_by_used: [0; BCP_LEARNED_1963_PRESSURE_USED_BUCKETS],
            bcp_learned_1963_fsw_conflict_steps_by_used: [0;
                BCP_LEARNED_1963_PRESSURE_USED_BUCKETS],
            bcp_learned_1963_fsw_repeat_by_bucket: [0; BCP_LEARNED_1963_PRESSURE_REPEAT_BUCKETS],
            bcp_learned_1963_fsw_repeat_steps_by_bucket: [0;
                BCP_LEARNED_1963_PRESSURE_REPEAT_BUCKETS],
            bcp_learned_1963_fsw_repeat_bucket_max: 0,
            bcp_learned_1963_identity: None,
            bcp_learned_1963_blocker_certs: Vec::new(),
            bcp_learned_1963_blocker_cert_candidates: 0,
            bcp_learned_1963_blocker_cert_elisions: 0,
            bcp_learned_1963_blocker_cert_shadow_hits: 0,
            bcp_learned_1963_blocker_cert_shadow_mismatches: 0,
            bcp_learned_1963_blocker_cert_mismatch_demotions: 0,
            bcp_learned_1963_blocker_cert_populates: 0,
            bcp_learned_1963_blocker_cert_stale_rejects: 0,
            bcp_learned_1963_blocker_cert_false_rejects: 0,
            bcp_learned_1963_blocker_cert_false_reject_demotions: 0,
            bcp_learned_1963_blocker_cert_repeat_rejects: 0,
            bcp_learned_1963_blocker_cert_elided_suffix_slots: 0,
            bcp_learned_1963_blocker_cert_shadow_elided_suffix_slots: 0,
            bcp_learned_1963_blocker_cert_affected_fsw_rows: 0,
            bcp_learned_1963_blocker_cert_shadow_affected_fsw_rows: 0,
            #[cfg(test)]
            bcp_learned_1963_blocker_cert_elision_test_enabled: false,
            #[cfg(test)]
            bcp_learned_1963_blocker_cert_shadow_test_enabled: false,
            #[cfg(test)]
            bcp_learned_1963_blocker_cert_false_reject_demote_test_enabled: false,
            bcp_learned_617_tail_reorder_candidates: 0,
            bcp_learned_617_tail_reorder_exercised: 0,
            bcp_learned_617_tail_reorder_changed: 0,
            bcp_learned_617_tail_reorder_swaps: 0,
            bcp_learned_18_tail_reorder_candidates: 0,
            bcp_learned_18_tail_reorder_exercised: 0,
            bcp_learned_18_tail_reorder_changed: 0,
            bcp_learned_18_tail_reorder_swaps: 0,
            bcp_learned_1963_tail_reorder_candidates: 0,
            bcp_learned_1963_tail_reorder_changed: 0,
            bcp_learned_1963_tail_reorder_swaps: 0,
            bcp_learned_1963_tail_reorder_budget_candidates: 0,
            bcp_learned_1963_tail_reorder_budget_applied: 0,
            bcp_learned_1963_tail_reorder_budget_skipped_over_budget: 0,
            bcp_learned_1963_tail_reorder_budget_swaps_applied: 0,
            bcp_learned_1963_tail_reorder_budget_swaps_skipped: 0,
            bcp_long_saved_pos_scans: 0,
            bcp_long_saved_pos_start_false: 0,
            bcp_long_saved_pos_found_true: 0,
            bcp_long_saved_pos_found_unassigned: 0,
            bcp_long_saved_pos_no_replacement: 0,
            bcp_len18_saved_pos_scans: 0,
            bcp_len18_saved_pos_start_false: 0,
            bcp_len18_saved_pos_found_true: 0,
            bcp_len18_saved_pos_found_unassigned: 0,
            bcp_len18_saved_pos_no_replacement: 0,
            lrat_materialize_calls: 0,
            lrat_materialize_minimize_calls: 0,
            lrat_materialize_root_trail_entries: 0,
            lrat_materialize_minimize_root_trail_entries: 0,
            lrat_materialize_emitted_unit_lines: 0,
            lrat_materialize_minimize_emitted_unit_lines: 0,
            lrat_materialize_unit_hints: 0,
            lrat_materialize_minimize_unit_hints: 0,
            lrat_materialize_unit_max_hints: 0,
            lrat_materialize_minimize_unit_max_hints: 0,
            lrat_materialize_incomplete_chains: 0,
            lrat_materialize_minimize_incomplete_chains: 0,
            lrat_materialize_hidden_trusted_units: 0,
            lrat_unit_chain_calls: 0,
            lrat_unit_chain_root_trail_entries: 0,
            lrat_unit_chain_hints: 0,
            lrat_unit_chain_max_hints: 0,
            lrat_unit_chain_missing_hints: 0,
            preprocess_level0_literals_removed: 0,
            preprocess_level0_satisfied_deleted: 0,
            random_decisions: 0,
            otfs_strengthened: 0,
            otfs_subsumed: 0,
            otfs_candidates: 0,
            otfs_blocked_open0: 0,
            otfs_blocked_watch: 0,
            otfs_blocked_strengthen: 0,
            otfs_branch_b: 0,
            otfs_branch_c: 0,
            otfs_clause_subsumed: 0,
            forced_backtracks: 0,
            focused_ema_checks: 0,
            focused_ema_fires: 0,
            stable_reluctant_fires: 0,
            stable_ema_fires: 0,
            lbd_sum: 0,
            lbd_count: 0,
            focused_ema_blocked_by_conflict_gate: 0,
            dense_mutex_focused_restart_gate_updates: 0,
            dense_mutex_focused_restart_runtime_checked: 0,
            dense_mutex_focused_restart_active_vars: 0,
            dense_mutex_focused_restart_active_clauses: 0,
            dense_mutex_focused_restart_active_binary_clauses: 0,
            dense_mutex_focused_restart_runtime_candidate: 0,
            dense_mutex_focused_restart_previous_gate: 0,
            dense_mutex_focused_restart_computed_gate: 0,
            dense_clique_mab_branch_route_enabled: 0,
            dense_clique_mab_branch_route_exercised: 0,
            trail_blocked_restarts: 0,
            restart_attribution: [0; RESTART_ATTRIBUTION_BUCKETS],
            restart_attribution_modes: [0; RESTART_MODE_BUCKETS],
            pending_restart_attribution: None,
            rephase_attribution: [0; REPHASE_ATTRIBUTION_BUCKETS],
            rephase_attribution_modes: [0; REPHASE_MODE_BUCKETS],
            rephase_direct_changed_phases: 0,
            rephase_target_phase_updates: 0,
            rephase_best_resets: 0,
            cold_restarts: 0,
            focused_decisions: 0,
            stable_decisions: 0,
            inprocessing_time_ns: [0; INPROCESS_TIMING_LABELS.len()],
            inprocessing_pass_attempts: [0; INPROCESS_ACCOUNTING_LABELS.len()],
            inprocessing_pass_runs: [0; INPROCESS_ACCOUNTING_LABELS.len()],
            inprocessing_pass_yields: [0; INPROCESS_ACCOUNTING_LABELS.len()],
            inprocessing_lrat_clamped_bve_due_rounds: 0,
            inprocessing_lrat_clamped_factor_due_rounds: 0,
            inprocessing_lrat_probe_rescue_rounds: 0,
            inprocessing_yield_rescue_backbone_cooldown_rounds: 0,
            bounded_backbone_backoff_triggers: 0,
            bounded_backbone_runs: 0,
            bounded_backbone_yields: 0,
            bounded_backbone_ms: 0,
            bounded_backbone_binary_suppressed: 0,
            inprocessing_rounds: 0,
            incremental_inprocessing_rounds: 0,
            rebuild_watches_us: 0,
            rebuild_watches_calls: 0,
            full_rebuild_watches_us: 0,
            full_rebuild_watches_calls: 0,
            incremental_reconnect_watches_us: 0,
            incremental_reconnect_watches_calls: 0,
            inprocessing_simplifications: 0,
            gpu_bve_dispatches: 0,
            gpu_bve_pairs: 0,
            gpu_bve_tautologies: 0,
            preprocess_time_ns: 0,
            search_time_ns: 0,
            lucky_time_ns: 0,
            walk_time_ns: 0,
            mab_arm_switches: 0,
            jit_propagations: 0,
            jit_conflicts: 0,
            jit_blocker_skips: 0,
            jit_hybrid_jit_literals: 0,
            jit_hybrid_2wl_literals: 0,
            jit_compile_time_us: 0,
            jit_clauses_compiled: 0,
            jit_learned_clauses_compiled: 0,
            jit_watches_detached: 0,
            jit_watches_reattached: 0,
            jit_recompilations_skipped: 0,
            jit_recompilations: 0,
            jit_delta_recompilations: 0,
            jit_incremental_compilations: 0,
            jit_incremental_pairs: 0,
            jit_guard_deletions: 0,
            jit_parallel_compiled: false,
            jit_cache_hits: 0,
            jit_cache_misses: 0,
            jit_pgo_recompilations: 0,
            jit_pgo_hot_functions: 0,
            jit_pgo_cold_removed: 0,
            jit_tier_promotions: 0,
            jit_tier_promotion_recompilations: 0,
            jit_scope_skipped_clauses: 0,
            code_cache_total_bytes: 0,
            code_cache_peak_bytes: 0,
            code_cache_evictions: 0,
            code_cache_bytes_evicted: 0,
            native_code_helpers_enabled: true,
            compilation_tier: "T0:interpret",
            tier_controller_promotions: 0,
            sat_whole_loop_guard_installs: 0,
            sat_whole_loop_guard_applications: 0,
            sat_propagation_native_active: false,
            sat_propagation_native_clauses: 0,
            sat_propagation_native_rounds: 0,
            sat_propagation_native_propagations: 0,
            sat_propagation_native_conflicts: 0,
            sat_propagation_native_compile_time_us: 0,
            sat_conflict_analysis_native_applications: 0,
            dense_propagations: 0,
            dense_conflicts: 0,
            dense_satisfied_deleted: 0,
            reduction_l0_satisfied_occ_scans: 0,
            reduction_l0_satisfied_full_scans: 0,
            reduction_l0_satisfied_no_occ_skips: 0,
            reduction_l0_satisfied_deleted: 0,
            learned_reduction_considered: 0,
            learned_reduction_deleted: 0,
            learned_reduction_reason_protected: 0,
            learned_reduction_ic3_protected: 0,
            learned_reduction_low_lbd_protected: 0,
            learned_reduction_usage_protected: 0,
            learned_reduction_target_kept: 0,
            learned_reduction_lrat_retained_delete_skips: 0,
            learned_reduction_hyper_deleted: 0,
            learned_reduction_hyper_kept: 0,
            learned_1963_pressure_reduction_candidates: 0,
            learned_1963_pressure_reduction_pressure_candidates: 0,
            learned_1963_pressure_reduction_ranked: 0,
            learned_1963_pressure_reduction_rank_bias_total: 0,
            learned_1963_pressure_reduction_selected: 0,
            learned_1963_pressure_reduction_selected_steps: 0,
            learned_1963_pressure_reduction_deleted: 0,
            learned_1963_pressure_reduction_deleted_steps: 0,
            learned_1963_pressure_reduction_kept: 0,
            learned_1963_pressure_reduction_kept_steps: 0,
            learned_1963_pressure_reduction_skipped_no_pressure: 0,
            learned_1963_pressure_reduction_lrat_retained_delete_skips: 0,
            learned_1963_pressure_retention_candidates: 0,
            learned_1963_pressure_retention_pressure_candidates: 0,
            learned_1963_pressure_retention_ranked: 0,
            learned_1963_pressure_retention_rank_bias_total: 0,
            learned_1963_pressure_retention_selected: 0,
            learned_1963_pressure_retention_selected_steps: 0,
            learned_1963_pressure_retention_deleted: 0,
            learned_1963_pressure_retention_deleted_steps: 0,
            learned_1963_pressure_retention_kept: 0,
            learned_1963_pressure_retention_kept_steps: 0,
            learned_1963_pressure_retention_skipped_no_pressure: 0,
            learned_1963_pressure_retention_lrat_retained_delete_skips: 0,
            lbd_buckets: [0; 5],
            lookahead_rounds: 0,
            lookahead_failed_literals: 0,
            lookahead_decisions_used: 0,
            peak_decision_level: 0,
            decision_level_sum: 0,
            decision_level_count: 0,
            flush_dirty_lits: 0,
            flush_watches_removed: 0,
            watches_shrunk: 0,
            trail_rewind_skipped: 0,
            trail_rewind_partial: 0,
            trail_rewind_full: 0,
            trail_rewind_saved_entries: 0,
            post_rebuild_bcp_ns: 0,
            post_rebuild_bcp_propagations: 0,
            post_full_rebuild_bcp_ns: 0,
            post_full_rebuild_bcp_propagations: 0,
            post_incremental_reconnect_bcp_ns: 0,
            post_incremental_reconnect_bcp_propagations: 0,
            ibcl_attempts: 0,
            ibcl_improvements: 0,
            ibcl_skipped_short_chain: 0,
            ibcl_skipped_missing_pivots: 0,
            bcp_theory_fixpoint_entries: 0,
            bcp_theory_fixpoint_iterations: 0,
            bcp_theory_fixpoint_max_depth: 0,
            bcp_theory_fixpoint_saturated: 0,
            bcp_theory_interleaved_force_calls: 0,
            bcp_theory_interleaved_force_hits: 0,
            backbone_binary_units: 0,
            occ_incremental_refreshes: 0,
            occ_full_rebuilds: 0,
            between_solve_reductions: 0,
            between_solve_clauses_deleted: 0,
            between_solve_used_decays: 0,
            ic3_memory_pressure_reduces: 0,
            domain_bcp_skips: 0,
            domain_bcp_calls: 0,
            assumption_cache_hits: 0,
            assumption_cache_misses: 0,
            assumption_cache_levels_reused: 0,
            ext_incremental_reset_hits: 0,
            ext_full_reset_hits: 0,
            ic3_lazy_removed: 0,
            leaked_learned_clauses_gc_removed: 0,
            ic3_domain_cache_hits: 0,
            ic3_domain_cache_misses: 0,
            stale_enqueue_skips: 0,
            stale_bcp_watch_skips: 0,
            trail_exhaustion_bailouts: 0,
            dip_attempts: 0,
            dip_found: 0,
            dip_extensions_created: 0,
            dip_gc_deleted: 0,
            dip_skipped: 0,
            dip_reuses: 0,
            mli_detected: 0,
            mli_reimplied: 0,
            mli_used_in_analysis: 0,
            compact_stale_clauses_deleted: 0,
            dedup_deleted: 0,
            approx_bcp_noop_matched: 0,
            approx_bcp_conflict_matched: 0,
            approx_bcp_mismatch_detected: 0,
        }
    }

    /// Record a learned clause's LBD into the distribution buckets (#8131).
    /// Buckets: [0]=1, [1]=2, [2]=3-5, [3]=6-10, [4]=11+.
    #[inline]
    pub(crate) fn record_lbd_bucket(&mut self, lbd: u32) {
        let idx = match lbd {
            0 | 1 => 0,
            2 => 1,
            3..=5 => 2,
            6..=10 => 3,
            _ => 4,
        };
        self.lbd_buckets[idx] += 1;
    }

    /// Record a decision level for peak/average tracking (#8131).
    #[inline]
    pub(crate) fn record_decision_level(&mut self, level: u32) {
        if level > self.peak_decision_level {
            self.peak_decision_level = level;
        }
        self.decision_level_sum += u64::from(level);
        self.decision_level_count += 1;
    }

    #[inline]
    pub(crate) fn record_restart_attribution(
        &mut self,
        cause: RestartAttribution,
        stable_mode: bool,
    ) {
        self.restart_attribution[cause.index()] += 1;
        self.restart_attribution_modes[usize::from(stable_mode)] += 1;
    }

    #[inline]
    pub(crate) fn clear_pending_restart_attribution(&mut self) {
        self.pending_restart_attribution = None;
    }

    #[inline]
    pub(crate) fn set_pending_restart_attribution(
        &mut self,
        cause: RestartAttribution,
        stable_mode: bool,
    ) {
        self.pending_restart_attribution = Some((cause, stable_mode));
    }

    #[inline]
    pub(crate) fn record_pending_restart_attribution(&mut self) {
        if let Some((cause, stable_mode)) = self.pending_restart_attribution.take() {
            self.record_restart_attribution(cause, stable_mode);
        }
    }

    #[inline]
    pub(crate) fn record_rephase_mode(&mut self, stable_mode: bool) {
        self.rephase_attribution_modes[usize::from(stable_mode)] += 1;
    }

    #[inline]
    pub(crate) fn record_rephase_attribution(
        &mut self,
        kind: RephaseAttribution,
        changed_phases: u64,
    ) {
        self.rephase_attribution[kind.index()] += 1;
        self.rephase_direct_changed_phases = self
            .rephase_direct_changed_phases
            .saturating_add(changed_phases);
    }

    pub(crate) fn record_inprocessing_time(&mut self, pass: DiagnosticPass, elapsed_ns: u64) {
        if let Some(index) = inprocessing_timing_index(pass) {
            self.inprocessing_time_ns[index] =
                self.inprocessing_time_ns[index].saturating_add(elapsed_ns);
        }
    }

    #[inline]
    pub(crate) fn record_inprocessing_attempt(&mut self, pass: DiagnosticPass) {
        if let Some(index) = inprocessing_timing_index(pass) {
            self.inprocessing_pass_attempts[index] =
                self.inprocessing_pass_attempts[index].saturating_add(1);
        }
    }

    #[inline]
    pub(crate) fn record_inprocessing_run(&mut self, pass: DiagnosticPass) {
        if let Some(index) = inprocessing_timing_index(pass) {
            self.inprocessing_pass_runs[index] =
                self.inprocessing_pass_runs[index].saturating_add(1);
        }
    }

    #[inline]
    pub(crate) fn record_inprocessing_yield(&mut self, pass: DiagnosticPass) {
        if let Some(index) = inprocessing_timing_index(pass) {
            self.inprocessing_pass_yields[index] =
                self.inprocessing_pass_yields[index].saturating_add(1);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn inprocessing_accounting_records_by_pass_index() {
        let mut stats = SolverStats::new();

        stats.record_inprocessing_attempt(DiagnosticPass::Subsume);
        stats.record_inprocessing_run(DiagnosticPass::Subsume);
        stats.record_inprocessing_yield(DiagnosticPass::Subsume);
        stats.record_inprocessing_attempt(DiagnosticPass::None);

        let idx = inprocessing_timing_index(DiagnosticPass::Subsume).unwrap();
        assert_eq!(stats.inprocessing_pass_attempts[idx], 1);
        assert_eq!(stats.inprocessing_pass_runs[idx], 1);
        assert_eq!(stats.inprocessing_pass_yields[idx], 1);
        assert!(stats
            .inprocessing_pass_attempts
            .iter()
            .enumerate()
            .all(|(i, &value)| i == idx || value == 0));
    }

    #[test]
    fn bcp_learned_1963_identity_top_fsw_rows_rank_by_fsw_steps() {
        let mut table = BcpLearned1963IdentityTable::default();

        table.record(10, 100, 32, 10, 0, 5, -1, -1, true, true, 4, 0);
        table.record(20, 200, 32, 10, 0, 100, 1, -1, false, false, 4, 0);
        table.record(30, 300, 32, 10, 0, 7, -1, 0, true, true, 4, 0);

        let top_all = table.top_rows(2);
        assert_eq!(top_all[0].clause_id, 20);

        let top_fsw = table.top_fsw_rows(2);
        assert_eq!(
            top_fsw.iter().map(|row| row.clause_id).collect::<Vec<_>>(),
            vec![30, 10]
        );
        assert!(top_fsw.iter().all(|row| row.fsw_steps > 0));
        assert_eq!(table.top_fsw_scan_steps(2), 12);
    }
}
