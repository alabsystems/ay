// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Scratch-term isolation for a DECLINING lane pass (Risk R11,
//! #qlra-nested-cegqi review).
//!
//! # Why
//!
//! The search mints its tree, selection and instance terms into the live
//! store (the consequence replay must find them there), and the replay's
//! same-context probe mints more. On decline those terms used to stay, and
//! the legacy path's whole-store scans then saw them: measured on the
//! differential fuzz, `ce-free-resolve` went from 1.5 s `unsat` to a 20 s
//! timeout on one problem and from 3.1 s to 8.5 s on another; an experiment
//! binary that only kept the search's terms reproduced the first, one that
//! discarded them decided both. It is the hazard `dt_abandon.rs` documents
//! for the lazy DT lane (#dt-lazy-isolation), and this module follows its
//! discipline.
//!
//! # Contract
//!
//! [`ay_core::TermStore::rollback_to`] recycles ids: no `TermId` minted by
//! the pass may survive anywhere. A declining pass hands ids only to holders
//! restored here — the consequence-replay attempt ledger (restored by
//! `qlra_publish_unsat` itself), the array-default sidecars the same-context
//! probe swaps, the thread-local LIA probe hint, the eval memo and the
//! store-indexed caches. Holders it cannot restore are CHECKED instead and
//! keep the store when dirty: the proof tracker (steps and scope depth), the
//! quantifier manager's existence, and the store's own structural stamp (a
//! compaction during the pass retires the checkpoint). The caller rolls back
//! only when no proof was installed and no in-place solve ran (the SAT
//! route), so a kept store is the pre-isolation behaviour: sound, just
//! scaffold-polluted.

use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::term::{TermStoreRollbackCheckpoint, TermStoreSnapshotStamp};
use ay_core::{Sort, TermId};

use super::super::Executor;

/// Everything a declining pass needs to erase itself.
pub(in crate::executor) struct QlraLaneEntry {
    checkpoint: TermStoreRollbackCheckpoint,
    /// The store length at the checkpoint (the session cache survives a
    /// rollback to it when every cached id lies below it).
    len: usize,
    stamp: TermStoreSnapshotStamp,
    proof_steps: usize,
    proof_scope_depth: usize,
    had_quantifier_manager: bool,
    array_default_epsilon_by_sort: HashMap<Sort, TermId>,
    array_default_diag_by_sort: HashMap<Sort, String>,
    lia_probe_state: ay_lia::ProbeStateSnapshot,
}

impl Executor {
    /// Snapshot the pass's entry state.
    pub(in crate::executor) fn qlra_lane_entry(&self) -> QlraLaneEntry {
        QlraLaneEntry {
            checkpoint: self.ctx.terms.rollback_checkpoint(),
            len: self.ctx.terms.len(),
            stamp: self.ctx.terms.snapshot_stamp(),
            proof_steps: self.proof_tracker.num_steps(),
            proof_scope_depth: self.proof_tracker.scope_depth(),
            had_quantifier_manager: self.quantifier_manager.is_some(),
            array_default_epsilon_by_sort: self.array_default_epsilon_by_sort.clone(),
            array_default_diag_by_sort: self.array_default_diag_by_sort.clone(),
            lia_probe_state: ay_lia::save_probe_state(),
        }
    }

    /// Erase a declined pass. Returns whether the store was rolled back;
    /// `false` keeps every scratch term (sound, only polluted). The outcome
    /// is recorded under the statistics key `stat_key`. Also used by the
    /// equality-QE lane (`eq_qe_lane.rs`), whose declining pass follows the
    /// same discipline.
    pub(in crate::executor) fn qlra_lane_roll_back(
        &mut self,
        entry: QlraLaneEntry,
        stat_key: &'static str,
    ) -> bool {
        let QlraLaneEntry {
            checkpoint,
            len,
            stamp,
            proof_steps,
            proof_scope_depth,
            had_quantifier_manager,
            array_default_epsilon_by_sort,
            array_default_diag_by_sort,
            lia_probe_state,
        } = entry;
        // Hints may name terms the rollback below recycles.
        self.qlra_lane.expansion_hints = None;
        ay_lia::restore_probe_state(lia_probe_state);
        crate::executor::model::eval_memo_clear();
        self.clear_dt_lazy_rebuildable_term_indexes();
        let clean = self.proof_tracker.num_steps() == proof_steps
            && self.proof_tracker.scope_depth() == proof_scope_depth
            && self.quantifier_manager.is_some() == had_quantifier_manager
            && stamp.is_append_only_prefix_of(&self.ctx.terms);
        if !clean {
            self.last_statistics.set_string(stat_key, "kept-dirty");
            return false;
        }
        self.array_default_epsilon_by_sort = array_default_epsilon_by_sort;
        self.array_default_diag_by_sort = array_default_diag_by_sort;
        // M4: the session cache outlives a rollback that recycles only ids
        // above everything it holds; re-bind it to the new generation.
        let survives = self
            .qlra_lane
            .session
            .survives_rollback_to(&self.ctx.terms, len);
        self.ctx.terms.rollback_to(checkpoint);
        self.qlra_lane
            .session
            .rebind_after_rollback(&self.ctx.terms, survives);
        self.clear_dt_lazy_rebuildable_term_indexes();
        self.last_statistics.set_string(stat_key, "rolled-back");
        true
    }
}
