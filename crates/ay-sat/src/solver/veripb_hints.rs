// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `--sat-veripb-hints`: learned clauses as annotated RUP on the VeriPB route.
//!
//! SAT Competition 2026 checks a VeriPB proof by elaborating it
//! (`veripb -u --elaborate`) into a kernel proof for the verified checker
//! CakePB. An unannotated `rup` step makes VeriPB propagate over the whole
//! constraint database to find the step's antecedents; on ER_500_50_1 a 3.9 GB
//! proof was still checking after 7 CPU hours, while the fully annotated
//! kernel proof of an ordinary 290 MB proof checks in 10 s against 75 s.
//!
//! The antecedents of a learned clause C are read off the trail after conflict
//! analysis, before backtracking: starting from the conflict clause, every
//! false literal not in C is explained by its reason clause, which joins the
//! hints and is explained in turn, or, at level 0, by a unit constraint (one
//! the proof already holds, or a plain `rup` unit written on the spot). A reason
//! is followed only when its other literals are false and strictly earlier on
//! the trail, so the hinted constraints replay the derivation by unit
//! propagation in trail order, and they are written in that order (root units,
//! reasons from the earliest, the conflict last): VeriPB propagates the ids
//! pass after pass in the order given, and one pass then reaches the conflict
//! (`veripb_hint_drain`). A jump reason is replaced by the real binary
//! clause it skipped, and a reason on-the-fly strengthening has shortened is
//! hinted as the conflict it has become. Hint ids come from the VeriPB writer's own
//! numbering, by clause content; any constraint whose id is not certain, a
//! decision outside C, or a walk over budget drops the hints and the clause is
//! written as before. A missing hint therefore costs checking time, never
//! validity, and every hinted step is still checked by VeriPB.

use super::veripb_sweep::{hint_mark, hint_stamped};
use super::*;
use crate::diagnostic_trace::DiagnosticPass;

#[derive(Clone, Default)]
pub(crate) struct VeripbHintState {
    /// Resolved on first use: the switch is on, the proof is VeriPB, no LRAT.
    active: Option<bool>,
    /// Conflict clause of the analysis in progress.
    conflict: Option<ClauseRef>,
    /// Hint ids for `learned`, valid while `learned` is non-empty.
    pub(super) ids: Vec<u64>,
    /// The learned clause the ids belong to, sorted (internal literals).
    learned: Vec<Literal>,
    /// Per variable, the walk that stamped it (high half) and its rank on
    /// the trail (low half, `hint_rank`), so a literal the walk has already
    /// met is checked against a later reason by one load.
    pub(super) stamp: Vec<u64>,
    stamp_counter: u32,
    /// Literals to explain, before the sweep (`veripb_hint_drain`).
    pub(super) stack: Vec<Literal>,
    /// Trail positions the sweep is still to explain, a bit each; all clear
    /// between walks.
    pub(super) need: Vec<u64>,
    /// A bit per `need` word that has one set (`veripb_hint_next_word`).
    pub(super) need_top: Vec<u64>,
    /// Root unit ids the walk in progress names (they lead the hints).
    pub(super) unit_ids: Vec<u64>,
    scratch: Vec<Literal>,
    pub(super) scratch2: Vec<Literal>,
    /// Jump reasons explained through the real binary clause instead.
    pub(super) jumps_resolved: u64,
    /// Literals the learned-clause walks explained, and hint ids they named.
    pub(super) walk_visited: u64,
    pub(super) walk_ids: u64,
    pub(super) drain_visited: u64,
    pub(super) walk_units: u64,
    pub(super) walk_ns: u64,
    pub(super) drain_units: u64,
    pub(super) hinted: u64,
    pub(super) fallbacks: u64,
    pub(super) units_written: u64,
    /// Why the last walk failed, and the count of fallbacks per reason.
    pub(super) fail: Option<HintFail>,
    pub(super) fail_counts: [u64; HINT_FAIL_KEYS.len()],
    /// Proof additions through `proof_emit_add` (on VeriPB, `red` steps with
    /// no antecedents unless `derived` hints them), by the diagnostic pass
    /// that wrote them.
    pub(super) adds_by_pass: [u64; DiagnosticPass::BY_CODE.len()],
    /// `red` steps by the call site that wrote them (`note_unhinted_add`).
    pub(super) red_sites: std::collections::HashMap<(&'static str, u32), u64>,
    /// RUP-probe walks (`veripb_probe_hints`) that failed, by reason and by
    /// the call site that asked.
    pub(super) probe_fail_counts: [u64; HINT_FAIL_KEYS.len()],
    pub(super) probe_fail_sites: std::collections::HashMap<(&'static str, u32), u64>,
    /// A decision the walk explains by a clause instead of failing: the
    /// variable and the clause (`veripb_probe_hints_through`).
    pub(super) decision_reason: Option<(usize, ClauseRef)>,
    /// Hints for clauses derived outside conflict analysis (`veripb_derived.rs`).
    pub(super) derived: super::veripb_derived::VeripbDerivedState,
}

/// Why a learned clause went out without hints.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum HintFail {
    NoConflict,
    LearnedNotFalse,
    ConflictNotFalse,
    ConflictIdUnknown,
    Budget,
    ConeLitNotFalse,
    Level0UnitMissing,
    TrailPosMismatch,
    AntecedentOrder,
    DecisionInCone,
    ReasonIdUnknown,
    EmitMismatch,
    EmitFailed,
}

/// The stat keys of `veripb_hint_fail_profile`, in `HintFail` order.
pub(super) const HINT_FAIL_KEYS: [&str; 13] = [
    "sat.veripb_hint_fail_no_conflict",
    "sat.veripb_hint_fail_learned_not_false",
    "sat.veripb_hint_fail_conflict_not_false",
    "sat.veripb_hint_fail_conflict_id_unknown",
    "sat.veripb_hint_fail_budget",
    "sat.veripb_hint_fail_cone_lit_not_false",
    "sat.veripb_hint_fail_level0_unit_missing",
    "sat.veripb_hint_fail_trail_pos_mismatch",
    "sat.veripb_hint_fail_antecedent_order",
    "sat.veripb_hint_fail_decision_in_cone",
    "sat.veripb_hint_fail_reason_id_unknown",
    "sat.veripb_hint_fail_emit_mismatch",
    "sat.veripb_hint_fail_emit_failed",
];

impl Solver {
    /// Inspect only the existing cache before an admitted analysis takes
    /// ownership. This never resolves flags, inspects a writer or enables hints.
    pub(in crate::solver) fn veripb_hints_cached_active(&self) -> bool {
        self.cold.veripb_hints.active == Some(true)
    }

    /// Unlike "not active", this rules out lazy configuration capture inside
    /// an admitted emission. Ordinary analysis resolves this before finalizing.
    pub(in crate::solver) fn veripb_hints_resolved_inactive(&self) -> bool {
        self.cold.veripb_hints.active == Some(false)
    }

    #[cfg(test)]
    pub(in crate::solver) fn mark_veripb_hints_active_for_test(&mut self) {
        self.cold.veripb_hints.active = Some(true);
    }

    /// Whether learned clauses get annotated RUP on this solver.
    pub(super) fn veripb_hints_active(&mut self) -> bool {
        if let Some(on) = self.cold.veripb_hints.active {
            return on;
        }
        let on = ay_core::sat_ab_switches().veripb_hints == Some(true)
            && !self.cold.lrat_enabled
            && self
                .proof_manager
                .as_mut()
                .is_some_and(|manager| manager.output_mut().is_veripb());
        self.cold.veripb_hints.active = Some(on);
        on
    }

    /// Formula clause `id` (its 1-based clause line) for hint lookup; called by
    /// the DIMACS reader for every clause line, before the solver sees it.
    pub fn note_veripb_original(&mut self, clause: &[Literal], id: u64) {
        if let Some(manager) = self.proof_manager.as_mut() {
            manager.output_mut().veripb_note_original(clause, id);
        }
    }

    /// The conflict clause of the analysis starting now: marked for streaming
    /// support (#8250) and remembered as the seed of the hint walk.
    #[inline]
    pub(super) fn note_analysis_conflict(&mut self, conflict: ClauseRef) {
        self.mark_streaming_core(conflict);
        self.veripb_hints_note_conflict(conflict);
    }

    /// Remember the conflict clause of the analysis starting now.
    #[inline]
    fn veripb_hints_note_conflict(&mut self, conflict: ClauseRef) {
        if self.cold.veripb_hints.active == Some(false) {
            return;
        }
        if self.veripb_hints_active() {
            self.cold.veripb_hints.conflict = Some(conflict);
        }
    }

    /// Read the hints of `learned` (the finished learned clause) off the trail.
    /// Called at the end of conflict analysis, before backtracking.
    pub(super) fn veripb_collect_hints(&mut self, learned: &[Literal]) {
        if !self.veripb_hints_active() {
            return;
        }
        let mut st = std::mem::take(&mut self.cold.veripb_hints);
        st.ids.clear();
        st.learned.clear();
        st.drain_units = 0;
        let started = ay_core::time::Instant::now();
        st.fail = self.veripb_hint_walk(&mut st, learned).err();
        st.walk_ns += started.elapsed().as_nanos() as u64;
        st.walk_units += std::mem::take(&mut st.drain_units);
        st.walk_ids += st.ids.len() as u64;
        st.walk_visited += std::mem::take(&mut st.drain_visited);
        if st.fail.is_some() {
            st.ids.clear();
        } else {
            st.learned.extend_from_slice(learned);
            st.learned.sort_unstable_by_key(|lit| lit.0);
        }
        st.conflict = None;
        self.cold.veripb_hints = st;
    }

    /// The walk proper: why not, when the hints cannot be made certain.
    fn veripb_hint_walk(
        &mut self,
        st: &mut VeripbHintState,
        learned: &[Literal],
    ) -> Result<(), HintFail> {
        let conflict = st.conflict.ok_or(HintFail::NoConflict)?;
        let stamp = self.veripb_hint_stamp(st, learned, None)?;
        self.veripb_hint_seed_conflict(st, conflict, stamp)?;
        self.veripb_hint_drain(st, stamp)
    }

    /// A fresh stamp with the variables of `clause` on it: its literals are
    /// assumed false by the RUP check, so never explained. None may be true on
    /// the trail, except `implied`, which is left to be explained.
    pub(super) fn veripb_hint_stamp(
        &mut self,
        st: &mut VeripbHintState,
        clause: &[Literal],
        implied: Option<Literal>,
    ) -> Result<u32, HintFail> {
        if st.stamp.len() < self.num_vars {
            st.stamp.resize(self.num_vars, 0);
        }
        if st.stamp_counter == u32::MAX {
            st.stamp.fill(0);
            st.stamp_counter = 0;
        }
        st.stamp_counter += 1;
        let stamp = st.stamp_counter;
        for &lit in clause {
            if Some(lit) == implied {
                continue;
            }
            let v = lit.variable().index();
            // Unassigned is as good as false here (no trail implication rests
            // on it); a true literal is not.
            if v >= st.stamp.len() || self.lit_val(lit) > 0 {
                return Err(HintFail::LearnedNotFalse);
            }
            st.stamp[v] = hint_mark(stamp, self.veripb_hint_rank(lit));
        }
        st.stack.clear();
        Ok(stamp)
    }

    /// Start the walk at a clause false under the RUP assumption: its id
    /// first, its literals queued. Each literal must be false on the trail,
    /// or unassigned with its variable stamped (a hyper-binary resolvent's
    /// propagated literal; the caller checks its sign).
    pub(super) fn veripb_hint_seed_conflict(
        &mut self,
        st: &mut VeripbHintState,
        conflict: ClauseRef,
        stamp: u32,
    ) -> Result<(), HintFail> {
        let conflict_idx = conflict.0 as usize;
        let conflict_len = self.arena.len_of(conflict_idx);
        st.scratch.clear();
        for i in 0..conflict_len {
            let lit = self.arena.literal(conflict_idx, i);
            let val = self.lit_val(lit);
            let stamped = st
                .stamp
                .get(lit.variable().index())
                .is_some_and(|&mark| hint_stamped(mark, stamp));
            if val > 0 || (val == 0 && !stamped) {
                return Err(HintFail::ConflictNotFalse);
            }
            st.scratch.push(lit);
            st.stack.push(lit);
        }
        let id = self
            .veripb_scratch_id(st)
            .ok_or(HintFail::ConflictIdUnknown)?;
        st.ids.push(id);
        Ok(())
    }

    /// The VeriPB id of the clause in `st.scratch` (internal literals, left
    /// unchanged).
    fn veripb_scratch_id(&mut self, st: &mut VeripbHintState) -> Option<u64> {
        st.scratch2.clear();
        st.scratch2.extend_from_slice(&st.scratch);
        self.veripb_constraint_id_of(&mut st.scratch2)
    }

    /// The VeriPB id of the constraint with content `lits` (internal literals;
    /// externalized in place when the proof speaks external variables).
    pub(super) fn veripb_constraint_id_of(&mut self, lits: &mut [Literal]) -> Option<u64> {
        if self.cold.proof_vars_compacted {
            for lit in lits.iter_mut() {
                *lit = self.externalize_for_proof(*lit);
            }
        }
        self.proof_manager
            .as_mut()?
            .output_mut()
            .veripb_constraint_id(lits)
    }

    /// Write learned clause `lits` as annotated RUP if the hints collected at
    /// the end of its analysis belong to it; `true` when written.
    pub(super) fn veripb_emit_learned_hinted(&mut self, lits: &[Literal]) -> bool {
        if self.cold.veripb_hints.active != Some(true) {
            return false;
        }
        let mut st = std::mem::take(&mut self.cold.veripb_hints);
        let written = self.veripb_emit_learned_hinted_with(&mut st, lits);
        match written {
            Ok(()) => st.hinted += 1,
            Err(emit_fail) => {
                st.fallbacks += 1;
                st.fail_counts[st.fail.unwrap_or(emit_fail) as usize] += 1;
            }
        }
        st.fail = None;
        st.ids.clear();
        st.learned.clear();
        self.cold.veripb_hints = st;
        written.is_ok()
    }

    fn veripb_emit_learned_hinted_with(
        &mut self,
        st: &mut VeripbHintState,
        lits: &[Literal],
    ) -> Result<(), HintFail> {
        if st.ids.is_empty() || st.learned.len() != lits.len() {
            return Err(HintFail::EmitMismatch);
        }
        st.scratch.clear();
        st.scratch.extend_from_slice(lits);
        st.scratch.sort_unstable_by_key(|lit| lit.0);
        if st.scratch != st.learned {
            return Err(HintFail::EmitMismatch);
        }
        st.scratch.clear();
        st.scratch.extend_from_slice(lits);
        if self.cold.proof_vars_compacted {
            for lit in st.scratch.iter_mut() {
                *lit = self.externalize_for_proof(*lit);
            }
        }
        let manager = self.proof_manager.as_mut().ok_or(HintFail::EmitFailed)?;
        manager
            .emit_add_veripb_rup(&st.scratch, &st.ids)
            .map(|_| ())
            .map_err(|_| HintFail::EmitFailed)
    }
}

#[cfg(test)]
#[path = "veripb_hints_tests.rs"]
mod tests;
