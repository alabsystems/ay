// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `--sat-veripb-hints` ready ids: a clause derived while its RUP refutation
//! is still on the trail (a probe's contradiction, an on-the-fly
//! strengthening, a hyper-binary resolvent) has its hint ids read off the
//! trail by the conflict-analysis walk, and the next derived addition of
//! exactly that clause is written with them (`veripb_emit_derived_hinted`).

use super::veripb_hints::{HintFail, VeripbHintState};
use super::*;

impl Solver {
    /// Hint ids for `clause` at a RUP probe's contradiction, before the probe
    /// backtracks: the negation of `clause` was decided and propagated, and
    /// either `conflict` is falsified or propagation made `implied`, a literal
    /// of `clause`, true (its reason is then falsified under the negation).
    /// The walk of conflict analysis reads the ids off the trail; `None` when
    /// it cannot. The pending learned clause's hints are left untouched.
    #[track_caller]
    pub(super) fn veripb_probe_hints(
        &mut self,
        clause: &[Literal],
        conflict: Option<ClauseRef>,
        implied: Option<Literal>,
    ) -> Option<Vec<u64>> {
        if !self.veripb_hints_active() {
            return None;
        }
        let mut st = std::mem::take(&mut self.cold.veripb_hints);
        let saved_ids = std::mem::take(&mut st.ids);
        let saved_fail = st.fail.take();
        let walked = self.veripb_probe_walk(&mut st, clause, conflict, implied);
        if let Err(fail) = walked {
            st.probe_fail_counts[fail as usize] += 1;
            let at = std::panic::Location::caller();
            *st.probe_fail_sites
                .entry((at.file(), at.line()))
                .or_default() += 1;
        }
        let ids = walked.is_ok().then(|| st.ids.clone());
        st.ids = saved_ids;
        st.fail = saved_fail;
        self.cold.veripb_hints = st;
        ids
    }

    /// `veripb_probe_hints` at a conflict reached after deciding `decided`,
    /// which `reason` implies under the RUP assumption: vivification's
    /// instantiation decides the clause's last literal true, and the clause
    /// itself, its other literals assumed false, implies it.
    #[track_caller]
    pub(super) fn veripb_probe_hints_through(
        &mut self,
        clause: &[Literal],
        conflict: ClauseRef,
        decided: Literal,
        reason: ClauseRef,
    ) -> Option<Vec<u64>> {
        if !self.veripb_hints_active() {
            return None;
        }
        self.cold.veripb_hints.decision_reason = Some((decided.variable().index(), reason));
        let ids = self.veripb_probe_hints(clause, Some(conflict), None);
        self.cold.veripb_hints.decision_reason = None;
        ids
    }

    /// `veripb_probe_hints` for a clause's RUP probe
    /// (`rup_clause_with_veripb_hints`), stopped at `conflict` or at
    /// `implied`, a clause literal found true. The propagation that stopped it
    /// can have made other literals of `clause` true first: the forward
    /// equivalence binary (¬lhs ∨ rhs) of a congruence edge decides lhs, which
    /// propagates rhs through the two gates' definitions and, when lhs is a
    /// failed literal, then conflicts. The walk stamps variables, so a true
    /// literal may not be among those it assumes false: it explains the first
    /// true literal (a root one, else the earliest on the trail) and leaves the
    /// other true literals out of the clause it refutes. Ids refuting the
    /// negation of that subclause refute the negation of `clause`, which only
    /// assigns more. With no other literal true this is `veripb_probe_hints`.
    #[track_caller]
    pub(super) fn veripb_clause_probe_hints(
        &mut self,
        clause: &[Literal],
        conflict: Option<ClauseRef>,
        implied: Option<Literal>,
    ) -> Option<Vec<u64>> {
        if !self.veripb_hints_active() {
            return None;
        }
        // The probe decides only negations of clause literals, which stay
        // stamped: no decision is ever explained by a clause here.
        debug_assert!(self.cold.veripb_hints.decision_reason.is_none());
        let first_true = clause
            .iter()
            .copied()
            .filter(|&lit| self.lit_val(lit) > 0)
            .min_by_key(|&lit| {
                self.var_data
                    .get(lit.variable().index())
                    .map_or((true, u32::MAX), |vd| (vd.level != 0, vd.trail_pos))
            });
        let Some(t) = first_true else {
            return self.veripb_probe_hints(clause, conflict, implied);
        };
        let kept: Vec<Literal> = clause
            .iter()
            .copied()
            .filter(|&lit| lit == t || self.lit_val(lit) <= 0)
            .collect();
        self.veripb_probe_hints(&kept, None, Some(t))
    }

    fn veripb_probe_walk(
        &mut self,
        st: &mut VeripbHintState,
        clause: &[Literal],
        conflict: Option<ClauseRef>,
        implied: Option<Literal>,
    ) -> Result<(), HintFail> {
        let stamp = self.veripb_hint_stamp(st, clause, implied)?;
        match (conflict, implied) {
            (Some(conflict), _) => self.veripb_hint_seed_conflict(st, conflict, stamp)?,
            (None, Some(t)) if self.lit_val(t) > 0 => st.stack.push(t.negated()),
            _ => return Err(HintFail::NoConflict),
        }
        self.veripb_hint_drain(st, stamp)
    }

    /// Conflict analysis is about to try on-the-fly strengthening while
    /// resolving from `conflict`.
    pub(super) fn veripb_note_otfs_conflict(&mut self, conflict: ClauseRef) {
        if self.veripb_hints_active() {
            self.cold.veripb_hints.derived.otfs_conflict = Some(conflict);
        }
    }

    /// Ready ids for `lits`, a reason OTFS shortened by its pivot (and root
    /// literals): every literal is false on the trail, so the conflict-analysis
    /// walk from the noted conflict clause, with `lits` assumed, reaches the
    /// pivot through the old reason and stops at `lits`. On
    /// aes_equiv_encry_3_rounds' neighbour 0be1e12a these strengthenings were
    /// 43,591 of the proof's 71,415 `red` steps.
    #[track_caller]
    pub(super) fn veripb_otfs_ready(&mut self, lits: &[Literal]) {
        let Some(conflict) = self.cold.veripb_hints.derived.otfs_conflict.take() else {
            return;
        };
        if let Some(ids) = self.veripb_probe_hints(lits, Some(conflict), None) {
            self.veripb_ready_hints(lits, &ids);
        }
    }

    /// Ready ids for `clause`, derived from `reason` (the clause propagating
    /// its last literal) and implications on the trail: a hyper-binary
    /// resolvent at the moment probing creates it. The walk takes an
    /// unassigned literal of `reason` as false only when `clause` has it with
    /// the same sign (it is then assumed false by the RUP check).
    #[track_caller]
    pub(super) fn veripb_ready_from_reason(&mut self, clause: &[Literal], reason: ClauseRef) {
        if !self.veripb_hints_active() {
            return;
        }
        let idx = reason.0 as usize;
        for i in 0..self.arena.len_of(idx) {
            let lit = self.arena.literal(idx, i);
            if self.lit_val(lit) == 0 && !clause.contains(&lit) {
                return;
            }
        }
        if let Some(ids) = self.veripb_probe_hints(clause, Some(reason), None) {
            self.veripb_ready_hints(clause, &ids);
        }
    }

    /// Hint ids read for `clause` by `veripb_probe_hints` at its RUP probe:
    /// the next derived addition of exactly this clause is written with them.
    pub(super) fn veripb_ready_hints(&mut self, clause: &[Literal], ids: &[u64]) {
        if ids.is_empty() || !self.veripb_hints_active() {
            return;
        }
        let derived = &mut self.cold.veripb_hints.derived;
        derived.ready_for.clear();
        derived.ready_for.extend_from_slice(clause);
        derived.ready_for.sort_unstable_by_key(|lit| lit.0);
        derived.ready.clear();
        derived.ready.extend_from_slice(ids);
    }
}
