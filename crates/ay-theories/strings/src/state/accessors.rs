// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Read-only solver-state accessors.

use super::{Constant, EqcInfo, SolverState, TermData, TermId, TermStore, TheoryLit};

impl SolverState {
    /// If `t` is `str.len(arg)`, return `Some(arg)`. Otherwise `None`.
    pub(crate) fn get_str_len_arg(&self, terms: &TermStore, t: TermId) -> Option<TermId> {
        // Check the term itself and all members of its EQC.
        if let TermData::App(sym, args) = terms.get(t) {
            if sym.name() == "str.len" && args.len() == 1 {
                return Some(args[0]);
            }
        }
        None
    }

    /// Get the current disequalities as (rep1, rep2, original_literal).
    pub(crate) fn disequalities(&self) -> &[(TermId, TermId, TheoryLit)] {
        &self.disequalities
    }

    /// Check whether two terms (or their representatives) have a recorded disequality.
    ///
    /// Returns true if there exists a disequality `(r1, r2, _)` in the active list
    /// such that `{find(a), find(b)} = {find(r1), find(r2)}`.
    ///
    /// Used by `process_simple_deq` to detect CVC5 "Simple Case 2": when
    /// two NF components have equal length and are known disequal, the
    /// overall disequality is satisfied without inference.
    pub(crate) fn are_disequal(&self, a: TermId, b: TermId) -> bool {
        let ra = self.find(a);
        let rb = self.find(b);
        if ra == rb {
            return false;
        }
        self.disequalities.iter().any(|&(r1, r2, _)| {
            let f1 = self.find(r1);
            let f2 = self.find(r2);
            (f1 == ra && f2 == rb) || (f1 == rb && f2 == ra)
        })
    }

    /// Get EQC info for a representative (immutable).
    pub(crate) fn get_eqc(&self, rep: &TermId) -> Option<&EqcInfo> {
        self.eqc_info.get(rep)
    }

    /// Get the constant value for an equivalence class, if known.
    pub(crate) fn get_constant(&self, rep: &TermId) -> Option<&str> {
        self.eqc_info
            .get(rep)
            .and_then(|info| info.constant.as_deref())
    }

    /// Find the string constant TermId within an EQC.
    ///
    /// When the EQC has a known constant value, the representative may not be
    /// the constant literal itself (e.g., it could be a concat term that merged
    /// with the constant). This searches EQC members for the actual
    /// `Const(String(_))` term, which the executor needs for ConstSplit lemma
    /// character extraction.
    pub(crate) fn find_constant_term_id_for_rep(
        &self,
        terms: &TermStore,
        rep: &TermId,
    ) -> Option<TermId> {
        if let Some(empty_id) = self.empty_string_id {
            if *rep == self.find(empty_id) {
                return Some(empty_id);
            }
        }
        let eqc = self.eqc_info.get(rep)?;
        eqc.constant.as_ref()?;
        eqc.members
            .iter()
            .find(|&&m| matches!(terms.get(m), TermData::Const(Constant::String(_))))
            .copied()
    }

    /// Get the members of an EQC by its representative.
    pub(crate) fn eqc_members(&self, rep: TermId) -> Option<&[TermId]> {
        self.eqc_info.get(&rep).map(|e| e.members.as_slice())
    }

    /// Get the pending conflict, if any.
    ///
    /// A pending conflict is set when `merge()` detects two distinct string
    /// constants in the same EQC. Returns the (winner, loser) EQC reps.
    /// Consumed by `BaseSolver::check_init()`.
    pub(crate) fn pending_conflict(&self) -> Option<(TermId, TermId)> {
        self.pending_conflict
    }

    /// Get all current assertions (for conflict explanations).
    pub(crate) fn assertions(&self) -> &[TheoryLit] {
        &self.assertions
    }
}
