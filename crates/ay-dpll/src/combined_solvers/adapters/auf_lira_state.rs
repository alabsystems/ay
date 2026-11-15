// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Learned-state transfer, conflict collection, and replay accessors for AUFLIRA.

// #8529: Use deterministic hash sets in all builds.
use ay_core::kani_compat::DetHashSet as HashSet;

use ay_core::{Sort, TermData, TermId, TheorySolver};

use super::auf_lira::AufLiraSolver;
use crate::term_helpers::{arg_involves_select_or_store, is_select_or_store};

/// Upper bound on the violated disequalities one refuted check names beside
/// its conflict. Each costs an explanation and a re-check.
const FURTHER_DISEQUALITY_CONFLICTS: usize = 64;

/// Which solvers the lazy split loop reads between two rounds: for the phase
/// of an atom, and for the conflicts of a refuted assignment beside the one
/// `check` reported.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum SplitLoopReads {
    /// The Real solver. It has every atom registered but is handed Real
    /// literals only, so it says nothing true about an Int atom; the loop
    /// has always read it, and a solve that checks its verdict still does
    /// (the search order is unchanged there).
    RealSolver,
    /// The Int solver for an atom with an Int side, the E-graph for an
    /// equality it already holds, and all three for further conflicts.
    EverySolver,
}

impl<'a> AufLiraSolver<'a> {
    /// The same solver with the split loop reading `reads`.
    pub(crate) fn split_loop_reading(mut self, reads: SplitLoopReads) -> Self {
        self.split_loop_reads = reads;
        self
    }
}

impl AufLiraSolver<'_> {
    pub(crate) fn take_learned_state(
        &mut self,
    ) -> (Vec<ay_lia::StoredCut>, HashSet<ay_lia::HnfCutKey>) {
        self.lia.take_learned_state()
    }

    pub(crate) fn import_learned_state(
        &mut self,
        cuts: Vec<ay_lia::StoredCut>,
        seen: HashSet<ay_lia::HnfCutKey>,
    ) {
        self.lia.import_learned_state(cuts, seen);
    }

    pub(crate) fn take_dioph_state(&mut self) -> ay_lia::DiophState {
        self.lia.take_dioph_state()
    }

    pub(crate) fn import_dioph_state(&mut self, state: ay_lia::DiophState) {
        self.lia.import_dioph_state(state);
    }

    /// Every conflict of the refuted assignment this solver can name without
    /// more search, beside the one `check` reported. Reading the Real solver
    /// only, its contradictory variable bounds. Reading every solver, also
    /// those of the Int solver and the disequalities the E-graph violates;
    /// the split loop learns them with the reported conflict, one round for
    /// all of them. Each of these is re-checked the way the loop re-checks
    /// the conflict it was handed, and one a fresh solver can satisfy is not
    /// named. The reported conflict may be among them; learning a clause
    /// twice is harmless.
    pub(crate) fn collect_all_bound_conflicts(
        &mut self,
        skip_first: bool,
    ) -> Vec<ay_core::TheoryConflict> {
        if self.split_loop_reads == SplitLoopReads::RealSolver {
            return self.lra.collect_all_bound_conflicts(skip_first);
        }
        let mut conflicts = self.lia.collect_all_bound_conflicts(false);
        conflicts.extend(self.lra.collect_all_bound_conflicts(false));
        conflicts.extend(
            self.euf
                .collect_disequality_conflicts(FURTHER_DISEQUALITY_CONFLICTS)
                .into_iter()
                .map(ay_core::TheoryConflict::new),
        );
        conflicts.retain(|conflict| {
            crate::verification::verify_conflict_semantic(&conflict.literals, self.terms, &[])
                .is_ok()
        });
        conflicts
    }

    /// The phase the split loop should try first for `atom`.
    pub(super) fn phase_hint(&self, atom: TermId) -> Option<bool> {
        let TermData::App(ref sym, ref args) = self.terms.get(atom) else {
            return self.lra.suggest_phase(atom);
        };
        let comparison = matches!(sym.name(), "<=" | ">=" | "<" | ">") && args.len() == 2;
        // Suppress phase hints for inequality atoms involving select/store
        // (#6303). See auf_lia.rs suggest_phase for full rationale.
        if comparison
            && (arg_involves_select_or_store(self.terms, args[0])
                || arg_involves_select_or_store(self.terms, args[1]))
        {
            return None;
        }
        let simple_equality = sym.name() == "="
            && args.len() == 2
            && !is_select_or_store(self.terms, args[0])
            && !is_select_or_store(self.terms, args[1]);
        if self.split_loop_reads == SplitLoopReads::EverySolver {
            // An equality the E-graph already holds is true in every model
            // of the assignment.
            if simple_equality && self.euf.suggest_phase_implied(atom) == Some(true) {
                return Some(true);
            }
            // An atom with an Int side reads the Int solver's model.
            if (comparison || simple_equality) && matches!(self.terms.sort(args[0]), Sort::Int) {
                if let Some(phase) = self.lia.suggest_phase(atom) {
                    return Some(phase);
                }
            }
        }
        // Index equality atoms: suggest false (distinct).
        // See auf_lia.rs for full rationale (#6282).
        if simple_equality {
            return Some(false);
        }
        self.lra.suggest_phase(atom)
    }

    /// Replay learned cuts into the LRA solver (#6665).
    ///
    /// Forwards to both the standalone LRA solver and the LIA solver's
    /// internal LRA state.
    pub(crate) fn replay_learned_cuts(&mut self) {
        self.lra.replay_learned_cuts();
        self.lia.replay_learned_cuts();
    }

    /// The receiver of the split loop's bound conflict collection (#6665):
    /// this solver, so that the collection reaches the Int solver and the
    /// E-graph beside the Real solver. Explaining a violated disequality
    /// updates the E-graph's proof caches, hence `&mut`.
    pub(crate) fn lra_solver(&mut self) -> &mut Self {
        self
    }
}
