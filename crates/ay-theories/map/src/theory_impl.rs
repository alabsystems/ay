// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! `TheorySolver` implementation for [`MapSolver`].
//!
//! Implements the DPLL(T) theory interface for the native map theory. The
//! implementation is **fail-closed**: when an out-of-fragment operator is
//! present, [`check`](MapSolver::check) returns [`TheoryResult::Unknown`]
//! rather than risk an unsound SAT/UNSAT verdict.

use super::*;

impl TheorySolver for MapSolver<'_> {
    fn register_atom(&mut self, atom: TermId) {
        self.cache_term(atom);
    }

    fn internalize_atom(&mut self, term: TermId) {
        self.cache_term(term);
    }

    fn assert_literal(&mut self, literal: TermId, value: bool) {
        let prev = self.assigns.insert(literal, value);
        self.trail.push((literal, prev));
        self.dirty = true;
        self.cache_term(literal);
    }

    fn check(&mut self) -> TheoryResult {
        if !self.dirty {
            return TheoryResult::Sat;
        }
        self.dirty = false;

        // Fail-closed: out-of-fragment (polymorphic / higher-order image)
        // operators are NOT decided. Returning Unknown here is mandatory — a
        // guessed SAT/UNSAT outside the sound fragment is a critical bug.
        if self.out_of_fragment {
            return TheoryResult::Unknown;
        }

        // Subset reflexivity refutation (¬subset(m, m) is unsatisfiable).
        if let Some(conflict) = self.check_subset_saturation() {
            return TheoryResult::Unsat(conflict);
        }

        TheoryResult::Sat
    }

    fn propagate(&mut self) -> Vec<TheoryPropagation> {
        Vec::new()
    }

    fn propagate_equalities(&mut self) -> EqualityPropagationResult {
        let equalities = std::mem::take(&mut self.pending_equalities);
        EqualityPropagationResult {
            equalities,
            ..Default::default()
        }
    }

    fn assert_shared_equality(&mut self, lhs: TermId, rhs: TermId, reason: &[TheoryLit]) {
        self.cache_term(lhs);
        self.cache_term(rhs);
        self.shared_equalities.push((lhs, rhs, reason.to_vec()));
        self.dirty = true;
    }

    fn push(&mut self) {
        self.scopes.push(self.trail.len());
        self.shared_eq_scopes.push(self.shared_equalities.len());
    }

    fn pop(&mut self) {
        if let Some(mark) = self.scopes.pop() {
            while self.trail.len() > mark {
                let (atom, prev) = self.trail.pop().expect("invariant: trail length > mark");
                match prev {
                    Some(v) => {
                        self.assigns.insert(atom, v);
                    }
                    None => {
                        self.assigns.remove(&atom);
                    }
                }
            }
            self.dirty = true;
        }
        if let Some(mark) = self.shared_eq_scopes.pop() {
            self.shared_equalities.truncate(mark);
        }
        // Derived state cleared on pop (push/pop contract).
        self.pending_equalities.clear();
    }

    fn reset(&mut self) {
        self.assigns.clear();
        self.trail.clear();
        self.scopes.clear();
        self.dom_atoms.clear();
        self.get_atoms.clear();
        self.subset_atoms.clear();
        self.empty_terms.clear();
        self.out_of_fragment = false;
        self.pending_equalities.clear();
        self.shared_equalities.clear();
        self.shared_eq_scopes.clear();
        self.dirty = false;
    }

    fn collect_statistics(&self) -> Vec<(&'static str, u64)> {
        vec![
            ("map_dom_atoms", self.dom_atoms.len() as u64),
            ("map_get_atoms", self.get_atoms.len() as u64),
            ("map_subset_atoms", self.subset_atoms.len() as u64),
            ("map_empty_terms", self.empty_terms.len() as u64),
            ("map_out_of_fragment", u64::from(self.out_of_fragment)),
        ]
    }
}
