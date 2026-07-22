// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `TheorySolver` trait implementation for `SeqSolver`.
//!
//! Implements the DPLL(T) theory interface for the sequence theory.

use super::*;

impl TheorySolver for SeqSolver<'_> {
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

        // Check for unit = empty conflicts
        if let Some(conflict) = self.check_unit_empty_conflict() {
            return TheoryResult::Unsat(conflict);
        }

        // Decide concat equality by extensionality: detect length/element
        // conflicts and propagate positional element equalities (#native-seq).
        if let Some(conflict) = self.check_concat_equality() {
            return TheoryResult::Unsat(conflict);
        }

        // Propagate unit injectivity equalities
        self.check_unit_injectivity();

        TheoryResult::Sat
    }

    fn propagate(&mut self) -> Vec<TheoryPropagation> {
        std::mem::take(&mut self.pending_propagations)
    }

    fn assert_shared_equality(&mut self, lhs: TermId, rhs: TermId, reason: &[TheoryLit]) {
        // Cache both terms so unit/empty caches are populated (#5951).
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
    }

    fn reset(&mut self) {
        self.assigns.clear();
        self.trail.clear();
        self.scopes.clear();
        self.unit_cache.clear();
        self.len_cache.clear();
        self.concat_cache.clear();
        self.empty_cache.clear();
        self.nth_cache.clear();
        self.equality_cache.clear();
        self.pending_propagations.clear();
        self.pending_equalities.clear();
        self.shared_equalities.clear();
        self.shared_eq_scopes.clear();
        self.dirty = false;
    }

    fn propagate_equalities(&mut self) -> EqualityPropagationResult {
        let equalities = std::mem::take(&mut self.pending_equalities);
        EqualityPropagationResult {
            equalities,
            ..Default::default()
        }
    }

    fn collect_statistics(&self) -> Vec<(&'static str, u64)> {
        vec![
            ("seq_unit_terms", self.unit_cache.len() as u64),
            ("seq_len_terms", self.len_cache.len() as u64),
            ("seq_concat_terms", self.concat_cache.len() as u64),
            ("seq_empty_terms", self.empty_cache.len() as u64),
        ]
    }
}
