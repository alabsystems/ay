// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `TheorySolver` trait implementation for `BvSolver`.
//!
//! Implements the DPLL(T) theory interface for the bitvector theory.

use super::*;

impl TheorySolver for BvSolver<'_> {
    fn assert_literal(&mut self, literal: TermId, value: bool) {
        self.trail.push(literal);
        self.asserted.insert(literal, value);
        self.process_assertion(literal, value);
    }

    fn check(&mut self) -> TheoryResult {
        self.check_count += 1;
        // All constraints are eagerly bit-blasted to CNF
        // The SAT solver will find inconsistencies
        tracing::debug!(
            asserted = self.asserted.len(),
            term_to_bits = self.term_to_bits.len(),
            "BV check: sat (eager bit-blast)"
        );
        TheoryResult::Sat
    }

    fn propagate(&mut self) -> Vec<TheoryPropagation> {
        // Eager bit-blasting doesn't propagate - all is in CNF
        Vec::new()
    }

    fn collect_statistics(&self) -> Vec<(&'static str, u64)> {
        vec![
            ("bv_checks", self.check_count),
            ("bv_conflicts", self.conflict_count),
            ("bv_propagations", self.propagation_count),
        ]
    }

    fn push(&mut self) {
        self.trail_stack.push(self.trail.len());
    }

    fn pop(&mut self) {
        if let Some(size) = self.trail_stack.pop() {
            while self.trail.len() > size {
                if let Some(term) = self.trail.pop() {
                    self.asserted.remove(&term);
                }
            }
        }
    }

    fn reset(&mut self) {
        self.term_to_bits.clear();
        self.predicate_to_var.clear();
        self.bool_to_var.clear();
        self.clauses.clear();
        self.next_var = 1;
        self.trail.clear();
        self.trail_stack.clear();
        self.asserted.clear();
        self.known_false.clear();
        self.and_cache.clear();
        self.and_children.clear();
        self.or_cache.clear();
        self.xor_cache.clear();
        self.mux_cache.clear();
        self.delay_enabled = false;
        self.delayed_ops.clear();
        // #8618: Clear division caches, ITE conditions, and other stale state
        // that was previously missed, causing memory accumulation across
        // push/pop cycles in incremental solving.
        self.unsigned_div_cache.clear();
        self.signed_div_cache.clear();
        self.bv_ite_conditions.clear();
        self.cached_false_lit = None;
        self.eager_terms.clear();
        self.interrupt = None;
        // Shrink collections that may have grown during encoding (#8599).
        // Gate caches and term maps can grow very large for complex BV formulas.
        self.term_to_bits.shrink_to_fit();
        self.predicate_to_var.shrink_to_fit();
        self.bool_to_var.shrink_to_fit();
        self.clauses.shrink_to_fit();
        self.and_cache.shrink_to_fit();
        self.and_children.shrink_to_fit();
        self.or_cache.shrink_to_fit();
        self.xor_cache.shrink_to_fit();
        self.mux_cache.shrink_to_fit();
        self.known_false.shrink_to_fit();
        self.unsigned_div_cache.shrink_to_fit();
        self.signed_div_cache.shrink_to_fit();
        self.bv_ite_conditions.shrink_to_fit();
        self.eager_terms.shrink_to_fit();
    }
}
