// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `BvSolver` support for delayed internalization (#7015).
//!
//! These methods control when wide BV operations stay symbolic and how the
//! solver materializes a full circuit when cheap delayed checks are exhausted.

use super::*;

impl BvSolver<'_> {
    /// Enable delayed internalization for expensive BV operations.
    ///
    /// When enabled, mul/div/rem operations on wide bitvectors (>12 bits)
    /// with 2+ variable arguments get fresh unconstrained bits instead of
    /// full circuits. The caller must check delayed operations against the
    /// SAT model after solving and add conflict clauses if needed.
    ///
    /// Reference: Z3's `should_bit_blast()` heuristic
    /// (`reference/z3/src/sat/smt/bv_delay_internalize.cpp:45-57`)
    pub fn set_delay_enabled(&mut self, enabled: bool) {
        self.delay_enabled = enabled;
    }

    /// Whether delayed internalization is enabled.
    pub fn delay_enabled(&self) -> bool {
        self.delay_enabled
    }

    /// Get the list of delayed operations (operations with unconstrained bits).
    pub fn delayed_ops(&self) -> &[DelayedBvOp] {
        &self.delayed_ops
    }

    /// Check if a BV operation should be delayed (not eagerly bit-blasted).
    ///
    /// Ports Z3's `should_bit_blast()` heuristic:
    /// - Width <= 12: always bit-blast (circuit is small)
    /// - At most 1 non-constant argument: always bit-blast
    /// - Addition with num_vars * bv_size <= 64: always bit-blast
    /// - Otherwise (wide mul/div/rem with 2+ variable args): delay
    ///
    /// For combined theories (#8142), terms in `eager_terms` are never delayed.
    /// This ensures BV terms used as array indices or UF arguments have
    /// fully constrained bits for axiom generation.
    ///
    /// Reference: `reference/z3/src/sat/smt/bv_delay_internalize.cpp:45-57`
    pub(super) fn should_delay(&self, term: TermId, op: &str, args: &[TermId], width: u32) -> bool {
        if !self.delay_enabled {
            return false;
        }

        // In combined theories, terms marked eager must be fully bit-blasted (#8142).
        if self.eager_terms.contains(&term) {
            return false;
        }

        match op {
            "bvmul" | "bvudiv" | "bvurem" | "bvsdiv" | "bvsrem" | "bvsmod" => {}
            "bvadd" => {
                let num_vars = self.count_variable_args(args);
                if (num_vars as u32) * width <= 64 {
                    return false;
                }
            }
            _ => return false,
        }

        if width <= 12 {
            return false;
        }

        self.count_variable_args(args) > 1
    }

    /// Set the eager terms set (#8142).
    ///
    /// Terms in this set and their BV sub-expressions are never delayed, even
    /// when `delay_enabled` is true. Used by combined theory paths (QF_ABV,
    /// QF_UFBV) to ensure array index and UF argument terms have fully
    /// constrained bit representations.
    pub fn set_eager_terms(&mut self, terms: HashSet<TermId>) {
        self.eager_terms = terms;
    }

    /// Recursively collect all BV sub-expression TermIds reachable from `root`.
    ///
    /// Used to build the `eager_terms` set: when an array index contains
    /// `bvadd(base, bvmul(i, stride))`, both the bvadd AND the bvmul must
    /// be eagerly internalized. This walks the term DAG and collects every
    /// BV-sorted sub-term.
    pub fn collect_bv_subterms(terms: &TermStore, root: TermId, out: &mut HashSet<TermId>) {
        if out.contains(&root) {
            return;
        }
        if !matches!(terms.sort(root), Sort::BitVec(_)) {
            return;
        }
        out.insert(root);
        match terms.get(root) {
            TermData::App(_, args) => {
                for &arg in args {
                    Self::collect_bv_subterms(terms, arg, out);
                }
            }
            TermData::Ite(cond, t, e) => {
                let (cond, t, e) = (*cond, *t, *e);
                Self::collect_bv_subterms(terms, cond, out);
                Self::collect_bv_subterms(terms, t, out);
                Self::collect_bv_subterms(terms, e, out);
            }
            _ => {}
        }
    }

    /// Count the number of non-constant (variable) arguments in an operation.
    fn count_variable_args(&self, args: &[TermId]) -> usize {
        let mut count = args.len();
        for &arg in args {
            if let TermData::Const(_) = self.terms.get(arg) {
                count -= 1;
            }
        }
        count
    }

    /// Extract owned delayed state for use after BvSolver is dropped (#7015).
    ///
    /// Returns `Some(DelayedBvState)` if there are unresolved delayed operations,
    /// `None` otherwise.
    pub fn take_delayed_state(&self) -> Option<DelayedBvState> {
        if self.delayed_ops.iter().any(|op| !op.circuit_built) {
            Some(DelayedBvState::new(
                self.delayed_ops.clone(),
                self.term_to_bits.clone(),
            ))
        } else {
            None
        }
    }

    /// Check if there are any delayed operations that haven't been resolved.
    pub fn has_unresolved_delayed_ops(&self) -> bool {
        self.delayed_ops.iter().any(|op| !op.circuit_built)
    }

    /// Build the full circuit for a delayed operation (Phase 2 fallback).
    ///
    /// Called from the delayed check loop when cheap axioms are insufficient.
    /// Builds the actual multiplier/divider circuit and adds equivalence clauses
    /// between the circuit output bits and the previously allocated result bits.
    ///
    /// Returns clauses in BV literal space.
    pub fn build_delayed_circuit(&mut self, op_idx: usize) -> Vec<CnfClause> {
        let op = self.delayed_ops[op_idx].clone();

        let circuit_bits = match op.op {
            "bvmul" => {
                let Some((a, b)) = self.get_binary_bits(op.args[0], op.args[1]) else {
                    return Vec::new();
                };
                self.bitblast_mul(&a, &b)
            }
            "bvadd" => {
                let Some((a, b)) = self.get_binary_bits(op.args[0], op.args[1]) else {
                    return Vec::new();
                };
                self.bitblast_add(&a, &b)
            }
            "bvudiv" => {
                let (q, _) = self.bitblast_udiv_urem_cached(op.args[0], op.args[1]);
                q
            }
            "bvurem" => {
                let (_, r) = self.bitblast_udiv_urem_cached(op.args[0], op.args[1]);
                r
            }
            "bvsdiv" => {
                let (abs_q, _, sign_a, sign_b) =
                    self.bitblast_signed_div_rem_cached(op.args[0], op.args[1]);
                if abs_q.is_empty() {
                    return Vec::new();
                }
                let result_neg = self.mk_xor(sign_a, sign_b);
                self.conditional_neg(&abs_q, result_neg)
            }
            "bvsrem" => {
                let (_, abs_r, sign_a, _) =
                    self.bitblast_signed_div_rem_cached(op.args[0], op.args[1]);
                if abs_r.is_empty() {
                    return Vec::new();
                }
                self.conditional_neg(&abs_r, sign_a)
            }
            "bvsmod" => {
                let Some((a, b)) = self.get_binary_bits(op.args[0], op.args[1]) else {
                    return Vec::new();
                };
                self.bitblast_smod(&a, &b)
            }
            _ => return Vec::new(),
        };

        let mut equiv_clauses = Vec::new();
        for (&result_bit, &circuit_bit) in op.result_bits.iter().zip(circuit_bits.iter()) {
            equiv_clauses.push(CnfClause::new(vec![-result_bit, circuit_bit]));
            equiv_clauses.push(CnfClause::new(vec![result_bit, -circuit_bit]));
        }

        self.delayed_ops[op_idx].circuit_built = true;

        let mut all_clauses = self.take_clauses();
        all_clauses.extend(equiv_clauses);
        all_clauses
    }
}
