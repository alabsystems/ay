// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! HTR resolution core: try_resolve, resolve_on_pivot, get_ternary_lits.
//!
//! Contains the actual resolution logic that produces binary or ternary
//! resolvents from pairs of ternary clauses.

use crate::clause_arena::ClauseArena;
use crate::lit_marks::LitMarks;
use crate::literal::{Literal, Variable};

use super::HTR;

impl HTR {
    /// Try to resolve two ternary clauses on a pivot literal
    ///
    /// Returns Some(resolvent) if successful, None if:
    /// - Resolvent is tautological
    /// - Resolvent has more than 3 literals
    /// - Resolvent already exists
    pub(super) fn try_resolve_with_marks(
        &mut self,
        clause_c: &[Literal],
        clause_d: &[Literal],
        pivot: Literal,
        marks: &mut LitMarks,
    ) -> Option<Vec<Literal>> {
        debug_assert_eq!(clause_c.len(), 3);
        debug_assert_eq!(clause_d.len(), 3);

        self.stats.pairs_checked += 1;

        // Defense-in-depth: clear any stale marks from other inprocessing
        // passes sharing the same LitMarks (matches bve.rs pattern).
        marks.clear_clause(clause_c);
        marks.clear_clause(clause_d);

        let mut resolvent = Vec::with_capacity(4);

        // Add literals from first clause (except pivot)
        for &lit in clause_c {
            if lit == pivot {
                continue;
            }
            marks.mark(lit);
            resolvent.push(lit);
        }

        // Add literals from second clause (except negated pivot)
        let neg_pivot = pivot.negated();
        for &lit in clause_d {
            if lit == neg_pivot {
                continue;
            }

            let sign: i8 = lit.sign_i8();

            if marks.get(lit.variable()) == -sign {
                // Tautology: both L and ~L present
                self.stats.tautologies_skipped += 1;
                marks.clear_clause(&resolvent);
                return None;
            }
            if marks.get(lit.variable()) == 0 {
                // New literal
                marks.mark(lit);
                resolvent.push(lit);
            }
            // If marks[var_idx] == sign, literal is duplicate, skip
        }

        // Check resolvent size
        if resolvent.len() > 3 {
            self.stats.too_large_skipped += 1;
            marks.clear_clause(&resolvent);
            return None;
        }

        // Clean up all marks set during this call. With shared LitMarks,
        // stale marks must not leak between resolution calls.
        marks.clear_clause(&resolvent);

        // Postcondition: all marks from this call are cleared.
        debug_assert!(
            resolvent.iter().all(|l| marks.get(l.variable()) == 0),
            "BUG: marks not cleared after HTR resolution",
        );

        // Check for duplicates
        match resolvent.len() {
            2 if self.binary_exists(resolvent[0], resolvent[1]) => {
                self.stats.duplicates_skipped += 1;
                return None;
            }
            3 if self.ternary_exists(resolvent[0], resolvent[1], resolvent[2]) => {
                self.stats.duplicates_skipped += 1;
                return None;
            }
            _ => {
                // Unit clause (len == 1) or empty - should not happen with ternary inputs
                // but we'll accept it if it does
            }
        }

        Some(resolvent)
    }

    /// Test helper wrapper using a temporary mark array.
    #[cfg(any(test, kani))]
    pub(super) fn try_resolve(
        &mut self,
        clause_c: &[Literal],
        clause_d: &[Literal],
        pivot: Literal,
    ) -> Option<Vec<Literal>> {
        let mut marks = LitMarks::new(self.num_vars);
        self.try_resolve_with_marks(clause_c, clause_d, pivot, &mut marks)
    }

    /// Return ternary literals from either a real clause or a virtual derived clause.
    #[inline]
    pub(super) fn get_ternary_lits(
        idx: usize,
        clauses: &ClauseArena,
        derived_ternary: &[[Literal; 3]],
        derived_base: usize,
        out: &mut [Literal; 3],
    ) -> bool {
        if idx < derived_base {
            if idx >= clauses.len() {
                return false;
            }
            if clauses.is_empty_clause(idx) || clauses.len_of(idx) != 3 {
                return false;
            }
            let lits = clauses.literals(idx);
            out[0] = lits[0];
            out[1] = lits[1];
            out[2] = lits[2];
            true
        } else {
            let di = idx - derived_base;
            if di >= derived_ternary.len() {
                return false;
            }
            *out = derived_ternary[di];
            true
        }
    }

    /// Run hyper-ternary resolution on a single pivot variable
    ///
    /// Returns resolvents with their antecedent clause indices
    /// `(resolvent, pos_idx, neg_idx)`. The caller decides which antecedents
    /// to delete: a binary resolvent subsumes both of its antecedents, but
    /// deletion is sound only if the resolvent is actually retained (added to
    /// the clause DB). Deletion must therefore be registered at retention
    /// time, not here (constraint-loss fix — see run_with_marks).
    #[allow(clippy::type_complexity)]
    pub(super) fn resolve_on_pivot_with_marks(
        &mut self,
        var: Variable,
        clauses: &ClauseArena,
        vals: &[i8],
        marks: &mut LitMarks,
    ) -> Vec<(Vec<Literal>, usize, usize)> {
        let pos_lit = Literal::positive(var);
        let neg_lit = Literal::negative(var);

        // Copy occurrence lists into reusable buffers to avoid per-call allocations
        self.pos_occ_buf.clear();
        self.pos_occ_buf.extend_from_slice(self.occ.get(pos_lit));
        self.neg_occ_buf.clear();
        self.neg_occ_buf.extend_from_slice(self.occ.get(neg_lit));

        let mut resolvents = Vec::new();

        // Try all pairs
        // Use index-based iteration to avoid borrow conflicts with mutable method calls
        let pos_len = self.pos_occ_buf.len();
        let neg_len = self.neg_occ_buf.len();

        for pi in 0..pos_len {
            let pos_idx = self.pos_occ_buf[pi];
            let mut pos_lits = [Literal::positive(Variable(0)); 3];
            if !Self::get_ternary_lits(
                pos_idx,
                clauses,
                &self.derived_ternary,
                self.derived_base,
                &mut pos_lits,
            ) {
                continue;
            }

            // Skip if any literal in clause is assigned
            let mut assigned = false;
            for &lit in &pos_lits {
                let vi = lit.variable().index();
                if vi * 2 < vals.len() && vals[vi * 2] != 0 {
                    assigned = true;
                    break;
                }
            }
            if assigned {
                continue;
            }

            for ni in 0..neg_len {
                let neg_idx = self.neg_occ_buf[ni];
                let mut neg_lits = [Literal::positive(Variable(0)); 3];
                if !Self::get_ternary_lits(
                    neg_idx,
                    clauses,
                    &self.derived_ternary,
                    self.derived_base,
                    &mut neg_lits,
                ) {
                    continue;
                }

                // Skip if any literal in clause is assigned
                let mut assigned = false;
                for &lit in &neg_lits {
                    let vi = lit.variable().index();
                    if vi * 2 < vals.len() && vals[vi * 2] != 0 {
                        assigned = true;
                        break;
                    }
                }
                if assigned {
                    continue;
                }

                // Try to resolve
                if let Some(resolvent) =
                    self.try_resolve_with_marks(&pos_lits, &neg_lits, pos_lit, marks)
                {
                    let is_binary = resolvent.len() == 2;

                    // Add to existing set to avoid duplicate detection
                    match resolvent.len() {
                        2 => {
                            let key = Self::normalize_binary(resolvent[0], resolvent[1]);
                            self.existing_binary.insert(key);
                            self.stats.binary_resolvents += 1;
                            // Binary resolvents subsume both antecedents, but
                            // the caller registers the deletion only if the
                            // resolvent survives the max_resolvents cap.
                        }
                        3 => {
                            let key =
                                Self::normalize_ternary(resolvent[0], resolvent[1], resolvent[2]);
                            self.existing_ternary.insert(key);
                            self.stats.ternary_resolvents += 1;
                        }
                        _ => {}
                    }

                    resolvents.push((resolvent, pos_idx, neg_idx));

                    // If we derived a binary clause, stop processing this positive clause
                    // (it will be deleted anyway)
                    if is_binary {
                        break;
                    }
                }
            }
        }

        resolvents
    }
}
