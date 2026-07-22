// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! BFS-based transitivity checking for binary implication edges.
//!
//! Given a binary clause `(a ∨ b)` representing implications `¬a → b` and
//! `¬b → a`, the check determines if the destination is reachable from the
//! source through alternate binary implications.

use crate::literal::Literal;
use crate::watched::{ClauseRef, WatchedLists};

#[cfg(not(kani))]
use super::debug_transred_clause;
use super::{Mark, TransRed, WitnessContext};

/// Result of a single transitive check
pub(super) struct TransitiveCheckResult {
    pub kind: CheckResult,
    pub propagations: u64,
}

/// Check result type
pub(super) enum CheckResult {
    /// Clause is transitive (can be removed)
    Transitive,
    /// Found a failed literal (unit to propagate)
    FailedLiteral(Literal),
    /// Clause is not transitive
    NotTransitive,
}

impl TransRed {
    /// Whether a binary clause can be used as a transitivity witness.
    #[inline]
    pub(super) fn is_valid_witness_clause(
        clause_idx: usize,
        witness_ctx: &WitnessContext<'_>,
        pending_delete: &[u32],
        generation: u32,
    ) -> bool {
        if clause_idx >= witness_ctx.clauses.len() {
            return false;
        }
        if clause_idx >= witness_ctx.original_clause_limit {
            return false;
        }

        let clauses = witness_ctx.clauses;
        let offset = clause_idx;
        if clauses.is_empty_clause(offset)
            || clauses.is_learned(offset)
            || clauses.len_of(offset) != 2
        {
            return false;
        }

        pending_delete[clause_idx] != generation
    }

    /// Check if clause src -> dst is transitive
    ///
    /// Does BFS from src through binary implications, checking if dst is reachable.
    /// Only uses ORIGINAL (non-learned) clauses as witnesses to avoid relying on
    /// learned clauses that may be deleted later (#1818 fix). Also excludes
    /// clauses already marked for deletion in the current transred round.
    pub(super) fn check_transitive(
        &mut self,
        src: Literal,
        dst: Literal,
        skip_clause: ClauseRef,
        watches: &WatchedLists,
        witness_ctx: &WitnessContext<'_>,
    ) -> TransitiveCheckResult {
        // CaDiCaL transred.cpp:130: work queue must be empty at BFS start
        debug_assert!(
            self.work.is_empty(),
            "BUG: check_transitive work queue not empty at entry",
        );
        // src and dst must be different literals
        debug_assert_ne!(src, dst, "BUG: check_transitive src == dst ({src:?})");
        // src and dst must be different variables
        debug_assert_ne!(
            src.variable(),
            dst.variable(),
            "BUG: check_transitive src and dst have same variable",
        );
        #[cfg(kani)]
        let trace = false;
        #[cfg(not(kani))]
        let trace = debug_transred_clause() == Some(skip_clause.0);

        self.work.clear();

        // Mark and queue the source
        self.mark(src);
        self.work.push(src);

        if trace {
            safe_eprintln!(
                "[transred] Checking {} -> {}",
                src.to_dimacs(),
                dst.to_dimacs()
            );
        }

        let mut propagations: u64 = 0;
        let mut j = 0; // BFS frontier index

        let mut transitive = false;
        let mut failed_lit: Option<Literal> = None;

        while j < self.work.len() && !transitive && failed_lit.is_none() {
            let lit = self.work[j];
            j += 1;
            propagations += 1;

            // CaDiCaL transred.cpp:146: every BFS-popped literal must be marked
            debug_assert!(
                self.is_marked_same(lit),
                "BUG: BFS popped unmarked literal {lit:?}",
            );

            // Traverse binary implications: ~lit is false, so binary clauses
            // containing ~lit propagate their other literal
            let neg_lit = lit.negated();
            let neg_wl = watches.get_watches(neg_lit);
            for wi in 0..neg_wl.len() {
                if !neg_wl.is_binary(wi) {
                    continue;
                }

                // Skip the clause we're checking
                let w_clause_ref = neg_wl.clause_ref(wi);
                if w_clause_ref == skip_clause {
                    continue;
                }

                // Skip non-original/learned clauses as witnesses:
                // witness paths must be stable over the solve, so we only follow
                // binary clauses from the original input formula.
                let clause_idx = w_clause_ref.0 as usize;
                if !Self::is_valid_witness_clause(
                    clause_idx,
                    witness_ctx,
                    &self.pending_delete,
                    self.generation,
                ) {
                    continue;
                }

                let other = neg_wl.blocker(wi);

                // Skip assigned literals
                if Self::is_assigned(other, witness_ctx.vals) {
                    continue;
                }

                // Found destination -> transitive
                if other == dst {
                    if trace {
                        safe_eprintln!(
                            "[transred]   Found dst via clause {} (from {})",
                            w_clause_ref.0,
                            lit.to_dimacs()
                        );
                    }
                    transitive = true;
                    break;
                }

                // Check if already marked
                if self.is_marked_same(other) {
                    // Already reached with same polarity, skip
                    continue;
                }

                if self.is_marked_opposite(other) {
                    // Found both polarities -> failed literal
                    // src implies both `x` and `~x`, so `~src` is a unit
                    failed_lit = Some(src.negated());
                    break;
                }

                // Mark and enqueue
                if trace {
                    safe_eprintln!(
                        "[transred]   {} -> {} via clause {}",
                        lit.to_dimacs(),
                        other.to_dimacs(),
                        w_clause_ref.0
                    );
                }
                self.mark(other);
                self.work.push(other);
            }
        }

        // Clean up marks - use index-based iteration to avoid borrow conflict
        for i in 0..self.work.len() {
            let lit = self.work[i];
            self.unmark(lit);
        }
        // Postcondition: all marks must be cleared after BFS cleanup
        debug_assert!(
            self.work.iter().all(|l| self.marked(*l) == Mark::None),
            "BUG: check_transitive: marks not fully cleared after BFS",
        );
        self.work.clear();

        let kind = if transitive {
            CheckResult::Transitive
        } else if let Some(unit) = failed_lit {
            CheckResult::FailedLiteral(unit)
        } else {
            CheckResult::NotTransitive
        };

        TransitiveCheckResult { kind, propagations }
    }
}
