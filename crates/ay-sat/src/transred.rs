// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Transitive Reduction for Binary Implication Graph
//!
//! A binary clause `(a -> b)` is *transitive* if there exists an alternate path
//! from `a` to `b` through other binary clauses. Transitive clauses can be
//! safely removed without affecting satisfiability.
//!
//! This technique is particularly important for BV-encoded problems where
//! Tseitin encoding generates many binary clauses with redundant edges.
//! CaDiCaL statistics show transitive reduction removes 30-50% of binary
//! clauses in structured BV problems.
//!
//! The algorithm does BFS from the source of each binary clause to check if
//! the destination is reachable via an alternate path.
//!
//! Reference: CaDiCaL's `transred.cpp`

mod check;
#[cfg(test)]
mod tests;
#[cfg(kani)]
mod verification;

use crate::clause_arena::ClauseArena;
use crate::literal::Literal;
use crate::watched::{ClauseRef, WatchedLists};

use check::CheckResult;

#[cfg(not(kani))]
fn debug_transred_trace_enabled() -> bool {
    ay_core::debug_channel_active(ay_core::DebugChannel::TransredTrace)
}

#[cfg(not(kani))]
fn debug_transred_clause() -> Option<u32> {
    // TransredClause is a numeric parameter, not a boolean flag. The clause
    // ID comes from `--debug-transred-clause=N` (preferred) or the
    // `AY_DEBUG_TRANSRED_CLAUSE` env var (deprecated), both of which are
    // read once and cached in `SatDebugEnvFlags` (#8506, #8834).
    ay_core::sat_debug_env_flags().debug_transred_clause
}

/// Statistics for transitive reduction
#[derive(Debug, Clone, Default)]
#[non_exhaustive]
pub struct TransRedStats {
    /// Number of transitive clauses removed
    pub clauses_removed: u64,
    /// Number of failed literals found
    pub failed_literals: u64,
    /// Number of BFS propagations performed
    pub propagations: u64,
    /// Number of rounds
    pub rounds: u64,
}

/// Mark values for BFS traversal
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Mark {
    /// Unmarked
    None,
    /// Reachable with positive polarity
    Positive,
    /// Reachable with negative polarity
    Negative,
}

/// Transitive Reduction engine
pub(crate) struct TransRed {
    /// Mark array for BFS (per variable: tracks reachability)
    marks: Vec<Mark>,
    /// BFS work queue
    work: Vec<Literal>,
    /// Statistics
    stats: TransRedStats,
    /// Generation counter per clause: checked[i] == generation means "checked this round"
    checked: Vec<u32>,
    /// Generation counter per clause: pending_delete[i] == generation means "delete this round"
    pending_delete: Vec<u32>,
    /// Current round generation (incremented per run, avoids re-allocation)
    generation: u32,
    /// Total propagations at last transred call (for tick-proportional effort).
    /// CaDiCaL tracks `last.transred.propagations` (transred.cpp:30).
    last_propagations: u64,
}

/// Immutable data needed to validate transitivity witnesses.
struct WitnessContext<'a> {
    clauses: &'a ClauseArena,
    vals: &'a [i8],
    original_clause_limit: usize,
}

/// Result of transitive reduction pass
#[derive(Debug, Default)]
pub(crate) struct TransRedResult {
    /// Clauses that are transitive and can be deleted
    pub transitive_clauses: Vec<ClauseRef>,
    /// Failed literals found (units to propagate)
    pub failed_literals: Vec<Literal>,
}

impl TransRed {
    /// Create a new transitive reduction engine for `num_vars` variables.
    pub(crate) fn new(num_vars: usize) -> Self {
        Self {
            marks: vec![Mark::None; num_vars],
            work: Vec::new(),
            stats: TransRedStats::default(),
            checked: Vec::new(),
            pending_delete: Vec::new(),
            generation: 0,
            last_propagations: 0,
        }
    }

    /// Get total propagations at last transred call.
    #[allow(dead_code)]
    pub(crate) fn last_propagations(&self) -> u64 {
        self.last_propagations
    }

    /// Record current propagation count for next effort computation.
    pub(crate) fn set_last_propagations(&mut self, props: u64) {
        self.last_propagations = props;
    }

    /// Ensure internal buffers can handle `num_vars` variables.
    pub(crate) fn ensure_num_vars(&mut self, num_vars: usize) {
        if self.marks.len() < num_vars {
            self.marks.resize(num_vars, Mark::None);
        }
    }

    /// Get statistics
    pub(crate) fn stats(&self) -> &TransRedStats {
        &self.stats
    }

    /// Restore previously saved statistics (e.g., after compaction recreates
    /// the engine via `TransRed::new()`). Without this, stats are zeroed.
    pub(crate) fn restore_stats(&mut self, stats: TransRedStats) {
        self.stats = stats;
    }

    /// Mark a literal as reachable
    fn mark(&mut self, lit: Literal) {
        let var_idx = lit.variable().index();
        if var_idx < self.marks.len() {
            self.marks[var_idx] = if lit.is_positive() {
                Mark::Positive
            } else {
                Mark::Negative
            };
        }
    }

    /// Get mark for a literal (returns what polarity is marked, if any)
    fn marked(&self, lit: Literal) -> Mark {
        let var_idx = lit.variable().index();
        if var_idx < self.marks.len() {
            self.marks[var_idx]
        } else {
            Mark::None
        }
    }

    /// Check if literal is marked with the same polarity
    fn is_marked_same(&self, lit: Literal) -> bool {
        let mark = self.marked(lit);
        match mark {
            Mark::None => false,
            Mark::Positive => lit.is_positive(),
            Mark::Negative => !lit.is_positive(),
        }
    }

    /// Check if literal is marked with opposite polarity (failed literal detection)
    fn is_marked_opposite(&self, lit: Literal) -> bool {
        let mark = self.marked(lit);
        match mark {
            Mark::None => false,
            Mark::Positive => !lit.is_positive(),
            Mark::Negative => lit.is_positive(),
        }
    }

    /// Unmark a literal
    fn unmark(&mut self, lit: Literal) {
        let var_idx = lit.variable().index();
        if var_idx < self.marks.len() {
            self.marks[var_idx] = Mark::None;
        }
    }

    /// Check if a variable is assigned using the vals[] array.
    fn is_assigned(lit: Literal, vals: &[i8]) -> bool {
        let var_idx = lit.variable().index();
        var_idx * 2 < vals.len() && vals[var_idx * 2] != 0
    }

    /// Run transitive reduction
    ///
    /// Returns a list of (clause_ref, failed_literal) tuples:
    /// - clause_ref: clauses to delete (transitive)
    /// - failed_literal: unit to propagate (failed literal found)
    ///
    /// Should be called at decision level 0.
    pub(crate) fn run(
        &mut self,
        clauses: &ClauseArena,
        watches: &WatchedLists,
        vals: &[i8],
        original_clause_limit: usize,
        effort_limit: u64,
    ) -> TransRedResult {
        // CaDiCaL transred.cpp:22: must run at decision level 0
        // (level not accessible here — caller asserts in inprocessing.rs)
        // Precondition: work queue must be empty at entry
        // CaDiCaL transred.cpp:130
        debug_assert!(
            self.work.is_empty(),
            "BUG: transred work queue not empty at entry (len={})",
            self.work.len(),
        );
        #[cfg(kani)]
        let trace = false;
        #[cfg(not(kani))]
        let trace = debug_transred_trace_enabled();
        self.stats.rounds += 1;
        // Advance generation counter instead of re-allocating Vec<bool>.
        // CaDiCaL uses a stamps array with the same technique.
        self.generation = self.generation.wrapping_add(1);
        if self.generation == 0 {
            // Wrapped around — zero everything and start at 1
            self.checked.fill(0);
            self.pending_delete.fill(0);
            self.generation = 1;
        }
        // Grow arrays if clause DB expanded since last round (zero-fill = "never seen")
        let num_clauses = clauses.len();
        if self.checked.len() < num_clauses {
            self.checked.resize(num_clauses, 0);
        }
        if self.pending_delete.len() < num_clauses {
            self.pending_delete.resize(num_clauses, 0);
        }

        let mut result = TransRedResult::default();
        let mut propagations: u64 = 0;

        // Iterate through all binary clauses
        for clause_idx in clauses.indices() {
            if propagations >= effort_limit {
                break;
            }

            if clauses.is_empty_clause(clause_idx) || clauses.len_of(clause_idx) != 2 {
                continue;
            }

            // Safety gate for #3312:
            // only delete clauses from the original input formula.
            // Derived clauses (even irredundant ones) may be removed in later rounds,
            // which can invalidate a transitivity witness chain after deletion.
            if clause_idx >= original_clause_limit || clauses.is_learned(clause_idx) {
                continue;
            }

            // Skip if already checked or pending deletion this round
            if self.checked[clause_idx] == self.generation {
                continue;
            }
            if self.pending_delete[clause_idx] == self.generation {
                continue;
            }
            self.checked[clause_idx] = self.generation;

            let lit0 = clauses.literal(clause_idx, 0);
            let lit1 = clauses.literal(clause_idx, 1);

            // Skip if either literal is already assigned
            if Self::is_assigned(lit0, vals) || Self::is_assigned(lit1, vals) {
                continue;
            }

            // Binary clause (lit0 \/ lit1) represents two directed implications:
            //   ~lit0 -> lit1
            //   ~lit1 -> lit0
            //
            // IMPORTANT: Deleting the *clause* removes *both* implications, so it is only
            // safe to delete if BOTH directions are transitively implied by other clauses.
            // (Checking only one direction is unsound.)
            let clause_ref = ClauseRef(clause_idx as u32);

            // Check ~lit0 -> lit1
            let witness_ctx = WitnessContext {
                clauses,
                vals,
                original_clause_limit,
            };
            let check_0_to_1 =
                self.check_transitive(lit0.negated(), lit1, clause_ref, watches, &witness_ctx);
            propagations += check_0_to_1.propagations;
            self.stats.propagations += check_0_to_1.propagations;
            if propagations >= effort_limit {
                break;
            }

            // Check ~lit1 -> lit0
            let check_1_to_0 =
                self.check_transitive(lit1.negated(), lit0, clause_ref, watches, &witness_ctx);
            propagations += check_1_to_0.propagations;
            self.stats.propagations += check_1_to_0.propagations;

            // Failed literals (units) are sound regardless of transitivity checks.
            if let CheckResult::FailedLiteral(unit) = check_0_to_1.kind {
                result.failed_literals.push(unit);
                self.stats.failed_literals += 1;
            }
            if let CheckResult::FailedLiteral(unit) = check_1_to_0.kind {
                result.failed_literals.push(unit);
                self.stats.failed_literals += 1;
            }

            // Only delete clause if BOTH implications are transitive.
            if matches!(check_0_to_1.kind, CheckResult::Transitive)
                && matches!(check_1_to_0.kind, CheckResult::Transitive)
            {
                self.pending_delete[clause_idx] = self.generation;
                if trace {
                    safe_eprintln!(
                        "[transred] DELETE clause {} ({} \\/ {}): both directions transitive",
                        clause_idx,
                        lit0.to_dimacs(),
                        lit1.to_dimacs()
                    );
                }
                result.transitive_clauses.push(clause_ref);
                self.stats.clauses_removed += 1;
            }
        }

        if trace && !result.transitive_clauses.is_empty() {
            safe_eprintln!(
                "[transred] Round {}: deleted {} clauses, {} failed literals",
                self.stats.rounds,
                result.transitive_clauses.len(),
                result.failed_literals.len()
            );
        }

        result
    }
}
