// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Shared signed mark array for inprocessing tautology checking.
//!
//! Used by BVE, BCE, HTR, and gate extraction engines to detect tautological
//! resolvents and duplicate literals during clause rewriting. One instance
//! lives on the solver and is threaded through all inprocessing passes,
//! eliminating per-engine allocation of `marks: Vec<i8>`.
//!
//! Reference: CaDiCaL `internal.hpp:481-495` (shared mark/unmark API).

use crate::literal::{Literal, Variable};

/// Shared signed mark array for tautology checking.
///
/// Indexed by variable and stores:
/// - `0` for unmarked
/// - `1` for positive literal
/// - `-1` for negative literal
///
/// Shared by inprocessing engines that perform clause rewriting or resolution
/// and need tautology / duplicate detection.
#[derive(Clone)]
pub(crate) struct LitMarks {
    marks: Vec<i8>,
}

impl LitMarks {
    pub(crate) fn new(num_vars: usize) -> Self {
        Self {
            marks: vec![0; num_vars],
        }
    }

    pub(crate) fn ensure_num_vars(&mut self, num_vars: usize) {
        if self.marks.len() < num_vars {
            self.marks.resize(num_vars, 0);
        }
    }

    /// Mark a literal's variable with its polarity and return the previous mark.
    #[inline]
    pub(crate) fn mark(&mut self, lit: Literal) -> i8 {
        let idx = lit.variable().index();
        if idx >= self.marks.len() {
            self.marks.resize(idx + 1, 0);
        }
        let prev = self.marks[idx];
        self.marks[idx] = lit.sign_i8();
        prev
    }

    /// Get the mark for a variable (`0` if out of bounds).
    #[inline]
    pub(crate) fn get(&self, var: Variable) -> i8 {
        self.marks.get(var.index()).copied().unwrap_or(0)
    }

    /// Clear a literal variable mark.
    #[inline]
    pub(crate) fn clear(&mut self, lit: Literal) {
        let idx = lit.variable().index();
        if idx < self.marks.len() {
            self.marks[idx] = 0;
        }
    }

    /// Clear marks for all literals in a clause.
    pub(crate) fn clear_clause(&mut self, clause: &[Literal]) {
        for &lit in clause {
            self.clear(lit);
        }
    }

    /// Promote a variable's mark by doubling it (1 → 2, -1 → -2).
    ///
    /// Used by AND gate detection (CaDiCaL `gates.cpp:405-414`) to distinguish
    /// side-clause marks that match the long base clause from stray binary marks.
    /// After promotion, `get()` returns 2 or -2 for promoted marks and 1 or -1
    /// for unpromoted ones.
    #[inline]
    pub(crate) fn promote(&mut self, var: Variable) {
        let idx = var.index();
        if idx < self.marks.len() {
            self.marks[idx] *= 2;
        }
    }

    /// Rewrite a clause by mapping literals through a representative table,
    /// deduplicating, and detecting tautologies.
    ///
    /// This is the shared clause rewrite logic used by sweep, decompose, and
    /// congruence. Each module builds its own `lit_map` (via SCC, Tarjan, or
    /// Union-Find), then delegates the per-clause rewrite to this method.
    ///
    /// If `vals` is non-empty, level-0 assignments are applied: true literals
    /// satisfy the clause, false literals are removed. `vals` is indexed by
    /// literal index: `1` = true, `-1` = false, `0` = unassigned.
    ///
    /// Uses the mark array for O(1) dedup and tautology detection per literal.
    /// Marks are cleaned up before returning.
    ///
    /// Reference: CaDiCaL `decompose.cpp:436-580`, `sweep.cpp:260-314`.
    pub(crate) fn rewrite_clause(
        &mut self,
        clause: &[Literal],
        lit_map: &[Literal],
        vals: &[i8],
        out: &mut Vec<Literal>,
    ) -> ClauseRewriteOutcome {
        out.clear();

        for &lit in clause {
            let idx = lit.index();
            let mapped = if idx < lit_map.len() {
                lit_map[idx]
            } else {
                lit
            };

            // Level-0 assignment elimination.
            if !vals.is_empty() {
                let mi = mapped.index();
                if mi < vals.len() {
                    let v = vals[mi];
                    if v > 0 {
                        // True at level 0 — clause is satisfied.
                        self.clear_clause(out);
                        out.clear();
                        return ClauseRewriteOutcome::Satisfied;
                    }
                    if v < 0 {
                        // False at level 0 — remove from clause.
                        continue;
                    }
                }
            }

            let var_idx = mapped.variable().index();
            if var_idx >= self.marks.len() {
                self.marks.resize(var_idx + 1, 0);
            }

            let sign = mapped.sign_i8();
            let mark = self.marks[var_idx];
            if mark == -sign {
                // Complementary literal — tautology.
                self.clear_clause(out);
                out.clear();
                return ClauseRewriteOutcome::Tautology;
            }
            if mark == 0 {
                self.marks[var_idx] = sign;
                out.push(mapped);
            }
            // mark == sign → duplicate, skip
        }

        self.clear_clause(out);

        match out.len() {
            0 => ClauseRewriteOutcome::Empty,
            1 => ClauseRewriteOutcome::Unit(out[0]),
            _ => {
                if out.len() == clause.len() && out.iter().zip(clause).all(|(a, b)| a == b) {
                    ClauseRewriteOutcome::Unchanged
                } else {
                    ClauseRewriteOutcome::Changed
                }
            }
        }
    }
}

/// Outcome of rewriting a single clause through a literal equivalence map.
///
/// Shared by sweep, decompose, and congruence modules.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ClauseRewriteOutcome {
    /// No literals changed — clause is identical to input.
    Unchanged,
    /// At least one literal changed, or the clause was shortened by dedup.
    /// The rewritten literals are in the `out` buffer passed to `rewrite_clause`.
    Changed,
    /// Clause reduced to a single literal (stored here for convenience).
    Unit(Literal),
    /// All literals were duplicates or mapped to the same representative — empty clause.
    Empty,
    /// Clause contains both `l` and `¬l` after mapping — tautological.
    Tautology,
    /// A mapped literal is true at level 0 — clause is satisfied.
    Satisfied,
}

#[cfg(test)]
#[path = "lit_marks_tests.rs"]
mod tests;
