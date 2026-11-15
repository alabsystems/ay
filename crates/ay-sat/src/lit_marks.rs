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

mod counted;

use crate::kani_compat::DetHashMap;
use crate::literal::{Literal, Variable};

/// Variables with an index below this bound keep their mark in the dense
/// array; the array therefore never grows to 2^28 entries. Marks for the
/// (rare) variables at or above it live in a sparse side table, so every
/// variable index a `Literal` can carry is still marked exactly.
const MAX_DENSE_MARK_VARS: usize = (1 << 28) - 1;

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
    /// Dense marks for variables below `MAX_DENSE_MARK_VARS`.
    marks: Vec<i8>,
    /// Non-zero marks for variables at or above `MAX_DENSE_MARK_VARS`.
    overflow: DetHashMap<usize, i8>,
}

impl LitMarks {
    pub(crate) fn new(num_vars: usize) -> Self {
        Self {
            marks: vec![0; num_vars.min(MAX_DENSE_MARK_VARS)],
            overflow: DetHashMap::default(),
        }
    }

    pub(crate) fn ensure_num_vars(&mut self, num_vars: usize) {
        let dense = num_vars.min(MAX_DENSE_MARK_VARS);
        if self.marks.len() < dense && dense <= MAX_DENSE_MARK_VARS {
            self.marks.resize(dense, 0);
        }
    }

    /// Current mark of the variable at `idx` (`0` if never marked).
    #[inline]
    fn mark_at(&self, idx: usize) -> i8 {
        if idx < MAX_DENSE_MARK_VARS {
            self.marks.get(idx).copied().unwrap_or(0)
        } else {
            self.overflow.get(&idx).copied().unwrap_or(0)
        }
    }

    /// Set the mark of the variable at `idx`, growing the dense array on
    /// demand, and return the previous mark.
    #[inline]
    fn set_mark_at(&mut self, idx: usize, value: i8) -> i8 {
        if idx < MAX_DENSE_MARK_VARS {
            if idx >= self.marks.len() {
                // `idx < MAX_DENSE_MARK_VARS`, so the new length stays below
                // 2^28 and cannot overflow.
                let Some(len) = idx.checked_add(1) else {
                    return 0;
                };
                if len <= MAX_DENSE_MARK_VARS {
                    self.marks.resize(len, 0);
                }
            }
            match self.marks.get_mut(idx) {
                Some(slot) => std::mem::replace(slot, value),
                None => 0,
            }
        } else if value == 0 {
            self.overflow.remove(&idx).unwrap_or(0)
        } else {
            self.overflow.insert(idx, value).unwrap_or(0)
        }
    }

    /// Mark a literal's variable with its polarity and return the previous mark.
    #[inline]
    pub(crate) fn mark(&mut self, lit: Literal) -> i8 {
        self.set_mark_at(lit.variable().index(), lit.sign_i8())
    }

    /// Get the mark for a variable (`0` if out of bounds).
    #[inline]
    pub(crate) fn get(&self, var: Variable) -> i8 {
        self.mark_at(var.index())
    }

    /// Clear a literal variable mark.
    #[inline]
    pub(crate) fn clear(&mut self, lit: Literal) {
        let idx = lit.variable().index();
        if idx < MAX_DENSE_MARK_VARS {
            if let Some(slot) = self.marks.get_mut(idx) {
                *slot = 0;
            }
        } else {
            self.overflow.remove(&idx);
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
        // Marks are 0, ±1 or ±2, so doubling is exact; saturation only
        // bounds the arithmetic for values no caller produces.
        let idx = var.index();
        if idx < MAX_DENSE_MARK_VARS {
            if let Some(slot) = self.marks.get_mut(idx) {
                *slot = slot.saturating_mul(2);
            }
        } else if let Some(slot) = self.overflow.get_mut(&idx) {
            *slot = slot.saturating_mul(2);
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
            let sign = mapped.sign_i8();
            let complement: i8 = if mapped.is_positive() { -1 } else { 1 };
            let mark = self.mark_at(var_idx);
            if mark == complement {
                // Complementary literal — tautology.
                self.clear_clause(out);
                out.clear();
                return ClauseRewriteOutcome::Tautology;
            }
            if mark == 0 {
                self.set_mark_at(var_idx, sign);
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
