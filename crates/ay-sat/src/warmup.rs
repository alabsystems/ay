// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Warmup-based phase initialization
//!
//! Implements CaDiCaL-style warmup for finding good initial phases.
//! Unlike walk (which uses ProbSAT random walk), warmup leverages CDCL's
//! propagation strength to set phases efficiently.
//!
//! ## How It Works
//!
//! 1. Make decisions using standard heuristics (VMTF in focused mode)
//! 2. Propagate using 2-watched literals (ignoring conflicts)
//! 3. Save resulting assignment as target phases for local search
//!
//! ## Why Warmup is Better Than Walk for Phase Initialization
//!
//! - Walk: O(degree) per flip due to break-value computation requiring clause scans
//! - Warmup: O(clause_length) amortized per propagation using 2-watched literals
//!
//! CaDiCaL uses warmup to prepare phases before walk. For small/medium instances,
//! warmup alone often provides sufficient phase quality without the walk overhead.

use crate::clause_arena::ClauseArena;
use crate::Literal;

/// Statistics from warmup phase
#[derive(Debug, Default, Clone)]
pub(crate) struct WarmupStats {
    /// Number of warmup rounds executed
    pub warmup_count: u64,
    /// Number of decisions made during warmup
    pub decisions: u64,
    /// Number of propagations made during warmup
    pub propagations: u64,
    /// Number of conflicts encountered (and ignored)
    pub conflicts: u64,
}

/// Warmup state for propagation
pub(crate) struct Warmup {
    /// Current assignment (None = unassigned)
    assignment: Vec<Option<bool>>,
    /// Trail of assigned literals
    trail: Vec<Literal>,
    /// Propagation pointer into trail
    propagated: usize,
    /// Watch lists: watches[2*var + sign] = list of clause indices watching -lit
    watches: Vec<Vec<WatchEntry>>,
    /// Number of variables
    num_vars: usize,
}

/// Entry in watch list
#[derive(Clone, Copy)]
struct WatchEntry {
    /// Blocking literal (optimization to avoid clause access)
    blocking: Literal,
    /// Clause index
    clause_idx: usize,
}

impl Warmup {
    /// Create warmup state for n variables
    pub(crate) fn new(num_vars: usize) -> Self {
        Self {
            assignment: vec![None; num_vars],
            trail: Vec::with_capacity(num_vars),
            propagated: 0,
            watches: vec![Vec::new(); num_vars * 2],
            num_vars,
        }
    }

    /// Reset state for new warmup round
    pub(crate) fn reset(&mut self) {
        self.assignment.fill(None);
        self.trail.clear();
        self.propagated = 0;
        for watch in &mut self.watches {
            watch.clear();
        }
    }

    /// Initialize watch lists from clause database
    fn init_watches(&mut self, clause_db: &ClauseArena) {
        for watch in &mut self.watches {
            watch.clear();
        }

        for idx in clause_db.indices() {
            if clause_db.is_empty_clause(idx) || clause_db.is_learned(idx) {
                continue;
            }

            let len = clause_db.len_of(idx);
            if len < 2 {
                continue; // Unit clauses handled separately
            }

            let lits = clause_db.literals(idx);
            let lit0 = lits[0];
            let lit1 = lits[1];

            // Watch -lit0 with blocking literal lit1
            let watch_idx0 = Self::watch_index(lit0.negated());
            self.watches[watch_idx0].push(WatchEntry {
                blocking: lit1,
                clause_idx: idx,
            });

            // Watch -lit1 with blocking literal lit0
            let watch_idx1 = Self::watch_index(lit1.negated());
            self.watches[watch_idx1].push(WatchEntry {
                blocking: lit0,
                clause_idx: idx,
            });
        }
    }

    /// Get watch list index for a literal
    #[inline]
    fn watch_index(lit: Literal) -> usize {
        let var = lit.variable().index();
        var * 2 + usize::from(!lit.is_positive())
    }

    /// Get value of a literal under current assignment
    #[inline]
    fn value(&self, lit: Literal) -> Option<bool> {
        let var = lit.variable().index();
        self.assignment[var].map(|v| if lit.is_positive() { v } else { !v })
    }

    /// Assign a literal during warmup
    fn assign(&mut self, lit: Literal) {
        let var = lit.variable().index();
        let val = lit.is_positive();
        debug_assert!(self.assignment[var].is_none());
        self.assignment[var] = Some(val);
        self.trail.push(lit);
    }

    /// Propagate beyond conflicts (warmup-specific)
    /// Returns number of conflicts encountered
    fn propagate_beyond_conflict(
        &mut self,
        clause_db: &ClauseArena,
        stats: &mut WarmupStats,
    ) -> usize {
        let mut conflicts = 0;

        while self.propagated < self.trail.len() {
            let lit = self.trail[self.propagated];
            self.propagated += 1;
            stats.propagations += 1;

            // Get watches for negation of propagated literal
            let watch_idx = Self::watch_index(lit);
            let mut watches = std::mem::take(&mut self.watches[watch_idx]);
            let mut j = 0;

            for i in 0..watches.len() {
                let entry = watches[i];

                // Check blocking literal first (optimization)
                if self.value(entry.blocking) == Some(true) {
                    watches[j] = entry;
                    j += 1;
                    continue;
                }

                // Need to look at clause
                if clause_db.is_empty_clause(entry.clause_idx) {
                    // Clause was deleted, skip
                    continue;
                }

                let lits = clause_db.literals(entry.clause_idx);
                let len = lits.len();

                // Find the other watched literal
                let lit0 = lits[0];
                let lit1 = lits[1];
                let neg_lit = lit.negated();
                let other = if lit0 == neg_lit { lit1 } else { lit0 };

                // Check if other watched literal is satisfied
                if self.value(other) == Some(true) {
                    watches[j] = WatchEntry {
                        blocking: other,
                        clause_idx: entry.clause_idx,
                    };
                    j += 1;
                    continue;
                }

                // Look for new literal to watch
                let mut found = false;
                for &new_lit in &lits[2..len] {
                    if self.value(new_lit) != Some(false) {
                        // Found a new literal to watch (unassigned or true)
                        // Swap it to position 0 or 1
                        // We can't actually swap in clause_db, so we just update watches
                        let new_watch_idx = Self::watch_index(new_lit.negated());
                        self.watches[new_watch_idx].push(WatchEntry {
                            blocking: other,
                            clause_idx: entry.clause_idx,
                        });
                        found = true;
                        break;
                    }
                }

                if found {
                    // Watch moved, don't keep this entry
                    continue;
                }

                // All other literals are false
                // Check if other watched literal is unit or conflict
                watches[j] = entry;
                j += 1;

                if self.value(other) == Some(false) {
                    // Conflict - ignore it (warmup behavior)
                    conflicts += 1;
                    stats.conflicts += 1;
                } else if self.value(other).is_none() {
                    // Unit propagation
                    self.assign(other);
                }
            }

            watches.truncate(j);
            self.watches[watch_idx] = watches;
        }

        conflicts
    }

    /// Perform warmup: propagate with decisions to set phases
    pub(crate) fn warmup(
        &mut self,
        clause_db: &ClauseArena,
        phases: &[i8],
        target_phases: &mut [i8],
        stats: &mut WarmupStats,
    ) {
        stats.warmup_count += 1;

        // Reset state
        self.reset();

        // Initialize watches
        self.init_watches(clause_db);

        // Handle unit clauses first
        for idx in clause_db.indices() {
            if clause_db.is_empty_clause(idx) || clause_db.is_learned(idx) {
                continue;
            }
            if clause_db.len_of(idx) == 1 {
                let lit = clause_db.literals(idx)[0];
                let var = lit.variable().index();
                if self.assignment[var].is_none() {
                    self.assign(lit);
                }
            }
        }

        // Propagate unit clauses
        self.propagate_beyond_conflict(clause_db, stats);

        // Make decisions until all variables assigned.
        // `phases` is expected to cover all solver variables.
        debug_assert!(
            phases.len() >= self.num_vars,
            "phase vector shorter than variable count"
        );
        for (var, &phase_hint) in phases.iter().take(self.num_vars).enumerate() {
            if self.assignment[var].is_some() {
                continue;
            }

            // Use existing phase or default to true (0 = unset -> true)
            let positive = phase_hint >= 0;
            let variable = crate::Variable(var as u32);
            let lit = if positive {
                Literal::positive(variable)
            } else {
                Literal::negative(variable)
            };

            self.assign(lit);
            stats.decisions += 1;

            // Propagate (ignoring conflicts)
            self.propagate_beyond_conflict(clause_db, stats);
        }

        // Copy warmup assignment to target phases
        for (&assignment, target) in self
            .assignment
            .iter()
            .zip(target_phases.iter_mut())
            .take(self.num_vars)
        {
            if let Some(val) = assignment {
                *target = if val { 1 } else { -1 };
            }
        }
    }
}

/// Performs warmup phase initialization.
///
/// Uses CDCL propagation (ignoring conflicts) to find good initial phases.
/// This is more efficient than walk for small/medium instances because
/// it uses O(1) amortized 2-watched literal propagation instead of O(n²)
/// break-value computation.
pub(crate) fn warmup(
    clause_db: &ClauseArena,
    num_vars: usize,
    phases: &[i8],
    target_phases: &mut [i8],
    stats: &mut WarmupStats,
) {
    let mut state = Warmup::new(num_vars);
    state.warmup(clause_db, phases, target_phases, stats);
}

#[cfg(test)]
#[path = "warmup_tests.rs"]
mod tests;
