// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Frame propagation and fixpoint detection for clause-level IC3 (#8211).
//!
//! After all bad cubes at the frontier are blocked, we try to push (propagate)
//! each blocked clause from frame F_i to F_{i+1}. A clause can be pushed if
//! it is inductive relative to F_i (i.e., F_i /\ T |= clause').
//!
//! If any frame F_i ends up with no clauses at its own level after
//! propagation, we have found a fixpoint — an inductive invariant proving
//! the property safe (every blocked lemma has been pushed to a strictly
//! higher level, matching Z3 Spacer's `propagate_to_next_level` semantics).
//!
//! Reference: Bradley VMCAI 2011, Section 3. Z3 Spacer:
//! `reference/z3/src/muz/spacer/spacer_legacy_frames.cpp`.
//!
//! # Delta encoding (#8672 Finding #1)
//!
//! Under delta encoding, each blocking clause is stored at exactly one frame
//! (its maximum proven level). When a clause at level i is shown inductive
//! at level i+1, it is MOVED (not copied) from `frames[i].blocked_clauses`
//! to `frames[i+1].blocked_clauses`. The SAT solver gets a single activation
//! clause `(¬frames[i+1].activation ∨ clause)`; the old `(¬frames[i].activation
//! ∨ clause)` remains in the solver but becomes a no-op since the clause is
//! logically stronger at its new level.

use super::cube::Cube;
use super::solver::Ic3Solver;
use ay_sat::Literal;

impl Ic3Solver {
    /// Propagate blocked clauses forward through the frame sequence.
    ///
    /// For each frame i from 1 to k-1, try to push each clause stored at
    /// that frame's level to frame i+1. A clause c (negation of blocked cube)
    /// is propagated if F_i /\ T /\ not-c' is UNSAT.
    ///
    /// Under delta encoding (#8672), propagation MOVES the clause from
    /// `frames[i]` to `frames[i+1]`. This keeps memory bounded at
    /// O(distinct_lemmas) instead of O(distinct_lemmas * depth).
    ///
    /// Returns true if a fixpoint is detected (some frame i becomes empty
    /// after propagation, meaning every clause at level i propagated up).
    pub(super) fn propagate(&mut self) -> bool {
        let k = self.frames.len() - 1;

        for i in 1..k {
            // Take ownership of this frame's clause list to iterate without
            // holding a borrow on self. Clauses that fail to propagate are
            // put back at the end. This avoids the pre-#8672 full clone of
            // blocked_clauses every propagation cycle.
            let clauses = std::mem::take(&mut self.frames[i].blocked_clauses);
            let mut retained: Vec<Vec<Literal>> = Vec::with_capacity(clauses.len());

            for clause in clauses {
                // Check if this clause is inductive relative to F_i.
                // The clause blocks a cube; we check if the cube (negated clause)
                // is inductive relative to frame i + 1 (using F_i as the
                // predecessor frame, per is_inductive_relative's level-1 contract).
                let cube_lits: Vec<Literal> = clause.iter().map(|&l| l.negated()).collect();
                let cube = Cube::new(cube_lits);

                if self.is_inductive_relative(&cube, i + 1) {
                    // Clause is inductive at level i+1: MOVE it up.
                    // Add the activated clause to the SAT solver under
                    // frames[i+1]'s activation, then push onto frames[i+1]'s
                    // blocked list. The old activation clause under frames[i]
                    // stays in the solver (harmless — it's a strictly weaker
                    // constraint now that the same lemma holds at a higher
                    // level under a different activation literal).
                    self.add_clause_to_single_frame(&clause, i + 1);
                    self.stats.clauses_propagated += 1;
                    // Do NOT put back on frames[i]: delta encoding removes
                    // the clause from its old level (Spacer: src.pop_back()).
                } else {
                    retained.push(clause);
                }
            }

            self.frames[i].blocked_clauses = retained;

            // Fixpoint: under delta encoding, F_i is exactly its own delta
            // clauses plus F_{i+1}. If no clauses remain stored at level i,
            // then F_i == F_{i+1}. This includes clauses strengthened directly
            // to a higher level during blocking rather than moved by this pass.
            if self.frames[i].blocked_clauses.is_empty() {
                return true;
            }
        }

        false
    }

    /// Add a clause to a single frame (delta encoding: single storage).
    ///
    /// If the same clause is already stored at `level` or above, this is a
    /// no-op — under delta encoding a clause at level j is active at all
    /// levels i <= j, so duplicate storage only wastes memory.
    fn add_clause_to_single_frame(&mut self, clause: &[Literal], level: usize) {
        if level >= self.frames.len() {
            return;
        }

        if self
            .frames
            .iter()
            .skip(level)
            .any(|frame| frame.blocked_clauses.iter().any(|c| c.as_slice() == clause))
        {
            return;
        }
        for frame in self.frames.iter_mut().take(level) {
            frame
                .blocked_clauses
                .retain(|existing| existing.as_slice() != clause);
        }

        let activation = self.frames[level].activation;
        // Assert: activation => clause
        // In CNF: (not-activation OR l1 OR l2 OR ... OR ln)
        let mut activated_clause = Vec::with_capacity(clause.len() + 1);
        activated_clause.push(activation.negated());
        activated_clause.extend_from_slice(clause);
        self.solver.add_clause(activated_clause);

        self.frames[level].add_blocked_clause(clause.to_vec());
    }
}
