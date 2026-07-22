// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Union-find data structure for literal equivalence classes.

use crate::literal::Literal;

use super::CongruenceStats;

/// Result of a union-find merge operation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum MergeResult {
    /// The two literals were already in the same equivalence class.
    NoChange,
    /// A new merge was performed successfully.
    Merged,
    /// Merging would equate a literal with its complement (`x ≡ ¬x`) -> UNSAT.
    Contradiction { unit: Literal },
}

/// Union-Find for literal equivalence classes.
/// Positive/negative literals of each variable remain complementary;
/// lower variable index wins representative ties (CaDiCaL convention).
pub(super) struct UnionFind {
    /// Parent pointers indexed by literal index (2 * num_vars entries).
    parent: Vec<usize>,
}

impl UnionFind {
    pub(super) fn new(size: usize) -> Self {
        Self {
            parent: (0..size).collect(),
        }
    }

    pub(super) fn find(&mut self, x: usize) -> usize {
        // Iterative two-pass full path compression (semantically identical to
        // the previous recursive form). The recursive version recursed as deep
        // as the equivalence-chain length and overflowed the stack on large
        // gate-heavy instances (e.g. SAT-COMP bvsub circuits build chains tens
        // of thousands deep once congruence runs on the default route). This
        // form first walks to the root, then points every node on the path
        // directly at the root, using O(1) stack.
        let mut root = x;
        while self.parent[root] != root {
            root = self.parent[root];
        }
        let mut node = x;
        while self.parent[node] != root {
            let next = self.parent[node];
            self.parent[node] = root;
            node = next;
        }
        debug_assert_eq!(
            self.parent[root], root,
            "BUG: find({x}) returned {root} which is not a fixpoint (parent={}).",
            self.parent[root]
        );
        root
    }

    /// Merge two literal equivalence classes, maintaining positive/negative
    /// pairing. The smaller variable index becomes the representative.
    ///
    /// Returns `MergeResult::Contradiction` if merging a literal with its
    /// complement (x ≡ ¬x), which occurs in XOR odd-cycle chains.
    pub(super) fn union_lits(&mut self, a: usize, b: usize) -> MergeResult {
        let ra = self.find(a);
        let rb = self.find(b);
        debug_assert_eq!(
            self.find(ra),
            ra,
            "BUG: union_lits lhs representative must be idempotent"
        );
        debug_assert_eq!(
            self.find(rb),
            rb,
            "BUG: union_lits rhs representative must be idempotent"
        );
        if ra == rb {
            return MergeResult::NoChange;
        }

        // Detect contradiction: complementary literals of the same variable.
        if ra / 2 == rb / 2 {
            return MergeResult::Contradiction {
                unit: Literal::from_index(ra),
            };
        }

        let var_a = ra / 2;
        let var_b = rb / 2;

        // Smaller variable becomes the representative (CaDiCaL convention).
        let (winner, loser) = if var_a <= var_b { (ra, rb) } else { (rb, ra) };
        debug_assert_eq!(
            self.find(winner),
            winner,
            "BUG: winner must be a canonical UF representative"
        );
        debug_assert_eq!(
            self.find(loser),
            loser,
            "BUG: loser must be a canonical UF representative before rewrite"
        );

        // Map loser's positive to winner's positive (or negative to negative).
        self.parent[loser] = winner;

        // Also merge the complementary literals.
        let loser_neg = loser ^ 1;
        let winner_neg = winner ^ 1;
        let loser_neg_root = self.find(loser_neg);
        let winner_neg_root = self.find(winner_neg);
        if loser_neg_root != winner_neg_root {
            // Secondary contradiction check on complement merge.
            if loser_neg_root / 2 == winner_neg_root / 2 {
                return MergeResult::Contradiction {
                    unit: Literal::from_index(loser_neg_root),
                };
            }
            self.parent[loser_neg_root] = winner_neg_root;
        }
        // Postcondition: complement pairing is consistent — merged pair's
        // representatives are complementary literals of the same variable.
        debug_assert_eq!(
            self.find(winner) / 2,
            self.find(winner ^ 1) / 2,
            "BUG: union_lits complement pairing broken: \
             find({winner})={}, find({})={}",
            self.find(winner),
            winner ^ 1,
            self.find(winner ^ 1)
        );
        MergeResult::Merged
    }
}

/// Merge two literal classes via union-find, recording the equivalence edge on success.
///
/// Returns `Ok(true)` if a new merge occurred, `Ok(false)` if already equivalent,
/// or `Err(unit)` on contradiction (literal merged with its complement).
pub(super) fn merge_or_contradict(
    uf: &mut UnionFind,
    a: usize,
    b: usize,
    equivalence_edges: &mut Vec<(Literal, Literal)>,
    provenance: crate::congruence::EdgeProvenance,
    edge_provenance: &mut Vec<crate::congruence::EdgeProvenance>,
    stats: &mut CongruenceStats,
) -> Result<bool, Literal> {
    match uf.union_lits(a, b) {
        MergeResult::NoChange => Ok(false),
        MergeResult::Contradiction { unit } => {
            // Record the contradicting merge as an edge too: the caller
            // inserts edge binaries into the clause DB BEFORE probing the
            // contradiction witness unit, and without this final edge the
            // cycle a ≡ … ≡ ¬a is never closed in the DB, so a CORRECT
            // UNSAT witness fails its RUP probe and the contradiction is
            // rejected every round (observed on 70da0b78 with clause-driven
            // XOR groups). Same justification class as every other merge
            // edge; proof mode still RUP-gates each edge individually
            // (fail-closed), so an unprovable final edge is skipped there.
            equivalence_edges.push((Literal::from_index(a), Literal::from_index(b)));
            edge_provenance.push(provenance);
            Err(unit)
        }
        MergeResult::Merged => {
            equivalence_edges.push((Literal::from_index(a), Literal::from_index(b)));
            edge_provenance.push(provenance);
            stats.equivalences_found += 1;
            Ok(true)
        }
    }
}
