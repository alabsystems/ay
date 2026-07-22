// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Literal equivalence class detection for IC3 incremental mode (#8662 Gap 4).
//!
//! GipSAT maintains a union-find for literal equivalences (gipsat/eq.rs:1-90).
//! When two literals are proven equivalent via binary clauses (a => b AND b => a),
//! all clauses can be rewritten to use canonical representatives. Over thousands
//! of IC3 queries with incremental lemma addition, equivalent literals accumulate,
//! inflating clause length and variable count.
//!
//! This module provides equivalence detection by scanning binary watch entries.
//! A binary watcher for literal `a` with blocker `b` encodes `!a | b` (i.e.,
//! `a => b`). If we also find `b => a` (literal `b.negated()` has a binary
//! watcher with blocker `a.negated()`), then `a ≡ b`.
//!
//! The equivalence map uses a union-find with path compression. Each literal
//! maps to its canonical representative. The map is computed lazily via
//! `detect_equivalences()` and can be queried via `canonical_literal()`.

use super::*;

/// Union-find for literal equivalences with path compression.
///
/// `parent[lit.index()]` stores the parent in the union-find tree.
/// After path compression, `find(lit)` returns the canonical representative.
///
/// Invariant: if `a ≡ b`, then `!a ≡ !b`. The union-find maintains this
/// by always unioning both `(a, b)` and `(!a, !b)` together.
#[derive(Debug, Clone)]
pub(crate) struct LiteralEquivMap {
    /// Parent pointer for each literal index. `parent[lit.index()] == lit.raw()`
    /// means `lit` is a root (canonical representative).
    parent: Vec<u32>,
    /// Rank for union-by-rank.
    rank: Vec<u8>,
    /// Number of equivalence classes with more than one member.
    num_nontrivial_classes: usize,
    /// Total number of literals merged (not counting roots).
    num_merged: usize,
}

impl LiteralEquivMap {
    /// Create an identity map for `num_lits` literal indices (= 2 * num_vars).
    pub(crate) fn new(num_lits: usize) -> Self {
        let parent: Vec<u32> = (0..num_lits as u32).collect();
        Self {
            parent,
            rank: vec![0; num_lits],
            num_nontrivial_classes: 0,
            num_merged: 0,
        }
    }

    /// Find the canonical representative for a literal, with path compression.
    #[inline]
    pub(crate) fn find(&mut self, lit: Literal) -> Literal {
        let idx = lit.index();
        let root = self.find_index(idx);
        Literal(root as u32)
    }

    /// Find by index with path compression.
    fn find_index(&mut self, mut idx: usize) -> usize {
        // Walk to root.
        let mut root = idx;
        while self.parent[root] as usize != root {
            root = self.parent[root] as usize;
        }
        // Path compression: point all nodes on the path directly to root.
        while idx != root {
            let next = self.parent[idx] as usize;
            self.parent[idx] = root as u32;
            idx = next;
        }
        root
    }

    /// Union two literals into the same equivalence class.
    ///
    /// Also unions their negations to maintain the `a ≡ b => !a ≡ !b` invariant.
    /// Returns `true` if the union was new (they were not already equivalent).
    pub(crate) fn union(&mut self, a: Literal, b: Literal) -> bool {
        let ra = self.find_index(a.index());
        let rb = self.find_index(b.index());
        if ra == rb {
            return false;
        }
        // Union a and b.
        self.link(ra, rb);
        // Union !a and !b to maintain polarity consistency.
        let na = a.negated();
        let nb = b.negated();
        let rna = self.find_index(na.index());
        let rnb = self.find_index(nb.index());
        if rna != rnb {
            self.link(rna, rnb);
        }
        self.num_nontrivial_classes += 1;
        self.num_merged += 2; // both a and !a collapsed
        true
    }

    /// Link two roots by rank.
    fn link(&mut self, ra: usize, rb: usize) {
        debug_assert_eq!(self.parent[ra] as usize, ra);
        debug_assert_eq!(self.parent[rb] as usize, rb);
        if self.rank[ra] < self.rank[rb] {
            self.parent[ra] = rb as u32;
        } else if self.rank[ra] > self.rank[rb] {
            self.parent[rb] = ra as u32;
        } else {
            self.parent[rb] = ra as u32;
            self.rank[ra] = self.rank[ra].saturating_add(1);
        }
    }

    /// Check if any non-trivial equivalence classes were detected.
    #[inline]
    pub(crate) fn has_equivalences(&self) -> bool {
        self.num_nontrivial_classes > 0
    }

    /// Number of non-trivial equivalence classes.
    #[inline]
    pub(crate) fn num_classes(&self) -> usize {
        self.num_nontrivial_classes
    }

    /// Total number of merged literals.
    #[inline]
    pub(crate) fn num_merged(&self) -> usize {
        self.num_merged
    }

    /// Get the canonical representative without path compression (read-only).
    #[inline]
    pub(crate) fn canonical(&self, lit: Literal) -> Literal {
        let mut idx = lit.index();
        while self.parent[idx] as usize != idx {
            idx = self.parent[idx] as usize;
        }
        Literal(idx as u32)
    }

    /// Reset to the identity map.
    pub(crate) fn reset(&mut self, num_lits: usize) {
        self.parent.clear();
        self.parent.extend(0..num_lits as u32);
        self.rank.clear();
        self.rank.resize(num_lits, 0);
        self.num_nontrivial_classes = 0;
        self.num_merged = 0;
    }
}

impl Solver {
    /// Detect literal equivalences from binary clauses.
    ///
    /// Scans binary watch entries for bidirectional implication pairs.
    /// A binary clause `(L | B)` is watched on both `L` and `B`:
    ///   - `watch_clause(ref, L, B)` adds `Watcher(B)` on `L` and `Watcher(L)` on `B`.
    ///   - BCP fires when `L` becomes false, propagating `B`. So the clause
    ///     encodes `!L => B` and `!B => L`.
    ///
    /// To detect `a ≡ b`:
    ///   - Need `a => b`: clause `(!a | b)`, watched on `!a` with blocker `b`.
    ///   - Need `b => a`: clause `(!b | a)`, watched on `!b` with blocker `a`.
    ///
    /// For efficiency, binary watchers are stored first in the SoA layout
    /// (binary-first invariant), so the scan terminates early at the first
    /// non-binary entry. To avoid duplicate work, only pairs with
    /// `a.index() < b.index()` are considered.
    ///
    /// Returns the equivalence map. Caller can check `has_equivalences()`.
    pub(crate) fn detect_equivalences(&self) -> LiteralEquivMap {
        let num_lits = self.num_vars * 2;
        let mut equiv = LiteralEquivMap::new(num_lits);

        // For each literal `watched_lit`, scan binary watchers. A binary
        // watcher on `watched_lit` with blocker `b` encodes clause
        // `(watched_lit | b)`, meaning `!watched_lit => b`.
        // Let `a = !watched_lit`. Then we have `a => b`.
        // Check if `b => a` also holds (binary watcher on `!b` with blocker `a`).
        // If so, `a ≡ b`.
        for li in 0..num_lits {
            let watched_lit = Literal(li as u32);
            let a = watched_lit.negated(); // a = !watched_lit

            let entry_slice = self.watches.entry_slice(watched_lit);

            for &entry in entry_slice {
                // Binary-first invariant: all binary entries precede long entries.
                if !crate::watched::entry_is_binary(entry) {
                    break;
                }

                let b = Literal(crate::watched::entry_blocker_raw(entry));
                // Avoid duplicate processing: only consider ordered pairs.
                if a.index() >= b.index() {
                    continue;
                }

                // Check reverse implication b => a: binary watcher on !b with blocker a.
                if self.has_binary_implication(b.negated(), a) {
                    equiv.union(a, b);
                }
            }
        }

        equiv
    }

    /// Check if there's a binary watcher on `watched_lit` with blocker `target`.
    ///
    /// This tests whether the clause `(watched_lit | target)` exists as a binary
    /// clause, which encodes the implication `!watched_lit => target`.
    fn has_binary_implication(&self, watched_lit: Literal, target: Literal) -> bool {
        let entry_slice = self.watches.entry_slice(watched_lit);
        let target_raw = target.raw();

        for &entry in entry_slice {
            if !crate::watched::entry_is_binary(entry) {
                break; // binary-first invariant
            }
            if crate::watched::entry_blocker_raw(entry) == target_raw {
                return true;
            }
        }
        false
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::solver::Solver;

    /// Helper: create a solver and add binary clauses to form equivalences.
    ///
    /// Calls `initialize_watches` after adding all clauses to populate the
    /// watch lists (watches are not attached by `add_clause` — they are
    /// normally set up at solve-time by `initialize_watches`).
    fn solver_with_binary_clauses(num_vars: usize, clauses: &[(i32, i32)]) -> Solver {
        let mut solver = Solver::new(num_vars);
        for &(a, b) in clauses {
            let lits = vec![
                if a > 0 {
                    Literal::positive(Variable(a as u32 - 1))
                } else {
                    Literal::negative(Variable((-a) as u32 - 1))
                },
                if b > 0 {
                    Literal::positive(Variable(b as u32 - 1))
                } else {
                    Literal::negative(Variable((-b) as u32 - 1))
                },
            ];
            solver.add_clause(lits);
        }
        // Attach watches so detect_equivalences can scan binary watchers.
        solver.initialize_watches();
        solver
    }

    #[test]
    fn test_equiv_detection_no_equivalences() {
        // Single implication a => b but not b => a.
        // Clause: (!a | b) = (-1 | 2) = (-1, 2) in DIMACS = (!x0 | x1)
        let solver = solver_with_binary_clauses(3, &[(-1, 2)]);
        let equiv = solver.detect_equivalences();
        assert!(
            !equiv.has_equivalences(),
            "single implication should not create equivalence"
        );
        assert_eq!(equiv.num_classes(), 0);
    }

    #[test]
    fn test_equiv_detection_simple_pair() {
        // a ≡ b: both a => b and b => a.
        // a => b: clause (!a | b) = (-1, 2)
        // b => a: clause (!b | a) = (-2, 1)
        let solver = solver_with_binary_clauses(3, &[(-1, 2), (-2, 1)]);
        let equiv = solver.detect_equivalences();
        assert!(
            equiv.has_equivalences(),
            "bidirectional implication should create equivalence"
        );
        assert_eq!(equiv.num_classes(), 1);

        // Check that the two literals have the same canonical representative.
        let a = Literal::positive(Variable(0));
        let b = Literal::positive(Variable(1));
        let ca = equiv.canonical(a);
        let cb = equiv.canonical(b);
        assert_eq!(
            ca, cb,
            "equivalent literals should have the same canonical representative"
        );

        // Check that negations are also equivalent.
        let na = Literal::negative(Variable(0));
        let nb = Literal::negative(Variable(1));
        let cna = equiv.canonical(na);
        let cnb = equiv.canonical(nb);
        assert_eq!(
            cna, cnb,
            "negated equivalent literals should also be equivalent"
        );
    }

    #[test]
    fn test_equiv_detection_no_binary_clauses() {
        // No clauses at all.
        let solver = Solver::new(4);
        let equiv = solver.detect_equivalences();
        assert!(!equiv.has_equivalences());
        assert_eq!(equiv.num_classes(), 0);
    }

    #[test]
    fn test_equiv_detection_chain() {
        // a ≡ b and b ≡ c should put a, b, c in the same class.
        // a => b: (-1, 2), b => a: (-2, 1)
        // b => c: (-2, 3), c => b: (-3, 2)
        let solver = solver_with_binary_clauses(4, &[(-1, 2), (-2, 1), (-2, 3), (-3, 2)]);
        let equiv = solver.detect_equivalences();
        assert!(equiv.has_equivalences());

        let a = Literal::positive(Variable(0));
        let b = Literal::positive(Variable(1));
        let c = Literal::positive(Variable(2));
        let ca = equiv.canonical(a);
        let cb = equiv.canonical(b);
        let cc = equiv.canonical(c);
        assert_eq!(ca, cb, "a and b should be in the same class");
        assert_eq!(cb, cc, "b and c should be in the same class");
    }

    #[test]
    fn test_equiv_detection_negative_literals() {
        // !a ≡ b: both !a => b and b => !a.
        // !a => b: clause (a | b) = (1, 2)
        // b => !a: clause (!b | !a) = (-2, -1)
        let solver = solver_with_binary_clauses(3, &[(1, 2), (-2, -1)]);
        let equiv = solver.detect_equivalences();
        assert!(equiv.has_equivalences());

        let na = Literal::negative(Variable(0));
        let b = Literal::positive(Variable(1));
        let cna = equiv.canonical(na);
        let cb = equiv.canonical(b);
        assert_eq!(cna, cb, "!a and b should be equivalent");
    }

    #[test]
    fn test_equiv_map_find_with_compression() {
        let mut equiv = LiteralEquivMap::new(10);
        let a = Literal(0);
        let b = Literal(2);
        let c = Literal(4);

        equiv.union(a, b);
        equiv.union(b, c);

        // All three should find the same root.
        let ra = equiv.find(a);
        let rb = equiv.find(b);
        let rc = equiv.find(c);
        assert_eq!(ra, rb);
        assert_eq!(rb, rc);
    }

    #[test]
    fn test_equiv_map_reset() {
        let mut equiv = LiteralEquivMap::new(10);
        let a = Literal(0);
        let b = Literal(2);
        equiv.union(a, b);
        assert!(equiv.has_equivalences());

        equiv.reset(10);
        assert!(!equiv.has_equivalences());
        assert_eq!(equiv.num_classes(), 0);
        // After reset, every literal is its own canonical.
        for i in 0..10u32 {
            let lit = Literal(i);
            assert_eq!(equiv.canonical(lit), lit);
        }
    }

    #[test]
    fn test_equiv_map_negation_consistency() {
        let mut equiv = LiteralEquivMap::new(10);
        let a = Literal::positive(Variable(0)); // index 0
        let b = Literal::positive(Variable(1)); // index 2
        let na = a.negated(); // index 1
        let nb = b.negated(); // index 3

        equiv.union(a, b);
        // Should also union !a and !b.
        let cna = equiv.canonical(na);
        let cnb = equiv.canonical(nb);
        assert_eq!(
            cna, cnb,
            "negation of equivalent literals should be equivalent"
        );
    }

    #[test]
    fn test_equiv_detection_multiple_independent_pairs() {
        // a ≡ b and c ≡ d (independent pairs).
        // a => b: (-1, 2), b => a: (-2, 1)
        // c => d: (-3, 4), d => c: (-4, 3)
        let solver = solver_with_binary_clauses(5, &[(-1, 2), (-2, 1), (-3, 4), (-4, 3)]);
        let equiv = solver.detect_equivalences();
        assert!(equiv.has_equivalences());
        assert_eq!(equiv.num_classes(), 2);

        let a = Literal::positive(Variable(0));
        let b = Literal::positive(Variable(1));
        let c = Literal::positive(Variable(2));
        let d = Literal::positive(Variable(3));

        assert_eq!(equiv.canonical(a), equiv.canonical(b));
        assert_eq!(equiv.canonical(c), equiv.canonical(d));
        assert_ne!(
            equiv.canonical(a),
            equiv.canonical(c),
            "independent equivalence classes should have different canonicals"
        );
    }
}
