// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Intree probing: BFS tree-structured failed literal probing.
//!
//! Ported from CryptoMiniSat `intree.cpp` (MIT licensed).
//!
//! Unlike sequential probing (which probes one literal at a time), intree
//! probing builds a tree from the binary implication graph and explores it
//! in a single DFS pass. This is more efficient because:
//!
//! 1. Shared implications are not re-propagated for each probe literal
//! 2. Failed literals deeper in the tree are discovered with less work
//! 3. The tree structure naturally identifies root literals
//!
//! ## Algorithm
//!
//! 1. **Find roots**: Literals with no incoming binary implications (no binary
//!    clause `(l, x)` watching them) are roots of the implication graph.
//!
//! 2. **Build BFS queue**: For each root `r`, enqueue `~r` and recursively
//!    follow binary implications: if `(lit, other)` is binary, enqueue `~other`.
//!    Sentinel markers delimit tree levels for backtracking.
//!
//! 3. **Tree look**: Process the queue as a DFS exploration:
//!    - Literal elements: decide, propagate, check for failed literals
//!    - Sentinel elements: backtrack one decision level
//!    - Failed literals (conflict or ancestor failed): record for unit learning
//!
//! 4. **Learn units**: At level 0, enqueue negations of failed literals.
//!
//! ## References
//!
//! - CryptoMiniSat `reference/cryptominisat/src/intree.cpp`
//! - Heule, Järvisalo, Biere: "Efficient CNF Simplification Based on Binary
//!   Implication Graphs" (SAT 2011)

use super::super::lifecycle::VarState;
use super::super::*;
use std::collections::VecDeque;

/// Queue element for intree BFS/DFS traversal.
///
/// CMS `InTree::QueueElem`. When `propagated` is `None`, this is a sentinel
/// marker indicating the end of a subtree (backtrack one level).
#[derive(Debug, Clone, Copy)]
struct IntreeQueueElem {
    /// Literal to propagate, or None for sentinel (backtrack marker).
    propagated: Option<Literal>,
}

impl Solver {
    /// Run intree probing as an inprocessing pass.
    ///
    /// Returns `true` if UNSAT is proven (level-0 conflict).
    /// Returns `false` otherwise (including when skipped).
    ///
    /// Must be called at decision level 0.
    pub(in crate::solver) fn intree_probe(&mut self) -> bool {
        if !self.require_level_zero() {
            return false;
        }

        // LRAT mode: intree probing collects LRAT hints for each failed
        // literal via collect_probe_conflict_lrat_hints before backtracking,
        // matching the regular probe pattern. The weaker but sound approach
        // is used: learn ~probe_lit (not dominator) since intree does not
        // maintain parent chains for LRAT proof. (#8382)

        self.ensure_level0_unit_proof_ids();

        let num_lits = self.num_vars * 2;
        let mut seen = vec![false; num_lits];
        let mut queue: VecDeque<IntreeQueueElem> = VecDeque::new();
        let mut failed: Vec<Literal> = Vec::new();

        // Track whether any ancestor in the current tree path failed.
        // Parallel to queue depth (literal elements push, sentinels pop).
        let mut depth_failed: Vec<bool> = Vec::new();
        depth_failed.push(false); // Sentinel for root level.

        // Track whether each depth_failed entry corresponds to an actual
        // decision level (true) or a skipped literal (false/true already assigned).
        // Only entries with decided=true should trigger backtracking.
        let mut decided_at_depth: Vec<bool> = Vec::new();
        decided_at_depth.push(false); // Root sentinel: no decision.

        // CMS intree.cpp:171: track free vars before/after for accurate stats.
        let free_vars_before = self.intree_count_free_vars();

        // Tick-proportional effort budget.
        let tick_start = self.cold.probe_ticks;
        const INTREE_EFFORT_PERMILLE: u64 = 8;
        const INTREE_MIN_EFFORT: u64 = 10_000;
        let ticks_now = self.search_ticks[0] + self.search_ticks[1];
        let ticks_delta = ticks_now.saturating_sub(self.inproc.prober.last_search_ticks());
        let effort = (ticks_delta * INTREE_EFFORT_PERMILLE / 1000).max(INTREE_MIN_EFFORT);
        let tick_limit = tick_start.saturating_add(effort);

        // ── Phase 1: Find roots ────────────────────────────────────────
        // A literal `l` is a root if `watches[l]` contains no binary watchers.
        // CMS intree.cpp:fill_roots(). Such literals are leaves of the binary
        // implication graph — no binary clause `(l, x)` exists.
        let mut roots: Vec<Literal> = Vec::new();
        for var_idx in 0..self.num_vars {
            if self.var_is_assigned(var_idx) || self.var_lifecycle.is_removed(var_idx) {
                continue;
            }
            let var = Variable(var_idx as u32);
            for &lit in &[Literal::positive(var), Literal::negative(var)] {
                let ws = self.watches.get_watches(lit);
                let has_binary = (0..ws.len()).any(|i| ws.is_binary(i));
                if !has_binary {
                    roots.push(lit);
                }
            }
        }

        if roots.is_empty() {
            return false;
        }

        // Shuffle roots for diversity across rounds.
        let seed = self.num_conflicts;
        shuffle_literals(&mut roots, seed);

        // ── Phase 2: Build BFS queue from roots ────────────────────────
        // CMS: `for(Lit lit: roots) enqueue(~lit, lit_Undef, false, 0);`
        for &root in &roots {
            Self::intree_enqueue(
                root.negated(),
                &self.watches,
                &self.vals,
                self.var_lifecycle.as_slice(),
                &mut seen,
                &mut queue,
            );
        }

        // Clear seen flags after building queue (CMS intree.cpp:168-170).
        for elem in queue.iter() {
            if let Some(lit) = elem.propagated {
                if lit.index() < seen.len() {
                    seen[lit.index()] = false;
                }
            }
        }

        let mut total_failed = 0u64;
        // LRAT hint storage: parallel to `failed` — each failed literal gets
        // its LRAT hint chain collected while the trail is still available.
        let mut failed_hints: Vec<Vec<u64>> = Vec::new();
        let lrat_enabled = self.cold.lrat_enabled;

        // ── Phase 3: Tree look — process queue as DFS ──────────────────
        // CMS intree.cpp:tree_look().
        while let Some(elem) = queue.pop_front() {
            // Effort limit. Also honor the caller's interrupt flag: the tick
            // budget bounds work, not wall time, and on competition-scale
            // inputs one tree-look pass can run minutes past a
            // solve_interruptible timeout (the dispatcher only checks the flag
            // between passes). Tree look is a pure optimization, so bailing
            // out mid-pass is always sound (see probe.rs).
            if self.cold.probe_ticks >= tick_limit || self.is_interrupted() {
                break;
            }

            if let Some(lit) = elem.propagated {
                // ── Literal element ────────────────────────────────────
                depth_failed.push(*depth_failed.last().unwrap_or(&false));

                // If the literal is already falsified or an ancestor failed,
                // this literal is failed. Don't create a decision level.
                // Skip BVE-eliminated / SCC-substituted variables (#8507).
                // The enqueue phase filters these, but a stale queue element
                // could still slip through if BVE ran between queue building
                // and processing (not currently possible, but defensive).
                if self.var_lifecycle.is_removed(lit.variable().index()) {
                    decided_at_depth.push(false);
                    continue;
                }

                if self.lit_val(lit) < 0 || *depth_failed.last().unwrap_or(&false) {
                    failed.push(lit.negated());
                    failed_hints.push(Vec::new());
                    total_failed += 1;
                    decided_at_depth.push(false);
                    continue;
                }

                if self.lit_val(lit) == 0 {
                    // Unassigned: decide and propagate.
                    // Use probe_propagate (BCP mode PROBE) for proper tick
                    // accounting and hyper-binary resolution at level 1.
                    // CMS uses a dedicated propagate_bfs for HBR at all levels;
                    // AY's HBR fires only at decision_level==1 in probe mode,
                    // which is still beneficial for the first level of the tree.
                    self.decide(lit);
                    decided_at_depth.push(true);

                    self.probing_mode = true;
                    let conflict = self.probe_propagate();
                    self.probing_mode = false;
                    if let Some(conflict_ref) = conflict {
                        if let Some(df) = depth_failed.last_mut() {
                            *df = true;
                        }
                        // LRAT: collect hints BEFORE backtracking so that level-1+
                        // trail entries and reason clauses are still accessible.
                        // Uses the same forward BCP trace as regular probe (#8382).
                        // For intree at decision_level==1 we use the standard
                        // collect_probe_conflict_lrat_hints. For deeper levels,
                        // the hints are empty (TrustedTransform fallback) since
                        // multi-level intree proof chains aren't implemented yet.
                        let hints = if lrat_enabled && self.decision_level == 1 {
                            let unit = lit.negated();
                            self.collect_probe_conflict_lrat_hints(conflict_ref, lit, Some(unit))
                        } else {
                            Vec::new()
                        };
                        failed.push(lit.negated());
                        failed_hints.push(hints);
                        total_failed += 1;
                    }
                } else {
                    // Already true: no decision needed.
                    decided_at_depth.push(false);
                }
            } else {
                // ── Sentinel element ───────────────────────────────────
                // Pop the depth tracking. If this depth had a real decision,
                // backtrack one level.
                let had_decision = decided_at_depth.pop().unwrap_or(false);
                if had_decision && self.decision_level > 0 {
                    self.backtrack(self.decision_level.saturating_sub(1));
                }
                depth_failed.pop();
                if depth_failed.is_empty() {
                    depth_failed.push(false);
                }
                if decided_at_depth.is_empty() {
                    decided_at_depth.push(false);
                }
            }

            // When at level 0, process accumulated failed literals.
            if self.decision_level == 0
                && !failed.is_empty()
                && self.intree_empty_failed_list_with_hints(&mut failed, &mut failed_hints)
            {
                return true; // UNSAT
            }
        }

        // Backtrack to level 0 if not already there.
        if self.decision_level > 0 {
            self.backtrack(0);
        }

        // Process any remaining failed literals.
        if !failed.is_empty()
            && self.intree_empty_failed_list_with_hints(&mut failed, &mut failed_hints)
        {
            return true;
        }

        // ── Update stats ───────────────────────────────────────────────
        // CMS intree.cpp:171-174: vars_set is the difference in free variables,
        // which is more accurate than just the failed literal count because
        // propagation from learned units can set additional variables.
        let free_vars_after = self.intree_count_free_vars();
        let vars_set = free_vars_before.saturating_sub(free_vars_after) as u64;

        self.cold.intree_rounds += 1;
        self.cold.intree_failed += total_failed;
        self.cold.intree_vars_set += vars_set;

        tracing::debug!(
            roots = roots.len(),
            failed = total_failed,
            vars_set = vars_set,
            "intree_probe: round complete"
        );

        debug_assert_eq!(
            self.decision_level, 0,
            "BUG: intree_probe did not restore decision level to 0"
        );

        false
    }

    /// Whether a literal is admissible as an intree probe node: unseen,
    /// unassigned, in-bounds, and not a removed (BVE/SCC-substituted) variable.
    /// Mirrors the entry guards of the original recursive `intree_enqueue`.
    fn intree_node_admits(
        lit: Literal,
        vals: &[i8],
        var_states: &[VarState],
        seen: &[bool],
    ) -> bool {
        if lit.index() >= seen.len() {
            return false;
        }
        if seen[lit.index()] {
            return false;
        }
        if lit.index() < vals.len() && vals[lit.index()] != 0 {
            return false;
        }
        // Skip BVE-eliminated / SCC-substituted variables (#8507).
        let vi = lit.variable().index();
        if vi < var_states.len() && var_states[vi].is_removed() {
            return false;
        }
        true
    }

    /// Enqueue a literal into the intree BFS queue, following binary
    /// implications in a depth-first pre-order.
    ///
    /// CMS `InTree::enqueue()`. For each binary clause `(lit, other)` in
    /// the watch list where `lit` appears, assigning `lit=true` implies
    /// `other=true`. Since we're building the probe tree, we enqueue `~other`
    /// as a child to explore.
    ///
    /// Implemented iteratively with an explicit stack. The original recursive
    /// form recursed once per edge along the binary-implication chain, which
    /// overflows the stack on large gate-heavy instances once congruence is
    /// enabled (equivalence binaries build chains tens of thousands deep). The
    /// iterative form emits the identical queue sequence — pre-order
    /// `Some(node)` on entry, the node's children, then a `None` subtree
    /// sentinel — with O(depth) heap stack instead of call stack.
    fn intree_enqueue(
        lit: Literal,
        watches: &WatchedLists,
        vals: &[i8],
        var_states: &[VarState],
        seen: &mut [bool],
        queue: &mut VecDeque<IntreeQueueElem>,
    ) {
        if !Self::intree_node_admits(lit, vals, var_states, seen) {
            return;
        }
        queue.push_back(IntreeQueueElem {
            propagated: Some(lit),
        });
        seen[lit.index()] = true;

        // Explicit DFS stack: (node, next watch index to scan for that node).
        let mut stack: Vec<(Literal, usize)> = Vec::new();
        stack.push((lit, 0));

        while let Some(&(cur, resume)) = stack.last() {
            // Follow binary implications from `cur`. Binary clause (cur, other)
            // encodes ~cur -> other; enqueue ~other as a child to explore.
            let ws = watches.get_watches(cur);
            let len = ws.len();
            let mut i = resume;
            let mut opened_child = false;
            while i < len {
                let bi = i;
                i += 1;
                if !ws.is_binary(bi) {
                    continue;
                }
                let other = ws.blocker(bi);
                let neg_other = other.negated();
                if neg_other.index() < seen.len()
                    && !seen[neg_other.index()]
                    && neg_other.index() < vals.len()
                    && vals[neg_other.index()] == 0
                    && Self::intree_node_admits(neg_other, vals, var_states, seen)
                {
                    // Remember where to resume scanning `cur` after this child's
                    // subtree, then descend into the child (pre-order push).
                    stack.last_mut().expect("stack non-empty").1 = i;
                    queue.push_back(IntreeQueueElem {
                        propagated: Some(neg_other),
                    });
                    seen[neg_other.index()] = true;
                    stack.push((neg_other, 0));
                    opened_child = true;
                    break;
                }
            }
            if !opened_child {
                // All children of `cur` explored: close its subtree.
                queue.push_back(IntreeQueueElem { propagated: None });
                stack.pop();
            }
        }
    }

    /// Process the failed literal list: learn negations as unit clauses.
    ///
    /// CMS `InTree::empty_failed_list()`.
    /// Returns `true` if UNSAT is detected.
    ///
    /// `hints` is parallel to `failed`: each element contains LRAT proof hints
    /// collected while the conflict-causing trail was still alive. Empty hints
    /// are used as TrustedTransform fallback (safe for DRAT and non-proof modes).
    fn intree_empty_failed_list_with_hints(
        &mut self,
        failed: &mut Vec<Literal>,
        hints: &mut Vec<Vec<u64>>,
    ) -> bool {
        debug_assert_eq!(self.decision_level, 0);
        for (i, &lit) in failed.iter().enumerate() {
            if self.has_empty_clause {
                failed.clear();
                hints.clear();
                return true;
            }
            let unit_hints = if i < hints.len() {
                hints[i].as_slice()
            } else {
                &[] as &[u64]
            };

            // LRAT soundness gate (root cause of manol-pipe-c9 probe failure):
            // intree only collects a checker-visible LRAT hint chain for
            // conflicts found at decision_level==1. Deeper-level tree-look
            // conflicts (and ancestor/clash failures) arrive here with EMPTY
            // hints. Learning such a literal as a derived unit emits it as a
            // hidden TrustedTransform unit (enqueue_derived_unit downgrades
            // empty-hint units in LRAT mode), which is stripped from the LRAT
            // file. A later search-learned clause that resolves through this
            // level-0 assignment then has no visible antecedent for it, so its
            // RUP hint chain fails ("multiple literals unassigned in hint ...").
            //
            // The intree-derived unit is a sound optimization, not required for
            // correctness: the formula is still proven UNSAT by the rest of the
            // search. So in LRAT mode we simply skip any failed literal that
            // lacks a complete, checker-visible hint chain rather than emit an
            // unprovable proof step. (Mirrors the OOB-literal skip in
            // inprocessing/probe.rs and the BVE/sweep LRAT clamps.)
            if self.cold.lrat_enabled && unit_hints.is_empty() {
                continue;
            }

            let val = self.lit_val(lit);
            if val == 0 {
                // Unassigned: learn as unit with LRAT hints if available.
                if self.learn_derived_unit(lit, unit_hints) {
                    failed.clear();
                    hints.clear();
                    return true; // UNSAT from propagation
                }
                // After learning a unit in LRAT mode, ensure proof IDs are
                // assigned for any newly propagated level-0 units (#7108).
                if self.cold.lrat_enabled {
                    self.ensure_level0_unit_proof_ids();
                }
            } else if val < 0 {
                // Already set to the opposite value — contradiction → UNSAT.
                // In LRAT mode this branch is only reached with a non-empty
                // hint chain (empty-hint literals are skipped above), so the
                // empty clause is backed by a checker-visible derivation: learn
                // the unit first (emitting its proof line) so the level-0
                // contradiction is provable, then mark the empty clause.
                if self.cold.lrat_enabled && self.learn_derived_unit(lit, unit_hints) {
                    failed.clear();
                    hints.clear();
                    return true;
                }
                self.mark_empty_clause();
                failed.clear();
                hints.clear();
                return true;
            }
            // val > 0: already satisfied, nothing to do.
        }
        failed.clear();
        hints.clear();
        false
    }

    /// Count the number of unassigned, non-removed variables.
    ///
    /// Used to compute accurate `intree_vars_set` stats (CMS intree.cpp:171).
    fn intree_count_free_vars(&self) -> usize {
        let mut count = 0;
        for vi in 0..self.num_vars {
            if !self.var_is_assigned(vi) && !self.var_lifecycle.is_removed(vi) {
                count += 1;
            }
        }
        count
    }
}

/// Simple Fisher-Yates shuffle using a u64 seed.
fn shuffle_literals(lits: &mut [Literal], seed: u64) {
    let n = lits.len();
    if n <= 1 {
        return;
    }
    let mut state = seed.wrapping_add(0x9E3779B97F4A7C15);
    for i in (1..n).rev() {
        // xorshift64
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        let j = (state as usize) % (i + 1);
        lits.swap(i, j);
    }
}

#[cfg(test)]
mod tests {
    use super::super::super::*;

    /// Intree probing on a 2-variable UNSAT formula.
    /// (a v b) & (~a v b) & (a v ~b) & (~a v ~b) is unsatisfiable.
    #[test]
    fn test_intree_probe_unsat_formula() {
        let mut solver = Solver::new(2);
        let a = Literal::positive(Variable(0));
        let b = Literal::positive(Variable(1));
        solver.add_clause(vec![a, b]);
        solver.add_clause(vec![a.negated(), b]);
        solver.add_clause(vec![a, b.negated()]);
        solver.add_clause(vec![a.negated(), b.negated()]);
        assert!(solver.process_initial_clauses().is_none());
        solver.initialize_watches();
        let _ = solver.propagate();

        let unsat = solver.intree_probe();
        if !unsat {
            let result = solver.solve().into_inner();
            assert!(
                result.is_unsat(),
                "Expected UNSAT for contradictory formula"
            );
        }
    }

    /// Intree probing on a formula with binary implication chains.
    /// (~a v b) & (~b v c) & (~c) forces chain a->b->c, contradicting ~c.
    /// (a v d) makes it satisfiable with a=false, d=true.
    #[test]
    fn test_intree_probe_implication_chain() {
        let mut solver = Solver::new(4);
        let a = Literal::positive(Variable(0));
        let b = Literal::positive(Variable(1));
        let c = Literal::positive(Variable(2));
        let d = Literal::positive(Variable(3));
        solver.add_clause(vec![a.negated(), b]); // ~a v b
        solver.add_clause(vec![b.negated(), c]); // ~b v c
        solver.add_clause(vec![c.negated()]); // ~c
        solver.add_clause(vec![a, d]); // a v d
        assert!(solver.process_initial_clauses().is_none());
        solver.initialize_watches();
        let _ = solver.propagate();

        let unsat = solver.intree_probe();
        assert!(!unsat, "Formula should be satisfiable");
        let result = solver.solve().into_inner();
        assert!(result.is_sat(), "Expected SAT");
    }

    /// Intree probing on a satisfiable formula should not break anything.
    #[test]
    fn test_intree_probe_satisfiable() {
        let mut solver = Solver::new(3);
        let a = Literal::positive(Variable(0));
        let b = Literal::positive(Variable(1));
        let c = Literal::positive(Variable(2));
        solver.add_clause(vec![a, b]);
        solver.add_clause(vec![a.negated(), c]);
        solver.add_clause(vec![b, c]);
        assert!(solver.process_initial_clauses().is_none());
        solver.initialize_watches();
        let _ = solver.propagate();

        let unsat = solver.intree_probe();
        assert!(!unsat, "Formula is satisfiable");
        let result = solver.solve().into_inner();
        assert!(result.is_sat(), "Expected SAT");
    }

    /// Intree probing on an empty solver.
    #[test]
    fn test_intree_probe_empty() {
        let mut solver = Solver::new(0);
        let unsat = solver.intree_probe();
        assert!(!unsat, "Empty formula is trivially SAT");
    }

    /// Intree probing discovers a failed literal via binary implications.
    /// (~a v b) & (~a v ~b) means probing a leads to b and ~b conflict.
    /// So ~a must be true (a is failed).
    #[test]
    fn test_intree_probe_binary_conflict() {
        let mut solver = Solver::new(3);
        let a = Literal::positive(Variable(0));
        let b = Literal::positive(Variable(1));
        let c = Literal::positive(Variable(2));
        solver.add_clause(vec![a.negated(), b]); // ~a v b (a -> b)
        solver.add_clause(vec![a.negated(), b.negated()]); // ~a v ~b (a -> ~b)
        solver.add_clause(vec![a, c]); // a v c (SAT with a=false, c=true)
        assert!(solver.process_initial_clauses().is_none());
        solver.initialize_watches();
        let _ = solver.propagate();

        let _unsat = solver.intree_probe();
        // Full solve should still work correctly.
        let result = solver.solve().into_inner();
        assert!(result.is_sat(), "Expected SAT with a=false");
    }

    /// Deep implication chain: a->b->c->d->e with ~e forces all false.
    /// Intree should discover this via tree traversal.
    #[test]
    fn test_intree_probe_deep_chain() {
        let mut solver = Solver::new(6);
        let a = Literal::positive(Variable(0));
        let b = Literal::positive(Variable(1));
        let c = Literal::positive(Variable(2));
        let d = Literal::positive(Variable(3));
        let e = Literal::positive(Variable(4));
        let f = Literal::positive(Variable(5));
        // Chain: a -> b -> c -> d -> e
        solver.add_clause(vec![a.negated(), b]);
        solver.add_clause(vec![b.negated(), c]);
        solver.add_clause(vec![c.negated(), d]);
        solver.add_clause(vec![d.negated(), e]);
        // e must be false
        solver.add_clause(vec![e.negated()]);
        // Make it SAT: a=false is forced, f is free
        solver.add_clause(vec![a, f]);
        assert!(solver.process_initial_clauses().is_none());
        solver.initialize_watches();
        let _ = solver.propagate();

        let unsat = solver.intree_probe();
        assert!(!unsat, "Formula is satisfiable");
        let result = solver.solve().into_inner();
        assert!(result.is_sat(), "Expected SAT");
    }

    /// Verify that intree stats counters are updated after a round.
    #[test]
    fn test_intree_probe_stats_updated() {
        let mut solver = Solver::new(3);
        let a = Literal::positive(Variable(0));
        let b = Literal::positive(Variable(1));
        let c = Literal::positive(Variable(2));
        solver.add_clause(vec![a.negated(), b]);
        solver.add_clause(vec![a.negated(), b.negated()]);
        solver.add_clause(vec![a, c]);
        assert!(solver.process_initial_clauses().is_none());
        solver.initialize_watches();
        let _ = solver.propagate();

        let (rounds_before, _, _) = solver.intree_stats();
        let _ = solver.intree_probe();
        let (rounds_after, _, _) = solver.intree_stats();
        assert!(
            rounds_after > rounds_before,
            "intree_rounds should increase after a probe round"
        );
    }

    /// (#8507) Intree probing must skip BVE-eliminated variables.
    ///
    /// Without the fix, binary implications from active variables can lead
    /// to eliminated variables in the intree queue. When `decide()` is called
    /// on an eliminated variable, it triggers:
    ///   `assert!(!is_removed)` → panic "decided removed variable"
    ///
    /// This test creates binary clauses involving a variable, marks it as
    /// eliminated, and runs intree_probe. Before the fix, this would panic.
    #[test]
    fn test_intree_probe_skips_eliminated_variable() {
        // 4 variables: a(0), b(1), c(2), d(3)
        // Binary clauses that create an implication chain involving b:
        //   ~a v b   (a -> b)
        //   ~b v c   (b -> c)
        //   a v d    (makes it satisfiable)
        //   ~c v d   (c -> d)
        let mut solver = Solver::new(4);
        let a = Literal::positive(Variable(0));
        let b = Literal::positive(Variable(1));
        let c = Literal::positive(Variable(2));
        let d = Literal::positive(Variable(3));
        solver.add_clause(vec![a.negated(), b]); // ~a v b
        solver.add_clause(vec![b.negated(), c]); // ~b v c
        solver.add_clause(vec![a, d]); // a v d
        solver.add_clause(vec![c.negated(), d]); // ~c v d
        assert!(solver.process_initial_clauses().is_none());
        solver.initialize_watches();
        let _ = solver.propagate();

        // Mark variable b as BVE-eliminated. In real BVE, watch lists would
        // be cleaned, but stale binary entries can remain. The intree enqueue
        // must skip variable b despite it appearing in binary implications.
        solver.var_lifecycle.mark_eliminated(1); // b = var index 1

        // This must NOT panic with "decided removed variable".
        let _unsat = solver.intree_probe();
    }
}
