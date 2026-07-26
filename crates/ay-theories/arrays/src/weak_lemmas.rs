// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! M2/M3: model-based read-over-weak-path array lemma instantiation.
//!
//! Activates the weak-equivalence graph (Christ/Hoenicke, "Weakly Equivalent
//! Arrays") built in `weak_equiv.rs` — previously an M1 *shadow* used only for
//! debug invariants — as a live, lazy, conflict-driven lemma source.
//!
//! ## The lemma (read-over-weak-eq)
//!
//! For two selects `s1 = select(a, i)` and `s2 = select(b, i')` with `i`, `i'`
//! known-equal, if there is a reason-carrying weak path `a … b` whose store
//! labels are `k_1 … k_n`, then `a` and `b` differ at most at those indices, so
//!
//! ```text
//!   (path strong-edge reasons)  ∧  i = i'  ∧  ⋀_m (i ≠ k_m)   ⟹   s1 = s2.
//! ```
//!
//! This is *model-based / lazy*: the pass fires only when the current model
//! makes `s1 ≠ s2` provable (`explain_distinct_if_provable`) — i.e. the implied
//! equality is violated — and emits the conflict clause that negates every
//! justifying reason, exactly as `row2_extended_conflict_lemmas` does for the
//! single-store case. It generalizes that pass from one store hop to an
//! arbitrary weak path, so it catches read-over-weak-eq conflicts the direct
//! store-chain resolution misses.
//!
//! ## Position and budget
//!
//! The pass is a LAST-RESORT BACKSTOP: it runs in `final_check` only after
//! every store-chain ROW2 pass, every specialized store-difference / nested-
//! select / array-equality check, and N-O interface-equality generation have
//! found nothing — i.e. only when the solver is about to declare the model SAT.
//! So it never preempts nor floods them, runs near-zero times, and purely adds
//! conflicts across arbitrary weak paths that direct store-chain resolution
//! misses. It is capped by `WEAK_PATH_LEMMA_BUDGET`:
//! a firing round emits only the few shortest (most general) conflict clauses
//! and lets the solver re-solve, so it can never flood the clause database (an
//! unbounded batch of ~99 lemmas/round, seen when the pass was trialled as the
//! PRIMARY finder, pushed `pointer-safe-5` from an 18s UNSAT into a timeout).
//!
//! It is deliberately NOT the primary array conflict finder: AY's eager
//! store-chain + equality-merge resolution already decides these conflicts at
//! propagation time (more completely, and as a better search driver), so the
//! weak graph leads to no net win as primary and a measured regression when
//! forced there. This pass is the sound completeness net and the lazy-weak-eq
//! (Christ/Hoenicke, z3/SMTInterpol-style) parity capability, kept live.
//!
//! ## Soundness
//!
//! Every emitted clause `¬[diseq(s1,s2) ∧ reasons ∧ (i=i') ∧ ⋀(i≠k_m)]` is a
//! valid array-theory lemma: the bracketed conjunction is unsatisfiable because
//! it forces `s1 = s2` (weak-equivalence-modulo-`i` gives `a[i] = b[i]`, and
//! `i = i'` gives `b[i] = b[i']`) while also asserting `s1 ≠ s2`. Each store
//! label is admitted only when `i ≠ k_m` is *provable* — otherwise a write at
//! the read index could change the value and the path would not imply equality.
//! Reason-free (unexplained) strong edges are never traversed (`weak_path` uses
//! `TraversalMode::Reasoned`), so every reason is a genuine SAT-visible literal.

use super::*;

/// Default per-round cap on emitted read-over-weak-path conflict clauses.
/// Small enough to avoid clause-DB bloat, large enough to make multi-conflict
/// rounds converge without a re-solve per single lemma.
const WEAK_PATH_LEMMA_BUDGET: usize = 8;

impl ArraySolver<'_> {
    /// Per-round lemma budget: the pass returns at most this many of the
    /// *shortest* (most general) conflict clauses each `final_check`, then the
    /// solver re-solves under the new model — bounded lazy instantiation that
    /// makes steady progress without the clause-DB flood an unbounded batch
    /// causes (a primary-position batch of ~99 lemmas/round pushed
    /// `pointer-safe-5` from an 18s UNSAT into a timeout).
    ///
    /// See the module doc for the lemma and its soundness argument. Returns one
    /// conflict clause per distinct model-violated `(select, select)` pair whose
    /// arrays are weakly equivalent modulo the (shared) read index.
    pub(crate) fn read_over_weak_path_conflict_lemmas(&self) -> Vec<TheoryLemma> {
        let candidate_pairs = self.select_conflict_candidate_pairs();
        let mut lemmas = Vec::new();
        let mut seen_clauses = HashSet::default();

        let budget = WEAK_PATH_LEMMA_BUDGET;
        // Bound the WORK, not just the output: once we hold a healthy pool to
        // pick the shortest `budget` clauses from, stop scanning further pairs
        // (each survivor costs a weak-path BFS).
        let pool_cap = budget.saturating_mul(4).max(budget);

        for &(s1, s2) in candidate_pairs.iter() {
            if self.interrupted_or_deadline() {
                break;
            }
            if lemmas.len() >= pool_cap {
                break;
            }
            if s1 == s2 {
                continue;
            }
            let Some(&(a, i1)) = self.select_cache.get(&s1) else {
                continue;
            };
            let Some(&(b, i2)) = self.select_cache.get(&s2) else {
                continue;
            };
            // Same read index (semantically).
            if !self.known_equal(i1, i2) {
                continue;
            }
            // Conflict driver: the selects are provably distinct in the current
            // state, so the implied read-over-weak-eq equality is violated.
            let Some(diseq_reasons) = self.explain_distinct_if_provable(s1, s2) else {
                continue;
            };
            // A reason-carrying weak path a … b: `labels` are the store indices
            // at which a and b may differ; `path_reasons` justify its strong
            // edges. `None` ⇒ not weakly connected through explainable edges.
            let Some((labels, path_reasons)) = self.weak_path(a, b) else {
                continue;
            };

            let mut reasons = diseq_reasons;
            reasons.extend(path_reasons);

            // Bridge the two read indices if they are distinct terms.
            if i1 != i2 {
                let Some(index_eq_reasons) = self.explain_equal_if_provable(i1, i2) else {
                    continue;
                };
                reasons.extend(index_eq_reasons);
            }

            // The read index must provably differ from every store label on the
            // path; otherwise a write at the read index could change the value.
            let mut path_admissible = true;
            for label in labels {
                let Some(neq_reasons) = self.explain_distinct_if_provable(i1, label) else {
                    path_admissible = false;
                    break;
                };
                reasons.extend(neq_reasons);
            }
            if !path_admissible {
                continue;
            }

            Self::canonicalize_theory_lits(&mut reasons);
            if reasons.is_empty() {
                continue;
            }

            // Conflict clause: at least one justifying reason must fail.
            let mut clause: Vec<TheoryLit> = reasons
                .into_iter()
                .map(|lit| TheoryLit::new(lit.term, !lit.value))
                .collect();
            clause.sort_by_key(|lit| (lit.term.0, lit.value));
            clause.dedup_by_key(|lit| (lit.term, lit.value));
            if clause.is_empty() || !seen_clauses.insert(clause.clone()) {
                continue;
            }
            // #lemma-must-prune: skip no-op lemmas (shared discipline with the
            // store-chain ROW2 passes).
            if self.lemma_is_unproductive(&clause) {
                continue;
            }
            lemmas.push(TheoryLemma::new(clause));
        }

        // Lazy budget: keep the shortest (most general — fewest justifying
        // reasons ⇒ tightest weak path) `budget` clauses. A stable sort over
        // the deterministically-ordered candidate scan keeps the result
        // reproducible across runs.
        if lemmas.len() > budget {
            lemmas.sort_by_key(|lemma| lemma.clause.len());
            lemmas.truncate(budget);
        }
        lemmas
    }
}
