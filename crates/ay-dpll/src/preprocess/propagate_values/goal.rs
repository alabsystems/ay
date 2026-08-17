// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Goal-mode value propagation, distinct from the solve-pipeline pass.

use super::*;

impl PropagateValues {
    /// Goal-mode value propagation — the transform behind the
    /// `(apply propagate-values)` tactic surface (z3's `propagate-values`
    /// GOAL semantics, distinct from the solve-pipeline
    /// [`PreprocessingPass::apply`], which must preserve defining equalities
    /// for EUF congruence closure).
    ///
    /// SOUNDNESS CONTRACT: this MUST be **equivalence-preserving** (every model
    /// preserved), not merely equisatisfiable — it also runs on live check-sat
    /// paths (`Z3_mk_solver_from_tactic("propagate-values")`,
    /// `Z3_solver_add_simplifier` and `TacticSolver::check_sat`), and a model
    /// produced after the transform must satisfy the ORIGINAL assertions.
    /// Every step is a conjunction equivalence:
    ///
    /// 1. substitutions are harvested only from top-level conjuncts of the same
    ///    goal — `F ∧ G[E] ≡ F ∧ G[c]` when `F ⊨ E = c` (and `F ∧ G[p] ≡
    ///    F ∧ G[true]` when `F` is the literal `p`);
    /// 2. a conjunct is never rewritten by its own harvest (rewrite BEFORE
    ///    harvest, with a FRESH map per sweep) — so a definition never erases
    ///    itself, while earlier/later definitions do rewrite it (fwd/bwd sweeps);
    /// 3. no substitution under binders (`rewrite` passes `Let`/`Forall`/
    ///    `Exists` through unchanged) — no capture;
    /// 4. map targets are always concrete `Const`s (plus the whole-formula
    ///    `f ↦ true` / `¬g ⇒ g ↦ false` literal rules) — acyclic, strictly
    ///    reducing;
    /// 5. rebuilds go through the canonical folding constructors;
    /// 6. dropping a `true` conjunct and collapsing a conjunction containing
    ///    `false` to `{false}` are equivalences of conjunctions.
    ///
    /// Returns whether the goal changed.
    pub(crate) fn apply_goal(&mut self, terms: &mut TermStore, fs: &mut Vec<TermId>) -> bool {
        let mut changed = false;
        for _round in 0..GOAL_MODE_MAX_ROUNDS {
            let forward = self.goal_sweep(terms, fs, true);
            let backward = self.goal_sweep(terms, fs, false);
            if !(forward || backward) {
                break;
            }
            changed = true;
        }

        // Post-pass (goal semantics, matching z3): a conflict collapses the
        // goal to the single literal `false`; otherwise formulas that folded
        // to `true` are dropped. Both are conjunction equivalences.
        let false_term = terms.false_term();
        let true_term = terms.true_term();
        if fs.contains(&false_term) {
            if fs.as_slice() != [false_term] {
                *fs = vec![false_term];
                changed = true;
            }
        } else {
            let before = fs.len();
            fs.retain(|&f| f != true_term);
            changed |= fs.len() != before;
        }
        changed
    }

    /// One goal-mode sweep (forward or backward) with a FRESH substitution map:
    /// each formula is rewritten under the facts harvested so far in THIS sweep,
    /// then harvested itself. Returns whether any formula changed.
    fn goal_sweep(&mut self, terms: &mut TermStore, fs: &mut [TermId], forward: bool) -> bool {
        // Fresh-state discipline: goal mode deliberately does NOT reuse
        // `reset()` (which preserves `value_map` for the solve pipeline). A
        // fresh map per sweep is what makes "rewrite before harvest" prevent a
        // definition from erasing itself; the rewrite cache is invalidated with
        // it (cache entries are keyed by term only, so they are only valid for
        // one map state). `defining_equalities` is a solve-pipeline concept and
        // is ignored here — in goal mode definers ARE rewritten by other
        // definers (z3 rewrites `(= (f (f 0)) 2)` under `(= (f 0) 1)`).
        self.value_map.clear();
        self.cache.clear();
        let mut changed = false;
        let len = fs.len();
        for step in 0..len {
            let i = if forward { step } else { len - 1 - step };
            let rewritten = self.rewrite(terms, fs[i]);
            if rewritten != fs[i] {
                fs[i] = rewritten;
                changed = true;
            }
            self.harvest_goal_formula(terms, rewritten);
        }
        changed
    }

    /// Harvest the facts an asserted goal formula `f` contributes (z3's
    /// `propagate_values` harvest):
    ///
    /// - `(= a b)` with exactly ONE `Const` side → `expr ↦ const` (NO
    ///   groundness gate in goal mode: `(= x 5)` over a `declare-const` and the
    ///   non-ground `(= (f y) 3)` are both harvested — capture-safe because
    ///   `rewrite` never substitutes under binders);
    /// - `(not g)` → `g ↦ false`;
    /// - any other Bool formula → `f ↦ true` (z3's general literal rule).
    fn harvest_goal_formula(&mut self, terms: &TermStore, f: TermId) {
        // A constant formula (`true`, or the `false` a conflict folded to)
        // contributes no substitution — and `Const` keys are banned from the
        // map (see `insert_goal_value`).
        if Self::is_constant(terms, f) {
            return;
        }
        let true_term = terms.true_term();
        let false_term = terms.false_term();
        match terms.get(f) {
            TermData::App(sym, args) if sym.name() == "=" && args.len() == 2 => {
                let (lhs, rhs) = (args[0], args[1]);
                let lhs_const = Self::is_constant(terms, lhs);
                let rhs_const = Self::is_constant(terms, rhs);
                match (lhs_const, rhs_const) {
                    (false, true) => self.insert_goal_value(terms, lhs, rhs),
                    (true, false) => self.insert_goal_value(terms, rhs, lhs),
                    // Zero (or two — impossible after mk_eq folding) const
                    // sides: still an asserted Bool atom, so the general
                    // `f ↦ true` rule applies.
                    _ => self.insert_goal_value(terms, f, true_term),
                }
            }
            TermData::Not(inner) => self.insert_goal_value(terms, *inner, false_term),
            _ if terms.sort(f) == &Sort::Bool => self.insert_goal_value(terms, f, true_term),
            _ => {}
        }
    }

    /// The single goal-mode map insertion point: record `key ↦ value` and
    /// invalidate the rewrite cache (cache entries are keyed by term only, so
    /// any entry computed under the previous map state may be stale).
    ///
    /// INVARIANT (defensive gate): a `Const` key must NEVER enter `value_map` —
    /// `rewrite` consults the map BEFORE its `Const` pass-through arm, so e.g.
    /// a `true ↦ false` entry (constructible only via a raw `Not(Const)` proof
    /// literal, `mk_not_raw`; `mk_not` folds it away) would rewrite the
    /// constant `true` globally — a wrong-verdict machine.
    fn insert_goal_value(&mut self, terms: &TermStore, key: TermId, value: TermId) {
        if Self::is_constant(terms, key) {
            debug_assert!(
                false,
                "BUG: attempted to insert a Const key into the propagate-values map"
            );
            return;
        }
        if self.value_map.insert(key, value) != Some(value) {
            self.cache.clear();
        }
    }
}
