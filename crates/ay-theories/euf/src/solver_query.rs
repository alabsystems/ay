// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! EUF solver query and utility methods.
//!
//! Term decoding, constant lookups, function application tracking,
//! and equality hashing. Extracted from `solver.rs` to keep each file
//! under 500 lines.

use super::solver::EufSolver;
// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::term::{Constant, Symbol, TermData, TermId};
use ay_core::{Sort, TheoryLit};

impl EufSolver<'_> {
    pub(crate) fn is_builtin_symbol(sym: &Symbol) -> bool {
        matches!(sym.name(), "and" | "or" | "=" | "distinct")
    }

    pub(crate) fn decode_eq(&self, term: TermId) -> Option<(TermId, TermId)> {
        match self.terms.get(term) {
            TermData::App(sym, args) if sym.name() == "=" && args.len() == 2 => {
                Some((args[0], args[1]))
            }
            _ => ay_core::decode_bool_biconditional_eq(self.terms, term),
        }
    }

    pub(crate) fn decode_distinct(&self, term: TermId) -> Option<&[TermId]> {
        match self.terms.get(term) {
            TermData::App(sym, args) if sym.name() == "distinct" => Some(args),
            _ => None,
        }
    }

    /// Check if a term is a constant (Int, Real, BV literal)
    pub(crate) fn is_constant(&self, term: TermId) -> bool {
        matches!(self.terms.get(term), TermData::Const(_))
    }

    /// Find the integer constant value in the same equivalence class as `term`,
    /// if one exists. Used by the Nelson-Oppen interface bridge to evaluate UF
    /// terms like `Succ(x)` when EUF knows `Succ(x) = 1` via congruence. (#5081)
    ///
    /// Returns `(value, const_term_id)` so the caller can build explain reasons.
    pub fn find_int_const_in_class(&self, term: TermId) -> Option<(num_bigint::BigInt, TermId)> {
        // Use E-graph class iteration in incremental mode (O(class_size)),
        // fall back to linear scan over UF in legacy mode (O(|terms|)).
        if !self.enodes_init || (term.0 as usize) >= self.enodes.len() {
            return None;
        }
        let rep = self.enode_find_const(term.0);
        for member in self.enode_class_iter(rep) {
            let tid = TermId(member);
            if let TermData::Const(Constant::Int(n)) = self.terms.get(tid) {
                return Some((n.clone(), tid));
            }
        }
        None
    }

    /// Check whether `a` and `b` are KNOWN-DISEQUAL: some `(= x y)` atom is
    /// asserted false whose two sides currently lie in `a`'s and `b`'s
    /// equivalence classes (in either orientation).
    ///
    /// Used by Nelson-Oppen model-equality discovery to AVOID proposing a model
    /// equality `(= a b)` for a pair the EUF theory has already pinned disequal
    /// (e.g. `(not (= (f x) (f y)))`). Proposing such an equality is futile — the
    /// SAT solver can never satisfy it — and it masks the disequality/expression
    /// split that actually constrains the arithmetic theory. Letting those pairs
    /// fall through to the split path is required for pigeonhole reasoning over
    /// bounded UF-result terms (#wrong-sat uflia_deep family). (#9701)
    ///
    /// Sound: only returns `true` when an actually-asserted disequality witnesses
    /// `a != b`; never invents a disequality.
    pub fn are_known_disequal(&self, a: TermId, b: TermId) -> bool {
        if a == b || !self.enodes_init {
            return false;
        }
        if (a.0 as usize) >= self.enodes.len() || (b.0 as usize) >= self.enodes.len() {
            return false;
        }
        let rep_a = self.enode_find_const(a.0);
        let rep_b = self.enode_find_const(b.0);
        if rep_a == rep_b {
            // Same class — cannot be (validly) disequal; EUF would already
            // have a conflict. Report not-disequal here.
            return false;
        }
        for (&eq_term, &value) in &self.assigns {
            if value {
                continue;
            }
            let Some((x, y)) = self.decode_eq(eq_term) else {
                continue;
            };
            if (x.0 as usize) >= self.enodes.len() || (y.0 as usize) >= self.enodes.len() {
                continue;
            }
            let rep_x = self.enode_find_const(x.0);
            let rep_y = self.enode_find_const(y.0);
            if (rep_x == rep_a && rep_y == rep_b) || (rep_x == rep_b && rep_y == rep_a) {
                return true;
            }
        }
        false
    }

    /// Build a map from TermId → (integer_value, constant_term_id) for all terms
    /// in equivalence classes that contain an integer constant. Single-pass O(n)
    /// construction, used by the Nelson-Oppen bridge to evaluate UF subterms. (#5081)
    pub fn build_int_value_map(&self) -> HashMap<TermId, (num_bigint::BigInt, TermId)> {
        // Pass 1: find the integer constant for each representative (if any).
        let mut rep_to_const: HashMap<u32, (num_bigint::BigInt, TermId)> = HashMap::default();
        for tid in self.terms.term_ids() {
            if let TermData::Const(Constant::Int(val)) = self.terms.get(tid) {
                let rep = self.enode_find_const(tid.0);
                rep_to_const
                    .entry(rep)
                    .or_insert_with(|| (val.clone(), tid));
            }
        }
        if rep_to_const.is_empty() {
            return HashMap::default();
        }
        // Pass 2: for each non-constant term, check if its representative has a constant.
        let mut result = HashMap::default();
        for tid in self.terms.term_ids() {
            if matches!(self.terms.get(tid), TermData::Const(Constant::Int(_))) {
                continue; // Skip constants themselves
            }
            let rep = self.enode_find_const(tid.0);
            if let Some(entry) = rep_to_const.get(&rep) {
                result.insert(tid, entry.clone());
            }
        }
        result
    }

    /// Check if a term is a UF function application (not a builtin) returning a theory sort
    pub(crate) fn is_theory_func_app(&self, term: TermId) -> bool {
        match self.terms.get(term) {
            TermData::App(sym, args) if !Self::is_builtin_symbol(sym) && !args.is_empty() => {
                // Check return sort is a theory sort (Int, Real, BV, Seq).
                // Seq (#uf-app-value-seq): a Seq-returning UF app has no atomic
                // model element, so the evaluator can only resolve it through a
                // tracked `(= (f x) t)` value — without one, a datatype-field =
                // UF-projection equality over `(Seq Int)` is unevaluable and the
                // self-check degrades a genuine sat to unknown (9227).
                let sort = self.terms.sort(term);
                matches!(
                    sort,
                    Sort::Int | Sort::Real | Sort::BitVec(_) | Sort::Seq(_)
                )
            }
            _ => false,
        }
    }

    /// Track function application value when processing (= func_app constant).
    pub(crate) fn try_track_func_app_value(&mut self, eq_term: TermId) {
        // `mem::take`/restore lets the shared body read `&self` while writing
        // the (moved-out, hence local) destination map — negligible cost (a
        // 3-word Vec/Map header move), and it keeps this logic in ONE place
        // shared with the in-place `resync_func_app_values_from_assigns` loop.
        let mut out = std::mem::take(&mut self.func_app_values);
        self.track_func_app_value_into(eq_term, &mut out);
        self.func_app_values = out;
    }

    /// Shared body of func-app-value tracking: if `eq_term` is an asserted-true
    /// `(= func_app constant/var)` equality, record `func_app -> partner` in
    /// `out`. Reads ONLY immutable solver state and writes the caller-owned
    /// `out` map, so a caller can iterate `self.assigns` in place and pass a
    /// moved-out map without a borrow conflict.
    pub(crate) fn track_func_app_value_into(
        &self,
        eq_term: TermId,
        out: &mut HashMap<TermId, TermId>,
    ) {
        // Fast out for pure QF_UF (and any instance with no Int/Real/BV func
        // apps): `func_app_values` can never be populated, so the per-assignment
        // decode_eq + is_theory_func_app work below is pure waste. Skipping it
        // keeps `out` empty — identical to running the full body, which never
        // inserts when no theory func app exists.
        if !self.has_theory_func_apps {
            return;
        }
        if let Some((lhs, rhs)) = self.decode_eq(eq_term) {
            // Check both directions: (= func_app value) and (= value func_app).
            // The partner may be a CONSTANT or a VARIABLE (#uf-app-value-seq):
            // the map records "this app equals this term in the model", and the
            // evaluator resolves the partner itself — a variable partner is
            // exactly the verification-consumer `(= (buckets old_self) (logic_field_buckets
            // old_self))` shape. Sound: the equality is ASSERTED TRUE, so any
            // model must interpret the two sides identically; recording it only
            // ADDS a resolution the evaluator otherwise lacks (Unknown). A
            // partner that cycles back through the same app is broken by the
            // evaluator's re-entrancy guard (fail-closed Unknown).
            let partner_ok = |this: &Self, t: TermId| {
                this.is_constant(t) || matches!(this.terms.get(t), TermData::Var(..))
            };
            let (func_app, constant) = if self.is_theory_func_app(lhs) && partner_ok(self, rhs) {
                (lhs, rhs)
            } else if self.is_theory_func_app(rhs) && partner_ok(self, lhs) {
                (rhs, lhs)
            } else {
                return;
            };

            // Only record if we don't already have a value for this func_app
            if !out.contains_key(&func_app) {
                out.insert(func_app, constant);
            }
        }
    }

    /// Rebuild tracked UF application values from the currently asserted literals.
    /// Needed after incremental pop(), which clears derived state but does not
    /// force a full rebuild before callers may extract a model.
    pub(crate) fn resync_func_app_values_from_assigns(&mut self) {
        // Pure QF_UF (no Int/Real/BV func apps): `func_app_values` can never be
        // populated, so the whole scan is dead work — clear and return.
        if !self.has_theory_func_apps {
            self.func_app_values.clear();
            return;
        }
        // Iterate the assignments IN PLACE instead of materializing every
        // true-valued term into a fresh `Vec` first. The old
        // `.collect::<Vec<_>>()` existed only to break the `&self` / `&mut self`
        // borrow so `try_track_func_app_value` could be called in the loop; on
        // the giant backtrack-heavy Certora QF_UFLIA files (|assigns| ~ 10^5)
        // that per-pop `from_iter` allocation-and-fill profiled at ~6.5% of
        // solve self-time (#euf-resync-inplace). `track_func_app_value_into`
        // reads only immutable state and writes the moved-out `out` map, so the
        // loop can hold an immutable borrow of `self.assigns` alongside the
        // immutable `&self` queries with no conflict and no allocation. Same
        // map contents in the same insertion order (identical `self.assigns`
        // iteration order) — byte-identical to the previous rebuild.
        let mut out = std::mem::take(&mut self.func_app_values);
        out.clear();
        for (&term, &value) in &self.assigns {
            if value {
                self.track_func_app_value_into(term, &mut out);
            }
        }
        self.func_app_values = out;
    }

    /// Helper to create a canonical edge key (smaller id first)
    pub(crate) fn edge_key(a: u32, b: u32) -> (u32, u32) {
        if a < b {
            (a, b)
        } else {
            (b, a)
        }
    }

    /// Internal method to collect disequalities for `propagate_equalities()` (#8469).
    ///
    /// Uses the registered `shared_arith_terms` and internal `propagated_diseq_pairs`
    /// tracking. Respects the merge_epoch dirty tracking to skip re-scanning when
    /// no new merges have occurred since the last scan.
    ///
    /// Fine-grained dirty tracking (#8471): when the epoch differs, instead of
    /// scanning ALL negated equality assignments, only process:
    /// (a) false_eqs whose `rep_a` or `rep_b` is in `dirty_merge_reps` (classes
    ///     that changed via merges), and
    /// (b) newly asserted negated equalities from `new_negated_eqs`.
    /// This reduces the per-iteration cost from O(|false_eqs| * |class|^2) to
    /// O(|dirty_false_eqs| * |class|^2) where |dirty_false_eqs| << |false_eqs|
    /// in typical N-O fixpoint iterations.
    ///
    /// This is the single unified disequality propagation path. EUF-implied
    /// disequalities flow through `propagate_equalities()` -> this method ->
    /// `EqualityPropagationResult.disequalities`, which `propagate_all_to()`
    /// forwards to the target theory. The old separate
    /// `collect_implied_disequalities()` API is retained for backward
    /// compatibility but delegates here.
    pub(crate) fn collect_disequalities_for_propagation(
        &mut self,
    ) -> Vec<ay_core::DiscoveredDisequality> {
        // Dirty tracking (#8469, #8471): skip if no class merges since last scan.
        // This avoids the O(|false_eqs| * |shared_terms|^2) cost when the E-graph
        // has not changed. The epoch is reset on pop() so that post-backtrack
        // scanning re-discovers disequalities for the restored state.
        if self.diseq_scan_epoch == self.merge_epoch {
            return Vec::new();
        }
        self.diseq_scan_epoch = self.merge_epoch;

        if !self.enodes_init || self.shared_arith_terms.is_empty() {
            // Drain dirty state even when skipping (#8471).
            self.dirty_merge_reps.clear();
            self.new_negated_eqs.clear();
            return Vec::new();
        }

        // Build representative -> shared terms map.
        let mut rep_to_shared: HashMap<u32, Vec<TermId>> = HashMap::default();
        for i in 0..self.shared_arith_terms.len() {
            let term = self.shared_arith_terms[i];
            if (term.0 as usize) >= self.enodes.len() {
                continue;
            }
            let rep = self.enode_find_const(term.0);
            rep_to_shared.entry(rep).or_default().push(term);
        }

        let mut result = Vec::new();

        // #8471 Fine-grained dirty tracking: collect the dirty state and
        // determine whether we can use the incremental path.
        // Take ownership of dirty_merge_reps and new_negated_eqs to avoid
        // borrow conflicts during the scan loop.
        let dirty_reps = std::mem::take(&mut self.dirty_merge_reps);
        let new_negs = std::mem::take(&mut self.new_negated_eqs);

        // Use incremental path when we have dirty tracking data and the
        // propagated_diseq_pairs set is non-empty (meaning we've done at
        // least one full scan before).
        let use_incremental = !self.propagated_diseq_pairs.is_empty()
            && (!dirty_reps.is_empty() || !new_negs.is_empty());

        if use_incremental {
            // Incremental path: only scan false_eqs involving dirty reps
            // or newly asserted negated equalities.

            // First: process newly asserted negated equalities directly.
            // These are guaranteed new and need processing regardless of
            // whether their reps are dirty. Build a set for O(1) dedup
            // lookups against the existing false_eqs loop below.
            let new_neg_terms: HashSet<TermId> = new_negs.iter().map(|&(t, _, _)| t).collect();
            for &(eq_term, a, b) in &new_negs {
                self.process_false_eq_for_diseq(eq_term, a, b, &rep_to_shared, &mut result);
            }

            // Second: scan existing false_eqs whose rep_a or rep_b
            // overlaps with a dirty representative. A merge of reps R1
            // and R2 means any false_eq whose terms map to the new
            // combined class (which has representative R2 after merge)
            // may now have new shared-term pairs.
            //
            // We need to check reps that ARE dirty or whose current rep
            // was formed by merging a dirty rep. Since merges always
            // produce a new rep that is one of the two old reps, checking
            // the current rep against dirty_reps catches this.
            if !dirty_reps.is_empty() {
                let false_eqs: Vec<(TermId, TermId, TermId)> = self
                    .assigns
                    .iter()
                    .filter(|(_, &v)| !v)
                    .filter_map(|(&eq_term, _)| {
                        let (a, b) = self.decode_eq(eq_term)?;
                        Some((eq_term, a, b))
                    })
                    .collect();

                for (eq_term, a, b) in false_eqs {
                    // Skip new negated eqs already processed above.
                    if new_neg_terms.contains(&eq_term) {
                        continue;
                    }
                    if (a.0 as usize) >= self.enodes.len() || (b.0 as usize) >= self.enodes.len() {
                        continue;
                    }
                    let rep_a = self.enode_find_const(a.0);
                    let rep_b = self.enode_find_const(b.0);

                    // Only process if at least one rep is dirty.
                    if !dirty_reps.contains(&rep_a) && !dirty_reps.contains(&rep_b) {
                        continue;
                    }

                    self.process_false_eq_for_diseq(eq_term, a, b, &rep_to_shared, &mut result);
                }
            }
        } else {
            // Full scan path: first time or after pop()/reset().
            // Process all negated equalities.
            let false_eqs: Vec<(TermId, TermId, TermId)> = self
                .assigns
                .iter()
                .filter(|(_, &v)| !v)
                .filter_map(|(&eq_term, _)| {
                    let (a, b) = self.decode_eq(eq_term)?;
                    Some((eq_term, a, b))
                })
                .collect();

            for (eq_term, a, b) in false_eqs {
                self.process_false_eq_for_diseq(eq_term, a, b, &rep_to_shared, &mut result);
            }
        }

        result
    }

    /// Process a single negated equality for disequality propagation.
    /// Extracted from the main scan loop for reuse in both full and
    /// incremental paths (#8471).
    fn process_false_eq_for_diseq(
        &mut self,
        eq_term: TermId,
        a: TermId,
        b: TermId,
        rep_to_shared: &HashMap<u32, Vec<TermId>>,
        result: &mut Vec<ay_core::DiscoveredDisequality>,
    ) {
        if self.terms.sort(a) != self.terms.sort(b) {
            return;
        }
        if (a.0 as usize) >= self.enodes.len() || (b.0 as usize) >= self.enodes.len() {
            return;
        }

        let rep_a = self.enode_find_const(a.0);
        let rep_b = self.enode_find_const(b.0);
        if rep_a == rep_b {
            // Same class -- contradicts the disequality, skip (EUF will handle).
            return;
        }

        let Some(terms_a) = rep_to_shared.get(&rep_a) else {
            return;
        };
        let Some(terms_b) = rep_to_shared.get(&rep_b) else {
            return;
        };

        for &c in terms_a {
            for &d in terms_b {
                if c == d {
                    continue;
                }
                let key = if c < d { (c, d) } else { (d, c) };
                if !self.propagated_diseq_pairs.insert(key) {
                    continue;
                }

                let mut reason = vec![TheoryLit::new(eq_term, false)];
                if c != a {
                    reason.extend(self.explain(a, c));
                }
                if d != b {
                    reason.extend(self.explain(b, d));
                }
                reason.sort_unstable_by_key(|l| (l.term.0, l.value));
                reason.dedup_by_key(|l| (l.term.0, l.value));

                result.push(ay_core::DiscoveredDisequality::new(c, d, reason));
            }
        }
    }

    /// Collect disequalities implied by EUF's congruence closure for Nelson-Oppen
    /// cross-theory propagation (#8163).
    ///
    /// When EUF knows `a != b` (a negated equality assignment) and shared terms
    /// `c` (in `a`'s equivalence class) and `d` (in `b`'s class) exist, then
    /// `c != d` must hold and should be propagated to the arithmetic solver.
    ///
    /// The `already_propagated` set tracks canonical `(min, max)` TermId pairs
    /// to avoid re-propagating the same disequality in subsequent fixpoint
    /// iterations.
    ///
    /// **Backward compatibility wrapper.** The preferred path is
    /// `propagate_equalities()` which calls `collect_disequalities_for_propagation()`
    /// internally using `shared_arith_terms`. This method is retained for
    /// callers that supply their own shared term set and dedup set.
    pub fn collect_implied_disequalities(
        &mut self,
        shared_terms: &[TermId],
        already_propagated: &mut HashSet<(TermId, TermId)>,
    ) -> Vec<DiscoveredDisequality> {
        // Dirty tracking (#8471): skip if no class merges since last scan.
        if self.diseq_scan_epoch == self.merge_epoch {
            return Vec::new();
        }
        self.diseq_scan_epoch = self.merge_epoch;

        if !self.enodes_init || shared_terms.is_empty() {
            return Vec::new();
        }

        // Build representative -> shared terms map.
        let mut rep_to_shared: HashMap<u32, Vec<TermId>> = HashMap::default();
        for &term in shared_terms {
            if (term.0 as usize) >= self.enodes.len() {
                continue;
            }
            let rep = self.enode_find_const(term.0);
            rep_to_shared.entry(rep).or_default().push(term);
        }

        let mut result = Vec::new();

        // Collect negated equalities (disequalities) from current EUF assignments.
        let false_eqs: Vec<(TermId, TermId, TermId)> = self
            .assigns
            .iter()
            .filter(|(_, &v)| !v)
            .filter_map(|(&eq_term, _)| {
                let (a, b) = self.decode_eq(eq_term)?;
                Some((eq_term, a, b))
            })
            .collect();

        for (eq_term, a, b) in false_eqs {
            // Only propagate disequalities for same-sort terms.
            if self.terms.sort(a) != self.terms.sort(b) {
                continue;
            }
            if (a.0 as usize) >= self.enodes.len() || (b.0 as usize) >= self.enodes.len() {
                continue;
            }

            let rep_a = self.enode_find_const(a.0);
            let rep_b = self.enode_find_const(b.0);
            if rep_a == rep_b {
                // Same class -- contradicts the disequality, skip (EUF will handle).
                continue;
            }

            let Some(terms_a) = rep_to_shared.get(&rep_a) else {
                continue;
            };
            let Some(terms_b) = rep_to_shared.get(&rep_b) else {
                continue;
            };

            for &c in terms_a {
                for &d in terms_b {
                    if c == d {
                        continue;
                    }
                    let key = if c < d { (c, d) } else { (d, c) };
                    if !already_propagated.insert(key) {
                        continue;
                    }

                    // Build reason: negated equality + congruence chains.
                    let mut reason = vec![TheoryLit::new(eq_term, false)];
                    if c != a {
                        reason.extend(self.explain(a, c));
                    }
                    if d != b {
                        reason.extend(self.explain(b, d));
                    }
                    reason.sort_unstable_by_key(|l| (l.term.0, l.value));
                    reason.dedup_by_key(|l| (l.term.0, l.value));

                    result.push(DiscoveredDisequality {
                        lhs: c,
                        rhs: d,
                        reason,
                    });
                }
            }
        }

        result
    }
}

/// A disequality discovered by EUF for Nelson-Oppen cross-theory propagation (#8163).
pub struct DiscoveredDisequality {
    /// Left-hand side of the implied disequality.
    pub lhs: TermId,
    /// Right-hand side of the implied disequality.
    pub rhs: TermId,
    /// Reason literals justifying `lhs != rhs` (negated equality + congruence chains).
    pub reason: Vec<TheoryLit>,
}
