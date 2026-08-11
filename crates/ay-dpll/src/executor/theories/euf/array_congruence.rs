// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Array congruence axiom generation: structural, value, other-side, and disjunctive index.
//!
//! Extracted from `array_patterns.rs` as part of code-health module split.
//! These methods manage the incremental congruence cache and generate axioms
//! connecting store/select operations across array equalities.

use super::super::super::Executor;
// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::{Sort, TermData, TermId};

impl Executor {
    /// Add array congruence axioms: if `(= a b)` where a, b are array-sorted,
    /// then for every `store(a, i, v)` add `¬(= a b) ∨ (= store(a,i,v) store(b,i,v))`,
    /// and for every `select(a, k)` add `¬(= a b) ∨ (= select(a,k) select(b,k))`.
    ///
    /// This ensures that when the SAT solver sets an array equality to true, the
    /// consequences propagate to all store/select operations over those arrays.
    /// Without this, the eager bit-blasting path treats `(= a b)` as an opaque atom
    /// with no connection to store(a,...) vs store(b,...) terms (#5116, #5083).
    pub(in crate::executor) fn add_array_congruence_axioms(&mut self) {
        let should_stop = self.make_should_stop();

        // Pass 1: collect array equality pairs and array-operation terms.
        let mut array_eq_pairs: Vec<(TermId, TermId, TermId)> = Vec::new(); // (eq_term, lhs, rhs)
        let mut store_by_base: HashMap<TermId, Vec<(TermId, TermId, TermId)>> = HashMap::default(); // base -> [(store_term, idx, val)]
        let mut select_by_base: HashMap<TermId, Vec<(TermId, TermId)>> = HashMap::default(); // base -> [(select_term, idx)]

        for idx in 0..self.ctx.terms.len() {
            let term = TermId(idx as u32);
            if !self.term_in_array_scope(term) {
                continue;
            }
            if let TermData::App(ref sym, ref args) = self.ctx.terms.get(term).clone() {
                match sym.name() {
                    "=" if args.len() == 2 => {
                        // BOTH sides, not just the left. Every consumer of
                        // `array_eq_pairs` builds `select(other, k)` /
                        // `store(other, i, v)` from the OPPOSITE side of the
                        // equality, which is well-sorted only if that side is an
                        // array of the same sort. Checking `args[0]` alone let an
                        // `(= t:Array u:Int)` pair through; `mk_select` on a
                        // non-array falls back to `Bool`, so the congruence builder
                        // then called `mk_eq(Int, Bool)` and tripped
                        // `BUG: mk_eq expects same sort` — killing the entire solve
                        // with `(:reason-unknown "internal solver error")`.
                        if matches!(self.ctx.terms.sort(args[0]), Sort::Array(..))
                            && self.ctx.terms.sort(args[0]) == self.ctx.terms.sort(args[1])
                        {
                            array_eq_pairs.push((term, args[0], args[1]));
                        }
                    }
                    "store" if args.len() == 3 => {
                        store_by_base
                            .entry(args[0])
                            .or_default()
                            .push((term, args[1], args[2]));
                    }
                    "select" if args.len() == 2 => {
                        select_by_base
                            .entry(args[0])
                            .or_default()
                            .push((term, args[1]));
                    }
                    _ => {}
                }
            }
        }

        if array_eq_pairs.is_empty() {
            tracing::debug!(
                selects = select_by_base.len(),
                stores = store_by_base.len(),
                "add_array_congruence_axioms: no array equality pairs found"
            );
            return;
        }
        tracing::debug!(
            eq_pairs = array_eq_pairs.len(),
            selects = select_by_base.len(),
            stores = store_by_base.len(),
            "add_array_congruence_axioms: processing"
        );

        // Pass 2: for each array equality, generate congruence axioms.
        let mut seen_pairs: HashSet<(TermId, TermId)> = HashSet::default();
        for (eq_term, lhs, rhs) in &array_eq_pairs {
            if should_stop() {
                return;
            }
            let pair = if lhs < rhs {
                (*lhs, *rhs)
            } else {
                (*rhs, *lhs)
            };
            if !seen_pairs.insert(pair) {
                continue;
            }

            let not_eq = self.ctx.terms.mk_not(*eq_term);

            // Store congruence: store(lhs, i, v) ↔ store(rhs, i, v) under equality.
            // For each store(lhs, i, v), create store(rhs, i, v) and assert congruence.
            // Also do the reverse direction (stores on rhs).
            for (base, other) in [(*lhs, *rhs), (*rhs, *lhs)] {
                if let Some(stores) = store_by_base.get(&base) {
                    for &(_store_term, store_idx, store_val) in stores {
                        let other_store = self.ctx.terms.mk_store(other, store_idx, store_val);
                        let store_eq = self.ctx.terms.mk_eq(_store_term, other_store);
                        // ¬(= a b) ∨ (= store(a,i,v) store(b,i,v))
                        let axiom = self.ctx.terms.mk_or(vec![not_eq, store_eq]);
                        self.push_array_axiom_assertion_site(axiom, "array_cong_store");
                    }
                }
            }

            // Select congruence: select(lhs, k) = select(rhs, k) under equality.
            //
            // #8596: Skip pairs where the `other` side is a store term.
            // When `other = store(base, i, v)`, mk_select(other, k) creates
            // select(store(base, i, v), k), which expand_select_store converts
            // to ite(i=k, v, select(base, k)). After lift_arithmetic_ite, the
            // equality becomes ite(i=k, select(a,k)=v, select(a,k)=select(base,k)).
            // The Tseitin encoding of this ITE creates clauses that force
            // select(a,k)=select(base,k) when i!=k, which combined with the
            // original assertion select(a,k)=1, can create a false UNSAT:
            // the SAT solver's default phase assigns both select(a,k)=1 and
            // select(a,k)=0 as true (no bound axiom connects them), and the
            // LIA solver sees contradictory bounds.
            //
            // This is safe because add_store_value_congruence_axioms and
            // add_store_other_side_congruence_axioms already handle the
            // store-equality case with explicit disjunctions:
            //   NOT(eq) OR (= store_value select(other, store_index))
            //   NOT(eq) OR (= i k) OR (= select(base, k) select(other, k))
            // These produce proper OR-clauses (not ITEs) that the SAT solver
            // can case-split on correctly.
            for (base, other) in [(*lhs, *rhs), (*rhs, *lhs)] {
                // Skip when `other` is a store term — store congruence axioms
                // handle this case without creating problematic ITE terms.
                let other_is_store = matches!(
                    self.ctx.terms.get(other),
                    TermData::App(ref sym, ref args) if sym.name() == "store" && args.len() == 3
                );
                if other_is_store {
                    continue;
                }
                if let Some(selects) = select_by_base.get(&base) {
                    for &(_select_term, sel_idx) in selects {
                        let other_select = self.ctx.terms.mk_select(other, sel_idx);
                        let select_eq = self.ctx.terms.mk_eq(_select_term, other_select);
                        // ¬(= a b) ∨ (= select(a,k) select(b,k))
                        let axiom = self.ctx.terms.mk_or(vec![not_eq, select_eq]);
                        self.push_array_axiom_assertion_site(axiom, "array_cong_select");
                    }
                }
            }
        }
    }

    #[inline]
    pub(super) fn reset_array_congruence_caches(&mut self) {
        self.cached_store_eqs.clear();
        self.store_eq_scan_hwm = 0;
        self.cached_select_indices_by_array.clear();
        self.select_index_scan_hwm = 0;
    }

    /// Refresh the incremental store/select caches used by eager array
    /// congruence. Terms are append-only during a fixpoint, so scanning only
    /// the suffix above each high-water mark is enough to pick up newly
    /// interned selects created by earlier congruence rounds.
    fn refresh_array_congruence_caches(&mut self) {
        let mut directly_negated_store_eqs: HashSet<TermId> = HashSet::default();
        for &assertion in &self.ctx.assertions {
            let TermData::Not(inner) = self.ctx.terms.get(assertion) else {
                continue;
            };
            let TermData::App(sym, args) = self.ctx.terms.get(*inner) else {
                continue;
            };
            if sym.name() != "=" || args.len() != 2 {
                continue;
            }
            let lhs_is_store = matches!(
                self.ctx.terms.get(args[0]),
                TermData::App(store_sym, store_args)
                    if store_sym.name() == "store" && store_args.len() == 3
            );
            let rhs_is_store = matches!(
                self.ctx.terms.get(args[1]),
                TermData::App(store_sym, store_args)
                    if store_sym.name() == "store" && store_args.len() == 3
            );
            if lhs_is_store || rhs_is_store {
                directly_negated_store_eqs.insert(*inner);
            }
        }

        let current_len = self.ctx.terms.len();
        for idx in self.store_eq_scan_hwm..current_len {
            let term_id = TermId(idx as u32);
            if !self.term_in_array_scope(term_id) {
                continue;
            }
            // A top-level `(assert (not (= store(...) ...)))` already fixes the
            // store equality to false. Eagerly caching it here only manufactures
            // guarded congruence clauses off a dead equality branch, which is
            // both redundant and a known bad interaction on storecomm_invalid
            // direct-disequality repros.
            if directly_negated_store_eqs.contains(&term_id) {
                continue;
            }
            if let TermData::App(sym, args) = self.ctx.terms.get(term_id) {
                if sym.name() == "=" && args.len() == 2 {
                    let lhs = args[0];
                    let rhs = args[1];
                    // Both sides must carry the SAME sort before either can seed a
                    // store-congruence entry.
                    //
                    // `add_store_value_congruence_axioms` builds
                    // `select(other_side, store_index)` and equates it with the
                    // store's VALUE. That is well-sorted only if `other_side` is an
                    // array of the store's sort. Nothing established that here, and
                    // a term store reached by this scan can hold an `App("=", [a, b])`
                    // whose sides disagree — `mk_select` on a non-array falls back to
                    // `Bool`, so the builder then called `mk_eq(Int, Bool)` and hit
                    // `BUG: mk_eq expects same sort`, killing the whole solve with
                    // `(:reason-unknown "internal solver error")`.
                    //
                    // Measured on the `qf_auflia_shadowed_store_value_requires_
                    // distinct_outer_index_8871` repro: the entry was
                    // `(= t4:Int t54:Array(Int,Int))`, giving `sel:Bool` against
                    // `store_value:Int`.
                    //
                    // Skipping such an entry loses nothing: an axiom relating a
                    // store's value to a `select` of a non-array is meaningless, so
                    // the only thing this suppresses is the crash.
                    if self.ctx.terms.sort(lhs) != self.ctx.terms.sort(rhs) {
                        continue;
                    }
                    if let TermData::App(lsym, largs) = self.ctx.terms.get(lhs) {
                        if lsym.name() == "store" && largs.len() == 3 {
                            self.cached_store_eqs
                                .push((term_id, largs[0], largs[1], largs[2], rhs));
                        }
                    }
                    if let TermData::App(rsym, rargs) = self.ctx.terms.get(rhs) {
                        if rsym.name() == "store" && rargs.len() == 3 {
                            self.cached_store_eqs
                                .push((term_id, rargs[0], rargs[1], rargs[2], lhs));
                        }
                    }
                }
            }
        }
        self.store_eq_scan_hwm = current_len;

        for idx in self.select_index_scan_hwm..current_len {
            let term_id = TermId(idx as u32);
            if !self.term_in_array_scope(term_id) {
                continue;
            }
            if let TermData::App(sym, args) = self.ctx.terms.get(term_id) {
                if sym.name() == "select" && args.len() == 2 {
                    self.cached_select_indices_by_array
                        .entry(args[0])
                        .or_default()
                        .push(args[1]);
                }
            }
        }
        self.select_index_scan_hwm = current_len;
    }

    pub(in crate::executor) fn add_store_value_congruence_axioms(&mut self) {
        self.refresh_array_congruence_caches();
        let should_stop = self.make_should_stop();

        let store_eqs = self.cached_store_eqs.clone();
        for (eq_term, store_base, store_index, store_value, other_side) in store_eqs {
            if should_stop() {
                return;
            }
            let not_eq = self.ctx.terms.mk_not(eq_term);

            // Value congruence: ¬eq ∨ (= store_value select(other_side, store_index))
            let sel = self.ctx.terms.mk_select(other_side, store_index);
            let val_eq = self.ctx.terms.mk_eq(store_value, sel);
            let val_axiom = self.ctx.terms.mk_or(vec![not_eq, val_eq]);
            self.push_array_axiom_assertion_site(val_axiom, "store_value_cong");

            // Base congruence: for each select(store_base, k) in the term store,
            // add ¬eq ∨ (= store_index k) ∨ (= select(store_base, k) select(other_side, k))
            if let Some(indices) = self
                .cached_select_indices_by_array
                .get(&store_base)
                .cloned()
            {
                for sel_index in indices {
                    if sel_index == store_index {
                        continue; // Handled by value congruence
                    }
                    let idx_eq = self.ctx.terms.mk_eq(store_index, sel_index);
                    let base_sel = self.ctx.terms.mk_select(store_base, sel_index);
                    let other_sel = self.ctx.terms.mk_select(other_side, sel_index);
                    let sel_eq = self.ctx.terms.mk_eq(base_sel, other_sel);
                    let base_axiom = self.ctx.terms.mk_or(vec![not_eq, idx_eq, sel_eq]);
                    self.push_array_axiom_assertion_site(base_axiom, "store_base_cong");
                }
            }

            // NOTE: Other-side congruence (selects from other_side -> store_base)
            // is NOT done here because it creates select(store, k) terms that
            // cause add_array_row_lemmas() to diverge in DPLL(T) paths.
            // The DPLL(T) theory solver handles this case lazily.
            // For eager paths (solve_abv), see add_store_other_side_congruence_axioms().
        }
    }

    /// Add other-side store congruence axioms (#5083, #4304).
    ///
    /// For every `(= store(a,i,v) T)` and every `select(T, k)` in the term store,
    /// add: `¬(= store(a,i,v) T) ∨ (= i k) ∨ (= select(T, k) select(a, k))`
    ///
    /// This connects selects from the "other side" of a store equality to the
    /// store chain. Without this, `select(mem_b, k)` is unconstrained even when
    /// `mem_b = store(a, i, v)`.
    ///
    /// Used in both eager bit-blasting (solve_abv) and DPLL(T) QF_AX paths.
    /// For QF_AX, this runs inside a fixpoint loop with store-value congruence
    /// and ROW lemmas; the fixpoint terminates because new terms decrease in
    /// nesting depth (ROW2 peels one store layer per iteration).
    pub(in crate::executor) fn add_store_other_side_congruence_axioms(&mut self) {
        self.refresh_array_congruence_caches();
        let should_stop = self.make_should_stop();

        let store_eqs = self.cached_store_eqs.clone();
        for (eq_term, store_base, store_index, _store_value, other_side) in store_eqs {
            if should_stop() {
                return;
            }
            let not_eq = self.ctx.terms.mk_not(eq_term);

            if let Some(indices) = self
                .cached_select_indices_by_array
                .get(&other_side)
                .cloned()
            {
                for sel_index in indices {
                    if sel_index == store_index {
                        continue; // Handled by value congruence
                    }
                    let idx_eq = self.ctx.terms.mk_eq(store_index, sel_index);
                    let other_sel = self.ctx.terms.mk_select(other_side, sel_index);
                    let base_sel = self.ctx.terms.mk_select(store_base, sel_index);
                    let sel_eq = self.ctx.terms.mk_eq(other_sel, base_sel);
                    let axiom = self.ctx.terms.mk_or(vec![not_eq, idx_eq, sel_eq]);
                    self.push_array_axiom_assertion_site(axiom, "store_other_side_cong");
                }
            }
        }
    }

    /// Add disjunctive store-index axioms for same-base store equalities (#5086).
    ///
    /// When two store terms with the same base are equal to the same target:
    ///   `store(a, x, v) = T` and `store(a, y, w) = T`
    ///
    /// the theory of arrays entails:
    ///   `x = y` OR `a = T`
    ///
    /// Proof: if `x ≠ y`, then from `store(a,x,v) = store(a,y,w)`:
    ///   - ROW2 at index x: `v = select(a, x)` (the store at y doesn't affect x)
    ///   - ROW2 at index y: `w = select(a, y)` (the store at x doesn't affect y)
    ///   - So both stores are self-stores: `store(a,x,v) = a` and `store(a,y,w) = a`
    ///   - Therefore `a = T`.
    ///
    /// We encode this as:
    ///   `¬(store(a,x,v) = T) ∨ ¬(store(a,y,w) = T) ∨ (x = y) ∨ (a = T)`
    ///
    /// This is needed for benchmarks like `array_incompleteness1.smt2` that require
    /// propagating a disjunction of equalities between shared terms.
    pub(in crate::executor) fn add_store_disjunctive_index_axioms(&mut self) {
        // #6820: Reuse cached store-eq tuples. The hwm scan in
        // add_store_value_congruence_axioms already ran this round.
        // Cached tuple: (eq_term, store_base, store_index, store_value, other_side)
        // We need: eq_term, store_base, store_index, other_side (store_value unused here).
        self.refresh_array_congruence_caches();
        let should_stop = self.make_should_stop();
        let store_eqs = self.cached_store_eqs.clone();

        // #6820: Budget cap to prevent O(N²) blowup for benchmarks with many
        // stores sharing the same base array (storecomm family). For N stores,
        // the pairwise loop generates N*(N-1)/2 axioms — 190 for N=20, 780 for
        // N=40 — each creating new terms that can trigger further axiom rounds.
        //
        // Budget: cap at 50 disjunctive axioms per fixpoint call. The runtime
        // theory solver handles any missed pairs lazily via check_self_store().
        const DISJUNCTIVE_INDEX_BUDGET: usize = 50;
        let mut generated = 0_usize;

        // For each pair of store equalities with the same (base, other_side),
        // generate the disjunctive index axiom.
        'outer: for i in 0..store_eqs.len() {
            if should_stop() {
                break;
            }
            for j in (i + 1)..store_eqs.len() {
                let (eq_i, base_i, idx_i, _val_i, target_i) = store_eqs[i];
                let (eq_j, base_j, idx_j, _val_j, target_j) = store_eqs[j];

                // Same base array and same target (both sides of the equality chain)
                if base_i == base_j && target_i == target_j && idx_i != idx_j {
                    let not_eq_i = self.ctx.terms.mk_not(eq_i);
                    let not_eq_j = self.ctx.terms.mk_not(eq_j);
                    let idx_eq = self.ctx.terms.mk_eq(idx_i, idx_j);
                    let base_eq_target = self.ctx.terms.mk_eq(base_i, target_i);
                    let axiom =
                        self.ctx
                            .terms
                            .mk_or(vec![not_eq_i, not_eq_j, idx_eq, base_eq_target]);
                    self.push_array_axiom_assertion_site(axiom, "store_disj_idx");
                    generated += 1;
                    if generated >= DISJUNCTIVE_INDEX_BUDGET {
                        break 'outer;
                    }
                }
            }
        }
    }

    /// Add the exact shadowing obligation for equal two-level store chains.
    ///
    /// For the structurally matched terms
    ///
    /// ```text
    /// lhs = store(store(a, i, v), j, x)
    /// rhs = store(store(a, i, w), j, x)
    /// ```
    ///
    /// array semantics entails
    ///
    /// ```text
    /// lhs = rhs  ==>  i = j OR v = w.
    /// ```
    ///
    /// If `i = j`, the common outer write shadows both inner values. If the
    /// indices differ, reading at `i` exposes `v` and `w`, so equality of the
    /// arrays forces `v = w`. Materializing this disjunction is essential for
    /// model construction: without it a combined arithmetic solver may choose
    /// distinct completion values for `i` and `j` while also choosing `v != w`,
    /// report SAT, and leave the independent model gate to reject the invalid
    /// witness even though the formula has the valid `i = j` branch.
    ///
    /// The matcher deliberately requires syntactically identical base, inner
    /// index, outer index, and outer value. Broader equality-based matching
    /// belongs in the reason-carrying ArraySolver; this eager lemma has no
    /// hidden premises and is therefore valid in every solve lane.
    pub(in crate::executor) fn add_shadowed_store_equality_axioms(&mut self) {
        let should_stop = self.make_should_stop();
        let scan_len = self.ctx.terms.len();

        for raw in 0..scan_len {
            if should_stop() {
                return;
            }
            let eq_term = TermId(raw as u32);
            if !self.term_in_array_scope(eq_term) {
                continue;
            }
            let TermData::App(eq_sym, eq_args) = self.ctx.terms.get(eq_term).clone() else {
                continue;
            };
            if eq_sym.name() != "=" || eq_args.len() != 2 {
                continue;
            }

            let (lhs, rhs) = (eq_args[0], eq_args[1]);
            let TermData::App(lhs_outer_sym, lhs_outer) = self.ctx.terms.get(lhs).clone() else {
                continue;
            };
            let TermData::App(rhs_outer_sym, rhs_outer) = self.ctx.terms.get(rhs).clone() else {
                continue;
            };
            if lhs_outer_sym.name() != "store"
                || rhs_outer_sym.name() != "store"
                || lhs_outer.len() != 3
                || rhs_outer.len() != 3
                || lhs_outer[1] != rhs_outer[1]
                || lhs_outer[2] != rhs_outer[2]
            {
                continue;
            }

            let TermData::App(lhs_inner_sym, lhs_inner) = self.ctx.terms.get(lhs_outer[0]).clone()
            else {
                continue;
            };
            let TermData::App(rhs_inner_sym, rhs_inner) = self.ctx.terms.get(rhs_outer[0]).clone()
            else {
                continue;
            };
            if lhs_inner_sym.name() != "store"
                || rhs_inner_sym.name() != "store"
                || lhs_inner.len() != 3
                || rhs_inner.len() != 3
                || lhs_inner[0] != rhs_inner[0]
                || lhs_inner[1] != rhs_inner[1]
            {
                continue;
            }

            let inner_index = lhs_inner[1];
            let outer_index = lhs_outer[1];
            let lhs_value = lhs_inner[2];
            let rhs_value = rhs_inner[2];
            if inner_index == outer_index || lhs_value == rhs_value {
                continue;
            }

            // Keep the same compact solve lemma in proof and non-proof modes.
            // Merely seeding witness reads is insufficient here: ordinary array
            // congruence deliberately skips store/store equality pairs, while
            // the store-side bridge it triggers is itself a derived theorem,
            // not a primitive ROW2 clause.  Proof attribution records this
            // compact lemma honestly as Generic; proof finalization expands the
            // exact schema into EUF congruence, ROW1/ROW2, transitivity, and
            // resolution steps that strict checkers can replay.
            let not_array_eq = self.ctx.terms.mk_not(eq_term);
            let index_eq = self.ctx.terms.mk_eq(inner_index, outer_index);
            let value_eq = self.ctx.terms.mk_eq(lhs_value, rhs_value);
            let axiom = self.ctx.terms.mk_or(vec![not_array_eq, index_eq, value_eq]);
            if !self.ctx.assertions.contains(&axiom) {
                self.push_array_axiom_assertion_site(axiom, "shadowed_store_eq");
            }
        }
    }
}
