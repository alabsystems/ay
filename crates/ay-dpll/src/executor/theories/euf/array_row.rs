// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Read-over-write (ROW/ROW2b) array axiom generation.
//!
//! Extracted from `array_patterns.rs` as part of code-health module split.
//! ROW (downward): `select(store(A,i,v), k)` decomposes by index equality.
//! ROW2b (upward): `select(A, j)` propagates to `select(store(A,i,v), j)`.

use super::super::super::Executor;
// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::{TermData, TermId};

impl Executor {
    /// Collect `select(store(a, i, v), k)` patterns where `i != k` (different
    /// index terms) that participate in disjunctive ROW axioms.
    #[allow(clippy::type_complexity)]
    fn collect_array_row_patterns(&self) -> Vec<(TermId, TermId, TermId, TermId, TermId)> {
        let mut patterns = Vec::new();
        for idx in 0..self.ctx.terms.len() {
            let select_term = TermId(idx as u32);
            if !self.term_in_array_scope(select_term) {
                continue;
            }

            let (array, sel_index) =
                if let TermData::App(ref sym, ref args) = self.ctx.terms.get(select_term).clone() {
                    if sym.name() == "select" && args.len() == 2 {
                        (args[0], args[1])
                    } else {
                        continue;
                    }
                } else {
                    continue;
                };

            let (base_array, store_index, store_value) =
                if let TermData::App(ref sym, ref args) = self.ctx.terms.get(array).clone() {
                    if sym.name() == "store" && args.len() == 3 {
                        (args[0], args[1], args[2])
                    } else {
                        continue;
                    }
                } else {
                    continue;
                };

            if store_index == sel_index {
                // Trivial ROW case handled by collect_array_row_trivial_patterns.
                continue;
            }

            patterns.push((select_term, base_array, store_index, store_value, sel_index));
        }
        patterns
    }

    /// Collect `select(store(a, i, v), i)` patterns where the store and select
    /// indices are the same term. These produce unconditional ROW1 axioms:
    /// `select(store(a, i, v), i) = v`.
    fn collect_array_row_trivial_patterns(&self) -> Vec<(TermId, TermId)> {
        let mut patterns = Vec::new();
        for idx in 0..self.ctx.terms.len() {
            let select_term = TermId(idx as u32);
            if !self.term_in_array_scope(select_term) {
                continue;
            }

            let (array, sel_index) =
                if let TermData::App(ref sym, ref args) = self.ctx.terms.get(select_term).clone() {
                    if sym.name() == "select" && args.len() == 2 {
                        (args[0], args[1])
                    } else {
                        continue;
                    }
                } else {
                    continue;
                };

            let (_base_array, store_index, store_value) =
                if let TermData::App(ref sym, ref args) = self.ctx.terms.get(array).clone() {
                    if sym.name() == "store" && args.len() == 3 {
                        (args[0], args[1], args[2])
                    } else {
                        continue;
                    }
                } else {
                    continue;
                };

            if store_index != sel_index {
                continue;
            }

            patterns.push((select_term, store_value));
        }
        patterns
    }

    pub(in crate::executor) fn seed_array_row_terms(&mut self) -> bool {
        let before = self.ctx.terms.len();
        for (select_term, base_array, _, _, sel_index) in self.collect_array_row_patterns() {
            if self.row_seeded_terms.contains(&select_term) {
                // #8785: once eager ROW creates a descendant select(base, k),
                // do not recursively use that descendant as a new seeding
                // source. Congruence-created and user-visible selects still
                // seed normally; this only blocks ROW-from-ROW recursion.
                continue;
            }
            let base_select = self.ctx.terms.mk_select(base_array, sel_index);
            if base_select != select_term {
                self.row_seeded_terms.insert(base_select);
            }
        }
        self.ctx.terms.len() != before
    }

    /// Add eager read-over-write clauses for already-seeded ROW patterns.
    pub(in crate::executor) fn add_array_row_clauses(&mut self) {
        self.add_array_row_clauses_with_cap(usize::MAX);
    }

    /// Like [`Self::add_array_row_clauses`] but stops emitting new axioms once
    /// the assertion count exceeds `cap`. `cap = usize::MAX` disables the cap.
    ///
    /// #7890: The unbudgeted variant generates N×M ROW clauses for N selects
    /// and M store chains — on QF_ALIA benchmarks with deep chains
    /// (cs_fib-2, ios_*, pointer-safe-*), a single fixpoint call can emit
    /// 10k+ clauses before the outer-loop budget check fires. Providing an
    /// assertion cap lets the fixpoint enforce a tight budget and rely on
    /// the runtime ArraySolver to add remaining axioms lazily.
    pub(in crate::executor) fn add_array_row_clauses_with_cap(&mut self, cap: usize) {
        // #8615: Check interrupt/deadline so ROW clause generation can be
        // cancelled on long-running array formulas.
        let should_stop = self.make_should_stop();

        // Trivial ROW: select(store(a, i, v), i) = v (unconditional).
        // When the store and select indices are the same TermId, the ROW1 axiom
        // is unconditionally true. Previously these patterns were skipped
        // entirely, causing Unknown on formulas like select(store(a,i,1),i)=1
        // where the array axiom was the only needed reasoning step.
        let trivial_patterns = self.collect_array_row_trivial_patterns();
        for (select_term, store_value) in trivial_patterns {
            if self.ctx.assertions.len() > cap {
                return;
            }
            let row1_eq = self.ctx.terms.mk_eq(select_term, store_value);
            self.push_array_axiom_assertion_site(row1_eq, "row1_trivial");
        }

        let top_level_disequalities = self.collect_top_level_disequalities();
        for (select_term, base_array, store_index, store_value, sel_index) in
            self.collect_array_row_patterns()
        {
            if self.row_seeded_terms.contains(&select_term) {
                // #8785: descendants created only by eager ROW seeding are an
                // internal bridge to expose reachable base selects, not a
                // license to project the original disequality onto shared
                // internal store prefixes with more eager ROW clauses.
                continue;
            }
            if should_stop() {
                return;
            }
            if self.ctx.assertions.len() > cap {
                return;
            }
            let indices_provably_distinct = self.are_terms_provably_distinct_from_assertions(
                store_index,
                sel_index,
                &top_level_disequalities,
            );

            let base_select = self.ctx.terms.mk_select(base_array, sel_index);
            let row2_eq = self.ctx.terms.mk_eq(select_term, base_select);

            // Create (= store_index sel_index)
            let idx_eq = self.ctx.terms.mk_eq(store_index, sel_index);
            let not_idx_eq = self.ctx.terms.mk_not(idx_eq);

            if !indices_provably_distinct {
                // ROW1 clause: ¬(= i k) ∨ (= select_term v)
                // "If the indices are equal, the select returns the stored value"
                let row1_eq = self.ctx.terms.mk_eq(select_term, store_value);
                let row1_clause = self.ctx.terms.mk_or(vec![not_idx_eq, row1_eq]);
                self.push_array_axiom_assertion_site(row1_clause, "row1_clause");
            }

            if indices_provably_distinct {
                self.push_array_axiom_assertion_site(row2_eq, "row2_unit_distinct_indices");
                continue;
            }

            // ROW2 clause: (= i k) ∨ (= select_term (select base_array sel_index))
            // "If the indices differ, the select passes through to the base array"
            // Note: mk_select may simplify if base_array is also a store with known index
            let row2_clause = self.ctx.terms.mk_or(vec![idx_eq, row2_eq]);
            // DIAGNOSTIC: trace ROW2 components for #8785 investigation
            if ay_core::debug_channel_active(ay_core::DebugChannel::Row2Components) {
                fn fmt_deep(terms: &ay_core::TermStore, t: TermId, depth: u32) -> String {
                    if depth == 0 {
                        return format!("#{}", t.0);
                    }
                    match terms.get(t).clone() {
                        TermData::Const(c) => format!("{c:?}"),
                        TermData::Var(n, _) => format!("V:{n}"),
                        TermData::App(s, a) => {
                            let args: Vec<String> =
                                a.iter().map(|x| fmt_deep(terms, *x, depth - 1)).collect();
                            format!("({} {})", s.name(), args.join(" "))
                        }
                        other => format!("{other:?}"),
                    }
                }
                eprintln!(
                    "[row2_diag] select_term=#{} pattern_array=deep={}",
                    select_term.0,
                    fmt_deep(&self.ctx.terms, select_term, 500)
                );
                eprintln!(
                    "[row2_diag]   base_array=#{} deep={}",
                    base_array.0,
                    fmt_deep(&self.ctx.terms, base_array, 500)
                );
                eprintln!(
                    "[row2_diag]   row2_clause=#{} store_index=#{} sel_index=#{}",
                    row2_clause.0, store_index.0, sel_index.0
                );
            }
            self.push_array_axiom_assertion_site(row2_clause, "row2_clause");
        }
    }

    /// #mgr-row-peel: demand-driven deep read-over-write peel (the MGR repair
    /// channel of the demand-driven array blueprint).
    ///
    /// The bounded eager phase deliberately withholds ROW case splits for
    /// descendant selects created by its own seeding (#8785 anti-recursion
    /// guard) — sound, but it makes inner-layer index-aliasing atoms
    /// `(= store_index sel_index)` inexpressible, so satisfying assignments
    /// that require aliasing a *non-top* store layer fail-close to `unknown`
    /// (the A2_alias / A3_comm corpus classes). This routine runs only as an
    /// escalation stage after the cheap phases returned a validated unknown:
    /// for every reachable `select`-over-`store` chain it emits the full
    /// ROW1/ROW2 case split for EVERY layer down to the chain's base,
    /// materializing exactly the missing atoms.
    ///
    /// SOUNDNESS: every emitted clause is a ground array-theory tautology
    /// (ROW1 `(= i k) → select(store(b,i,v),k) = v`; ROW2 `¬(= i k) →
    /// select(store(b,i,v),k) = select(b,k)`), routed through
    /// `push_array_axiom_assertion_site` so unsat proofs remain
    /// Alethe-checkable. Verdicts stay licensed by the solve pipeline plus the
    /// independent model gate — never by this repair; a miss here only leaves
    /// the verdict `unknown`, exactly as before.
    ///
    /// TERMINATION/BOUND: the worklist strictly descends store chains and the
    /// visited set dedups selects, so the instance universe is at most
    /// (#select roots × max chain depth); `cap` bounds emission on top.
    /// Returns the number of clauses emitted.
    pub(in crate::executor) fn add_array_row_deep_peel_clauses(&mut self, cap: usize) -> usize {
        let should_stop = self.make_should_stop();
        let top_level_disequalities = self.collect_top_level_disequalities();
        let mut worklist: Vec<(TermId, TermId, TermId)> = Vec::new();
        for (select_term, base_array, store_index, store_value, sel_index) in
            self.collect_array_row_patterns()
        {
            let _ = (base_array, store_index, store_value);
            let TermData::App(sym, args) = self.ctx.terms.get(select_term) else {
                continue;
            };
            debug_assert!(sym.name() == "select" && args.len() == 2);
            worklist.push((select_term, args[0], sel_index));
        }
        let mut visited: HashSet<TermId> = HashSet::default();
        let mut emitted = 0_usize;
        while let Some((select_term, array, sel_index)) = worklist.pop() {
            if emitted >= cap || should_stop() {
                break;
            }
            if !visited.insert(select_term) {
                continue;
            }
            let (base_array, store_index, store_value) = match self.ctx.terms.get(array).clone() {
                TermData::App(ref sym, ref args) if sym.name() == "store" && args.len() == 3 => {
                    (args[0], args[1], args[2])
                }
                _ => continue,
            };
            if store_index == sel_index {
                // The read resolves at this layer unconditionally: ROW1-trivial.
                let row1_eq = self.ctx.terms.mk_eq(select_term, store_value);
                self.push_array_axiom_assertion_site(row1_eq, "row1_trivial");
                emitted += 1;
                continue;
            }
            let base_select = self.ctx.terms.mk_select(base_array, sel_index);
            let row2_eq = self.ctx.terms.mk_eq(select_term, base_select);
            if self.are_terms_provably_distinct_from_assertions(
                store_index,
                sel_index,
                &top_level_disequalities,
            ) {
                self.push_array_axiom_assertion_site(row2_eq, "row2_unit_distinct_indices");
                emitted += 1;
            } else {
                let idx_eq = self.ctx.terms.mk_eq(store_index, sel_index);
                let not_idx_eq = self.ctx.terms.mk_not(idx_eq);
                let row1_eq = self.ctx.terms.mk_eq(select_term, store_value);
                let row1_clause = self.ctx.terms.mk_or(vec![not_idx_eq, row1_eq]);
                self.push_array_axiom_assertion_site(row1_clause, "row1_clause");
                let row2_clause = self.ctx.terms.mk_or(vec![idx_eq, row2_eq]);
                self.push_array_axiom_assertion_site(row2_clause, "row2_clause");
                emitted += 2;
            }
            // Descend: keep peeling while the pass-through read is itself a
            // select over a store (mk_select may have simplified it away).
            if let TermData::App(sym, args) = self.ctx.terms.get(base_select) {
                if sym.name() == "select" && args.len() == 2 {
                    let (inner_array, inner_index) = (args[0], args[1]);
                    if matches!(
                        self.ctx.terms.get(inner_array),
                        TermData::App(s, a) if s.name() == "store" && a.len() == 3
                    ) {
                        worklist.push((base_select, inner_array, inner_index));
                    }
                }
            }
        }
        emitted
    }

    pub(in crate::executor) fn add_array_row_lemmas(&mut self) {
        self.row_seeded_terms.clear();
        // #8635: Cap the seeding loop and check for interrupt/deadline.
        // The original `while seed_array_row_terms() {}` was unbounded —
        // on deep store chains it could run hundreds of rounds before the
        // fixpoint converged. 50 rounds is generous for practical formulas
        // while protecting against runaway expansion.
        let should_stop = self.make_should_stop();
        let mut row_lemma_rounds = 0;
        while self.seed_array_row_terms() {
            row_lemma_rounds += 1;
            if row_lemma_rounds >= 50 || should_stop() {
                break;
            }
        }
        self.add_array_row_clauses();
        self.row_seeded_terms.clear();
    }

    /// Add Axiom 2b (upward select propagation through store parents).
    ///
    /// Z3 reference: `theory_array.cpp:212-221`, `instantiate_axiom2b`.
    ///
    /// For every `select(A, j)` where `A` is the base array of some store term
    /// `B = store(A, i, v)`, asserts:
    ///   `(= i j) ∨ (= (select A j) (select B j))`
    ///
    /// This "upward" propagation complements the existing "downward" propagation
    /// in `add_array_row_lemmas` (which handles `select(store(A,i,v), j)` → `select(A,j)`).
    /// For deeply nested `_nf_` store expressions where intermediate stores are
    /// subterms (not named variables with explicit equality assertions), the downward
    /// propagation alone cannot create the select terms needed to chain through
    /// multiple nesting levels.
    ///
    /// Upward propagation ensures that a select on a base array is connected to
    /// the same index on all store results built from that base, enabling the
    /// fixpoint loop to fully resolve through nested store chains (#6282).
    ///
    /// Returns the number of axioms added (for budget tracking).
    /// Duplicate axioms across rounds are harmless — the caller deduplicates
    /// assertions after the fixpoint loop completes.
    #[allow(clippy::type_complexity)]
    /// Collect equality atoms `(= a b)` that are asserted POSITIVELY at the top
    /// level (directly, or as conjuncts of a top-level `and`). These are the
    /// only equalities that may be treated as unconditional definitional facts
    /// by ROW2b alias generation; any equality reached under a negation,
    /// disjunction, or ITE condition may be assigned false and must be guarded.
    fn collect_top_level_positive_equality_terms(&self, term: TermId, out: &mut HashSet<TermId>) {
        let TermData::App(sym, args) = self.ctx.terms.get(term) else {
            return;
        };
        match sym.name() {
            "=" if args.len() == 2 => {
                out.insert(term);
            }
            "and" => {
                let args = args.clone();
                for arg in args {
                    self.collect_top_level_positive_equality_terms(arg, out);
                }
            }
            _ => {}
        }
    }

    fn collect_array_row2b_context(
        &self,
    ) -> (
        HashMap<TermId, Vec<(TermId, TermId, TermId, Option<TermId>)>>,
        HashMap<TermId, (TermId, Option<TermId>)>,
        Vec<(TermId, TermId, TermId)>,
    ) {
        // Build parent-stores index: base_array -> [(store, index, value, guard)].
        // The guard is present for non-definitional aliases so ROW2b only fires
        // when the store equality itself is active.
        let mut parent_stores: HashMap<TermId, Vec<(TermId, TermId, TermId, Option<TermId>)>> =
            HashMap::default();
        // Store-alias map: for equalities (= X store(...)), map
        // store_term -> (alias, optional guard equality).
        let mut store_aliases: HashMap<TermId, (TermId, Option<TermId>)> = HashMap::default();

        // An `(= X store(...))` equality only licenses an UNCONDITIONAL (guard
        // = None) ROW2b alias when the equality is genuinely asserted true at
        // the top level — i.e. it is a definitional fact `X = store(...)`. An
        // equality term that merely exists in the term store (e.g. as the inner
        // atom of `(assert (not (= X store(...))))`, or as an ITE condition) may
        // be assigned FALSE, in which case substituting `X` for the store inside
        // an unconditional ROW2b alias clause is unsound and can drop genuine
        // models, producing wrong-UNSAT (e.g. const-array vs store disequality).
        // Guard every non-definitional alias with the equality atom so the alias
        // clause only fires when the equality is active. (Soundness fix for the
        // const-array/store finite-index disequality wrong-UNSAT family.)
        let mut definitional_equalities: HashSet<TermId> = HashSet::default();
        for &assertion in &self.ctx.assertions {
            self.collect_top_level_positive_equality_terms(assertion, &mut definitional_equalities);
        }

        for idx in 0..self.ctx.terms.len() {
            let term_id = TermId(idx as u32);
            if !self.term_in_array_scope(term_id) {
                continue;
            }
            match self.ctx.terms.get(term_id).clone() {
                TermData::App(ref sym, ref args) if sym.name() == "store" && args.len() == 3 => {
                    parent_stores
                        .entry(args[0])
                        .or_default()
                        .push((term_id, args[1], args[2], None));
                }
                TermData::App(ref sym, ref args) if sym.name() == "=" && args.len() == 2 => {
                    let (lhs, rhs) = (args[0], args[1]);
                    let lhs_is_store = matches!(
                        self.ctx.terms.get(lhs),
                        TermData::App(ref s, ref a) if s.name() == "store" && a.len() == 3
                    );
                    let rhs_is_store = matches!(
                        self.ctx.terms.get(rhs),
                        TermData::App(ref s, ref a) if s.name() == "store" && a.len() == 3
                    );
                    // A definitional top-level positive equality may be treated
                    // as unconditional; any other equality must be guarded by
                    // its own atom (store-store equalities were already guarded).
                    let is_definitional = definitional_equalities.contains(&term_id);
                    if rhs_is_store {
                        let guard = if lhs_is_store || !is_definitional {
                            Some(term_id)
                        } else {
                            None
                        };
                        store_aliases.insert(rhs, (lhs, guard));
                    }
                    if lhs_is_store {
                        let guard = if rhs_is_store || !is_definitional {
                            Some(term_id)
                        } else {
                            None
                        };
                        store_aliases.insert(lhs, (rhs, guard));
                    }
                }
                _ => {}
            }
        }

        // Extend parent_stores for store aliases. Definitional aliases are
        // unconditional; store-store equalities are guarded by the equality atom.
        for (&store_term, &(alias, guard)) in &store_aliases {
            if let TermData::App(ref sym, ref args) = self.ctx.terms.get(store_term).clone() {
                if sym.name() == "store" && args.len() == 3 {
                    parent_stores
                        .entry(alias)
                        .or_default()
                        .push((store_term, args[1], args[2], guard));
                }
            }
        }

        if parent_stores.is_empty() {
            return (parent_stores, store_aliases, Vec::new());
        }

        // Collect select terms: (select_term, array, index)
        let mut selects: Vec<(TermId, TermId, TermId)> = Vec::new();
        for idx in 0..self.ctx.terms.len() {
            let term_id = TermId(idx as u32);
            if !self.term_in_array_scope(term_id) {
                continue;
            }
            if let TermData::App(ref sym, ref args) = self.ctx.terms.get(term_id).clone() {
                if sym.name() == "select" && args.len() == 2 {
                    selects.push((term_id, args[0], args[1]));
                }
            }
        }

        (parent_stores, store_aliases, selects)
    }

    pub(in crate::executor) fn seed_array_row2b_terms(&mut self, budget: usize) -> usize {
        let (parent_stores, store_aliases, selects) = self.collect_array_row2b_context();
        if parent_stores.is_empty() {
            return 0;
        }

        // #8615: Check interrupt/deadline so ROW2b seeding can be cancelled.
        let should_stop = self.make_should_stop();
        let mut seeded = 0_usize;
        for (_, array, sel_index) in &selects {
            if should_stop() {
                return seeded;
            }
            let Some(stores) = parent_stores.get(array) else {
                continue;
            };
            for &(store_term, store_index, _store_value, _guard) in stores {
                if seeded >= budget {
                    return seeded;
                }
                if store_index == *sel_index {
                    continue;
                }

                let before = self.ctx.terms.len();
                let upward_select = self.ctx.terms.mk_select(store_term, *sel_index);
                if self.ctx.terms.len() != before {
                    seeded += 1;
                    if seeded >= budget {
                        return seeded;
                    }
                }

                if let Some(&(alias, _alias_guard)) = store_aliases.get(&store_term) {
                    let before = self.ctx.terms.len();
                    let alias_select = self.ctx.terms.mk_select(alias, *sel_index);
                    if alias_select != upward_select && self.ctx.terms.len() != before {
                        seeded += 1;
                    }
                }
            }
        }
        seeded
    }

    #[allow(clippy::type_complexity)]
    pub(in crate::executor) fn add_array_row2b_clauses(&mut self, budget: usize) -> usize {
        let (parent_stores, store_aliases, selects) = self.collect_array_row2b_context();
        if parent_stores.is_empty() {
            return 0;
        }

        // For each select(A, j), check if A is the base of any store(A, i, v) = B.
        // Budget prevents O(selects × stores) blowup on large formulas (#6282).
        // #8615: Check interrupt/deadline so ROW2b clause generation can be cancelled.
        let should_stop = self.make_should_stop();
        let mut added = 0_usize;
        for (select_term, array, sel_index) in &selects {
            if should_stop() {
                return added;
            }
            let Some(stores) = parent_stores.get(array) else {
                continue;
            };
            for &(store_term, store_index, _store_value, guard) in stores {
                if added >= budget {
                    return added;
                }
                // Skip if indices are syntactically identical (ROW1 handles this via mk_select)
                if store_index == *sel_index {
                    continue;
                }

                let idx_eq = self.ctx.terms.mk_eq(store_index, *sel_index);
                let upward_select = self.ctx.terms.mk_select(store_term, *sel_index);

                let sel_eq = self.ctx.terms.mk_eq(*select_term, upward_select);
                let axiom = if let Some(eq_term) = guard {
                    let neg_guard = self.ctx.terms.mk_not(eq_term);
                    self.ctx.terms.mk_or(vec![neg_guard, idx_eq, sel_eq])
                } else {
                    self.ctx.terms.mk_or(vec![idx_eq, sel_eq])
                };
                self.push_array_axiom_assertion_site(axiom, "row2b_upward");
                added += 1;

                if let Some(&(alias, alias_guard)) = store_aliases.get(&store_term) {
                    if added >= budget {
                        return added;
                    }
                    let alias_select = self.ctx.terms.mk_select(alias, *sel_index);
                    if alias_select != upward_select {
                        let alias_sel_eq = self.ctx.terms.mk_eq(*select_term, alias_select);
                        let alias_axiom = if let Some(alias_eq) = alias_guard {
                            let neg = self.ctx.terms.mk_not(alias_eq);
                            self.ctx.terms.mk_or(vec![neg, idx_eq, alias_sel_eq])
                        } else {
                            self.ctx.terms.mk_or(vec![idx_eq, alias_sel_eq])
                        };
                        self.push_array_axiom_assertion_site(alias_axiom, "row2b_alias");
                        added += 1;
                    }
                }
            }
        }
        added
    }

    pub(in crate::executor) fn add_array_row2b_upward_lemmas(&mut self, budget: usize) -> usize {
        let _ = self.seed_array_row2b_terms(budget);
        self.add_array_row2b_clauses(budget)
    }
}
