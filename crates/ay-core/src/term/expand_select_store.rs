// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Expand `select(store(...))` into ITE chains at preprocessing time.
//!
//! Z3 ref: `array_rewriter.cpp:354-381` (`expand_select_store`).
//!
//! Converts `select(store(a, I, v), J)` → `ite(I = J, v, select(a, J))`,
//! eliminating store chains at preprocessing time. Critical for storeinv-family
//! benchmarks where deep swap chains cause the lazy array theory to cycle
//! through exponentially many models.

use super::*;
use crate::kani_compat::{det_hash_map_new, DetHashMap};

/// Red zone size for `stacker::maybe_grow` in expand_select_store recursion (#8414).
const EXPAND_SS_STACK_RED_ZONE: usize = 32 * 1024;

/// Stack segment size allocated by stacker for expand_select_store recursion.
const EXPAND_SS_STACK_SIZE: usize = 1024 * 1024;

impl TermStore {
    /// Expand `select(store(a, I, v), J)` into `ite(I = J, v, select(a, J))`.
    ///
    /// The expansion chains recursively: if `a` is itself `store(a', I', v')`,
    /// the new `select(a', J)` term is also expanded. Bounded at 50 levels
    /// to prevent runaway expansion on pathological inputs.
    pub fn expand_select_store(&mut self, term: TermId) -> TermId {
        self.expand_select_store_inner(term, &mut det_hash_map_new())
    }

    /// Uses `stacker::maybe_grow` for stack safety on deeply nested terms (#8414).
    fn expand_select_store_inner(
        &mut self,
        term: TermId,
        cache: &mut DetHashMap<TermId, TermId>,
    ) -> TermId {
        stacker::maybe_grow(EXPAND_SS_STACK_RED_ZONE, EXPAND_SS_STACK_SIZE, || {
            if let Some(&cached) = cache.get(&term) {
                return cached;
            }

            let result = match self.get(term).clone() {
                TermData::App(Symbol::Named(ref name), ref args)
                    if name == "select" && args.len() == 2 =>
                {
                    let array = args[0];
                    let index = args[1];

                    // Recursively expand children first
                    let expanded_array = self.expand_select_store_inner(array, cache);
                    let expanded_index = self.expand_select_store_inner(index, cache);

                    // Now try to expand select-over-store on the result
                    self.expand_select_over_store(expanded_array, expanded_index, 50)
                }
                TermData::App(ref sym, ref args) => {
                    let new_args: Vec<TermId> = args
                        .iter()
                        .map(|&a| self.expand_select_store_inner(a, cache))
                        .collect();
                    if new_args == *args {
                        term
                    } else {
                        let sort = self.sort(term).clone();
                        self.intern(TermData::App(sym.clone(), new_args), sort)
                    }
                }
                TermData::Not(inner) => {
                    let new_inner = self.expand_select_store_inner(inner, cache);
                    if new_inner == inner {
                        term
                    } else {
                        self.mk_not(new_inner)
                    }
                }
                TermData::Ite(c, t, e) => {
                    let new_c = self.expand_select_store_inner(c, cache);
                    let new_t = self.expand_select_store_inner(t, cache);
                    let new_e = self.expand_select_store_inner(e, cache);
                    if new_c == c && new_t == t && new_e == e {
                        term
                    } else {
                        self.mk_ite(new_c, new_t, new_e)
                    }
                }
                _ => term,
            };

            cache.insert(term, result);
            result
        }) // stacker::maybe_grow
    }

    /// Expand `select(store_term, index)` into ITE chain.
    ///
    /// If `store_term` is `store(a, I, v)`, produces:
    ///   `ite(I = index, v, select(a, index))`
    /// and recursively expands the else-branch if `a` is also a store.
    ///
    /// Two depth limits apply:
    /// - `depth`: overall recursion bound (concrete skip-throughs + symbolic ITEs)
    /// - `symbolic_ite_budget`: number of symbolic ITE branches allowed before
    ///   stopping expansion. Each symbolic (non-concrete-distinct) store level
    ///   consumes one unit. Bounded to prevent O(2^N) ITE explosion on deep
    ///   store chains with symbolic indices (storeinv-family, #6367).
    ///
    /// Concrete-distinct indices never generate ITEs (they skip through), so
    /// they only consume from `depth`, not from `symbolic_ite_budget`.
    fn expand_select_over_store(&mut self, array: TermId, index: TermId, depth: usize) -> TermId {
        self.expand_select_over_store_inner(array, index, depth, Self::SYMBOLIC_ITE_BUDGET)
    }

    /// Maximum number of symbolic ITE branches generated per select-over-store
    /// expansion. Benchmarks with short chains (add4, dlx, pipeline) typically
    /// have 1-3 symbolic store levels and converge with ITE expansion. Deep
    /// storeinv chains (5-20 levels) produce O(2^N) ITEs and must be stopped.
    pub(crate) const SYMBOLIC_ITE_BUDGET: usize = 4;

    fn expand_select_over_store_inner(
        &mut self,
        array: TermId,
        index: TermId,
        depth: usize,
        symbolic_ite_budget: usize,
    ) -> TermId {
        if depth == 0 {
            return self.mk_select(array, index);
        }

        match self.get(array).clone() {
            TermData::App(Symbol::Named(ref name), ref args)
                if name == "store" && args.len() == 3 =>
            {
                let inner_array = args[0];
                let store_index = args[1];
                let store_value = args[2];

                // If indices are syntactically identical, just return the value
                if store_index == index {
                    return store_value;
                }

                // If both are provably distinct indices, skip this store level
                // without generating an ITE (no symbolic budget consumed).
                // Handles: concrete constants, and structural patterns like
                // bvadd(base, k1) vs bvadd(base, k2) where k1 != k2 (byte-level
                // memory access patterns common in QF_ABV benchmarks).
                let concrete_distinct = self.are_provably_distinct_indices(index, store_index);
                if concrete_distinct {
                    return self.expand_select_over_store_inner(
                        inner_array,
                        index,
                        depth - 1,
                        symbolic_ite_budget,
                    );
                }

                // Symbolic indices: generate ITE if budget remains, otherwise stop.
                // Stopping at deep chains prevents O(2^N) ITE explosion on
                // storeinv-family benchmarks (#6367). The runtime array theory
                // solver handles the remaining store levels via ROW1/ROW2 lemmas.
                if symbolic_ite_budget == 0 {
                    return self.mk_select(array, index);
                }

                let eq = self.mk_eq_coerce(store_index, index);
                let else_branch = self.expand_select_over_store_inner(
                    inner_array,
                    index,
                    depth - 1,
                    symbolic_ite_budget - 1,
                );
                self.mk_ite(eq, store_value, else_branch)
            }
            // Push select inside ITE of array sort (#8140):
            //   select(ite(c, a1, a2), i) -> ite(c, select(a1, i), select(a2, i))
            //
            // Critical for CBMC-generated benchmarks (bubble_sort, wchains) where
            // conditional swaps produce ITE-wrapped store chains like:
            //   ite(cond, store(store(arr, j, v1), j+1, v2), arr)
            //
            // Fast-path: check if the "then" branch (typically
            // store(store(base, j, v1), j+1, v2)) only modifies indices
            // provably distinct from `index`. If so, reading through the
            // store gives the same result as reading from the "else" branch
            // (typically the unmodified base). We skip the ITE entirely:
            //   select(ite(c, store(a, j, v), a), i) where i != j => select(a, i)
            //
            // This reduces O(2^N) branching to O(N) for bubble sort patterns
            // where each conditional swap only touches 2 indices out of N.
            TermData::Ite(_cond, then_arr, else_arr) if depth > 0 => {
                // Fast-path: check if the "then" branch stores at indices
                // all provably distinct from `index`. Walk the store chain.
                if self.ite_branch_stores_distinct_from(then_arr, else_arr, index) {
                    // The store chain in the "then" branch doesn't affect `index`.
                    // select(ite(c, store_chain(base, ...), base), index) = select(base, index)
                    // Continue expanding through the else branch (which is the
                    // unmodified base array that both ITE branches share).
                    return self.expand_select_over_store_inner(
                        else_arr,
                        index,
                        depth - 1,
                        symbolic_ite_budget,
                    );
                }

                // Symmetric: check if the "else" branch stores are distinct.
                if self.ite_branch_stores_distinct_from(else_arr, then_arr, index) {
                    return self.expand_select_over_store_inner(
                        then_arr,
                        index,
                        depth - 1,
                        symbolic_ite_budget,
                    );
                }

                // General case: neither branch is provably irrelevant.
                // Do NOT expand both branches -- that causes O(2^N) blowup
                // on deeply nested ITE store chains with symbolic indices.
                // Fall through to mk_select and let the array theory solver
                // handle the remaining axioms lazily via ROW1/ROW2 lemmas.
                self.mk_select(array, index)
            }
            _ => {
                // Not a store or ITE — create select normally
                self.mk_select(array, index)
            }
        }
    }

    /// Check if `branch_arr` is a store chain over `base_arr` where ALL store
    /// indices are provably distinct from `read_index` (#8140).
    ///
    /// Pattern: `store(store(base, j1, v1), j2, v2)` where j1 != read_index
    /// and j2 != read_index. Returns true if reading at `read_index` through
    /// the store chain yields the same value as reading from `base_arr`.
    ///
    /// Walks up to 32 store levels. Handles the CBMC bubble sort pattern:
    ///   ite(cond, store(store(arr, j, val1), j+1, val2), arr)
    /// where a select at index `i` with i != j and i != j+1 can skip the ITE.
    fn ite_branch_stores_distinct_from(
        &self,
        branch_arr: TermId,
        base_arr: TermId,
        read_index: TermId,
    ) -> bool {
        let mut current = branch_arr;
        for _ in 0..32 {
            if current == base_arr {
                // Reached the base: all intermediate stores were distinct
                return true;
            }
            match self.get(current).clone() {
                TermData::App(Symbol::Named(ref name), ref args)
                    if name == "store" && args.len() == 3 =>
                {
                    let inner_array = args[0];
                    let store_index = args[1];

                    // If store index equals read index, the store affects the read
                    if store_index == read_index {
                        return false;
                    }

                    // If store index is NOT provably distinct, we can't skip
                    if !self.are_provably_distinct_indices(read_index, store_index) {
                        return false;
                    }

                    // This store level doesn't affect the read; continue to inner
                    current = inner_array;
                }
                _ => {
                    // Not a store -- check if we've reached the base
                    return current == base_arr;
                }
            }
        }
        false // depth limit exceeded
    }

    /// Apply expand_select_store to all assertions.
    pub fn expand_select_store_all(&mut self, terms: &[TermId]) -> Vec<TermId> {
        let mut cache = det_hash_map_new();
        terms
            .iter()
            .map(|&t| self.expand_select_store_inner(t, &mut cache))
            .collect()
    }

    /// Adaptive expand_select_store: uses a higher symbolic ITE budget for
    /// formulas where store chains are moderate depth. This allows the solver
    /// to resolve more store chains at the term level, reducing the number of
    /// bit-level ROW axioms generated by `generate_array_bv_axioms` and thus
    /// the total clause count sent to the SAT solver.
    ///
    /// For bubble_sort22-like benchmarks: 22-deep store chains with SSA-renamed
    /// symbolic indices generate O(N*M) ROW axioms when the ITE budget is only
    /// 4. With budget 8, more store levels are resolved as ITEs (bounded by
    /// EQ_ITE_EXPAND_DEPTH=3 in mk_eq), keeping the term count reasonable while
    /// dramatically reducing the clause count.
    ///
    /// Budget selection:
    /// - <= 200 stores: budget 12 (small formulas, safe to expand more)
    /// - <= 500 stores: budget 8 (medium formulas)
    /// - > 500 stores: budget 4 (large formulas, original conservative bound)
    pub fn expand_select_store_all_adaptive(
        &mut self,
        terms: &[TermId],
        num_stores: usize,
    ) -> Vec<TermId> {
        let budget = if num_stores <= 200 {
            12
        } else if num_stores <= 500 {
            8
        } else {
            Self::SYMBOLIC_ITE_BUDGET
        };

        if budget == Self::SYMBOLIC_ITE_BUDGET {
            return self.expand_select_store_all(terms);
        }

        let mut cache = det_hash_map_new();
        terms
            .iter()
            .map(|&t| self.expand_select_store_inner_with_budget(t, &mut cache, budget))
            .collect()
    }

    /// Uses `stacker::maybe_grow` for stack safety on deeply nested terms (#8414).
    fn expand_select_store_inner_with_budget(
        &mut self,
        term: TermId,
        cache: &mut DetHashMap<TermId, TermId>,
        budget: usize,
    ) -> TermId {
        stacker::maybe_grow(EXPAND_SS_STACK_RED_ZONE, EXPAND_SS_STACK_SIZE, || {
            if let Some(&cached) = cache.get(&term) {
                return cached;
            }

            let result = match self.get(term).clone() {
                TermData::App(Symbol::Named(ref name), ref args)
                    if name == "select" && args.len() == 2 =>
                {
                    let array = args[0];
                    let index = args[1];

                    let expanded_array =
                        self.expand_select_store_inner_with_budget(array, cache, budget);
                    let expanded_index =
                        self.expand_select_store_inner_with_budget(index, cache, budget);

                    self.expand_select_over_store_inner(expanded_array, expanded_index, 50, budget)
                }
                TermData::App(ref sym, ref args) => {
                    let new_args: Vec<TermId> = args
                        .iter()
                        .map(|&a| self.expand_select_store_inner_with_budget(a, cache, budget))
                        .collect();
                    if new_args == *args {
                        term
                    } else {
                        let sort = self.sort(term).clone();
                        self.intern(TermData::App(sym.clone(), new_args), sort)
                    }
                }
                TermData::Not(inner) => {
                    let new_inner =
                        self.expand_select_store_inner_with_budget(inner, cache, budget);
                    if new_inner == inner {
                        term
                    } else {
                        self.mk_not(new_inner)
                    }
                }
                TermData::Ite(c, t, e) => {
                    let new_c = self.expand_select_store_inner_with_budget(c, cache, budget);
                    let new_t = self.expand_select_store_inner_with_budget(t, cache, budget);
                    let new_e = self.expand_select_store_inner_with_budget(e, cache, budget);
                    if new_c == c && new_t == t && new_e == e {
                        term
                    } else {
                        self.mk_ite(new_c, new_t, new_e)
                    }
                }
                _ => term,
            };

            cache.insert(term, result);
            result
        }) // stacker::maybe_grow
    }
}
