// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Array operations for TermStore.

use super::*;

enum StoreIndexRewrite {
    Keep,
    SwapDistinct,
}

impl TermStore {
    // ==================== Array Operations ====================

    /// Create array select with read-over-write simplification: (select a i)
    pub fn mk_select(&mut self, array: TermId, index: TermId) -> TermId {
        // Get the element sort from the array sort
        let elem_sort = match self.sort(array) {
            Sort::Array(arr) => {
                debug_assert!(
                    self.sort(index) == &arr.index_sort,
                    "BUG: mk_select index sort mismatch: expected {:?}, got {:?}",
                    arr.index_sort,
                    self.sort(index)
                );
                arr.element_sort.clone()
            }
            _ => {
                // Sort mismatch: caller passed a non-Array term.
                // CHC solver paths (algebraic invariant validation, portfolio
                // query-only verification) can hit this when back-translated
                // model variables have degraded sorts. Return a dummy select
                // term so catch_ay_panics / SMT Unknown handles it gracefully.
                return self.intern(
                    TermData::App(Symbol::named("select"), vec![array, index]),
                    Sort::Bool,
                );
            }
        };

        // Read-over-const-array simplification: select(const-array(v), i) → v
        if let Some(default_value) = self.get_const_array(array) {
            return default_value;
        }

        // Read-over-lambda-array simplification (beta reduction):
        // select(lambda(x) body, idx) → body[x/idx]
        //
        // Z3 ref: array_rewriter.cpp lambda reduction, theory_array_full.cpp:572
        if let Some((var_term, body)) = self.get_lambda_array(array) {
            return self.substitute_var(body, var_term, index);
        }

        // Read-over-as-array simplification:
        // select(as-array(f), i) → f(i)
        //
        // This implements the select-as-array axiom at the term rewriting level.
        // Z3 ref: theory_array_full.cpp:637-666 (instantiate_select_as_array_axiom)
        if let Some(func_name) = self.get_as_array_func(array) {
            let func_name = func_name.to_string();
            return self.intern(
                TermData::App(Symbol::named(&func_name), vec![index]),
                elem_sort,
            );
        }

        // Read-over-map simplification:
        // select(map[f](a1,...,an), i) → f(select(a1,i),...,select(an,i))
        //
        // This implements the select-map axiom at the term rewriting level,
        // following Z3's approach in array_rewriter.cpp:296-306.
        // The rewrite eagerly unfolds map applications during term construction,
        // exposing the underlying function application to the EUF/theory solvers.
        if let Some((func_name, map_args)) = self.get_array_map(array) {
            let func_name = func_name.to_string();
            let map_args = map_args.to_vec();
            let selects: Vec<TermId> = map_args
                .iter()
                .map(|&arr| self.mk_select(arr, index))
                .collect();
            return self.intern(TermData::App(Symbol::named(&func_name), selects), elem_sort);
        }

        // Read-over-write simplification: select(store(a, i, v), i) → v
        if let TermData::App(Symbol::Named(name), args) = self.get(array) {
            if name == "store" && args.len() == 3 {
                let store_index = args[1];
                let store_value = args[2];
                let inner_array = args[0];

                // If indices are identical, return the stored value
                if store_index == index {
                    return store_value;
                }

                // If both indices are constants and different, look through
                if let (Some(idx1), Some(idx2)) = (self.get_int(index), self.get_int(store_index)) {
                    if idx1 != idx2 {
                        return self.mk_select(inner_array, index);
                    }
                }
                if let (Some((val1, _)), Some((val2, _))) =
                    (self.get_bitvec(index), self.get_bitvec(store_index))
                {
                    if val1 != val2 {
                        return self.mk_select(inner_array, index);
                    }
                }
            }
        }

        self.intern(
            TermData::App(Symbol::named("select"), vec![array, index]),
            elem_sort,
        )
    }

    /// Create an array store (write) operation: (store a i v)
    ///
    /// Returns a new array identical to `a` except at index `i` where it has value `v`.
    ///
    /// Simplifications:
    /// - Store-over-store at same index: store(store(a, i, v1), i, v2) → store(a, i, v2)
    /// - Sort-store normalization: store(store(a, j, w), i, v) → store(store(a, i, v), j, w)
    ///   when `i` and `j` are provably distinct interpreted constants and `i < j`
    /// - Squash-store: collapse store chains where the same index appears deeper than 1 level
    ///   (Z3 ref: array_rewriter.cpp:206-239, up to 10 levels deep)
    /// - Constant-array no-op: store(const-array(v), i, v) → const-array(v)
    pub fn mk_store(&mut self, array: TermId, index: TermId, value: TermId) -> TermId {
        if !matches!(self.sort(array), Sort::Array(_)) {
            // Sort mismatch: caller passed a non-Array term. See mk_select
            // comment for the CHC paths that can trigger this.
            let array_sort = self.sort(array).clone();
            return self.intern(
                TermData::App(Symbol::named("store"), vec![array, index, value]),
                array_sort,
            );
        }
        if let Sort::Array(arr) = self.sort(array) {
            debug_assert!(
                self.sort(index) == &arr.index_sort,
                "BUG: mk_store index sort mismatch: expected {:?}, got {:?}",
                arr.index_sort,
                self.sort(index)
            );
            debug_assert!(
                self.sort(value) == &arr.element_sort,
                "BUG: mk_store value sort mismatch: expected {:?}, got {:?}",
                arr.element_sort,
                self.sort(value)
            );
        }
        let array_sort = self.sort(array).clone();

        // store(const-array(v), i, v) -> const-array(v)
        // Z3 ref: array_rewriter.cpp:184-189
        if self.get_const_array(array) == Some(value) {
            return array;
        }

        // Identity store elimination: store(a, i, select(a, i)) → a (#6282)
        if let TermData::App(Symbol::Named(n), a) = self.get(value) {
            if n == "select" && a.len() == 2 && a[0] == array && a[1] == index {
                return array;
            }
        }

        // Store-over-store and sort/squash rewrites require inner store
        if let TermData::App(Symbol::Named(name), args) = self.get(array) {
            if name == "store" && args.len() == 3 {
                let inner_index = args[1];
                let inner_array = args[0];
                let inner_value = args[2];

                if inner_index == index {
                    return self.mk_store(inner_array, index, value);
                }

                let rewrite = if self.store_chain_contains_index(inner_array, index) {
                    // #8785: if the outer index already occurs deeper in the
                    // chain, keep the raw topology instead of commuting the
                    // outer store inward until it collapses onto that older
                    // write. This narrows the concrete sort-store rewrite to
                    // non-duplicate concrete prefixes.
                    StoreIndexRewrite::Keep
                } else {
                    self.store_index_rewrite(index, inner_index)
                };

                match rewrite {
                    StoreIndexRewrite::Keep => {}
                    StoreIndexRewrite::SwapDistinct => {
                        let new_inner = self.mk_store(inner_array, index, value);
                        return self.mk_store(new_inner, inner_index, inner_value);
                    }
                }

                if let Some(squashed) =
                    self.squash_store(index, value, inner_array, inner_index, inner_value)
                {
                    return squashed;
                }
            }
        }

        self.intern(
            TermData::App(Symbol::named("store"), vec![array, index, value]),
            array_sort,
        )
    }

    /// Classify the rewrite to apply to a nested store pair.
    ///
    /// Concrete distinct indices can usually commute because distinctness is
    /// proven, but callers may still keep the raw order when a deeper duplicate
    /// index needs to be preserved for shadowed-store topology. Symbolic indices
    /// are left in their original order — the runtime array theory solver
    /// handles the semantic reasoning about index equality/disequality via
    /// ROW1/ROW2 lemmas.
    ///
    /// Prior to this change, symbolic indices triggered `SwapWithEqualityGuard`
    /// which generated `ite(i=j, ...)` terms. This caused combinatorial
    /// explosion on storeinv-family benchmarks where N symbolic swap indices
    /// produce O(2^N) ITE branches (#6367). Z3's approach handles this at the
    /// theory solver level with binary clauses, not at the term level.
    ///
    /// Z3 ref: array_rewriter.cpp:158-176 (concrete swap only; symbolic sorting
    /// uses AST ID ordering but does NOT generate ITE guards).
    fn store_index_rewrite(&self, index: TermId, inner_index: TermId) -> StoreIndexRewrite {
        if let (Some(idx_outer), Some(idx_inner)) = (self.get_int(index), self.get_int(inner_index))
        {
            if idx_inner > idx_outer {
                StoreIndexRewrite::SwapDistinct
            } else {
                StoreIndexRewrite::Keep
            }
        } else if let (Some((val_outer, w_outer)), Some((val_inner, w_inner))) =
            (self.get_bitvec(index), self.get_bitvec(inner_index))
        {
            if w_outer == w_inner && val_inner > val_outer {
                StoreIndexRewrite::SwapDistinct
            } else {
                StoreIndexRewrite::Keep
            }
        } else {
            // Symbolic indices: keep original order. Commuting stores requires
            // proven distinctness — if i and j are equal at runtime,
            // store(store(a,j,w),i,v) ≠ store(store(a,i,v),j,w) because the
            // outer store wins at the shared index.
            // Z3 ref: array_rewriter.cpp:130-139 returns l_undef for symbolic
            // indices, blocking sort_store. Only concrete constants go through
            // are_distinct().
            StoreIndexRewrite::Keep
        }
    }

    fn store_chain_contains_index(&self, mut array: TermId, index: TermId) -> bool {
        const MAX_DEPTH: usize = 64;
        let mut depth = 0usize;

        while depth < MAX_DEPTH {
            match self.get(array) {
                TermData::App(Symbol::Named(name), args) if name == "store" && args.len() == 3 => {
                    if args[1] == index {
                        return true;
                    }
                    array = args[0];
                    depth += 1;
                }
                _ => return false,
            }
        }

        false
    }

    /// Collapse store chains where the same index appears deeper than 1 level.
    ///
    /// Walks down the inner chain up to 10 levels. If a store at `index` is found,
    /// removes it by threading the base array through the intermediate parents,
    /// then wraps with `store(result, index, value)`.
    /// Z3 ref: array_rewriter.cpp:206-239
    fn squash_store(
        &mut self,
        index: TermId,
        value: TermId,
        inner_array: TermId,
        inner_index: TermId,
        inner_value: TermId,
    ) -> Option<TermId> {
        const MAX_DEPTH: usize = 10;
        if !self.are_provably_distinct_indices(index, inner_index) {
            return None;
        }

        let mut cursor = inner_array;
        let mut parents: Vec<(TermId, TermId)> = vec![(inner_index, inner_value)];
        let mut depth = 1usize;

        while depth < MAX_DEPTH {
            match self.get(cursor) {
                TermData::App(Symbol::Named(n), a) if n == "store" && a.len() == 3 => {
                    let cur_index = a[1];
                    let cur_value = a[2];
                    let cur_base = a[0];

                    if cur_index == index {
                        let mut result = cur_base;
                        for &(p_idx, p_val) in parents.iter().rev() {
                            result = self.mk_store(result, p_idx, p_val);
                        }
                        return Some(self.mk_store(result, index, value));
                    }

                    if !self.are_provably_distinct_indices(index, cur_index) {
                        return None;
                    }

                    parents.push((cur_index, cur_value));
                    cursor = cur_base;
                    depth += 1;
                }
                _ => return None,
            }
        }
        None
    }

    /// Check if two indices are provably distinct.
    ///
    /// Handles:
    /// - Concrete constants (Int, BV): direct comparison
    /// - Structural patterns: `bvadd(base, k1)` vs `bvadd(base, k2)` where
    ///   k1 != k2, and `bvadd(base, k)` vs `base` (where k != 0)
    ///
    /// The structural patterns are critical for QF_ABV byte-level memory access:
    /// `select(store(store(store(store(mem, bvadd(sp,0), v0), bvadd(sp,1), v1),
    ///   bvadd(sp,2), v2), bvadd(sp,3), v3), bvadd(sp2, k))` — the store chain
    /// uses `bvadd(base, offset)` indices that differ only in the constant offset.
    /// Without structural detection, these consume symbolic ITE budget and generate
    /// huge CNF encodings (150k+ vars from 60-line benchmarks).
    pub fn are_provably_distinct_indices(&self, a: TermId, b: TermId) -> bool {
        if a == b {
            return false;
        }
        // Check 1: concrete constants
        if let (Some(va), Some(vb)) = (self.get_int(a), self.get_int(b)) {
            return va != vb;
        }
        if let (Some((va, wa)), Some((vb, wb))) = (self.get_bitvec(a), self.get_bitvec(b)) {
            return wa == wb && va != vb;
        }
        // Check 2: structural bvadd/bvsub patterns
        if self.are_structurally_distinct_bv_indices(a, b) {
            return true;
        }
        // Check 3: structural Int offset patterns — `(+ base k1)` vs
        // `(+ base k2)` with `k1 != k2`, and `(+ base k)` vs `base` (`k != 0`).
        // Unlike the BV case there is no wraparound, so distinct constant
        // offsets of one base are unconditionally distinct. Critical for the
        // Ultimate-Automizer QF_ALIA memory encodings (cs_lazy.i_*), whose
        // store chains index one struct base at distinct byte offsets
        // (`(+ off 32)`, `(+ off 40)`, …): without this check every
        // read-over-write kept the whole chain symbolic, and the AUFLIA
        // Shannon ITE lift blew 2.5k terms up to the 200k budget.
        self.are_structurally_distinct_int_indices(a, b)
    }

    /// Decompose an Int index into `(base, constant_offset)` form.
    ///
    /// Returns `Some((base, offset))` for `(+ base k)` / `(+ k base)` /
    /// `(- base k)` with constant `k`, and `(base, 0)` for any other Int term.
    fn decompose_int_offset(&self, term: TermId) -> Option<(TermId, BigInt)> {
        if self.sort(term) != &Sort::Int {
            return None;
        }
        if let TermData::App(Symbol::Named(name), args) = self.get(term) {
            if args.len() == 2 {
                match name.as_str() {
                    "+" => {
                        if let Some(val) = self.get_int(args[1]) {
                            return Some((args[0], val.clone()));
                        }
                        if let Some(val) = self.get_int(args[0]) {
                            return Some((args[1], val.clone()));
                        }
                    }
                    "-" => {
                        if let Some(val) = self.get_int(args[1]) {
                            return Some((args[0], -val.clone()));
                        }
                    }
                    _ => {}
                }
            }
        }
        Some((term, BigInt::from(0u8)))
    }

    /// Check structural distinctness for Int index expressions: same base,
    /// different constant offsets (no overflow in Int, so always distinct).
    fn are_structurally_distinct_int_indices(&self, a: TermId, b: TermId) -> bool {
        let Some((base_a, off_a)) = self.decompose_int_offset(a) else {
            return false;
        };
        let Some((base_b, off_b)) = self.decompose_int_offset(b) else {
            return false;
        };
        base_a == base_b && off_a != off_b
    }

    /// Decompose a BV index into (base, constant_offset) form.
    ///
    /// Returns `Some((base, offset, width))` for patterns:
    /// - `bvadd(base, const)` -> (base, const, width)
    /// - `bvadd(const, base)` -> (base, const, width) [commutative]
    /// - `bvsub(base, const)` -> (base, -const mod 2^w, width)
    /// - bare `base` -> (base, 0, width) when base is a BV term
    fn decompose_bv_offset(&self, term: TermId) -> Option<(TermId, BigInt, u32)> {
        let width = match self.sort(term) {
            Sort::BitVec(bv) => bv.width,
            _ => return None,
        };

        match self.get(term) {
            TermData::App(Symbol::Named(name), args) if args.len() == 2 => {
                match name.as_str() {
                    "bvadd" => {
                        // bvadd(base, const) or bvadd(const, base)
                        if let Some((val, _)) = self.get_bitvec(args[1]) {
                            Some((args[0], val.clone(), width))
                        } else if let Some((val, _)) = self.get_bitvec(args[0]) {
                            Some((args[1], val.clone(), width))
                        } else {
                            None
                        }
                    }
                    "bvsub" => {
                        // bvsub(base, const) -> base + (-const mod 2^w)
                        if let Some((val, _)) = self.get_bitvec(args[1]) {
                            let modulus = BigInt::from(1u8) << width;
                            let neg_val = ((&modulus - val) % &modulus + &modulus) % &modulus;
                            Some((args[0], neg_val, width))
                        } else {
                            None
                        }
                    }
                    _ => None,
                }
            }
            _ => {
                // Bare BV term: offset = 0
                Some((term, BigInt::from(0u8), width))
            }
        }
    }

    /// Check structural distinctness for BV index expressions.
    ///
    /// Detects: `bvadd(base, k1)` vs `bvadd(base, k2)` where k1 != k2,
    /// and `bvadd(base, k)` vs `base` (implicit offset 0).
    fn are_structurally_distinct_bv_indices(&self, a: TermId, b: TermId) -> bool {
        let Some((base_a, off_a, w_a)) = self.decompose_bv_offset(a) else {
            return false;
        };
        let Some((base_b, off_b, w_b)) = self.decompose_bv_offset(b) else {
            return false;
        };
        // Same base, same width, different offsets
        base_a == base_b && w_a == w_b && off_a != off_b
    }

    /// Create a constant array: ((as const (Array T1 T2)) v)
    ///
    /// Returns an array where every index maps to the given default value.
    /// The array has sort (Array index_sort elem_sort) where elem_sort is the sort of the value.
    pub fn mk_const_array(&mut self, index_sort: Sort, value: TermId) -> TermId {
        let elem_sort = self.sort(value).clone();
        let array_sort = Sort::array(index_sort, elem_sort);

        self.intern(
            TermData::App(Symbol::named("const-array"), vec![value]),
            array_sort,
        )
    }

    /// Check if a term is a constant array, returning the default value if so
    pub fn get_const_array(&self, term: TermId) -> Option<TermId> {
        match self.get(term) {
            TermData::App(Symbol::Named(name), args)
                if name == "const-array" && args.len() == 1 =>
            {
                Some(args[0])
            }
            _ => None,
        }
    }

    /// Create a lambda array: `(lambda ((x T)) body)`
    ///
    /// Returns an array where `select(arr, i) = body[x/i]` (beta reduction).
    /// The array has sort `(Array index_sort body_sort)`.
    ///
    /// Internally represented as `App("lambda-array", [var_term, body_term])`.
    /// The `var_term` is a `Var` node used as the bound variable; `mk_select`
    /// performs beta reduction by substituting it with the index argument.
    ///
    /// Z3 ref: `theory_array_full.cpp:572` (`instantiate_default_lambda_def_axiom`)
    pub fn mk_lambda_array(&mut self, var_term: TermId, body: TermId) -> TermId {
        let index_sort = self.sort(var_term).clone();
        let elem_sort = self.sort(body).clone();
        let array_sort = Sort::array(index_sort, elem_sort);

        self.intern(
            TermData::App(Symbol::named("lambda-array"), vec![var_term, body]),
            array_sort,
        )
    }

    /// Check if a term is a lambda array, returning `(var_term, body)` if so.
    pub fn get_lambda_array(&self, term: TermId) -> Option<(TermId, TermId)> {
        match self.get(term) {
            TermData::App(Symbol::Named(name), args)
                if name == "lambda-array" && args.len() == 2 =>
            {
                Some((args[0], args[1]))
            }
            _ => None,
        }
    }

    /// Substitute all occurrences of `var_term` with `replacement` in `term`.
    ///
    /// Performs a recursive tree walk with memoization. Used for lambda array
    /// beta reduction: `select(lambda(x) body, idx) → body[x/idx]`.
    ///
    /// Respects variable scoping: does not substitute inside nested binders
    /// (forall/exists) that shadow the same variable name.
    pub fn substitute_var(
        &mut self,
        term: TermId,
        var_term: TermId,
        replacement: TermId,
    ) -> TermId {
        // Fast path: if the term IS the variable, return replacement.
        if term == var_term {
            return replacement;
        }

        // Extract the var name for shadow-checking inside binders.
        let var_name = match self.get(var_term) {
            TermData::Var(name, _) => name.clone(),
            _ => {
                // Not a variable term — nothing to substitute.
                return term;
            }
        };

        let mut cache = crate::kani_compat::det_hash_map_new();
        self.substitute_var_inner(term, var_term, replacement, &var_name, &mut cache)
    }

    fn substitute_var_inner(
        &mut self,
        term: TermId,
        var_term: TermId,
        replacement: TermId,
        var_name: &str,
        cache: &mut crate::kani_compat::DetHashMap<TermId, TermId>,
    ) -> TermId {
        if term == var_term {
            return replacement;
        }
        if let Some(&cached) = cache.get(&term) {
            return cached;
        }

        let result = match self.get(term).clone() {
            TermData::Const(_) => term,
            TermData::Var(_, _) => {
                // Different var (we already checked term == var_term above).
                term
            }
            TermData::App(sym, args) => {
                let mut changed = false;
                let new_args: Vec<TermId> = args
                    .iter()
                    .map(|&arg| {
                        let new_arg =
                            self.substitute_var_inner(arg, var_term, replacement, var_name, cache);
                        if new_arg != arg {
                            changed = true;
                        }
                        new_arg
                    })
                    .collect();
                if changed {
                    // Rebuild through the folding constructor so beta-reduced
                    // ground nodes collapse (e.g. `(+ 41 1)` -> `42`) exactly
                    // as if built directly — a raw intern here leaves an
                    // unfolded node the solver core does not evaluate.
                    self.rebuild_app(&sym, new_args, term)
                } else {
                    term
                }
            }
            TermData::Not(inner) => {
                let new_inner =
                    self.substitute_var_inner(inner, var_term, replacement, var_name, cache);
                if new_inner != inner {
                    self.mk_not(new_inner)
                } else {
                    term
                }
            }
            TermData::Ite(c, t, e) => {
                let new_c = self.substitute_var_inner(c, var_term, replacement, var_name, cache);
                let new_t = self.substitute_var_inner(t, var_term, replacement, var_name, cache);
                let new_e = self.substitute_var_inner(e, var_term, replacement, var_name, cache);
                if new_c != c || new_t != t || new_e != e {
                    self.mk_ite(new_c, new_t, new_e)
                } else {
                    term
                }
            }
            TermData::Let(bindings, body) => {
                let mut changed = false;
                let new_bindings: Vec<(String, TermId)> = bindings
                    .iter()
                    .map(|(name, val)| {
                        let new_val =
                            self.substitute_var_inner(*val, var_term, replacement, var_name, cache);
                        if new_val != *val {
                            changed = true;
                        }
                        (name.clone(), new_val)
                    })
                    .collect();
                // Check if any let binding shadows our variable.
                let shadowed = new_bindings.iter().any(|(name, _)| name == var_name);
                let new_body = if shadowed {
                    body
                } else {
                    let nb =
                        self.substitute_var_inner(body, var_term, replacement, var_name, cache);
                    if nb != body {
                        changed = true;
                    }
                    nb
                };
                if changed {
                    let sort = self.sort(term).clone();
                    self.intern(TermData::Let(new_bindings, new_body), sort)
                } else {
                    term
                }
            }
            TermData::Forall(bindings, body, triggers) => {
                // If the quantifier shadows our variable, do not descend.
                if bindings.iter().any(|(name, _)| name == var_name) {
                    term
                } else {
                    let new_body =
                        self.substitute_var_inner(body, var_term, replacement, var_name, cache);
                    if new_body != body {
                        let sort = self.sort(term).clone();
                        self.intern(TermData::Forall(bindings, new_body, triggers), sort)
                    } else {
                        term
                    }
                }
            }
            TermData::Exists(bindings, body, triggers) => {
                if bindings.iter().any(|(name, _)| name == var_name) {
                    term
                } else {
                    let new_body =
                        self.substitute_var_inner(body, var_term, replacement, var_name, cache);
                    if new_body != body {
                        let sort = self.sort(term).clone();
                        self.intern(TermData::Exists(bindings, new_body, triggers), sort)
                    } else {
                        term
                    }
                }
            }
        };

        cache.insert(term, result);
        result
    }

    /// Substitute whole sub-terms according to `map` (key term -> replacement),
    /// rebuilding the term DAG bottom-up. Keys are matched by term id, so a key
    /// must be a *closed* (ground) term to remain capture-free under binders;
    /// callers that only collect keys outside quantifier bodies satisfy this.
    pub fn substitute_terms(
        &mut self,
        term: TermId,
        map: &crate::kani_compat::DetHashMap<TermId, TermId>,
    ) -> TermId {
        if map.is_empty() {
            return term;
        }
        let mut cache = crate::kani_compat::det_hash_map_new();
        self.substitute_terms_inner(term, map, &mut cache)
    }

    fn substitute_terms_inner(
        &mut self,
        term: TermId,
        map: &crate::kani_compat::DetHashMap<TermId, TermId>,
        cache: &mut crate::kani_compat::DetHashMap<TermId, TermId>,
    ) -> TermId {
        if let Some(&r) = map.get(&term) {
            return r;
        }
        if let Some(&c) = cache.get(&term) {
            return c;
        }
        let result = match self.get(term).clone() {
            TermData::Const(_) | TermData::Var(_, _) => term,
            TermData::App(sym, args) => {
                let mut changed = false;
                let new_args: Vec<TermId> = args
                    .iter()
                    .map(|&arg| {
                        let na = self.substitute_terms_inner(arg, map, cache);
                        if na != arg {
                            changed = true;
                        }
                        na
                    })
                    .collect();
                if changed {
                    let sort = self.sort(term).clone();
                    self.intern(TermData::App(sym, new_args), sort)
                } else {
                    term
                }
            }
            TermData::Not(inner) => {
                let ni = self.substitute_terms_inner(inner, map, cache);
                if ni != inner {
                    self.mk_not(ni)
                } else {
                    term
                }
            }
            TermData::Ite(c, t, e) => {
                let nc = self.substitute_terms_inner(c, map, cache);
                let nt = self.substitute_terms_inner(t, map, cache);
                let ne = self.substitute_terms_inner(e, map, cache);
                if nc != c || nt != t || ne != e {
                    self.mk_ite(nc, nt, ne)
                } else {
                    term
                }
            }
            TermData::Let(bindings, body) => {
                let mut changed = false;
                let new_bindings: Vec<(String, TermId)> = bindings
                    .iter()
                    .map(|(name, val)| {
                        let nv = self.substitute_terms_inner(*val, map, cache);
                        if nv != *val {
                            changed = true;
                        }
                        (name.clone(), nv)
                    })
                    .collect();
                let nb = self.substitute_terms_inner(body, map, cache);
                if nb != body {
                    changed = true;
                }
                if changed {
                    let sort = self.sort(term).clone();
                    self.intern(TermData::Let(new_bindings, nb), sort)
                } else {
                    term
                }
            }
            TermData::Forall(bindings, body, triggers) => {
                let nb = self.substitute_terms_inner(body, map, cache);
                if nb != body {
                    let sort = self.sort(term).clone();
                    self.intern(TermData::Forall(bindings, nb, triggers), sort)
                } else {
                    term
                }
            }
            TermData::Exists(bindings, body, triggers) => {
                let nb = self.substitute_terms_inner(body, map, cache);
                if nb != body {
                    let sort = self.sort(term).clone();
                    self.intern(TermData::Exists(bindings, nb, triggers), sort)
                } else {
                    term
                }
            }
        };
        cache.insert(term, result);
        result
    }

    /// Create an as-array term: `(as-array f)`
    ///
    /// Converts a function symbol into an array term.
    /// The resulting array has sort `(Array index_sort element_sort)` derived from
    /// the function's signature: `f : index_sort -> element_sort`.
    /// The key axiom is: `select(as-array(f), i) = f(i)`.
    ///
    /// The `func_name` is the name of the declared function and `array_sort` is
    /// the resulting array sort (determined by the elaboration layer from the
    /// function's domain/range).
    pub fn mk_as_array(&mut self, func_name: &str, array_sort: Sort) -> TermId {
        debug_assert!(
            matches!(array_sort, Sort::Array(_)),
            "BUG: mk_as_array sort must be Array, got {array_sort:?}"
        );
        // as-array is represented as a nullary App with a special symbol that
        // encodes the function name. This mirrors Z3's OP_AS_ARRAY which carries
        // the function declaration as a parameter.
        self.intern(
            TermData::App(Symbol::named(format!("as-array[{func_name}]")), vec![]),
            array_sort,
        )
    }

    /// Check if a term is an as-array term, returning the function name if so.
    pub fn get_as_array_func(&self, term: TermId) -> Option<&str> {
        match self.get(term) {
            TermData::App(Symbol::Named(name), args) if args.is_empty() => name
                .strip_prefix("as-array[")
                .and_then(|s| s.strip_suffix(']')),
            _ => None,
        }
    }

    /// Create an array default term: `(default a)`
    ///
    /// Returns the default (else-case) value of an array.
    /// Key axioms:
    /// - `default(const(v)) = v`
    /// - `default(store(a, i, v)) = default(a)`
    /// - `default(as-array(f)) = f(epsilon)` (for some arbitrary epsilon)
    pub fn mk_array_default(&mut self, array: TermId) -> TermId {
        // Simplification: default(const-array(v)) = v
        if let Some(default_value) = self.get_const_array(array) {
            return default_value;
        }

        // Simplification: default(lambda-array(x, body)) = body
        // The default of a lambda array is the body with an unspecified index
        // (epsilon). Since the bound variable is free in the body, this returns
        // the body as-is (the variable acts as the epsilon witness).
        // Z3 ref: theory_array_full.cpp:572 (instantiate_default_lambda_def_axiom)
        if let Some((_var_term, body)) = self.get_lambda_array(array) {
            return body;
        }

        // Simplification: default(store(a, i, v)) = default(a)
        if let TermData::App(Symbol::Named(name), args) = self.get(array) {
            if name == "store" && args.len() == 3 {
                let base_array = args[0];
                return self.mk_array_default(base_array);
            }
        }

        let elem_sort = match self.sort(array) {
            Sort::Array(arr) => arr.element_sort.clone(),
            _ => {
                // Sort mismatch — return a dummy term (similar to mk_select fallback).
                return self.intern(
                    TermData::App(Symbol::named("default"), vec![array]),
                    Sort::Bool,
                );
            }
        };

        self.intern(
            TermData::App(Symbol::named("default"), vec![array]),
            elem_sort,
        )
    }

    /// Check if a term is an array default term, returning the array argument if so.
    pub fn get_array_default(&self, term: TermId) -> Option<TermId> {
        match self.get(term) {
            TermData::App(Symbol::Named(name), args) if name == "default" && args.len() == 1 => {
                // Only return if the argument has Array sort
                if matches!(self.sort(args[0]), Sort::Array(_)) {
                    Some(args[0])
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    /// Create an array map application: `map[f](a1, ..., an)`
    ///
    /// Applies function `f` pointwise over arrays. The result is an array
    /// with the same index sort as the input arrays and element sort equal
    /// to the return sort of `f`.
    ///
    /// The semantic axiom is:
    /// `select(map[f](a1, ..., an), i) = f(select(a1, i), ..., select(an, i))`
    ///
    /// The map term is represented as `App(Symbol::Named("map[<f>]"), [a1, ..., an])`
    /// where `<f>` is the mapped function name. The array solver detects map terms
    /// by the `"map["` prefix and generates select-map axioms on demand.
    ///
    /// Z3 ref: `array_decl_plugin.cpp:458-463` (OP_ARRAY_MAP)
    pub fn mk_array_map(
        &mut self,
        func_name: &str,
        arrays: Vec<TermId>,
        result_sort: Sort,
    ) -> TermId {
        let map_sym = format!("map[{func_name}]");
        self.intern(TermData::App(Symbol::named(map_sym), arrays), result_sort)
    }

    /// Check if a term is an array map application, returning the function name
    /// and the array arguments if so.
    pub fn get_array_map(&self, term: TermId) -> Option<(&str, &[TermId])> {
        match self.get(term) {
            TermData::App(Symbol::Named(name), args)
                if name.starts_with("map[") && name.ends_with(']') =>
            {
                let func_name = &name[4..name.len() - 1];
                Some((func_name, args))
            }
            _ => None,
        }
    }

    /// Lookup a named variable/constant
    pub fn lookup(&self, name: &str) -> Option<TermId> {
        self.names.get(name).map(|(id, _)| *id)
    }

    /// Check if a term is a Boolean constant
    pub fn is_bool_const(&self, id: TermId) -> Option<bool> {
        match self.get(id) {
            TermData::Const(Constant::Bool(b)) => Some(*b),
            _ => None,
        }
    }

    /// Check if a term is true
    pub fn is_true(&self, id: TermId) -> bool {
        self.is_bool_const(id) == Some(true)
    }

    /// Check if a term is false
    pub fn is_false(&self, id: TermId) -> bool {
        self.is_bool_const(id) == Some(false)
    }

    /// Get all children of a term
    pub fn children(&self, id: TermId) -> Vec<TermId> {
        match self.get(id) {
            TermData::Const(_) | TermData::Var(_, _) => vec![],
            TermData::App(_, args) => args.clone(),
            TermData::Let(bindings, body) => {
                let mut children: Vec<_> = bindings.iter().map(|(_, t)| *t).collect();
                children.push(*body);
                children
            }
            TermData::Not(t) => vec![*t],
            TermData::Ite(c, t, e) => vec![*c, *t, *e],
            TermData::Forall(_, body, _) | TermData::Exists(_, body, _) => vec![*body],
        }
    }
}
