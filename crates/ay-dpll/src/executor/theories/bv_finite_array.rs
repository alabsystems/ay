// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Fail-closed finite BV-array initializer rewrites for QF_ABV.
//!
//! SMT-COMP KLEE ABV instances commonly encode byte tables as thousands of
//! assertions `(= (select table #x000000NN) #x00)` and later read the table at
//! symbolic-but-range-bounded offsets. Eager FC axiom generation is too expensive
//! for those 2K direct selects. This pass keeps the direct facts and rewrites only
//! derived reads whose whole syntactic index interval is inside a dense same-value
//! run asserted for that exact array.

use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::term::{Constant, Symbol, TermData};
use ay_core::{Sort, TermId, TermStore};
use num_bigint::BigInt;
use num_traits::ToPrimitive;

use super::super::Executor;

const MIN_DENSE_RUN_LEN: u128 = 16;
const MAX_PREDICATE_ENUM_RANGE: u128 = 1024;
const MAX_SPARSE_PREDICATE_TERMS: usize = 32;

#[derive(Clone, Debug)]
struct DenseArrayInterval {
    start: u128,
    end: u128,
    value: TermId,
}

#[derive(Clone, Copy, Debug)]
struct BvRange {
    width: u32,
    lower: u128,
    upper: u128,
}

#[derive(Default)]
struct DenseArrayRewriteContext {
    intervals: HashMap<TermId, Vec<DenseArrayInterval>>,
    values: HashMap<TermId, HashMap<u128, TermId>>,
    rewrites: u64,
    exact_rewrites: u64,
    predicate_rewrites: u64,
    select_candidates: u64,
    range_misses: u64,
    interval_misses: u64,
    debug_misses_logged: u64,
}

#[derive(Default)]
struct DenseArrayCollectionSummary {
    defining_facts: u64,
    arrays_with_const_selects: u64,
    dense_arrays: u64,
    dense_intervals: u64,
    conflicted_arrays: u64,
}

impl Executor {
    pub(in crate::executor) fn rewrite_dense_bv_array_initializer_selects(&mut self) -> bool {
        let (values, intervals, defining_facts, collection) =
            self.collect_dense_bv_array_intervals();
        self.last_statistics.set_int(
            "smt.abv.finite_array.defining_facts",
            collection.defining_facts,
        );
        self.last_statistics.set_int(
            "smt.abv.finite_array.const_select_arrays",
            collection.arrays_with_const_selects,
        );
        self.last_statistics
            .set_int("smt.abv.finite_array.dense_arrays", collection.dense_arrays);
        self.last_statistics.set_int(
            "smt.abv.finite_array.dense_intervals",
            collection.dense_intervals,
        );
        self.last_statistics.set_int(
            "smt.abv.finite_array.conflicted_arrays",
            collection.conflicted_arrays,
        );

        if debug_abv_finite_array_enabled() {
            safe_eprintln!(
                "[abv-finite-array] facts={} const_select_arrays={} dense_arrays={} dense_intervals={} conflicted_arrays={}",
                collection.defining_facts,
                collection.arrays_with_const_selects,
                collection.dense_arrays,
                collection.dense_intervals,
                collection.conflicted_arrays
            );
        }

        if values.is_empty() {
            self.last_statistics
                .set_int("smt.abv.finite_array.select_candidates", 0);
            self.last_statistics
                .set_int("smt.abv.finite_array.exact_rewrites", 0);
            self.last_statistics
                .set_int("smt.abv.finite_array.predicate_rewrites", 0);
            self.last_statistics
                .set_int("smt.abv.finite_array.range_misses", 0);
            self.last_statistics
                .set_int("smt.abv.finite_array.interval_misses", 0);
            self.last_statistics
                .set_int("smt.abv.finite_array.rewrites", 0);
            return false;
        }

        let mut ctx = DenseArrayRewriteContext {
            intervals,
            values,
            rewrites: 0,
            exact_rewrites: 0,
            predicate_rewrites: 0,
            select_candidates: 0,
            range_misses: 0,
            interval_misses: 0,
            debug_misses_logged: 0,
        };
        let mut changed = false;
        let mut rewritten = Vec::with_capacity(self.ctx.assertions.len());
        let mut rewrite_cache = HashMap::default();
        let assertions = self.ctx.assertions.clone();

        for assertion in assertions {
            if defining_facts.contains(&assertion) {
                rewritten.push(assertion);
                continue;
            }

            let next = self.rewrite_dense_bv_array_term(assertion, &mut ctx, &mut rewrite_cache);
            changed |= next != assertion;
            rewritten.push(next);
        }

        self.last_statistics.set_int(
            "smt.abv.finite_array.select_candidates",
            ctx.select_candidates,
        );
        self.last_statistics
            .set_int("smt.abv.finite_array.exact_rewrites", ctx.exact_rewrites);
        self.last_statistics.set_int(
            "smt.abv.finite_array.predicate_rewrites",
            ctx.predicate_rewrites,
        );
        self.last_statistics
            .set_int("smt.abv.finite_array.range_misses", ctx.range_misses);
        self.last_statistics
            .set_int("smt.abv.finite_array.interval_misses", ctx.interval_misses);
        self.last_statistics
            .set_int("smt.abv.finite_array.rewrites", ctx.rewrites);

        if debug_abv_finite_array_enabled() {
            safe_eprintln!(
                "[abv-finite-array] select_candidates={} rewrites={} exact_rewrites={} predicate_rewrites={} range_misses={} interval_misses={}",
                ctx.select_candidates,
                ctx.rewrites,
                ctx.exact_rewrites,
                ctx.predicate_rewrites,
                ctx.range_misses,
                ctx.interval_misses
            );
        }

        if changed {
            self.ctx.assertions = rewritten;
        }

        changed
    }

    fn collect_dense_bv_array_intervals(
        &self,
    ) -> (
        HashMap<TermId, HashMap<u128, TermId>>,
        HashMap<TermId, Vec<DenseArrayInterval>>,
        HashSet<TermId>,
        DenseArrayCollectionSummary,
    ) {
        let mut entries_by_array: HashMap<TermId, Vec<(u128, TermId)>> = HashMap::default();
        let mut seen_values: HashMap<(TermId, u128), TermId> = HashMap::default();
        let mut conflicted_arrays = HashSet::default();
        let mut defining_facts = HashSet::default();
        let mut summary = DenseArrayCollectionSummary::default();

        for &assertion in &self.ctx.assertions {
            let Some((array, index, value)) = self.select_const_bv_equality(assertion) else {
                continue;
            };
            let Some((idx_value, _idx_width)) = const_bv_u128(&self.ctx.terms, index) else {
                continue;
            };
            if !matches!(
                self.ctx.terms.get(value),
                TermData::Const(Constant::BitVec { .. })
            ) {
                continue;
            }

            defining_facts.insert(assertion);
            summary.defining_facts += 1;
            match seen_values.insert((array, idx_value), value) {
                Some(existing) if existing != value => {
                    conflicted_arrays.insert(array);
                }
                Some(_) => {}
                None => {
                    entries_by_array
                        .entry(array)
                        .or_default()
                        .push((idx_value, value));
                }
            }
        }
        summary.arrays_with_const_selects = entries_by_array.len() as u64;
        summary.conflicted_arrays = conflicted_arrays.len() as u64;

        let mut values_by_array = HashMap::default();
        let mut intervals_by_array = HashMap::default();
        for (array, mut entries) in entries_by_array {
            if conflicted_arrays.contains(&array) {
                continue;
            }

            entries.sort_by_key(|(idx, _)| *idx);
            let values = entries.iter().copied().collect::<HashMap<_, _>>();
            values_by_array.insert(array, values);

            if entries.len() < MIN_DENSE_RUN_LEN as usize {
                continue;
            }

            let mut intervals = Vec::new();
            let mut run_start = entries[0].0;
            let mut run_end = entries[0].0;
            let mut run_value = entries[0].1;

            for &(idx, value) in entries.iter().skip(1) {
                if idx == run_end.saturating_add(1) && value == run_value {
                    run_end = idx;
                    continue;
                }

                if run_end - run_start + 1 >= MIN_DENSE_RUN_LEN {
                    intervals.push(DenseArrayInterval {
                        start: run_start,
                        end: run_end,
                        value: run_value,
                    });
                }
                run_start = idx;
                run_end = idx;
                run_value = value;
            }

            if run_end - run_start + 1 >= MIN_DENSE_RUN_LEN {
                intervals.push(DenseArrayInterval {
                    start: run_start,
                    end: run_end,
                    value: run_value,
                });
            }

            if !intervals.is_empty() {
                summary.dense_arrays += 1;
                summary.dense_intervals += intervals.len() as u64;
                intervals_by_array.insert(array, intervals);
            }
        }

        (values_by_array, intervals_by_array, defining_facts, summary)
    }

    fn select_const_bv_equality(&self, assertion: TermId) -> Option<(TermId, TermId, TermId)> {
        let TermData::App(sym, args) = self.ctx.terms.get(assertion) else {
            return None;
        };
        if sym.name() != "=" || args.len() != 2 {
            return None;
        }

        self.select_const_bv_side(args[0], args[1])
            .or_else(|| self.select_const_bv_side(args[1], args[0]))
    }

    fn select_const_bv_side(
        &self,
        select_term: TermId,
        value: TermId,
    ) -> Option<(TermId, TermId, TermId)> {
        let TermData::App(sym, args) = self.ctx.terms.get(select_term) else {
            return None;
        };
        if sym.name() != "select" || args.len() != 2 {
            return None;
        }
        const_bv_u128(&self.ctx.terms, args[1])?;
        Some((args[0], args[1], value))
    }

    fn select_bv_const_predicate(&self, equality: TermId) -> Option<(TermId, TermId, TermId)> {
        let TermData::App(sym, args) = self.ctx.terms.get(equality) else {
            return None;
        };
        if sym.name() != "=" || args.len() != 2 {
            return None;
        }

        self.select_bv_const_predicate_side(args[0], args[1])
            .or_else(|| self.select_bv_const_predicate_side(args[1], args[0]))
    }

    fn select_bv_const_predicate_side(
        &self,
        select_term: TermId,
        value: TermId,
    ) -> Option<(TermId, TermId, TermId)> {
        let TermData::App(sym, args) = self.ctx.terms.get(select_term) else {
            return None;
        };
        if sym.name() != "select" || args.len() != 2 {
            return None;
        }
        if !matches!(
            self.ctx.terms.get(value),
            TermData::Const(Constant::BitVec { .. })
        ) || self.ctx.terms.sort(select_term) != self.ctx.terms.sort(value)
        {
            return None;
        }
        Some((args[0], args[1], value))
    }

    fn masked_concat_select_zero_predicate(
        &self,
        equality: TermId,
    ) -> Option<(TermId, TermId, u128)> {
        let TermData::App(sym, args) = self.ctx.terms.get(equality) else {
            return None;
        };
        if sym.name() != "=" || args.len() != 2 {
            return None;
        }
        self.masked_concat_select_zero_side(args[0], args[1])
            .or_else(|| self.masked_concat_select_zero_side(args[1], args[0]))
    }

    fn masked_concat_select_zero_side(
        &self,
        zero_term: TermId,
        masked_term: TermId,
    ) -> Option<(TermId, TermId, u128)> {
        let (zero, zero_width) = const_bv_u128(&self.ctx.terms, zero_term)?;
        if zero != 0 {
            return None;
        }

        let TermData::App(sym, args) = self.ctx.terms.get(masked_term) else {
            return None;
        };
        if sym.name() != "bvand" || args.len() != 2 {
            return None;
        }

        for (value_term, mask_term) in [(args[0], args[1]), (args[1], args[0])] {
            let (mask, mask_width) = const_bv_u128(&self.ctx.terms, mask_term)?;
            if mask == 0
                || mask_width != zero_width
                || self.ctx.terms.sort(value_term) != self.ctx.terms.sort(mask_term)
            {
                continue;
            }
            if let Some(result) = self.masked_concat_select_source(value_term, mask) {
                return Some(result);
            }
        }

        None
    }

    fn masked_concat_select_source(
        &self,
        value_term: TermId,
        mask: u128,
    ) -> Option<(TermId, TermId, u128)> {
        let (value_term, mask) = self.strip_zero_extend_mask(value_term, mask)?;
        let mut leaves = Vec::new();
        self.flatten_concat_terms(value_term, &mut leaves);
        if leaves.is_empty() {
            leaves.push(value_term);
        }

        let mut bit_offset = 0u32;
        let mut matched = None;
        for &leaf in leaves.iter().rev() {
            let leaf_width = bv_width(&self.ctx.terms, leaf)?;
            let leaf_mask = bv_mask_u128(leaf_width)?;
            let shifted_leaf_mask = if bit_offset >= 128 {
                0
            } else {
                leaf_mask.checked_shl(bit_offset).unwrap_or(0)
            };
            let masked_bits = mask & shifted_leaf_mask;
            if masked_bits != 0 {
                if matched.is_some() {
                    return None;
                }
                let local_mask = masked_bits >> bit_offset;
                let TermData::App(sym, args) = self.ctx.terms.get(leaf) else {
                    return None;
                };
                if sym.name() != "select" || args.len() != 2 {
                    return None;
                }
                matched = Some((args[0], args[1], local_mask));
            }
            bit_offset = bit_offset.checked_add(leaf_width)?;
        }

        matched
    }

    fn strip_zero_extend_mask(&self, term: TermId, mask: u128) -> Option<(TermId, u128)> {
        let TermData::App(sym, args) = self.ctx.terms.get(term) else {
            return Some((term, mask));
        };
        if sym.name() != "zero_extend" || args.len() != 1 {
            return Some((term, mask));
        }
        let inner_width = bv_width(&self.ctx.terms, args[0])?;
        let inner_mask = bv_mask_u128(inner_width)?;
        if mask & !inner_mask != 0 {
            return None;
        }
        Some((args[0], mask))
    }

    fn flatten_concat_terms(&self, term: TermId, out: &mut Vec<TermId>) {
        let TermData::App(sym, args) = self.ctx.terms.get(term) else {
            out.push(term);
            return;
        };
        if sym.name() == "concat" && args.len() == 2 {
            self.flatten_concat_terms(args[0], out);
            self.flatten_concat_terms(args[1], out);
        } else {
            out.push(term);
        }
    }

    fn rewrite_dense_bv_array_term(
        &mut self,
        term: TermId,
        ctx: &mut DenseArrayRewriteContext,
        cache: &mut HashMap<TermId, TermId>,
    ) -> TermId {
        if let Some(&cached) = cache.get(&term) {
            return cached;
        }

        let rewritten = stacker::maybe_grow(64 * 1024, 1024 * 1024, || {
            match self.ctx.terms.get(term).clone() {
                TermData::Const(_) | TermData::Var(_, _) => term,
                TermData::App(sym, args) => {
                    if sym.name() == "=" && args.len() == 2 {
                        if let Some(result) = self
                            .dense_array_select_const_predicate_for_bool_eq(args[0], args[1], ctx)
                        {
                            ctx.rewrites += 1;
                            ctx.predicate_rewrites += 1;
                            return result;
                        }
                        if let Some(result) =
                            self.dense_array_select_const_predicate(term, true, ctx)
                        {
                            ctx.rewrites += 1;
                            ctx.predicate_rewrites += 1;
                            return result;
                        }
                        if let Some(result) =
                            self.dense_array_masked_select_zero_predicate(term, true, ctx)
                        {
                            ctx.rewrites += 1;
                            ctx.predicate_rewrites += 1;
                            return result;
                        }
                    }

                    let new_args: Vec<_> = args
                        .iter()
                        .map(|&arg| self.rewrite_dense_bv_array_term(arg, ctx, cache))
                        .collect();

                    if sym.name() == "select" && new_args.len() == 2 {
                        if let Some(value) =
                            self.dense_array_select_value(new_args[0], new_args[1], ctx)
                        {
                            ctx.rewrites += 1;
                            return value;
                        }
                    }

                    if new_args == args {
                        term
                    } else {
                        self.rebuild_bv_rewrite_app(term, sym, new_args)
                    }
                }
                TermData::Not(inner) => {
                    if let Some(result) = self.dense_array_select_const_predicate(inner, false, ctx)
                    {
                        ctx.rewrites += 1;
                        ctx.predicate_rewrites += 1;
                        return result;
                    }
                    if let Some(result) =
                        self.dense_array_masked_select_zero_predicate(inner, false, ctx)
                    {
                        ctx.rewrites += 1;
                        ctx.predicate_rewrites += 1;
                        return result;
                    }
                    let new_inner = self.rewrite_dense_bv_array_term(inner, ctx, cache);
                    if new_inner == inner {
                        term
                    } else {
                        self.ctx.terms.mk_not(new_inner)
                    }
                }
                TermData::Ite(cond, then_term, else_term) => {
                    let new_cond = self.rewrite_dense_bv_array_term(cond, ctx, cache);
                    let new_then = self.rewrite_dense_bv_array_term(then_term, ctx, cache);
                    let new_else = self.rewrite_dense_bv_array_term(else_term, ctx, cache);
                    if new_cond == cond && new_then == then_term && new_else == else_term {
                        term
                    } else {
                        self.ctx.terms.mk_ite(new_cond, new_then, new_else)
                    }
                }
                TermData::Let(bindings, body) => {
                    let mut changed = false;
                    let mut new_bindings = Vec::with_capacity(bindings.len());
                    for (name, value) in bindings {
                        let new_value = self.rewrite_dense_bv_array_term(value, ctx, cache);
                        changed |= new_value != value;
                        new_bindings.push((name, new_value));
                    }
                    let new_body = self.rewrite_dense_bv_array_term(body, ctx, cache);
                    changed |= new_body != body;
                    if changed {
                        self.ctx.terms.mk_let(new_bindings, new_body)
                    } else {
                        term
                    }
                }
                TermData::Forall(_, _, _) | TermData::Exists(_, _, _) => term,
                other => {
                    unreachable!("unhandled TermData variant in dense array rewrite: {other:?}")
                }
            }
        });

        cache.insert(term, rewritten);
        rewritten
    }

    fn dense_array_select_value(
        &self,
        array: TermId,
        index: TermId,
        ctx: &mut DenseArrayRewriteContext,
    ) -> Option<TermId> {
        let mut range_cache = HashMap::default();
        self.dense_array_select_value_inner(array, index, ctx, &mut range_cache, 0)
    }

    fn dense_array_select_const_predicate_for_bool_eq(
        &mut self,
        lhs: TermId,
        rhs: TermId,
        ctx: &mut DenseArrayRewriteContext,
    ) -> Option<TermId> {
        if let Some(want_equal) = bool_const(&self.ctx.terms, lhs) {
            return self.dense_array_select_const_predicate(rhs, want_equal, ctx);
        }
        if let Some(want_equal) = bool_const(&self.ctx.terms, rhs) {
            return self.dense_array_select_const_predicate(lhs, want_equal, ctx);
        }
        None
    }

    fn dense_array_select_const_predicate(
        &mut self,
        equality: TermId,
        want_equal: bool,
        ctx: &mut DenseArrayRewriteContext,
    ) -> Option<TermId> {
        let (array, index, value) = self.select_bv_const_predicate(equality)?;
        let mut range_cache = HashMap::default();
        self.dense_array_select_const_predicate_inner(
            array,
            index,
            value,
            want_equal,
            ctx,
            &mut range_cache,
            0,
        )
    }

    fn dense_array_masked_select_zero_predicate(
        &mut self,
        equality: TermId,
        want_equal: bool,
        ctx: &mut DenseArrayRewriteContext,
    ) -> Option<TermId> {
        let (array, index, local_mask) = self.masked_concat_select_zero_predicate(equality)?;
        let mut range_cache = HashMap::default();
        self.dense_array_masked_select_zero_predicate_inner(
            array,
            index,
            local_mask,
            want_equal,
            ctx,
            &mut range_cache,
            0,
        )
    }

    fn dense_array_masked_select_zero_predicate_inner(
        &mut self,
        array: TermId,
        index: TermId,
        local_mask: u128,
        want_zero: bool,
        ctx: &mut DenseArrayRewriteContext,
        range_cache: &mut HashMap<TermId, Option<BvRange>>,
        depth: usize,
    ) -> Option<TermId> {
        const MAX_STORE_PEELED_DEPTH: usize = 64;

        if local_mask == 0 {
            return Some(self.ctx.terms.mk_bool(want_zero));
        }

        if let Some((base, store_index, store_value)) = self.store_parts(array) {
            if index == store_index {
                let (store_value, _) = const_bv_u128(&self.ctx.terms, store_value)?;
                return Some(
                    self.ctx
                        .terms
                        .mk_bool(((store_value & local_mask) == 0) == want_zero),
                );
            }
            if depth < MAX_STORE_PEELED_DEPTH
                && bv_ranges_provably_disjoint(&self.ctx.terms, index, store_index, range_cache)
            {
                return self.dense_array_masked_select_zero_predicate_inner(
                    base,
                    index,
                    local_mask,
                    want_zero,
                    ctx,
                    range_cache,
                    depth + 1,
                );
            }
        }

        let values = ctx.values.get(&array)?;
        if const_bv_u128(&self.ctx.terms, index).is_some() {
            return None;
        }
        ctx.select_candidates += 1;
        let range = bv_range(&self.ctx.terms, index, range_cache)?;
        let range_len = range.upper.checked_sub(range.lower)?.checked_add(1)?;
        if range_len > MAX_PREDICATE_ENUM_RANGE {
            return None;
        }

        let mut satisfying = Vec::new();
        let mut failing = Vec::new();
        for idx in range.lower..=range.upper {
            let &entry_value = values.get(&idx)?;
            let (entry_value, _) = const_bv_u128(&self.ctx.terms, entry_value)?;
            if ((entry_value & local_mask) == 0) == want_zero {
                satisfying.push(idx);
            } else {
                failing.push(idx);
            }
        }

        if satisfying.len() <= failing.len() && satisfying.len() <= MAX_SPARSE_PREDICATE_TERMS {
            return Some(self.build_index_membership(index, range.width, &satisfying, true));
        }
        if failing.len() <= MAX_SPARSE_PREDICATE_TERMS {
            return Some(self.build_index_membership(index, range.width, &failing, false));
        }

        None
    }

    fn dense_array_select_const_predicate_inner(
        &mut self,
        array: TermId,
        index: TermId,
        value: TermId,
        want_equal: bool,
        ctx: &mut DenseArrayRewriteContext,
        range_cache: &mut HashMap<TermId, Option<BvRange>>,
        depth: usize,
    ) -> Option<TermId> {
        const MAX_STORE_PEELED_DEPTH: usize = 64;

        if let Some((base, store_index, store_value)) = self.store_parts(array) {
            if index == store_index {
                let equal = if store_value == value {
                    true
                } else {
                    const_bv_terms_equal(&self.ctx.terms, store_value, value)?
                };
                return Some(self.ctx.terms.mk_bool(equal == want_equal));
            }
            if depth < MAX_STORE_PEELED_DEPTH
                && bv_ranges_provably_disjoint(&self.ctx.terms, index, store_index, range_cache)
            {
                return self.dense_array_select_const_predicate_inner(
                    base,
                    index,
                    value,
                    want_equal,
                    ctx,
                    range_cache,
                    depth + 1,
                );
            }
        }

        let values = ctx.values.get(&array)?;
        if const_bv_u128(&self.ctx.terms, index).is_some() {
            return None;
        }
        ctx.select_candidates += 1;
        let range = bv_range(&self.ctx.terms, index, range_cache)?;
        let range_len = range.upper.checked_sub(range.lower)?.checked_add(1)?;
        if range_len > MAX_PREDICATE_ENUM_RANGE {
            return None;
        }

        let mut satisfying = Vec::new();
        let mut failing = Vec::new();
        for idx in range.lower..=range.upper {
            let &entry_value = values.get(&idx)?;
            let equal = if entry_value == value {
                true
            } else {
                const_bv_terms_equal(&self.ctx.terms, entry_value, value)?
            };
            if equal == want_equal {
                satisfying.push(idx);
            } else {
                failing.push(idx);
            }
        }

        if satisfying.len() <= failing.len() && satisfying.len() <= MAX_SPARSE_PREDICATE_TERMS {
            return Some(self.build_index_membership(index, range.width, &satisfying, true));
        }
        if failing.len() <= MAX_SPARSE_PREDICATE_TERMS {
            return Some(self.build_index_membership(index, range.width, &failing, false));
        }

        None
    }

    fn build_index_membership(
        &mut self,
        index: TermId,
        index_width: u32,
        indices: &[u128],
        positive: bool,
    ) -> TermId {
        if indices.is_empty() {
            return self.ctx.terms.mk_bool(!positive);
        }

        let mut terms = Vec::with_capacity(indices.len());
        for &idx in indices {
            let idx_term = self.ctx.terms.mk_bitvec(BigInt::from(idx), index_width);
            let eq = self.ctx.terms.mk_eq(index, idx_term);
            terms.push(if positive {
                eq
            } else {
                self.ctx.terms.mk_not(eq)
            });
        }

        if positive {
            self.ctx.terms.mk_or(terms)
        } else {
            self.ctx.terms.mk_and(terms)
        }
    }

    fn dense_array_select_value_inner(
        &self,
        array: TermId,
        index: TermId,
        ctx: &mut DenseArrayRewriteContext,
        range_cache: &mut HashMap<TermId, Option<BvRange>>,
        depth: usize,
    ) -> Option<TermId> {
        const MAX_STORE_PEELED_DEPTH: usize = 64;

        if let Some((base, store_index, store_value)) = self.store_parts(array) {
            if index == store_index {
                return Some(store_value);
            }
            if depth < MAX_STORE_PEELED_DEPTH
                && bv_ranges_provably_disjoint(&self.ctx.terms, index, store_index, range_cache)
            {
                return self.dense_array_select_value_inner(
                    base,
                    index,
                    ctx,
                    range_cache,
                    depth + 1,
                );
            }
        }

        let values = ctx.values.get(&array)?;
        ctx.select_candidates += 1;
        if let Some((idx, _)) = const_bv_u128(&self.ctx.terms, index) {
            if let Some(&value) = values.get(&idx) {
                ctx.exact_rewrites += 1;
                return Some(value);
            }
        }

        let Some(intervals) = ctx.intervals.get(&array) else {
            ctx.interval_misses += 1;
            self.debug_abv_finite_array_miss("interval", array, index, None, ctx);
            return None;
        };
        let Some(range) = bv_range(&self.ctx.terms, index, range_cache) else {
            ctx.range_misses += 1;
            self.debug_abv_finite_array_miss("range", array, index, None, ctx);
            return None;
        };
        let matched = intervals
            .iter()
            .find(|interval| range.lower >= interval.start && range.upper <= interval.end);
        if let Some(interval) = matched {
            Some(interval.value)
        } else {
            ctx.interval_misses += 1;
            self.debug_abv_finite_array_miss("interval", array, index, Some(range), ctx);
            None
        }
    }

    fn store_parts(&self, array: TermId) -> Option<(TermId, TermId, TermId)> {
        let TermData::App(sym, args) = self.ctx.terms.get(array) else {
            return None;
        };
        if sym.name() == "store" && args.len() == 3 {
            Some((args[0], args[1], args[2]))
        } else {
            None
        }
    }

    fn debug_abv_finite_array_miss(
        &self,
        reason: &str,
        array: TermId,
        index: TermId,
        range: Option<BvRange>,
        ctx: &mut DenseArrayRewriteContext,
    ) {
        if !debug_abv_finite_array_enabled() || ctx.debug_misses_logged >= 8 {
            return;
        }
        ctx.debug_misses_logged += 1;
        let interval_summary = ctx
            .intervals
            .get(&array)
            .map(|intervals| {
                intervals
                    .iter()
                    .take(3)
                    .map(|interval| format!("{}..{}", interval.start, interval.end))
                    .collect::<Vec<_>>()
                    .join(",")
            })
            .unwrap_or_default();
        let range_summary = range
            .map(|r| format!("{}..{}:{}", r.lower, r.upper, r.width))
            .unwrap_or_else(|| "unknown".to_string());
        safe_eprintln!(
            "[abv-finite-array] miss reason={} range={} intervals=[{}] index={}",
            reason,
            range_summary,
            interval_summary,
            self.format_term(index)
        );
    }

    fn rebuild_bv_rewrite_app(
        &mut self,
        original: TermId,
        sym: Symbol,
        args: Vec<TermId>,
    ) -> TermId {
        match sym.name() {
            "=" if args.len() == 2 => self.ctx.terms.mk_eq_coerce(args[0], args[1]),
            "distinct" => self.ctx.terms.mk_distinct(args),
            "and" => self.ctx.terms.mk_and(args),
            "or" => self.ctx.terms.mk_or(args),
            "=>" if args.len() == 2 => self.ctx.terms.mk_implies(args[0], args[1]),
            "xor" if args.len() == 2 => self.ctx.terms.mk_xor(args[0], args[1]),
            "+" => self.ctx.terms.mk_add(args),
            "-" => self.ctx.terms.mk_sub(args),
            "*" => self.ctx.terms.mk_mul(args),
            "<" if args.len() == 2 => self.ctx.terms.mk_lt(args[0], args[1]),
            "<=" if args.len() == 2 => self.ctx.terms.mk_le(args[0], args[1]),
            ">" if args.len() == 2 => self.ctx.terms.mk_gt(args[0], args[1]),
            ">=" if args.len() == 2 => self.ctx.terms.mk_ge(args[0], args[1]),
            "div" if args.len() == 2 => self.ctx.terms.mk_intdiv(args[0], args[1]),
            "mod" if args.len() == 2 => self.ctx.terms.mk_mod(args[0], args[1]),
            "abs" if args.len() == 1 => self.ctx.terms.mk_abs(args[0]),
            "bvadd" if args.len() == 2 => self.ctx.terms.mk_bvadd(args),
            "bvsub" if args.len() == 2 => self.ctx.terms.mk_bvsub(args),
            "bvmul" if args.len() == 2 => self.ctx.terms.mk_bvmul(args),
            "bvand" if args.len() == 2 => self.ctx.terms.mk_bvand(args),
            "bvor" if args.len() == 2 => self.ctx.terms.mk_bvor(args),
            "bvxor" if args.len() == 2 => self.ctx.terms.mk_bvxor(args),
            "bvnot" if args.len() == 1 => self.ctx.terms.mk_bvnot(args[0]),
            "bvneg" if args.len() == 1 => self.ctx.terms.mk_bvneg(args[0]),
            "bvnand" if args.len() == 2 => self.ctx.terms.mk_bvnand(args),
            "bvnor" if args.len() == 2 => self.ctx.terms.mk_bvnor(args),
            "bvxnor" if args.len() == 2 => self.ctx.terms.mk_bvxnor(args),
            "bvshl" if args.len() == 2 => self.ctx.terms.mk_bvshl(args),
            "bvlshr" if args.len() == 2 => self.ctx.terms.mk_bvlshr(args),
            "bvashr" if args.len() == 2 => self.ctx.terms.mk_bvashr(args),
            "bvudiv" if args.len() == 2 => self.ctx.terms.mk_bvudiv(args),
            "bvurem" if args.len() == 2 => self.ctx.terms.mk_bvurem(args),
            "bvsdiv" if args.len() == 2 => self.ctx.terms.mk_bvsdiv(args),
            "bvsrem" if args.len() == 2 => self.ctx.terms.mk_bvsrem(args),
            "bvsmod" if args.len() == 2 => self.ctx.terms.mk_bvsmod(args),
            "bvult" if args.len() == 2 => self.ctx.terms.mk_bvult(args[0], args[1]),
            "bvule" if args.len() == 2 => self.ctx.terms.mk_bvule(args[0], args[1]),
            "bvugt" if args.len() == 2 => self.ctx.terms.mk_bvugt(args[0], args[1]),
            "bvuge" if args.len() == 2 => self.ctx.terms.mk_bvuge(args[0], args[1]),
            "bvslt" if args.len() == 2 => self.ctx.terms.mk_bvslt(args[0], args[1]),
            "bvsle" if args.len() == 2 => self.ctx.terms.mk_bvsle(args[0], args[1]),
            "bvsgt" if args.len() == 2 => self.ctx.terms.mk_bvsgt(args[0], args[1]),
            "bvsge" if args.len() == 2 => self.ctx.terms.mk_bvsge(args[0], args[1]),
            "bvcomp" if args.len() == 2 => self.ctx.terms.mk_bvcomp(args[0], args[1]),
            "concat" if args.len() >= 2 => self.ctx.terms.mk_bvconcat(args),
            "select" if args.len() == 2 => self.ctx.terms.mk_select(args[0], args[1]),
            "store" if args.len() == 3 => self.ctx.terms.mk_store(args[0], args[1], args[2]),
            "extract" if args.len() == 1 => {
                if let Symbol::Indexed(_, indices) = &sym {
                    if indices.len() == 2 {
                        return self.ctx.terms.mk_bvextract(indices[0], indices[1], args[0]);
                    }
                }
                let sort = self.ctx.terms.sort(original).clone();
                self.ctx.terms.mk_app(sym, args, sort)
            }
            "zero_extend" if args.len() == 1 => {
                if let Symbol::Indexed(_, indices) = &sym {
                    if indices.len() == 1 {
                        return self.ctx.terms.mk_bvzero_extend(indices[0], args[0]);
                    }
                }
                let sort = self.ctx.terms.sort(original).clone();
                self.ctx.terms.mk_app(sym, args, sort)
            }
            "sign_extend" if args.len() == 1 => {
                if let Symbol::Indexed(_, indices) = &sym {
                    if indices.len() == 1 {
                        return self.ctx.terms.mk_bvsign_extend(indices[0], args[0]);
                    }
                }
                let sort = self.ctx.terms.sort(original).clone();
                self.ctx.terms.mk_app(sym, args, sort)
            }
            "repeat" if args.len() == 1 => {
                if let Symbol::Indexed(_, indices) = &sym {
                    if indices.len() == 1 {
                        return self.ctx.terms.mk_bvrepeat(indices[0], args[0]);
                    }
                }
                let sort = self.ctx.terms.sort(original).clone();
                self.ctx.terms.mk_app(sym, args, sort)
            }
            "rotate_left" if args.len() == 1 => {
                if let Symbol::Indexed(_, indices) = &sym {
                    if indices.len() == 1 {
                        return self.ctx.terms.mk_bvrotate_left(indices[0], args[0]);
                    }
                }
                let sort = self.ctx.terms.sort(original).clone();
                self.ctx.terms.mk_app(sym, args, sort)
            }
            "rotate_right" if args.len() == 1 => {
                if let Symbol::Indexed(_, indices) = &sym {
                    if indices.len() == 1 {
                        return self.ctx.terms.mk_bvrotate_right(indices[0], args[0]);
                    }
                }
                let sort = self.ctx.terms.sort(original).clone();
                self.ctx.terms.mk_app(sym, args, sort)
            }
            _ => {
                let sort = self.ctx.terms.sort(original).clone();
                self.ctx.terms.mk_app(sym, args, sort)
            }
        }
    }
}

fn debug_abv_finite_array_enabled() -> bool {
    ay_core::misc_cli_flags().debug_abv_finite_array
}

fn bv_range(
    terms: &TermStore,
    term: TermId,
    cache: &mut HashMap<TermId, Option<BvRange>>,
) -> Option<BvRange> {
    if let Some(&cached) = cache.get(&term) {
        return cached;
    }

    let range = stacker::maybe_grow(64 * 1024, 1024 * 1024, || match terms.get(term).clone() {
        TermData::Const(Constant::BitVec { value, width }) => {
            let value = value.to_u128()?;
            Some(BvRange {
                width,
                lower: value,
                upper: value,
            })
        }
        TermData::Var(_, _) => full_bv_range(terms, term),
        TermData::App(sym, args) => match sym.name() {
            "select" if args.len() == 2 => full_bv_range(terms, term),
            "bvadd" => bv_range_signed_bias_sum(terms, term, &args, cache)
                .or_else(|| bv_range_sum(terms, &args, cache)),
            "bvmul" => bv_range_product(terms, &args, cache),
            "bvand" => bv_range_bvand(terms, term, &args, cache),
            "concat" => bv_range_concat(terms, &args, cache),
            "extract" if args.len() == 1 => {
                if let Symbol::Indexed(_, indices) = &sym {
                    if indices.len() == 2 {
                        return bv_range_extract(terms, args[0], indices[0], indices[1], cache);
                    }
                }
                full_bv_range(terms, term)
            }
            "zero_extend" if args.len() == 1 => {
                if let Symbol::Indexed(_, indices) = &sym {
                    if indices.len() == 1 {
                        return bv_range_zero_extend(terms, term, args[0], indices[0], cache);
                    }
                }
                full_bv_range(terms, term)
            }
            "sign_extend" if args.len() == 1 => {
                if let Symbol::Indexed(_, indices) = &sym {
                    if indices.len() == 1 {
                        return bv_range_sign_extend(terms, term, args[0], indices[0], cache);
                    }
                }
                full_bv_range(terms, term)
            }
            "ite" if args.len() == 3 => {
                let then_range = bv_range(terms, args[1], cache)?;
                let else_range = bv_range(terms, args[2], cache)?;
                merge_same_width_ranges(then_range, else_range)
            }
            _ => full_bv_range(terms, term),
        },
        TermData::Ite(_, then_term, else_term) => {
            let then_range = bv_range(terms, then_term, cache)?;
            let else_range = bv_range(terms, else_term, cache)?;
            merge_same_width_ranges(then_range, else_range)
        }
        TermData::Not(_)
        | TermData::Let(_, _)
        | TermData::Forall(_, _, _)
        | TermData::Exists(_, _, _) => None,
        other => unreachable!("unhandled TermData variant in dense array range: {other:?}"),
    });

    cache.insert(term, range);
    range
}

fn bv_range_sum(
    terms: &TermStore,
    args: &[TermId],
    cache: &mut HashMap<TermId, Option<BvRange>>,
) -> Option<BvRange> {
    let width = bv_width(terms, *args.first()?)?;
    let mask = bv_mask_u128(width)?;
    let mut lower = 0u128;
    let mut upper = 0u128;
    for &arg in args {
        let range = bv_range(terms, arg, cache)?;
        if range.width != width {
            return None;
        }
        lower = lower.checked_add(range.lower)?;
        upper = upper.checked_add(range.upper)?;
        if upper > mask {
            return Some(BvRange {
                width,
                lower: 0,
                upper: mask,
            });
        }
    }
    Some(BvRange {
        width,
        lower,
        upper,
    })
}

fn bv_range_signed_bias_sum(
    terms: &TermStore,
    term: TermId,
    args: &[TermId],
    cache: &mut HashMap<TermId, Option<BvRange>>,
) -> Option<BvRange> {
    if args.len() != 2 {
        return None;
    }
    let term_width = bv_width(terms, term)?;
    let (bias, signed_term) = match (const_bv_u128(terms, args[0]), const_bv_u128(terms, args[1])) {
        (Some((bias, _)), None) => (bias, args[1]),
        (None, Some((bias, _))) => (bias, args[0]),
        _ => return None,
    };
    let TermData::App(sym, sign_args) = terms.get(signed_term) else {
        return None;
    };
    if sym.name() != "sign_extend" || sign_args.len() != 1 {
        return None;
    }
    let inner_width = bv_width(terms, sign_args[0])?;
    if inner_width == 0 || inner_width >= term_width || inner_width > 127 {
        return None;
    }
    if bias != (1u128 << (inner_width - 1)) {
        return None;
    }
    let inner = bv_range(terms, sign_args[0], cache)?;
    if inner.lower != 0 || inner.upper != bv_mask_u128(inner_width)? {
        return None;
    }
    Some(BvRange {
        width: term_width,
        lower: 0,
        upper: bv_mask_u128(inner_width)?,
    })
}

fn bv_range_product(
    terms: &TermStore,
    args: &[TermId],
    cache: &mut HashMap<TermId, Option<BvRange>>,
) -> Option<BvRange> {
    let width = bv_width(terms, *args.first()?)?;
    let mask = bv_mask_u128(width)?;
    let mut upper = 1u128;
    for &arg in args {
        let range = bv_range(terms, arg, cache)?;
        if range.width != width {
            return None;
        }
        upper = upper.checked_mul(range.upper)?;
        if upper > mask {
            return Some(BvRange {
                width,
                lower: 0,
                upper: mask,
            });
        }
    }
    Some(BvRange {
        width,
        lower: 0,
        upper,
    })
}

fn bv_range_bvand(
    terms: &TermStore,
    term: TermId,
    args: &[TermId],
    cache: &mut HashMap<TermId, Option<BvRange>>,
) -> Option<BvRange> {
    let width = bv_width(terms, term)?;
    let mut upper = bv_mask_u128(width)?;
    for &arg in args {
        let range = bv_range(terms, arg, cache)?;
        if range.width != width {
            return None;
        }
        upper = upper.min(range.upper);
    }
    Some(BvRange {
        width,
        lower: 0,
        upper,
    })
}

fn bv_range_concat(
    terms: &TermStore,
    args: &[TermId],
    cache: &mut HashMap<TermId, Option<BvRange>>,
) -> Option<BvRange> {
    let mut width = 0u32;
    let mut lower = 0u128;
    let mut upper = 0u128;

    for &arg in args {
        let range = bv_range(terms, arg, cache)?;
        width = width.checked_add(range.width)?;
        if width > 128 {
            return None;
        }
        lower = (lower << range.width) | range.lower;
        upper = (upper << range.width) | range.upper;
    }

    Some(BvRange {
        width,
        lower,
        upper,
    })
}

fn bv_range_extract(
    terms: &TermStore,
    arg: TermId,
    high: u32,
    low: u32,
    cache: &mut HashMap<TermId, Option<BvRange>>,
) -> Option<BvRange> {
    if high < low {
        return None;
    }
    let width = high - low + 1;
    let mask = bv_mask_u128(width)?;
    let inner = bv_range(terms, arg, cache)?;
    let inner_mask = bv_mask_u128(inner.width)?;
    let low_mask = if low == 0 { 0 } else { (1u128 << low) - 1 };
    let lower = if inner.upper <= inner_mask && inner.lower & low_mask == 0 {
        (inner.lower >> low).min(mask)
    } else {
        0
    };
    let upper = (inner.upper >> low).min(mask);
    Some(BvRange {
        width,
        lower,
        upper,
    })
}

fn bv_range_zero_extend(
    terms: &TermStore,
    term: TermId,
    arg: TermId,
    extra: u32,
    cache: &mut HashMap<TermId, Option<BvRange>>,
) -> Option<BvRange> {
    let mut range = bv_range(terms, arg, cache)?;
    range.width = range.width.checked_add(extra)?;
    if range.width > 128 {
        return full_bv_range(terms, term);
    }
    Some(range)
}

fn bv_range_sign_extend(
    terms: &TermStore,
    term: TermId,
    arg: TermId,
    extra: u32,
    cache: &mut HashMap<TermId, Option<BvRange>>,
) -> Option<BvRange> {
    let mut range = bv_range(terms, arg, cache)?;
    if range.width == 0 || range.width > 128 {
        return full_bv_range(terms, term);
    }
    let sign_bit = 1u128 << (range.width - 1);
    range.width = range.width.checked_add(extra)?;
    if range.width > 128 {
        return full_bv_range(terms, term);
    }
    if range.upper < sign_bit {
        Some(range)
    } else {
        full_bv_range(terms, term)
    }
}

fn merge_same_width_ranges(a: BvRange, b: BvRange) -> Option<BvRange> {
    if a.width != b.width {
        return None;
    }
    Some(BvRange {
        width: a.width,
        lower: a.lower.min(b.lower),
        upper: a.upper.max(b.upper),
    })
}

fn bv_ranges_provably_disjoint(
    terms: &TermStore,
    a: TermId,
    b: TermId,
    cache: &mut HashMap<TermId, Option<BvRange>>,
) -> bool {
    let Some(a_range) = bv_range(terms, a, cache) else {
        return false;
    };
    let Some(b_range) = bv_range(terms, b, cache) else {
        return false;
    };
    a_range.width == b_range.width
        && (a_range.upper < b_range.lower || b_range.upper < a_range.lower)
}

fn full_bv_range(terms: &TermStore, term: TermId) -> Option<BvRange> {
    let width = bv_width(terms, term)?;
    Some(BvRange {
        width,
        lower: 0,
        upper: bv_mask_u128(width)?,
    })
}

fn bv_width(terms: &TermStore, term: TermId) -> Option<u32> {
    match terms.sort(term) {
        Sort::BitVec(sort) if sort.width > 0 && sort.width <= 128 => Some(sort.width),
        _ => None,
    }
}

fn const_bv_u128(terms: &TermStore, term: TermId) -> Option<(u128, u32)> {
    match terms.get(term) {
        TermData::Const(Constant::BitVec { value, width }) if *width <= 128 => {
            Some((value.to_u128()?, *width))
        }
        _ => None,
    }
}

fn const_bv_terms_equal(terms: &TermStore, lhs: TermId, rhs: TermId) -> Option<bool> {
    let (lhs_value, lhs_width) = const_bv_u128(terms, lhs)?;
    let (rhs_value, rhs_width) = const_bv_u128(terms, rhs)?;
    (lhs_width == rhs_width).then_some(lhs_value == rhs_value)
}

fn bool_const(terms: &TermStore, term: TermId) -> Option<bool> {
    match terms.get(term) {
        TermData::Const(Constant::Bool(value)) => Some(*value),
        _ => None,
    }
}

fn bv_mask_u128(width: u32) -> Option<u128> {
    match width {
        0 => None,
        1..=127 => Some((1u128 << width) - 1),
        128 => Some(u128::MAX),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn sparse_predicate_same_index_symbolic_store_value_fails_closed_11924() {
        let mut exec = Executor::new();
        let index_sort = Sort::bitvec(8);
        let value_sort = Sort::bitvec(8);
        let array_sort = Sort::array(index_sort.clone(), value_sort.clone());
        let table = exec.ctx.terms.mk_var("table", array_sort);
        let index = exec.ctx.terms.mk_var("index", index_sort);
        let symbolic_value = exec.ctx.terms.mk_var("value", value_sort.clone());

        let zero_index = exec.ctx.terms.mk_bitvec(BigInt::from(0u8), 8);
        let zero_value = exec.ctx.terms.mk_bitvec(BigInt::from(0u8), 8);
        let defining_select = exec.ctx.terms.mk_select(table, zero_index);
        let defining_fact = exec.ctx.terms.mk_eq(defining_select, zero_value);

        let store = exec.ctx.terms.mk_store(table, index, symbolic_value);
        let raw_select =
            exec.ctx
                .terms
                .mk_app(Symbol::named("select"), vec![store, index], value_sort);
        let target_value = exec.ctx.terms.mk_bitvec(BigInt::from(5u8), 8);
        let predicate = exec.ctx.terms.mk_eq(raw_select, target_value);
        exec.ctx.assertions.push(defining_fact);
        exec.ctx.assertions.push(predicate);

        assert!(exec.rewrite_dense_bv_array_initializer_selects());

        let expected = exec.ctx.terms.mk_eq(symbolic_value, target_value);
        assert_eq!(exec.ctx.assertions[1], expected);
        assert_ne!(exec.ctx.assertions[1], exec.ctx.terms.false_term());
        assert_eq!(
            exec.last_statistics
                .get_int("smt.abv.finite_array.predicate_rewrites")
                .unwrap_or(0),
            0
        );
    }

    #[test]
    fn masked_predicate_same_index_symbolic_store_value_fails_closed_11924() {
        let mut exec = Executor::new();
        let index_sort = Sort::bitvec(8);
        let value_sort = Sort::bitvec(8);
        let array_sort = Sort::array(index_sort.clone(), value_sort.clone());
        let table = exec.ctx.terms.mk_var("table", array_sort);
        let index = exec.ctx.terms.mk_var("index", index_sort);
        let symbolic_value = exec.ctx.terms.mk_var("value", value_sort.clone());

        let zero_index = exec.ctx.terms.mk_bitvec(BigInt::from(0u8), 8);
        let zero_value = exec.ctx.terms.mk_bitvec(BigInt::from(0u8), 8);
        let defining_select = exec.ctx.terms.mk_select(table, zero_index);
        let defining_fact = exec.ctx.terms.mk_eq(defining_select, zero_value);

        let store = exec.ctx.terms.mk_store(table, index, symbolic_value);
        let raw_select =
            exec.ctx
                .terms
                .mk_app(Symbol::named("select"), vec![store, index], value_sort);
        let zero = exec.ctx.terms.mk_bitvec(BigInt::from(0u8), 8);
        let mask = exec.ctx.terms.mk_bitvec(BigInt::from(1u8), 8);
        let masked = exec.ctx.terms.mk_bvand(vec![raw_select, mask]);
        let predicate = exec.ctx.terms.mk_eq(zero, masked);
        exec.ctx.assertions.push(defining_fact);
        exec.ctx.assertions.push(predicate);

        assert!(exec.rewrite_dense_bv_array_initializer_selects());

        assert_ne!(exec.ctx.assertions[1], exec.ctx.terms.true_term());
        assert_ne!(exec.ctx.assertions[1], exec.ctx.terms.false_term());
        assert_eq!(
            exec.last_statistics
                .get_int("smt.abv.finite_array.predicate_rewrites")
                .unwrap_or(0),
            0
        );
    }
}
