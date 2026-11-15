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

    /// (#proof-capability) The proof-carrying subset of
    /// [`Self::rewrite_dense_bv_array_initializer_selects`], computed as a
    /// WINDOW rather than written to the root assertion vector: ONLY the
    /// exact cell fold `(select A k) -> v` licensed by a top-level defining
    /// fact `(= (select A k) v)` (either spelling; `k` and `v` bit-vector
    /// constants), and only for a cell every such fact agrees on.
    ///
    /// The full pass is gated off under proof production for two reasons
    /// this method respects. Its interval, predicate and masked-concat
    /// rewrites have no derivation the proof replay could re-check, so only
    /// the exact fold is taken — the shape the `PropagateValues` provenance
    /// channel already carries (an entry `expr ↦ value` licensed by an
    /// asserted defining equality, plus one `before -> after` record per
    /// rewritten assertion), returned here for the caller to merge through
    /// [`Executor::merge_propagation_records`] like the harness's own
    /// substitution rewrites. And a rewrite of the ROOT vector would make the
    /// checked SAT refutation's frozen roots differ from the exact public
    /// query roots (measured: `unknown (incomplete self-check-rejected)` on a
    /// quantifier-free reduction), so the fold is handed back as a window
    /// for one theory lane to install and restore, exactly as that lane
    /// already scopes its bridge assertions. The defining facts themselves
    /// are left untouched (they stay the replay's premises); only OTHER
    /// assertions mentioning the cell are rewritten.
    ///
    /// Why it exists: under proof production the deductive-checks set-fold ground
    /// core (`C_sets/87167-00066`, its 6-assertion reduction) reached the
    /// BV/LIA bridge lane with `(bvadd (select state 0) (select ordering 0))`
    /// still in place; the bridge's `bv2nat` decomposition of that sum ties
    /// both arrays into the arithmetic lane, whose candidate model the strict
    /// gate refuses (`arrays-read-conflict-uneval`), and the query was left
    /// `unknown (incomplete)` where the no-proof run — whose full dense pass
    /// folds `(select state 0)` to `#x0` and the sum to a single read — answers
    /// `unsat` (z3: `unsat`). Same fold, now with the provenance the proof
    /// lane demands and without touching the authored roots.
    ///
    /// Sound: each rewrite replaces a term by one an asserted top-level
    /// equality makes equal to it, in a conjunction that keeps that equality.
    /// `None` when nothing folds.
    pub(in crate::executor) fn pinned_bv_array_read_fold_window(
        &mut self,
    ) -> Option<(Vec<TermId>, crate::preprocess::PropagationRecords)> {
        if !crate::quant_unit_authority::quant_unit_authority_enabled() {
            return None;
        }
        let mut subst: HashMap<TermId, TermId> = HashMap::default();
        let mut sources: HashMap<TermId, TermId> = HashMap::default();
        let mut conflicted: HashSet<TermId> = HashSet::default();
        let mut facts: HashSet<TermId> = HashSet::default();
        for &assertion in &self.ctx.assertions {
            let Some((array, index, value)) = self.select_const_bv_equality(assertion) else {
                continue;
            };
            if !matches!(
                self.ctx.terms.get(value),
                TermData::Const(Constant::BitVec { .. })
            ) {
                continue;
            }
            let Some(select) = self.pinned_select_term(assertion, array, index) else {
                continue;
            };
            match subst.insert(select, value) {
                Some(existing) if existing != value => {
                    conflicted.insert(select);
                }
                _ => {}
            }
            sources.entry(select).or_insert(assertion);
            facts.insert(assertion);
        }
        for select in &conflicted {
            subst.remove(select);
            sources.remove(select);
        }
        if subst.is_empty() {
            return None;
        }

        let mut pv = crate::preprocess::PropagateValues::new();
        pv.seed_substitution(&subst);
        let mut rewrites: Vec<crate::preprocess::PropagatedRewriteRecord> = Vec::new();
        let mut window = Vec::with_capacity(self.ctx.assertions.len());
        for i in 0..self.ctx.assertions.len() {
            let before = self.ctx.assertions[i];
            if facts.contains(&before) {
                window.push(before);
                continue;
            }
            let after = pv.rewrite_seeded(&mut self.ctx.terms, before);
            if after != before {
                rewrites.push(crate::preprocess::PropagatedRewriteRecord {
                    before,
                    after,
                    stamp: 1,
                });
            }
            window.push(after);
        }
        if rewrites.is_empty() {
            return None;
        }
        let entries: Vec<crate::preprocess::PropagatedEntrySource> = subst
            .iter()
            .filter_map(|(&expr, &value)| {
                let source_assertion = *sources.get(&expr)?;
                Some(crate::preprocess::PropagatedEntrySource {
                    expr,
                    value,
                    source_assertion,
                    stamp: 1,
                })
            })
            .collect();
        self.last_statistics.set_int(
            "smt.abv.finite_array.pinned_read_proof_rewrites",
            rewrites.len() as u64,
        );
        Some((
            window,
            crate::preprocess::PropagationRecords {
                rewrites,
                entries,
                ..crate::preprocess::PropagationRecords::default()
            },
        ))
    }

    /// The `(select array index)` side of a defining fact, as the term the
    /// fact actually mentions (never a rebuilt one, so the recorded entry's
    /// `expr` is the exact subterm the rewrite replaces).
    fn pinned_select_term(
        &self,
        assertion: TermId,
        array: TermId,
        index: TermId,
    ) -> Option<TermId> {
        let TermData::App(_, args) = self.ctx.terms.get(assertion) else {
            return None;
        };
        args.iter().copied().find(|&side| {
            matches!(
                self.ctx.terms.get(side),
                TermData::App(sym, sargs)
                    if sym.name() == "select" && sargs.len() == 2 && sargs[0] == array && sargs[1] == index
            )
        })
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
        // Any other shape has no bit-vector range, and every caller reads
        // `None` as "decline the dense rewrite". The index of a select reached
        // here need not be a bit-vector: fresh nestfin_2909_0018 --z3-mode
        // (`(select (store m0 true b0) false)` on an `(Array Bool (Array (_
        // BitVec 2) (_ BitVec 2)))`) handed the Bool constant `false` to this
        // match, whose last arm was `unreachable!` -- a panic, then `unknown`
        // where z3 5.1.0 and the default posture answer `unsat`.
        _ => None,
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
        // A 128-bit first operand shifts the empty prefix by 128, which
        // `<<` rejects (overflow checks are on in release); the prefix is 0.
        lower = lower.checked_shl(range.width).unwrap_or(0) | range.lower;
        upper = upper.checked_shl(range.width).unwrap_or(0) | range.upper;
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
    let inner = bv_range(terms, arg, cache)?;
    extract_range(inner, high, low)
}

/// The range of `extract[high:low](v)` for every `v` in `inner`.
fn extract_range(inner: BvRange, high: u32, low: u32) -> Option<BvRange> {
    if high < low {
        return None;
    }
    let width = high - low + 1;
    let mask = bv_mask_u128(width)?;
    if high >= inner.width || inner.lower > inner.upper {
        return full_bv_range_of_width(width);
    }
    // `extract[high:low](v) = (v >> low) mod 2^width`. The shift is monotone,
    // so `v >> low` ranges over `[lower >> low, upper >> low]`, and the
    // reduction mod 2^width keeps that order only while both ends lie in one
    // period of 2^width (`lower >> (high+1) == upper >> (high+1)`); across a
    // period boundary the image wraps and is taken as the whole width. The
    // reduction is `& mask`, not a clamp: `extract[7:0]` of `[256, 300]` is
    // `[0, 44]`, where `min(v >> low, mask)` claimed `[255, 255]` and the
    // dense-table rewrite then read one cell for a read that can touch 45.
    let shifted_lower = inner.lower.checked_shr(low).unwrap_or(0);
    let shifted_upper = inner.upper.checked_shr(low).unwrap_or(0);
    if shifted_lower.checked_shr(width).unwrap_or(0)
        != shifted_upper.checked_shr(width).unwrap_or(0)
    {
        return full_bv_range_of_width(width);
    }
    Some(BvRange {
        width,
        lower: shifted_lower & mask,
        upper: shifted_upper & mask,
    })
}

fn full_bv_range_of_width(width: u32) -> Option<BvRange> {
    Some(BvRange {
        width,
        lower: 0,
        upper: bv_mask_u128(width)?,
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

    /// #proof-capability: the windowed pinned-read fold replaces
    /// `(select a 0)` inside the sum by its pinned `#x00` and folds the sum,
    /// hands back one rewrite record licensed by the pin, keeps the pin
    /// itself verbatim, and never touches the root assertion vector.
    #[test]
    fn pinned_read_fold_window_folds_the_sum_and_keeps_the_roots() {
        let mut exec = Executor::new();
        let index_sort = Sort::bitvec(8);
        let value_sort = Sort::bitvec(8);
        let array_sort = Sort::array(index_sort.clone(), value_sort.clone());
        let a = exec.ctx.terms.mk_var("a", array_sort);
        let zero = exec.ctx.terms.mk_bitvec(BigInt::from(0u8), 8);
        let one = exec.ctx.terms.mk_bitvec(BigInt::from(1u8), 8);
        let nine = exec.ctx.terms.mk_bitvec(BigInt::from(9u8), 8);
        let a0 = exec.ctx.terms.mk_select(a, zero);
        let a1 = exec.ctx.terms.mk_select(a, one);
        // The pin, spelled value-first as deductive-checks spells it.
        let pin = exec.ctx.terms.mk_eq(zero, a0);
        let sum = exec
            .ctx
            .terms
            .mk_app(Symbol::named("bvadd"), vec![a0, nine], value_sort);
        let step = exec.ctx.terms.mk_eq(sum, a1);
        exec.ctx.assertions.push(pin);
        exec.ctx.assertions.push(step);
        let roots = exec.ctx.assertions.clone();

        let (window, records) = exec
            .pinned_bv_array_read_fold_window()
            .expect("the pinned read folds");
        assert_eq!(exec.ctx.assertions, roots, "the roots must not move");
        assert_eq!(window.len(), 2);
        assert_eq!(window[0], pin, "the defining fact stays verbatim");
        let expected = exec.ctx.terms.mk_eq(nine, a1);
        assert_eq!(
            window[1], expected,
            "`#x00 + #x09` folds to the pinned value"
        );
        assert_eq!(records.rewrites.len(), 1);
        assert_eq!(records.rewrites[0].before, step);
        assert_eq!(records.rewrites[0].after, expected);
        assert_eq!(records.entries.len(), 1);
        assert_eq!(records.entries[0].expr, a0);
        assert_eq!(records.entries[0].value, zero);
        assert_eq!(records.entries[0].source_assertion, pin);
    }

    /// Two facts disagreeing on one cell license nothing: the window is
    /// declined rather than built from either value.
    #[test]
    fn pinned_read_fold_window_declines_a_conflicted_cell() {
        let mut exec = Executor::new();
        let index_sort = Sort::bitvec(8);
        let value_sort = Sort::bitvec(8);
        let array_sort = Sort::array(index_sort.clone(), value_sort.clone());
        let a = exec.ctx.terms.mk_var("a", array_sort);
        let zero = exec.ctx.terms.mk_bitvec(BigInt::from(0u8), 8);
        let one = exec.ctx.terms.mk_bitvec(BigInt::from(1u8), 8);
        let nine = exec.ctx.terms.mk_bitvec(BigInt::from(9u8), 8);
        let a0 = exec.ctx.terms.mk_select(a, zero);
        let a1 = exec.ctx.terms.mk_select(a, one);
        let pin_zero = exec.ctx.terms.mk_eq(a0, zero);
        let pin_one = exec.ctx.terms.mk_eq(a0, one);
        let sum = exec
            .ctx
            .terms
            .mk_app(Symbol::named("bvadd"), vec![a0, nine], value_sort);
        let step = exec.ctx.terms.mk_eq(sum, a1);
        exec.ctx.assertions.push(pin_zero);
        exec.ctx.assertions.push(pin_one);
        exec.ctx.assertions.push(step);
        assert!(exec.pinned_bv_array_read_fold_window().is_none());
    }

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

    // ---- D9 (2026-09-23 hunt): `bv_range_extract` ignored the wrap ----
    //
    // The syntactic index range feeds three rewrites that each replace a
    // read by what the table holds on EVERY index of the range: the value
    // rewrite, the predicate enumeration, and store peeling through
    // `bv_ranges_provably_disjoint`. A range that misses a reachable index
    // therefore proves a false equality. `extract[7:0]` of an index in
    // `[256, 511]` was given the range `[255, 255]` (a clamp, not the
    // reduction mod 2^8), so a read of every low byte was folded against the
    // single cell `T[255]`. The generators below check the range lattice
    // against the operators' definitions, not against the implementation.

    /// xorshift64: deterministic, so a failure replays from its case number.
    struct XorShift(u64);

    impl XorShift {
        fn next(&mut self) -> u64 {
            self.0 ^= self.0 << 13;
            self.0 ^= self.0 >> 7;
            self.0 ^= self.0 << 17;
            self.0
        }

        fn below(&mut self, n: u64) -> u64 {
            self.next() % n
        }

        fn range_u32(&mut self, lo: u32, hi: u32) -> u32 {
            lo + self.below(u64::from(hi - lo) + 1) as u32
        }

        fn range_u128(&mut self, lo: u128, hi: u128) -> u128 {
            let raw = (u128::from(self.next()) << 64) | u128::from(self.next());
            match (hi - lo).checked_add(1) {
                Some(span) => lo + raw % span,
                None => raw,
            }
        }
    }

    fn mask_of(width: u32) -> u128 {
        bv_mask_u128(width).expect("test widths are 1..=128")
    }

    /// Exhaustive over every interval of every inner width up to 6 bits and
    /// every `extract[high:low]`: the range contains each extracted value, and
    /// is exactly their hull when the interval does not cross a period of
    /// `2^(high+1)`.
    #[test]
    fn extract_range_contains_every_extracted_value_exhaustive_d9() {
        for inner_width in 1..=6u32 {
            let top = mask_of(inner_width);
            for lower in 0..=top {
                for upper in lower..=top {
                    let inner = BvRange {
                        width: inner_width,
                        lower,
                        upper,
                    };
                    for high in 0..inner_width {
                        for low in 0..=high {
                            let got = extract_range(inner, high, low)
                                .expect("a well-formed extract has a range");
                            assert_eq!(got.width, high - low + 1);
                            let mask = mask_of(got.width);
                            let (mut min, mut max) = (u128::MAX, 0u128);
                            for v in lower..=upper {
                                let e = (v >> low) & mask;
                                assert!(
                                    got.lower <= e && e <= got.upper,
                                    "extract[{high}:{low}] of {v} in [{lower}, {upper}] \
                                     (width {inner_width}) is {e}, outside the claimed \
                                     [{}, {}]",
                                    got.lower,
                                    got.upper
                                );
                                min = min.min(e);
                                max = max.max(e);
                            }
                            if lower >> (high + 1) == upper >> (high + 1) {
                                assert_eq!(
                                    (got.lower, got.upper),
                                    (min, max),
                                    "extract[{high}:{low}] of [{lower}, {upper}] stays in one \
                                     period, so its range is exact"
                                );
                            }
                        }
                    }
                }
            }
        }
    }

    /// The witness shapes themselves: `extract[7:0]` of `[256, 511]` is every
    /// byte, of `[300, 363]` (`(bvadd (bvand y #x3f) #x12c)`) it is
    /// `[44, 107]`, and of `[250, 260]` (a real wrap) it is every byte —
    /// never `[255, 255]`.
    #[test]
    fn extract_range_of_the_hunt_witness_intervals_d9() {
        let range = |lower, upper| {
            let got = extract_range(
                BvRange {
                    width: 16,
                    lower,
                    upper,
                },
                7,
                0,
            )
            .expect("a well-formed extract");
            (got.width, got.lower, got.upper)
        };
        assert_eq!(range(256, 511), (8, 0, 255));
        assert_eq!(range(300, 363), (8, 44, 107));
        assert_eq!(range(250, 260), (8, 0, 255));
    }

    /// Random intervals over every inner width up to 128 bits, half of them
    /// straddling a multiple of `2^(high+1)` (the wrap). Each interval is
    /// probed at its ends, next to every period boundary it crosses (up to
    /// eight), and at random interior points.
    #[test]
    fn extract_range_contains_wrapping_intervals_up_to_128_bits_d9() {
        let mut rng = XorShift(0x9e37_79b9_7f4a_7c15);
        for case in 0..20_000u32 {
            let inner_width = rng.range_u32(1, 128);
            let high = rng.range_u32(0, inner_width - 1);
            let low = rng.range_u32(0, high);
            let top = mask_of(inner_width);
            let period_bits = high + 1;
            let (lower, upper) = if period_bits < inner_width && rng.below(2) == 0 {
                // Straddle a period boundary of the extract.
                let boundary = rng.range_u128(1, top >> period_bits) << period_bits;
                let below = rng.range_u128(1, 1u128 << period_bits.min(20));
                let above = rng.range_u128(0, 1u128 << period_bits.min(20));
                (
                    boundary.saturating_sub(below),
                    boundary.saturating_add(above).min(top),
                )
            } else {
                let a = rng.range_u128(0, top);
                let b = rng.range_u128(0, top);
                (a.min(b), a.max(b))
            };
            let inner = BvRange {
                width: inner_width,
                lower,
                upper,
            };
            let got = extract_range(inner, high, low).expect("a well-formed extract");
            let mask = mask_of(got.width);
            let mut probes = vec![lower, upper, lower.saturating_add(1).min(upper)];
            probes.push(upper.saturating_sub(1).max(lower));
            if period_bits < 128 {
                let step = 1u128 << period_bits;
                let mut boundary = ((lower >> period_bits) + 1).checked_mul(step);
                for _ in 0..8 {
                    let Some(at) = boundary.filter(|&at| at <= upper) else {
                        break;
                    };
                    probes.push(at - 1);
                    probes.push(at);
                    boundary = at.checked_add(step);
                }
            }
            for _ in 0..8 {
                probes.push(rng.range_u128(lower, upper));
            }
            for v in probes {
                let e = (v >> low) & mask;
                assert!(
                    got.lower <= e && e <= got.upper,
                    "case {case}: extract[{high}:{low}] of {v} in [{lower}, {upper}] (width \
                     {inner_width}) is {e}, outside the claimed [{}, {}]",
                    got.lower,
                    got.upper
                );
            }
        }
    }

    fn eval_index_term(terms: &TermStore, term: TermId, y: TermId, y_value: u128) -> Option<u128> {
        let width = bv_width(terms, term)?;
        let mask = mask_of(width);
        let value = match terms.get(term).clone() {
            TermData::Const(Constant::BitVec { value, .. }) => value.to_u128()?,
            TermData::Var(_, _) if term == y => y_value,
            TermData::Ite(cond, then_term, else_term) => {
                if eval_index_condition(terms, cond, y, y_value)? {
                    eval_index_term(terms, then_term, y, y_value)?
                } else {
                    eval_index_term(terms, else_term, y, y_value)?
                }
            }
            TermData::App(sym, args) => {
                let indices = match &sym {
                    Symbol::Indexed(_, indices) => indices.clone(),
                    _ => Vec::new(),
                };
                let name = sym.name();
                if name == "ite" && args.len() == 3 {
                    return if eval_index_condition(terms, args[0], y, y_value)? {
                        eval_index_term(terms, args[1], y, y_value)
                    } else {
                        eval_index_term(terms, args[2], y, y_value)
                    };
                }
                let values: Option<Vec<u128>> = args
                    .iter()
                    .map(|&arg| eval_index_term(terms, arg, y, y_value))
                    .collect();
                let values = values?;
                match (name, values.as_slice()) {
                    ("bvadd", vs) => vs.iter().fold(0u128, |a, &v| a.wrapping_add(v)),
                    ("bvsub", [a, b]) => a.wrapping_sub(*b),
                    ("bvmul", vs) => vs.iter().fold(1u128, |a, &v| a.wrapping_mul(v)),
                    ("bvand", vs) => vs.iter().fold(mask, |a, &v| a & v),
                    ("bvor", vs) => vs.iter().fold(0, |a, &v| a | v),
                    ("bvxor", vs) => vs.iter().fold(0, |a, &v| a ^ v),
                    ("bvnot", [a]) => !a,
                    ("bvneg", [a]) => a.wrapping_neg(),
                    ("bvshl", [a, b]) if *b < u128::from(width) => a << b,
                    ("bvshl", [_, _]) => 0,
                    ("bvlshr", [a, b]) if *b < u128::from(width) => a >> b,
                    ("bvlshr", [_, _]) => 0,
                    ("concat", vs) => {
                        let mut acc = 0u128;
                        for (&arg, &v) in args.iter().zip(vs) {
                            acc = (acc << bv_width(terms, arg)?) | v;
                        }
                        acc
                    }
                    ("extract", [a]) if indices.len() == 2 => a >> indices[1],
                    ("zero_extend", [a]) => *a,
                    ("sign_extend", [a]) => {
                        let inner = bv_width(terms, args[0])?;
                        if (a >> (inner - 1)) & 1 == 1 {
                            a | !mask_of(inner)
                        } else {
                            *a
                        }
                    }
                    _ => return None,
                }
            }
            _ => return None,
        };
        Some(value & mask)
    }

    fn eval_index_condition(
        terms: &TermStore,
        cond: TermId,
        y: TermId,
        y_value: u128,
    ) -> Option<bool> {
        match terms.get(cond).clone() {
            TermData::Const(Constant::Bool(value)) => Some(value),
            TermData::Not(inner) => Some(!eval_index_condition(terms, inner, y, y_value)?),
            TermData::App(sym, args) if args.len() == 2 => {
                let a = eval_index_term(terms, args[0], y, y_value)?;
                let b = eval_index_term(terms, args[1], y, y_value)?;
                match sym.name() {
                    "bvult" => Some(a < b),
                    "bvule" => Some(a <= b),
                    "bvugt" => Some(a > b),
                    "bvuge" => Some(a >= b),
                    "=" => Some(a == b),
                    _ => None,
                }
            }
            _ => None,
        }
    }

    /// A random index expression of `width` bits over `y`, drawn from every
    /// operator the range lattice reads (the family generator's `base`).
    fn gen_index_term(
        terms: &mut TermStore,
        rng: &mut XorShift,
        y: TermId,
        y_width: u32,
        width: u32,
        depth: u32,
    ) -> TermId {
        let pick = if depth == 0 {
            rng.below(2)
        } else {
            rng.below(11)
        };
        let mask = mask_of(width);
        match pick {
            0 => {
                if y_width == width {
                    y
                } else if y_width < width {
                    terms.mk_bvzero_extend(width - y_width, y)
                } else {
                    terms.mk_bvextract(width - 1, 0, y)
                }
            }
            1 => terms.mk_bitvec(BigInt::from(rng.range_u128(0, mask)), width),
            2 | 3 => {
                let a = gen_index_term(terms, rng, y, y_width, width, depth - 1);
                let b = if rng.below(10) < 7 {
                    let c = match rng.below(4) {
                        0 => 1u128 << (width - 1),
                        1 => 1,
                        2 => mask,
                        _ => rng.range_u128(1, mask),
                    };
                    terms.mk_bitvec(BigInt::from(c), width)
                } else {
                    gen_index_term(terms, rng, y, y_width, width, depth - 1)
                };
                terms.mk_bvadd(vec![a, b])
            }
            4 => {
                let a = gen_index_term(terms, rng, y, y_width, width, depth - 1);
                let c = terms.mk_bitvec(BigInt::from(rng.range_u128(0, mask)), width);
                terms.mk_bvand(vec![a, c])
            }
            5 => {
                let a = gen_index_term(terms, rng, y, y_width, width, depth - 1);
                let c = [2u128, 3, 4, 5, rng.range_u128(0, mask)][rng.below(5) as usize] & mask;
                let c = terms.mk_bitvec(BigInt::from(c), width);
                terms.mk_bvmul(vec![a, c])
            }
            6 if width >= 2 => {
                let high_width = rng.range_u32(1, width - 1);
                let hi = terms.mk_bitvec(
                    BigInt::from(rng.range_u128(0, mask_of(high_width))),
                    high_width,
                );
                let lo = gen_index_term(terms, rng, y, y_width, width - high_width, depth - 1);
                terms.mk_bvconcat(vec![hi, lo])
            }
            7 => {
                let a = gen_index_term(terms, rng, y, y_width, width, depth - 1);
                let b = gen_index_term(terms, rng, y, y_width, width, depth - 1);
                let t = terms.mk_bitvec(BigInt::from(rng.range_u128(0, mask_of(y_width))), y_width);
                let cond = terms.mk_bvult(y, t);
                terms.mk_ite(cond, a, b)
            }
            8 => {
                let wide = (width + rng.range_u32(1, 8)).min(16);
                let a = gen_index_term(terms, rng, y, y_width, wide, depth - 1);
                let low = if rng.below(3) == 0 {
                    rng.range_u32(0, wide - width)
                } else {
                    0
                };
                terms.mk_bvextract(low + width - 1, low, a)
            }
            9 if width >= 2 => {
                let narrow = rng.range_u32(1, width - 1);
                let a = gen_index_term(terms, rng, y, y_width, narrow, depth - 1);
                terms.mk_bvzero_extend(width - narrow, a)
            }
            10 if width >= 2 => {
                let narrow = rng.range_u32(1, width - 1);
                let a = gen_index_term(terms, rng, y, y_width, narrow, depth - 1);
                terms.mk_bvsign_extend(width - narrow, a)
            }
            _ => gen_index_term(terms, rng, y, y_width, width, 0),
        }
    }

    /// The generator's AIMED shape: an extract of an offset, masked-offset or
    /// concatenated source whose range crosses `2^(high+1)`.
    fn gen_aimed_extract(
        terms: &mut TermStore,
        rng: &mut XorShift,
        y: TermId,
        y_width: u32,
        width: u32,
    ) -> TermId {
        let wide = (width + rng.range_u32(1, 8)).min(16);
        let inner_width = rng.range_u32(1, wide - 1);
        let depth = rng.range_u32(0, 1);
        let a = gen_index_term(terms, rng, y, y_width, inner_width, depth);
        let source = match rng.below(4) {
            0 | 1 => {
                let span = mask_of(wide) - mask_of(inner_width);
                let c = terms.mk_bitvec(BigInt::from(rng.range_u128(1, span.max(1))), wide);
                let widened = terms.mk_bvzero_extend(wide - inner_width, a);
                terms.mk_bvadd(vec![widened, c])
            }
            2 => {
                let m = rng.range_u128(0, mask_of(inner_width));
                let c = rng.range_u128(1, (mask_of(wide) - m).max(1));
                let widened = terms.mk_bvzero_extend(wide - inner_width, a);
                let m = terms.mk_bitvec(BigInt::from(m), wide);
                let masked = terms.mk_bvand(vec![widened, m]);
                let c = terms.mk_bitvec(BigInt::from(c), wide);
                terms.mk_bvadd(vec![masked, c])
            }
            _ => {
                let hi_width = wide - inner_width;
                let hi =
                    terms.mk_bitvec(BigInt::from(rng.range_u128(1, mask_of(hi_width))), hi_width);
                terms.mk_bvconcat(vec![hi, a])
            }
        };
        let low = if rng.below(4) == 0 {
            rng.range_u32(0, wide - width)
        } else {
            0
        };
        terms.mk_bvextract(low + width - 1, low, source)
    }

    /// Generated index terms (6,000 cases, 60% of them the aimed wrap-around
    /// extract) over a variable of 1..=8 bits: the range `bv_range` computes
    /// must contain the term's value under EVERY assignment of the variable.
    #[test]
    fn bv_range_contains_every_value_of_generated_index_terms_d9() {
        let mut rng = XorShift(0xd9d9_5eed_0bad_c0de);
        let mut checked = 0u32;
        let mut aimed_wraps = 0u32;
        for case in 0..6_000u32 {
            let mut terms = TermStore::new();
            let y_width = [1u32, 2, 3, 4, 5, 6, 8][rng.below(7) as usize];
            let y = terms.mk_var("y", Sort::bitvec(y_width));
            let width = rng.range_u32(1, 8);
            let aimed = rng.below(10) < 6;
            let term = if aimed {
                gen_aimed_extract(&mut terms, &mut rng, y, y_width, width)
            } else {
                let depth = rng.range_u32(1, 3);
                gen_index_term(&mut terms, &mut rng, y, y_width, width, depth)
            };
            let mut cache = HashMap::default();
            let Some(range) = bv_range(&terms, term, &mut cache) else {
                continue;
            };
            assert_eq!(Some(range.width), bv_width(&terms, term), "case {case}");
            let values: Option<Vec<(u128, u128)>> = (0..=mask_of(y_width))
                .map(|y_value| Some((y_value, eval_index_term(&terms, term, y, y_value)?)))
                .collect();
            let Some(values) = values else {
                continue;
            };
            checked += 1;
            let lo = values.iter().map(|&(_, v)| v).min().unwrap_or(0);
            let hi = values.iter().map(|&(_, v)| v).max().unwrap_or(0);
            if aimed
                && hi - lo < mask_of(width)
                && range.lower == 0
                && range.upper == mask_of(width)
            {
                aimed_wraps += 1;
            }
            for (y_value, value) in values {
                assert!(
                    range.lower <= value && value <= range.upper,
                    "case {case}: the index term {:?} is {value} at y = {y_value} (y has \
                     {y_width} bits), outside the claimed range [{}, {}]",
                    terms.get(term),
                    range.lower,
                    range.upper
                );
            }
        }
        assert!(
            checked >= 5_000,
            "only {checked} of 6000 generated terms were checked"
        );
        assert!(
            aimed_wraps > 0,
            "the aimed generator must reach a wrapping extract"
        );
    }

    /// End to end on the rewrite: `T[#xff] = #x00` and a read of `T` at
    /// `extract[7:0](#x0100 + zero_extend(y))` — every byte — must not be
    /// rewritten against the one known cell (it was folded to `false`).
    #[test]
    fn dense_predicate_rewrite_does_not_fold_a_wrapping_extract_index_d9() {
        let mut exec = Executor::new();
        let table_sort = Sort::array(Sort::bitvec(8), Sort::bitvec(8));
        let table = exec.ctx.terms.mk_var("t", table_sort);
        let y = exec.ctx.terms.mk_var("y", Sort::bitvec(8));
        let ff = exec.ctx.terms.mk_bitvec(BigInt::from(255u32), 8);
        let zero = exec.ctx.terms.mk_bitvec(BigInt::from(0u32), 8);
        let pinned = exec.ctx.terms.mk_select(table, ff);
        let fact = exec.ctx.terms.mk_eq(pinned, zero);
        let offset = exec.ctx.terms.mk_bitvec(BigInt::from(256u32), 16);
        let widened = exec.ctx.terms.mk_bvzero_extend(8, y);
        let sum = exec.ctx.terms.mk_bvadd(vec![offset, widened]);
        let index = exec.ctx.terms.mk_bvextract(7, 0, sum);
        let read = exec.ctx.terms.mk_select(table, index);
        let read_is_zero = exec.ctx.terms.mk_eq(read, zero);
        let goal = exec.ctx.terms.mk_not(read_is_zero);
        exec.ctx.assertions = vec![fact, goal];

        exec.rewrite_dense_bv_array_initializer_selects();

        assert_eq!(exec.ctx.assertions[0], fact);
        assert_ne!(
            exec.ctx.assertions[1],
            exec.ctx.terms.false_term(),
            "a read that can touch every cell was rewritten against T[#xff] alone"
        );
        assert_eq!(
            exec.last_statistics
                .get_int("smt.abv.finite_array.predicate_rewrites")
                .unwrap_or(0),
            0
        );
    }

    /// A 128-bit first operand of a `concat` shifted the empty prefix by 128
    /// bits, which overflow-checked `<<` rejects with a panic.
    #[test]
    fn bv_range_of_a_concat_with_a_128_bit_head_does_not_overflow() {
        let mut terms = TermStore::new();
        let head = terms.mk_var("head", Sort::bitvec(128));
        let tail = terms.mk_var("tail", Sort::bitvec(8));
        let mut cache = HashMap::default();
        let head_only = bv_range_concat(&terms, &[head], &mut cache)
            .expect("a 128-bit operand alone has a range");
        assert_eq!((head_only.lower, head_only.upper), (0, u128::MAX));
        let mut cache = HashMap::default();
        assert!(bv_range_concat(&terms, &[head, tail], &mut cache).is_none());
    }

    /// A select index that is not a bit-vector -- the Bool index of an outer
    /// `(Array Bool ..)` -- has no range: `None`, never a panic (fresh
    /// nestfin_2909_0018 --z3-mode aborted on `false` here).
    #[test]
    fn bv_range_of_a_non_bitvector_index_is_none() {
        let mut terms = TermStore::new();
        let index = terms.mk_bool(false);
        let mut cache = HashMap::default();
        assert!(bv_range(&terms, index, &mut cache).is_none());
    }
}
