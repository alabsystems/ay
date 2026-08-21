// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Model-value reconstruction for the array/datatype census, memoized.
//!
//! The census (dt_model.rs) asks "do any two reads of one array identity class
//! at one evaluated index disagree?". Answering that means reconstructing each
//! read's value from the model — a canonical key for a scalar, a cell function
//! for an array, a constructor tuple for a datatype. This module holds that
//! reconstruction and the per-pass memo that makes it pay once.

use std::cell::RefCell;

use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::term::TermData;
use ay_core::{Sort, TermId};

use super::super::{EvalValue, Executor, Model};

/// Canonical census key. `Rc<str>` rather than `String`: the same key is stored
/// once per cell, once per class-cell list and once per collected cell map, so
/// `String` meant three heap allocations and memcpys per read. Sharing an
/// immutable buffer makes those copies a refcount bump.
pub(in crate::executor::model) type CensusKey = std::rc::Rc<str>;

/// The observed cell function of one array term under the model:
/// `(evaluated-index key -> value term, const-array fill)`.
pub(in crate::executor::model) type CensusCells =
    std::rc::Rc<(HashMap<CensusKey, TermId>, Option<TermId>)>;

/// Per-pass memo for the census.
///
/// The all-pairs compatibility scan asks for the SAME term's canonical key or
/// cell function once per partner, so a cell of `n` reads recomputed `n`
/// distinct answers `n*(n-1)` times, each rebuilding formatted keys from
/// scratch. On `inv_Newton` that made the census 15.5% of on-CPU solver work.
///
/// Memoizing is exact here: every memoized function is a pure function of
/// `(&self, model, args)`, the census runs under `&self` with a fixed `&Model`
/// and mutates neither, and a `CensusMemo` is created at a census entry point
/// and dropped before it returns, so no pass can observe another's model. The
/// recursion budget is part of every key because these functions genuinely
/// return `None` at `depth == 0`. No verdict changes: the same pairs are
/// compared, by the same predicate, to the same answers.
#[derive(Default)]
pub(in crate::executor::model) struct CensusMemo {
    value_key: RefCell<HashMap<(TermId, u32), Option<CensusKey>>>,
    cells: RefCell<HashMap<(TermId, u32), CensusCells>>,
    compatible: RefCell<HashMap<(TermId, TermId, u32), Option<bool>>>,
}

impl CensusMemo {
    pub(in crate::executor::model) fn new() -> Self {
        Self::default()
    }
}

/// Everything one census pass reads that does not change while it runs: the
/// array identity structure derived from the model, and the memo of answers
/// already computed. Threaded as one borrow so the recursive comparisons keep
/// signatures clippy's argument limit accepts.
pub(in crate::executor::model) struct CensusCtx<'a> {
    pub(super) uf: &'a HashMap<TermId, TermId>,
    pub(super) class_cells: &'a HashMap<TermId, Vec<(CensusKey, TermId)>>,
    pub(super) memo: &'a CensusMemo,
}

impl Executor {
    /// Canonical model key of an INDEX term: a datatype index reconstructs to its
    /// canonical constructor tuple; a scalar index to its evaluated value. `None`
    /// if the model does not determine it (fail-closed at the call site).
    pub(in crate::executor::model) fn census_index_key(
        &self,
        model: &Model,
        index: TermId,
        memo: &CensusMemo,
    ) -> Option<CensusKey> {
        self.census_value_key(model, index, 20, memo)
    }

    /// Recursive canonical model key of a term — the census `RValue` tree
    /// flattened to a string: a datatype value reconstructs to its constructor
    /// tuple `(ctor field..)` with EACH field recursively keyed (INCLUDING
    /// array-typed fields, which `dt_mat_canonical` bailed on with `None`); an
    /// array to a const/store/identity canonical; a scalar/uninterpreted leaf to
    /// its evaluated value. `None` when the model does not determine it
    /// (fail-closed at the call site). Two terms are model-equal iff their keys
    /// are equal (over-approximate for bare-array fields — same syntactic term ⇒
    /// same key; a false inequality can only over-reject to a sound `unknown`,
    /// never certify a false SAT).
    pub(in crate::executor::model) fn census_value_key(
        &self,
        model: &Model,
        term: TermId,
        depth: u32,
        memo: &CensusMemo,
    ) -> Option<CensusKey> {
        if depth == 0 {
            return None;
        }
        if let Some(hit) = memo.value_key.borrow().get(&(term, depth)) {
            return hit.clone();
        }
        let computed = self.census_value_key_uncached(model, term, depth, memo);
        memo.value_key
            .borrow_mut()
            .insert((term, depth), computed.clone());
        computed
    }

    /// [`Self::census_value_key`] without the memo lookup — the body that
    /// actually reconstructs. Split out so the memo has exactly one insert site
    /// and every early return still lands in the cache.
    fn census_value_key_uncached(
        &self,
        model: &Model,
        term: TermId,
        depth: u32,
        memo: &CensusMemo,
    ) -> Option<CensusKey> {
        let sort = self.ctx.terms.sort(term).clone();
        if let Sort::Array(_) = sort {
            return self.census_array_canonical(model, term, depth, memo);
        }
        let is_dt = matches!(&sort, Sort::Datatype(dt) if self.ctx.datatype_iter().any(|(n,_)| n==dt.name.as_str()))
            || matches!(&sort, Sort::Uninterpreted(n) if self.ctx.datatype_iter().any(|(d,_)| d==n.as_str()));
        if is_dt {
            // Literal constructor application: head + recursively-keyed args.
            if let TermData::App(sym, args) = self.ctx.terms.get(term) {
                if let Some((_dt, ctor)) = self.ctx.is_constructor(sym.name()) {
                    let args_v: Vec<TermId> = args.clone();
                    let mut parts = vec![ctor];
                    for arg in args_v {
                        parts.push(
                            self.census_value_key(model, arg, depth - 1, memo)?
                                .to_string(),
                        );
                    }
                    return Some(format!("({})", parts.join(" ")).into());
                }
            }
            // Datatype-sorted variable / selector result: read the model's
            // constructor, then each field via its selector application.
            let (ctor, _) = self.dt_constructor_of(model, term)?;
            let selectors: Vec<String> = self
                .ctx
                .constructor_selectors(&ctor)
                .map(|s| s.to_vec())
                .unwrap_or_default();
            if selectors.is_empty() {
                return Some(ctor.into());
            }
            let mut parts = vec![ctor];
            for sel in selectors {
                let sel_app = self.find_dt_selector_app(&sel, term)?;
                parts.push(
                    self.census_value_key(model, sel_app, depth - 1, memo)?
                        .to_string(),
                );
            }
            return Some(format!("({})", parts.join(" ")).into());
        }
        // A read the preprocessor substituted away (its live twin carries the
        // bits) evaluates Unknown by TermId; the asserted equality that PINS it
        // (`(= (ptr (select A j)) #xFF)`) still defines its model value — the
        // same resolution `concrete_select_pairs` uses for the strict oracle.
        let v = match self.evaluate_term(model, term) {
            EvalValue::Unknown => self
                .extract_value_from_asserted_equalities(model, term)
                .unwrap_or(EvalValue::Unknown),
            v => v,
        };
        match v {
            EvalValue::BitVec { value, width } => Some(format!("bv{width}:{value}").into()),
            EvalValue::Bool(b) => Some(format!("b:{b}").into()),
            EvalValue::Rational(r) => Some(format!("r:{r}").into()),
            EvalValue::Element(e) => Some(format!("e:{e}").into()),
            _ => None,
        }
    }

    /// Canonical of an ARRAY term under the model: a const-array to
    /// `const(<fill>)`, a store to `store(<base>,<idx>,<val>)`, a nested
    /// `(select B k)` to `sel(<B id>,<eval k>)` (same base term + evaluated index ⇒
    /// same inner array, by array congruence), and any other bare/computed array
    /// to an identity marker `arr#<term id>`. SOUND: identity-by-term over-rejects
    /// (degrades) two model-equal but syntactically-distinct arrays, never
    /// under-rejects. Used to key datatype ARRAY fields (e.g. `Slice.data`).
    pub(in crate::executor::model) fn census_array_canonical(
        &self,
        model: &Model,
        arr: TermId,
        depth: u32,
        memo: &CensusMemo,
    ) -> Option<CensusKey> {
        if depth == 0 {
            return None;
        }
        if let Some(fill) = self.ctx.terms.get_const_array(arr) {
            return Some(
                format!(
                    "const({})",
                    self.census_value_key(model, fill, depth - 1, memo)?
                )
                .into(),
            );
        }
        if let Some((base_term, index, value)) = self.exact_cegar_store_parts(arr) {
            let base = self.census_array_canonical(model, base_term, depth - 1, memo)?;
            let idx = self.census_index_key(model, index, memo)?;
            let val = self.census_value_key(model, value, depth - 1, memo)?;
            return Some(format!("store({base},{idx},{val})").into());
        }
        if let Some((base, index)) = self.exact_cegar_select_parts(arr) {
            let idx = self.census_index_key(model, index, memo)?;
            return Some(format!("sel({},{idx})", base.0).into());
        }
        Some(format!("arr#{}", arr.0).into())
    }

    /// Structural model-COMPATIBILITY of two terms: `Some(true)` iff the model's
    /// partial assignment can be completed with both denoting the SAME value,
    /// `Some(false)` iff they are DEFINITELY unequal (differing constructor,
    /// differing scalar/EUF value, or a common observed array cell that
    /// conflicts), `None` if a needed value is undecidable (caller fails closed).
    ///
    /// This is the sound notion of "select-congruent" for values carrying
    /// arrays: two array fields are compatible unless they disagree on a cell
    /// BOTH were observed at — disjoint / unread cells complete freely, so two
    /// unconstrained `Slice.data` arrays are compatible rather than falsely
    /// conflicting on their `arr#id` identity. Certifying on compatibility is
    /// sound because a satisfying completion demonstrably exists; only cells the
    /// model already pins can force `Some(false)`.
    pub(in crate::executor::model) fn census_compatible(
        &self,
        model: &Model,
        t1: TermId,
        t2: TermId,
        depth: u32,
        ctx: &CensusCtx<'_>,
    ) -> Option<bool> {
        if depth == 0 {
            return None; // recursion budget exhausted -> undecidable, fail closed
        }
        if let Some(hit) = ctx.memo.compatible.borrow().get(&(t1, t2, depth)) {
            return *hit;
        }
        let computed = self.census_compatible_uncached(model, t1, t2, depth, ctx);
        ctx.memo
            .compatible
            .borrow_mut()
            .insert((t1, t2, depth), computed);
        computed
    }

    /// [`Self::census_compatible`] without the memo lookup. Same contract; split
    /// so the memo has one insert site covering every early return.
    /// Array arm of [`Self::census_compatible`]: two arrays are compatible
    /// unless a COMMON observed cell (or an overlapping const-default) holds
    /// definitely-incompatible values. Disjoint or unread cells complete
    /// freely, so nothing here can manufacture a conflict.
    fn census_arrays_compatible(
        &self,
        model: &Model,
        t1: TermId,
        t2: TermId,
        depth: u32,
        ctx: &CensusCtx<'_>,
    ) -> Option<bool> {
        let cells1 = self.census_collect_cells(model, t1, depth, ctx);
        let cells2 = self.census_collect_cells(model, t2, depth, ctx);
        let (c1, d1) = (&cells1.0, cells1.1);
        let (c2, d2) = (&cells2.0, cells2.1);
        for (k, v1) in c1 {
            if let Some(v2) = c2.get(k).copied().or(d2) {
                if !self.census_compatible(model, *v1, v2, depth - 1, ctx)? {
                    return Some(false);
                }
            }
        }
        let Some(dv1) = d1 else { return Some(true) };
        for (k, v2) in c2 {
            if c1.contains_key(k) {
                continue;
            }
            if !self.census_compatible(model, dv1, *v2, depth - 1, ctx)? {
                return Some(false);
            }
        }
        if let Some(dv2) = d2 {
            if !self.census_compatible(model, dv1, dv2, depth - 1, ctx)? {
                return Some(false);
            }
        }
        Some(true)
    }

    fn census_compatible_uncached(
        &self,
        model: &Model,
        t1: TermId,
        t2: TermId,
        depth: u32,
        ctx: &CensusCtx<'_>,
    ) -> Option<bool> {
        let sort = self.ctx.terms.sort(t1).clone();
        if let Sort::Array(_) = sort {
            return self.census_arrays_compatible(model, t1, t2, depth, ctx);
        }
        // Datatype values: same constructor, then each field pairwise compatible.
        let is_dt = matches!(&sort, Sort::Datatype(dt) if self.ctx.datatype_iter().any(|(n,_)| n==dt.name.as_str()))
            || matches!(&sort, Sort::Uninterpreted(n) if self.ctx.datatype_iter().any(|(d,_)| d==n.as_str()));
        if is_dt {
            let (c1, _) = self.dt_constructor_of(model, t1)?;
            let (c2, _) = self.dt_constructor_of(model, t2)?;
            if c1 != c2 {
                return Some(false); // different constructors -> definitely unequal
            }
            let selectors: Vec<String> = self
                .ctx
                .constructor_selectors(&c1)
                .map(|s| s.to_vec())
                .unwrap_or_default();
            for sel in selectors {
                let dbg = ay_core::misc_cli_flags().census_trace;
                let (Some(a1), Some(a2)) = (
                    self.find_dt_selector_app(&sel, t1),
                    self.find_dt_selector_app(&sel, t2),
                ) else {
                    if dbg {
                        eprintln!(
                            "c census-dbg no-selector-app sel={sel} t1={} t2={}",
                            t1.0, t2.0
                        );
                    }
                    return None;
                };
                let r = self.census_compatible(model, a1, a2, depth - 1, ctx);
                if dbg && r.is_none() {
                    eprintln!(
                        "c census-dbg field-undecidable sel={sel} a1={} ({}) a2={} ({})",
                        a1.0,
                        self.format_term(a1),
                        a2.0,
                        self.format_term(a2)
                    );
                }
                if !r? {
                    return Some(false);
                }
            }
            return Some(true);
        }
        // Scalar / EUF leaf: compare evaluated values (undecidable -> None).
        let dbg = ay_core::misc_cli_flags().census_trace;
        let k1 = self.census_value_key(model, t1, depth, ctx.memo);
        let k2 = self.census_value_key(model, t2, depth, ctx.memo);
        if dbg && (k1.is_none() || k2.is_none()) {
            eprintln!(
                "c census-dbg leaf-undecidable t1={} ({}) k1={:?} t2={} ({}) k2={:?}",
                t1.0,
                self.format_term(t1),
                k1,
                t2.0,
                self.format_term(t2),
                k2
            );
        }
        Some(k1? == k2?)
    }

    /// Observed cell function of an array term under the model: `(cells, default)`
    /// where `cells` maps an evaluated-index key to a value term and `default` is
    /// a const-array fill (if the array is/reduces to `((as const ..) f)`).
    /// Combines the array's syntactic `store`/const structure with every
    /// `(select S k)` read on its identity class. Used by `census_compatible` to
    /// compare two array fields cell-by-cell.
    ///
    /// Memoized on `(arr, depth)`: the all-pairs comparison above asks for the
    /// SAME array's cell function once per partner, so an `n`-read cell rebuilt
    /// `n` identical maps `n-1` times each. This was the second-hottest
    /// self-time frame in the solver on `inv_Newton`. See [`CensusMemo`].
    pub(in crate::executor::model) fn census_collect_cells(
        &self,
        model: &Model,
        arr: TermId,
        depth: u32,
        ctx: &CensusCtx<'_>,
    ) -> CensusCells {
        let hit = ctx.memo.cells.borrow().get(&(arr, depth)).cloned();
        if let Some(hit) = hit {
            // Debug-build differential oracle: recompute and compare. The memo
            // is only sound while the census's inputs are immutable for the
            // pass; if that ever stops holding, this fires loudly instead of
            // silently answering a congruence question from a stale cell map.
            // Cheap here — the recomputation walks one store chain and reads
            // one class-cell list, and every nested key it needs is itself
            // memoized.
            #[cfg(debug_assertions)]
            {
                let fresh = self.census_collect_cells_uncached(model, arr, depth, ctx);
                debug_assert!(
                    fresh.0 == hit.0 && fresh.1 == hit.1,
                    "CensusMemo cell map diverged on recompute for term {} at depth {depth} \
                     (census inputs mutated mid-pass?)",
                    arr.0
                );
            }
            return hit;
        }
        let built = self.census_collect_cells_uncached(model, arr, depth, ctx);
        ctx.memo
            .cells
            .borrow_mut()
            .insert((arr, depth), built.clone());
        built
    }

    /// [`Self::census_collect_cells`] without the memo — the body that builds.
    fn census_collect_cells_uncached(
        &self,
        model: &Model,
        arr: TermId,
        depth: u32,
        ctx: &CensusCtx<'_>,
    ) -> CensusCells {
        let mut cells: HashMap<CensusKey, TermId> = HashMap::default();
        let mut default: Option<TermId> = None;
        // Walk the syntactic store/const chain: outermost store wins each index.
        let mut cur = arr;
        for _ in 0..depth.min(64) {
            if let Some(fill) = self.ctx.terms.get_const_array(cur) {
                default = Some(fill);
                break;
            }
            if let Some((base, index, value)) = self.exact_cegar_store_parts(cur) {
                if let Some(key) = self.census_index_key(model, index, ctx.memo) {
                    cells.entry(key).or_insert(value);
                }
                cur = base;
                continue;
            }
            break;
        }
        // Observed selects on the array's (and the reduced base's) identity class.
        for base in [arr, cur] {
            let cls = Self::census_find(ctx.uf, base);
            if let Some(list) = ctx.class_cells.get(&cls) {
                for (k, t) in list {
                    cells.entry(k.clone()).or_insert(*t);
                }
            }
        }
        std::rc::Rc::new((cells, default))
    }
}
