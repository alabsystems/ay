// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Term classification helpers for model validation.
//!
//! Contains methods on `Executor` for classifying terms: internal symbols,
//! datatype content, quantifiers, array operations, term flag precomputation, etc.
//!
//! Extracted from `validation.rs` as part of the code-health module split.

use ay_core::term::{Constant, TermData};
use ay_core::{Sort, TermId};

use super::{
    TERM_FLAG_ARRAY, TERM_FLAG_BV_CMP, TERM_FLAG_DATATYPE, TERM_FLAG_FP, TERM_FLAG_INTERNAL,
    TERM_FLAG_QUANTIFIER, TERM_FLAG_SEQ, TERM_FLAG_STRING,
};
use crate::executor::model::{Executor, Model, EVAL_STACK_RED_ZONE, EVAL_STACK_SIZE};

impl Executor {
    /// Check whether a term tree contains an internal encoding symbol.
    /// Internal symbols (`__ay_*`) are auxiliary encoding artifacts and are
    /// excluded from top-level model validation.
    /// Whether the asserted problem contains any term of a *datatype-carrying
    /// array* sort (`Array(_, …Datatype…)` / `Array(…Datatype…, _)`).
    ///
    /// SOUNDNESS: the combined DT + Array/BV route bit-blasts datatype values
    /// stored in arrays without constructor injectivity through array equality,
    /// so it can return a spurious SAT (e.g. `store(a,i,Ctor x) = store(b,i,Ctor
    /// (x+1))` is UNSAT — the arrays must differ at `i` — yet the bit-blasted
    /// model satisfies it). `finalize_sat_model_validation` uses this to degrade
    /// such a SAT to a sound `unknown` (degrade-only; never affects UNSAT).
    pub(crate) fn problem_has_datatype_carrying_array(&self) -> bool {
        // Fast path: no datatypes declared -> no datatype-carrying array possible.
        // Keeps the common pure-BV / pure-array solve free of the assertion walk.
        if self.ctx.datatype_iter().next().is_none() {
            return false;
        }
        self.ctx
            .assertions
            .iter()
            .any(|&assertion| self.term_has_datatype_carrying_array_sort(assertion))
    }

    /// Whether any assertion mentions an ARRAY-sorted subterm — the trigger for
    /// the general select-congruence model gate
    /// (`array_select_congruence_violated`). Cheap SAT-path-only walk.
    pub(crate) fn problem_has_array(&self) -> bool {
        self.ctx
            .assertions
            .iter()
            .any(|&assertion| self.term_mentions_array_sort(assertion))
    }

    fn term_mentions_array_sort(&self, term: TermId) -> bool {
        stacker::maybe_grow(EVAL_STACK_RED_ZONE, EVAL_STACK_SIZE, || {
            if self.ctx.terms.sort(term).is_array() {
                return true;
            }
            match self.ctx.terms.get(term) {
                TermData::App(_, args) => {
                    args.iter().any(|&arg| self.term_mentions_array_sort(arg))
                }
                TermData::Not(inner) => self.term_mentions_array_sort(*inner),
                TermData::Ite(c, t, e) => {
                    self.term_mentions_array_sort(*c)
                        || self.term_mentions_array_sort(*t)
                        || self.term_mentions_array_sort(*e)
                }
                TermData::Let(bindings, body) => {
                    bindings
                        .iter()
                        .any(|(_, bound)| self.term_mentions_array_sort(*bound))
                        || self.term_mentions_array_sort(*body)
                }
                TermData::Forall(_, body, _) | TermData::Exists(_, body, _) => {
                    self.term_mentions_array_sort(*body)
                }
                _ => false,
            }
        })
    }

    /// A sort that (recursively) carries a datatype, recognizing BOTH
    /// `Sort::Datatype` AND `Sort::Uninterpreted(name)` where `name` is a
    /// declared datatype — the abv/euf solve path lowers datatypes to opaque
    /// `Uninterpreted` sorts, so a plain `Sort::Datatype` match misses them.
    fn sort_carries_datatype(&self, sort: &Sort) -> bool {
        match sort {
            Sort::Datatype(_) => true,
            Sort::Uninterpreted(name) => {
                self.ctx.datatype_iter().any(|(dt, _)| dt == name.as_str())
            }
            Sort::Array(arr) => {
                self.sort_carries_datatype(&arr.index_sort)
                    || self.sort_carries_datatype(&arr.element_sort)
            }
            _ => false,
        }
    }

    /// `Array(idx, elem)` whose index or element sort carries a datatype.
    fn sort_is_datatype_carrying_array(&self, sort: &Sort) -> bool {
        match sort {
            Sort::Array(arr) => {
                self.sort_carries_datatype(&arr.index_sort)
                    || self.sort_carries_datatype(&arr.element_sort)
            }
            _ => false,
        }
    }

    /// A FINITE ALL-NULLARY ENUM sort (`Sort::Datatype` inline or
    /// `Sort::Uninterpreted` naming a declared datatype) whose every constructor
    /// is nullary — an enum like `(declare-datatype Color ((red) (green) (blue)))`.
    /// Used to admit DT-free-value arrays with such an INDEX into the
    /// observational-completeness bypass: no datatype VALUE flows through them,
    /// so the injectivity hazard cannot arise. Returns `false` for any
    /// field-bearing or recursive datatype index (richer structure).
    fn is_finite_nullary_enum_sort(&self, sort: &Sort) -> bool {
        let ctor_names: Vec<String> = match sort {
            Sort::Datatype(dt) => {
                if dt.constructors.is_empty() {
                    return false;
                }
                return dt.constructors.iter().all(|c| c.fields.is_empty());
            }
            Sort::Uninterpreted(name) => self
                .ctx
                .datatype_iter()
                .find(|(dt_name, _)| dt_name == name)
                .map(|(_, cs)| cs.iter().map(String::clone).collect())
                .unwrap_or_default(),
            _ => return false,
        };
        if ctor_names.is_empty() {
            return false;
        }
        // Nullary iff each constructor has no selectors (no fields).
        ctor_names.iter().all(|c| {
            self.ctx
                .constructor_selector_info(c)
                .map_or(true, |sels| sels.is_empty())
        })
    }

    /// A "plain scalar datatype" sort: a datatype value that is NOT itself an
    /// array/seq. These are the element values the store-value constructor-
    /// injectivity bridge (`dt_store_value_injectivity_axioms`) models.
    fn is_plain_scalar_datatype(&self, sort: &Sort) -> bool {
        match sort {
            Sort::Datatype(_) => true,
            Sort::Uninterpreted(name) => {
                self.ctx.datatype_iter().any(|(dt, _)| dt == name.as_str())
            }
            _ => false,
        }
    }

    /// An `Array(idx, elem)` sort that the store-value injectivity bridge fully
    /// models: a NON-datatype index and a PLAIN-SCALAR-datatype element. Nested
    /// datatype-carrying arrays (array-of-array, datatype-indexed) are excluded
    /// because their injectivity is not captured by the store-value pass.
    fn is_bridge_modeled_dt_array_sort(&self, sort: &Sort) -> bool {
        match sort {
            Sort::Array(arr) => {
                !self.sort_carries_datatype(&arr.index_sort)
                    && self.is_plain_scalar_datatype(&arr.element_sort)
            }
            _ => false,
        }
    }

    /// Whether `name` is a declared datatype SELECTOR (field accessor such as
    /// `fld_data`). Used by the observational-completeness walk to treat a
    /// field-array extraction as a non-observing structural pass-through.
    fn is_declared_selector(&self, name: &str) -> bool {
        self.ctx
            .ctor_selectors_iter()
            .any(|(_ctor, selectors)| selectors.iter().any(|sel| sel == name))
    }

    /// Whether `name` is a declared datatype CONSTRUCTOR (such as
    /// `Vec_PbTerm_mk`). Used to treat constructor packing of a datatype-element
    /// array as a non-observing structural pass-through.
    fn is_declared_constructor(&self, name: &str) -> bool {
        self.ctx.is_constructor(name).is_some()
    }

    /// Whether `sort` IS, or — through datatype fields, transitively — CONTAINS,
    /// an `Array` sort whose index or element carries a datatype.
    ///
    /// This recognizes WRAPPER datatypes (e.g. `Vec_PbTerm`, `PbConstraint`,
    /// `Slice_PbTerm`) that pack a datatype-element array, in addition to bare
    /// `Array(_, Datatype)` sorts. A plain scalar datatype that carries only a
    /// NON-datatype array (e.g. `PbTerm` over a `bv40` array) returns `false`.
    /// Cycle-guarded by datatype name so recursive datatypes terminate.
    ///
    /// Used by the `=`/`distinct` arm of
    /// [`Self::dt_array_footprint_observationally_complete`] to fail closed on a
    /// wrapper-datatype (dis)equality that constructor injectivity could push
    /// down to a datatype-element array equality (the store-store injectivity
    /// hazard, one wrapper level up).
    fn sort_recursively_carries_dt_element_array(&self, sort: &Sort) -> bool {
        let mut seen: ay_core::kani_compat::DetHashSet<String> = Default::default();
        self.sort_recursively_carries_dt_element_array_rec(sort, &mut seen)
    }

    fn sort_recursively_carries_dt_element_array_rec(
        &self,
        sort: &Sort,
        seen: &mut ay_core::kani_compat::DetHashSet<String>,
    ) -> bool {
        match sort {
            Sort::Array(_) => self.sort_is_datatype_carrying_array(sort),
            Sort::Datatype(dt) => {
                if !seen.insert(dt.name.clone()) {
                    return false;
                }
                dt.constructors.iter().any(|c| {
                    c.fields
                        .iter()
                        .any(|f| self.sort_recursively_carries_dt_element_array_rec(&f.sort, seen))
                })
            }
            Sort::Uninterpreted(name) => {
                // Resolve an opaque uninterpreted sort naming a declared datatype
                // to its constructor field sorts (the abv/euf path lowers
                // datatypes to `Uninterpreted`).
                let ctors: Vec<String> = self
                    .ctx
                    .datatype_iter()
                    .find(|(dt, _)| *dt == name.as_str())
                    .map(|(_, cs)| cs.to_vec())
                    .unwrap_or_default();
                if ctors.is_empty() {
                    return false;
                }
                if !seen.insert(name.clone()) {
                    return false;
                }
                for ctor in ctors {
                    if let Some(sels) = self.ctx.constructor_selector_info(&ctor) {
                        for (_, fsort) in sels {
                            if self.sort_recursively_carries_dt_element_array_rec(fsort, seen) {
                                return true;
                            }
                        }
                    }
                }
                false
            }
            _ => false,
        }
    }

    /// Whether EVERY datatype-carrying-array injectivity hazard in the current
    /// problem is provably modeled by the store-value constructor-injectivity
    /// bridge (`dt_store_value_injectivity_axioms`).
    ///
    /// When this holds, a returned SAT model already satisfies every emitted
    /// constructor injectivity/disjointness implication (they are part of the
    /// solved formula), so the `problem_has_datatype_carrying_array` degrade gate
    /// can be soundly bypassed. The check is a CONSERVATIVE whitelist: it returns
    /// `true` only when the datatype-carrying-array footprint is confined to the
    /// shapes the bridge covers exhaustively —
    ///   - `store(a, i, v)` and array VARIABLES over `Array(non-dt-index,
    ///     plain-scalar-datatype-element)`,
    ///   - `=` / `distinct` over such arrays,
    ///   - `select` on such an array yielding a datatype value IS a hazard and
    ///     returns `false` (the bridge covers store pairs, not select
    ///     injectivity/disjointness — see
    ///     `dt_array_footprint_observationally_complete` for the
    ///     route-independent single-select allowance),
    /// and returns `false` (fail-closed: keep the gate) for ANY other datatype-
    /// carrying-array construct: datatype-valued `select`, `const-array` /
    /// `map` / `as-array` / `default` of a datatype array, datatype-INDEXED
    /// arrays, array-of-datatype-array nesting, datatype-carrying arrays flowing
    /// through uninterpreted functions or ITEs, or any quantifier over the
    /// datatype-array fragment.
    ///
    /// SOUNDNESS: erring toward `false` can only RETAIN the sound degrade;
    /// returning `true` is justified only for footprints where the bridge's
    /// emitted axioms make the SAT model self-certifying.
    pub(crate) fn dt_array_injectivity_fully_modeled(&self) -> bool {
        // No datatypes -> the gate never fires; trivially "modeled".
        if self.ctx.datatype_iter().next().is_none() {
            return true;
        }

        // Walk terms reachable from the (original) assertions.
        let mut visited: ay_core::kani_compat::DetHashSet<TermId> = Default::default();
        let mut stack: Vec<TermId> = self.ctx.assertions.to_vec();
        while let Some(t) = stack.pop() {
            if !visited.insert(t) {
                continue;
            }
            let s = self.ctx.terms.sort(t).clone();
            match self.ctx.terms.get(t) {
                TermData::App(sym, args) => {
                    let name = sym.name().to_string();
                    let args_v: Vec<TermId> = args.clone();
                    match name.as_str() {
                        "store" => {
                            // Modeled only for a plain-scalar-datatype element,
                            // non-datatype index. Nested / datatype-indexed stores
                            // are hazards.
                            if self.sort_is_datatype_carrying_array(&s)
                                && !self.is_bridge_modeled_dt_array_sort(&s)
                            {
                                return false;
                            }
                        }
                        "select" => {
                            // Datatype-valued select, or select over a datatype-
                            // indexed array, is an unmodeled hazard.
                            if self.sort_carries_datatype(&s) {
                                return false;
                            }
                            if let Some(&arr_arg) = args_v.first() {
                                if let Sort::Array(arr) = self.ctx.terms.sort(arr_arg) {
                                    if self.sort_carries_datatype(&arr.index_sort) {
                                        return false;
                                    }
                                }
                            }
                        }
                        "=" | "distinct" => {
                            for &a in &args_v {
                                let sa = self.ctx.terms.sort(a).clone();
                                if self.sort_is_datatype_carrying_array(&sa)
                                    && !self.is_bridge_modeled_dt_array_sort(&sa)
                                {
                                    return false;
                                }
                            }
                        }
                        _ => {
                            // Any other head (uninterpreted function, const-array,
                            // map, as-array, default, ...): a datatype-carrying
                            // array in the result or any argument is unmodeled.
                            if self.sort_is_datatype_carrying_array(&s) {
                                return false;
                            }
                            for &a in &args_v {
                                if self.sort_is_datatype_carrying_array(self.ctx.terms.sort(a)) {
                                    return false;
                                }
                            }
                        }
                    }
                    stack.extend(args_v);
                }
                TermData::Var(_, _) => {
                    if self.sort_is_datatype_carrying_array(&s)
                        && !self.is_bridge_modeled_dt_array_sort(&s)
                    {
                        return false;
                    }
                }
                TermData::Const(_) => {
                    if self.sort_is_datatype_carrying_array(&s) {
                        return false;
                    }
                }
                TermData::Ite(c, th, el) => {
                    if self.sort_is_datatype_carrying_array(&s) {
                        return false;
                    }
                    stack.push(*c);
                    stack.push(*th);
                    stack.push(*el);
                }
                TermData::Not(inner) => {
                    stack.push(*inner);
                }
                TermData::Let(bindings, body) => {
                    stack.push(*body);
                    for (_, v) in bindings {
                        stack.push(*v);
                    }
                }
                TermData::Forall(_, _, _) | TermData::Exists(_, _, _) => {
                    // The bridge does not model quantified datatype-array
                    // structure (bound-variable capture); keep the gate whenever
                    // any datatype-carrying array appears under a quantifier.
                    if self.term_has_datatype_carrying_array_sort(t) {
                        return false;
                    }
                }
                _ => {}
            }
        }
        true
    }

    /// A sort containing an `Array` whose INDEX side (recursively) carries a
    /// datatype — a datatype-INDEXED array. The witness-index extensionality pass
    /// does NOT model these (a witness index would be a datatype value, needing a
    /// different mechanism than the BitVec/scalar-index witness).
    fn sort_has_datatype_indexed_array(&self, sort: &Sort) -> bool {
        match sort {
            Sort::Array(arr) => {
                self.sort_carries_datatype(&arr.index_sort)
                    || self.sort_has_datatype_indexed_array(&arr.element_sort)
            }
            _ => false,
        }
    }

    /// The datatype name carried on the ELEMENT side of a field/array sort: a
    /// datatype sort returns its own name; an `Array _ E` returns the datatype
    /// carried by `E` (recursively). `None` for a bit-blastable leaf. Index-side
    /// datatypes are ignored here (handled by `sort_has_datatype_indexed_array`).
    fn field_element_datatype_name(&self, sort: &Sort) -> Option<String> {
        match sort {
            Sort::Datatype(dt) => Some(dt.name.clone()),
            Sort::Uninterpreted(name)
                if self.ctx.datatype_iter().any(|(dt, _)| dt == name.as_str()) =>
            {
                Some(name.clone())
            }
            Sort::Array(a) => self.field_element_datatype_name(&a.element_sort),
            _ => None,
        }
    }

    /// Max nesting depth of datatype-valued fields in the values of datatype
    /// `dt_name` (0 = only bit-blastable leaf fields). `None` if the datatype is
    /// RECURSIVE (a constructor field transitively re-enters `dt_name`), so its
    /// values have UNBOUNDED depth. `in_progress` tracks the current DFS path for
    /// cycle detection (mirrors `sort_recursively_carries_dt_element_array_rec`).
    fn dt_nesting_depth(&self, dt_name: &str, in_progress: &mut Vec<String>) -> Option<usize> {
        if in_progress.iter().any(|n| n == dt_name) {
            return None; // recursive cycle — unbounded value depth
        }
        let ctors: Vec<String> = self
            .ctx
            .datatype_iter()
            .find(|(dt, _)| *dt == dt_name)
            .map(|(_, cs)| cs.to_vec())
            .unwrap_or_default();
        if ctors.is_empty() {
            return Some(0);
        }
        in_progress.push(dt_name.to_string());
        let mut max_depth = 0usize;
        for ctor in ctors {
            if let Some(sels) = self.ctx.constructor_selector_info(&ctor) {
                for (_, fsort) in sels {
                    if let Some(child) = self.field_element_datatype_name(fsort) {
                        match self.dt_nesting_depth(&child, in_progress) {
                            Some(d) => max_depth = max_depth.max(1 + d),
                            None => {
                                in_progress.pop();
                                return None;
                            }
                        }
                    }
                }
            }
        }
        in_progress.pop();
        Some(max_depth)
    }

    /// Whether the bounded constructor-field congruence (recursion depth
    /// `MAX_READ_CONGRUENCE_DT_DEPTH` in
    /// `dt_array_equality_read_congruence_axioms`) FULLY decomposes every value of
    /// datatype `dt_name` down to its bit-blastable leaves — i.e. the datatype is
    /// non-recursive and nests datatype-valued fields no deeper than the bound.
    ///
    /// A RECURSIVE datatype (`Lst = nil | cons(hd, tl:Lst)`, values of unbounded
    /// depth) or one nesting PAST the bound has contradictions the truncated
    /// recursion never reaches: `(= X Y)` over its element-array can then be a
    /// FALSE SAT (the search builds an inconsistent model the bounded congruence
    /// cannot refute — adversarial audit, recursive-dt class). The bypass must NOT
    /// trust the search for these; they keep the fail-closed degrade gate.
    fn datatype_congruence_fully_covered(&self, dt_name: &str) -> bool {
        // Must be MAX_READ_CONGRUENCE_DT_DEPTH - 1 (dt_axioms/selector.rs = 3).
        // The field-congruence recursion `emit_dt_read_field_congruence` DECOMPOSES
        // a datatype pair at recursion depth `d` only while `d < max_depth`, and
        // the deepest datatype of a nesting-depth-D value sits at recursion depth
        // D — so its scalar leaf fields are emitted only when `D < max_depth`, i.e.
        // `D <= max_depth - 1 = 2`. A depth-3 datatype (`E0->E1->E2->E3->bv`) has
        // its `E3` leaf clash NEVER forced (adversarial audit, minchain: derived-
        // equal-index selects whose depth-4 field congruence is truncated), so it
        // must NOT be treated as covered. Conservative: raising the recursion
        // bound only lets MORE datatypes qualify here; keep this strictly below it.
        const COVER_DEPTH: usize = 2;
        matches!(
            self.dt_nesting_depth(dt_name, &mut Vec::new()),
            Some(d) if d <= COVER_DEPTH
        )
    }

    /// Whether ANY datatype-ELEMENT array reachable from the assertions (+
    /// `extra`) has a RECURSIVE or too-deeply-nested element datatype — one the
    /// bounded constructor-field congruence cannot fully decompose. When true, the
    /// datatype-array degrade gate MUST stay closed regardless of which bypass
    /// predicate (`dt_array_footprint_observationally_complete` or
    /// `dt_array_extensionality_modeled`) otherwise matched: the truncated
    /// recursion cannot refute a deep constructor-field clash, so a returned SAT
    /// can be a FALSE SAT (adversarial audit, recursive-dt class). This is a
    /// route-independent, fail-closed backstop over BOTH bypass paths.
    pub(crate) fn problem_has_uncovered_dt_element_array(&self, extra: &[TermId]) -> bool {
        if self.ctx.datatype_iter().next().is_none() {
            return false;
        }
        let mut visited: ay_core::kani_compat::DetHashSet<TermId> = Default::default();
        let mut stack: Vec<TermId> = self.ctx.assertions.to_vec();
        stack.extend(extra.iter().copied());
        while let Some(t) = stack.pop() {
            if !visited.insert(t) {
                continue;
            }
            let s = self.ctx.terms.sort(t);
            // A RECURSIVE datatype anywhere (as a VALUE or an array element) makes
            // the bounded field congruence depth-incomplete, so the model
            // validator cannot certify a deep clash and the bypass's fast-skip
            // would trust an inconsistent model (observed: `store a i L64 = store a
            // i R64` simplifies to a recursive value equality `L64 = R64` that the
            // depth-bounded congruence cannot refute) — keep the gate.
            if self.sort_carries_recursive_datatype(s) {
                return true;
            }
            if self.sort_has_uncovered_dt_element_array(s) {
                return true;
            }
            // A DISEQUALITY (`distinct`, or `(= .. ..)` under a `not`) whose operand
            // carries a datatype through an ARRAY (a datatype-element array, or a
            // datatype VALUE with a datatype-array field like `Wrap = W(Array _
            // Inner)`) is NOT modeled: the witness pass instantiates extensionality
            // only POSITIVELY, never the Skolem `X != Y => exists k. X[k] != Y[k]`,
            // so two equivalence-class representatives whose equality is DERIVED
            // (`l1=l2 => store(a,i,mk l1)=store(a,i,mk l2)`, or a finite-domain
            // pigeonhole) escape as a false SAT (adversarial audit, disequality /
            // nested-dt-array over `distinct`). Keep the gate over BOTH bypass paths
            // — this also closes a pre-existing footprint over-approval of the same
            // ite-store shape.
            match self.ctx.terms.get(t) {
                TermData::App(sym, args) if sym.name() == "distinct" => {
                    if args
                        .iter()
                        .any(|&arg| self.sort_carries_dt_array_structure(self.ctx.terms.sort(arg)))
                    {
                        return true;
                    }
                }
                TermData::Not(inner) => {
                    if let TermData::App(s2, a2) = self.ctx.terms.get(*inner) {
                        if s2.name() == "="
                            && a2.iter().any(|&arg| {
                                self.sort_carries_dt_array_structure(self.ctx.terms.sort(arg))
                            })
                        {
                            return true;
                        }
                    }
                }
                // A select yielding a DATATYPE VALUE (element sort is DIRECTLY a
                // datatype, not a nested array) at a SYMBOLIC (non-constant) index is
                // NOT modeled: the witness pass models array (dis)equality
                // extensionality, not datatype-valued SELECT-CONGRUENCE at a DERIVED-
                // equal index — `(bvadd i c)=(bvadd j c) => i=j => (select A i)=
                // (select A j)`, or `i=const` derivable — which the eager encoding
                // does not enforce for an opaque datatype value, so a distinct/pinned
                // pair of such selects escapes as a false SAT (adversarial audit,
                // select-cong). A CONSTANT-index select is safe (ROW-foldable), and
                // an OUTER nested-array select (`Array _ (Array _ D)`) yields an
                // ARRAY value — handled by the separate nested-array/equality guards
                // — so it stays bypassable. Keep the gate only for the datatype-VALUE
                // case.
                // Any datatype-carrying array (element carries a datatype directly
                // OR through further array nesting) SELECTED at a SYMBOLIC index is
                // NOT modeled: the witness pass models array (dis)equality
                // extensionality, not SELECT-CONGRUENCE at a DERIVED-equal index
                // (`(bvadd i c)=(bvadd j c) => i=j => (select A i)=(select A j)`), for
                // EITHER a datatype-VALUE select (single-level) or an inner-array
                // select feeding a constant-index read (nested — `(select (select AA
                // i) c)`). The eager encoding does not enforce this for opaque
                // datatype-carrying selects at derived-equal indices, so a
                // distinct/pinned pair escapes as a false SAT (adversarial audit,
                // select-cong / nested-array). A CONSTANT-index select is safe
                // (ROW-foldable). Keep the gate.
                TermData::App(sym, args) if sym.name() == "select" && args.len() == 2 => {
                    let idx = args[1];
                    // "Constant index" includes a NULLARY constructor literal
                    // (`(select a red)` over an enum-indexed array): it is a
                    // ground, pinned cell exactly like a numeric constant — two
                    // distinct nullary constructors can never become derived-
                    // equal, so no select-congruence hazard exists. Non-nullary
                    // constructor indices stay gated (fail-closed): their
                    // equality routes through argument equality, which IS a
                    // derived-index channel. (Nullary constructors appear as both
                    // bare `Var`s named after the constructor and empty `App`s,
                    // depending on the frontend path.)
                    let idx_is_const = match self.ctx.terms.get(idx) {
                        TermData::Const(_) => true,
                        TermData::Var(name, _) => self.ctx.is_constructor(name).is_some(),
                        TermData::App(s, a) => {
                            a.is_empty() && self.ctx.is_constructor(s.name()).is_some()
                        }
                        _ => false,
                    };
                    if self.sort_is_datatype_carrying_array(self.ctx.terms.sort(args[0]))
                        && !idx_is_const
                    {
                        return true;
                    }
                }
                _ => {}
            }
            match self.ctx.terms.get(t) {
                TermData::App(_, args) => stack.extend(args.iter().copied()),
                TermData::Not(inner) => stack.push(*inner),
                TermData::Ite(c, th, el) => {
                    stack.push(*c);
                    stack.push(*th);
                    stack.push(*el);
                }
                TermData::Let(bindings, body) => {
                    stack.push(*body);
                    for (_, v) in bindings {
                        stack.push(*v);
                    }
                }
                _ => {}
            }
        }
        false
    }

    /// Whether datatype `dt_name` (transitively through datatype-valued fields)
    /// has a constructor field that is a datatype-carrying ARRAY (`Array _ D` /
    /// `Array D _`). Such a datatype VALUE (`Wrap = W(arr: Array _ Inner)`) makes a
    /// value (dis)equality push into an array congruence the witness pass models
    /// only positively.
    fn datatype_has_dt_array_field(
        &self,
        dt_name: &str,
        visited: &mut ay_core::kani_compat::DetHashSet<String>,
    ) -> bool {
        if !visited.insert(dt_name.to_string()) {
            return false;
        }
        let ctors: Vec<String> = self
            .ctx
            .datatype_iter()
            .find(|(dt, _)| *dt == dt_name)
            .map(|(_, cs)| cs.to_vec())
            .unwrap_or_default();
        for ctor in ctors {
            if let Some(sels) = self.ctx.constructor_selector_info(&ctor) {
                for (_, fsort) in sels {
                    match fsort {
                        Sort::Array(a) => {
                            if self.sort_carries_datatype(&a.element_sort)
                                || self.sort_carries_datatype(&a.index_sort)
                            {
                                return true;
                            }
                        }
                        other => {
                            if let Some(child) = self.field_element_datatype_name(other) {
                                if self.datatype_has_dt_array_field(&child, visited) {
                                    return true;
                                }
                            }
                        }
                    }
                }
            }
        }
        false
    }

    /// Whether `sort` carries a datatype through an ARRAY — either a
    /// datatype-carrying array directly, or a datatype VALUE with a
    /// datatype-array field (recursively). Used to fail-close the bypass on
    /// DISEQUALITIES over such operands (see `problem_has_uncovered_dt_element_array`).
    fn sort_carries_dt_array_structure(&self, sort: &Sort) -> bool {
        match sort {
            Sort::Array(a) => {
                self.sort_carries_datatype(&a.element_sort)
                    || self.sort_carries_datatype(&a.index_sort)
                    || self.sort_carries_dt_array_structure(&a.element_sort)
            }
            Sort::Datatype(dt) => {
                self.datatype_has_dt_array_field(&dt.name, &mut Default::default())
            }
            Sort::Uninterpreted(name)
                if self.ctx.datatype_iter().any(|(dt, _)| dt == name.as_str()) =>
            {
                self.datatype_has_dt_array_field(name, &mut Default::default())
            }
            _ => false,
        }
    }

    /// Whether `sort` (recursively, through arrays) carries a RECURSIVE datatype —
    /// one whose values have unbounded depth, so the depth-bounded field
    /// congruence and the model validator cannot certify a deep constructor clash.
    /// `dt_nesting_depth` returns `None` exactly for a datatype that is recursive
    /// OR transitively contains one, which is the property we want.
    fn sort_carries_recursive_datatype(&self, sort: &Sort) -> bool {
        match sort {
            Sort::Datatype(dt) => self.dt_nesting_depth(&dt.name, &mut Vec::new()).is_none(),
            Sort::Uninterpreted(name)
                if self.ctx.datatype_iter().any(|(dt, _)| dt == name.as_str()) =>
            {
                self.dt_nesting_depth(name, &mut Vec::new()).is_none()
            }
            Sort::Array(a) => {
                self.sort_carries_recursive_datatype(&a.index_sort)
                    || self.sort_carries_recursive_datatype(&a.element_sort)
            }
            _ => false,
        }
    }

    /// Any datatype-ELEMENT array anywhere in `sort` whose element datatype is NOT
    /// fully covered by the bounded field congruence (recursive or nested too
    /// deep). Such an array is outside the witness pass's sound coverage.
    fn sort_has_uncovered_dt_element_array(&self, sort: &Sort) -> bool {
        match sort {
            Sort::Array(a) => {
                let elem_uncovered = self.sort_carries_datatype(&a.element_sort)
                    && self
                        .field_element_datatype_name(&a.element_sort)
                        .is_none_or(|dt| !self.datatype_congruence_fully_covered(&dt));
                elem_uncovered || self.sort_has_uncovered_dt_element_array(&a.element_sort)
            }
            _ => false,
        }
    }

    /// A NESTED array-of-array carrying a datatype (`Array _ (Array _ ... D)`):
    /// the array's element is ITSELF a datatype-carrying array. An EQUALITY of two
    /// such arrays needs a witness at BOTH the outer and inner index (the outer
    /// witness read is an inner ARRAY value, not a datatype value), but the pass
    /// mints only ONE level, so a nested-const clash is unrefuted (adversarial
    /// audit, nested-dt-array). Such an equality keeps the gate. Merely SELECTING
    /// through a nested array (BMC transition-table lookup) is safe and stays
    /// bypassable — so this is checked only on `=`/`distinct` operands.
    fn sort_is_nested_dt_array(&self, sort: &Sort) -> bool {
        matches!(sort, Sort::Array(a)
            if a.element_sort.is_array() && self.sort_carries_datatype(&a.element_sort))
    }

    /// ROUTE-INDEPENDENT bypass for the datatype-carrying-array degrade gate,
    /// justified by the WITNESS-INDEX EXTENSIONALITY pass
    /// (#dt-array-extensionality-witness in `dt_array_equality_read_congruence_axioms`).
    ///
    /// That pass soundly models the datatype-ELEMENT array fragment WITHOUT
    /// enumerating the index domain — the eager-array wall that made const-array /
    /// large-index datatype-array equalities false-SAT. For `Array Idx E` with a
    /// datatype-FREE index sort and datatype-carrying element `E`:
    ///   - array (dis)equality `(= X Y)` is discharged by instantiating
    ///     extensionality at a fresh SYMBOLIC witness index shared per index sort
    ///     (`(= X Y) => (select X w) = (select Y w)`), so a clash at an
    ///     UNOBSERVED index still surfaces;
    ///   - `select` / `store` / `const-array` / `ite` fold through
    ///     ROW / McCarthy / const / ite-distribution (`dt_fold_select`), reducing
    ///     the witness read to the stored / fill / branch value;
    ///   - constructor fields (incl. nested datatype and array-of-datatype fields)
    ///     are decomposed by folded selector/tester congruence
    ///     (`emit_dt_read_field_congruence`).
    /// Every emitted axiom is a valid Array+DT consequence (extensionality
    /// instance, ROW identity, selector/tester congruence), so a returned SAT
    /// model already satisfies them: it is self-certifying and the fail-closed
    /// degrade gate is soundly bypassed.
    ///
    /// Returns `true` only when EVERY datatype-carrying array reachable from the
    /// assertions is of the modeled element-array shape. A datatype-INDEXED array
    /// (index carries a datatype) or any datatype-carrying array under a
    /// quantifier keeps the gate (fail-closed): those are outside the pass's
    /// coverage. Strict model validation still runs before this bypass is
    /// consulted. Erring toward `false` only RETAINS the sound degrade.
    pub(crate) fn dt_array_extensionality_modeled(&self, extra: &[TermId]) -> bool {
        // No datatypes -> the gate never fires; trivially "modeled".
        if self.ctx.datatype_iter().next().is_none() {
            return true;
        }
        let mut visited: ay_core::kani_compat::DetHashSet<TermId> = Default::default();
        let mut stack: Vec<TermId> = self.ctx.assertions.to_vec();
        stack.extend(extra.iter().copied());
        while let Some(t) = stack.pop() {
            if !visited.insert(t) {
                continue;
            }
            // A datatype-INDEXED array anywhere in this term's sort is outside the
            // witness pass's coverage — keep the gate.
            if self.sort_has_datatype_indexed_array(self.ctx.terms.sort(t)) {
                return false;
            }
            // A datatype-ELEMENT array whose element datatype is RECURSIVE or
            // nests past the field-congruence bound is likewise uncovered: the
            // truncated recursion cannot refute a deep constructor-field clash, so
            // trusting the search there would admit a false SAT (recursive-dt).
            if self.sort_has_uncovered_dt_element_array(self.ctx.terms.sort(t)) {
                return false;
            }
            match self.ctx.terms.get(t) {
                TermData::App(sym, args) => {
                    // A datatype-carrying array PRODUCED by `store` / `map` /
                    // `as-array` / `lambda` / `default` is NOT soundly modeled by
                    // the witness pass: a datatype-value `store` gives a McCarthy
                    // ROW `ite(i=k, V, base[k])` over OPAQUE datatype values, and a
                    // functional array element is likewise opaque, so a value read
                    // back through it (`(select (store a i (C..)) j)`, or a wrapper
                    // (dis)equality over stored arrays) can disagree freely —
                    // admitting a false SAT (adversarial audit: symbolic-index
                    // store, nested wrapper store). Only bare VARIABLES and
                    // const-arrays are safe producers; keep the gate otherwise.
                    if matches!(
                        sym.name(),
                        "store" | "map" | "as-array" | "lambda" | "default"
                    ) && self.sort_carries_datatype(self.ctx.terms.sort(t))
                    {
                        return false;
                    }
                    // A NESTED-array (`Array _ (Array _ D)`) (dis)equality needs a
                    // second-level witness the pass does not mint — keep the gate.
                    // Only equality operands matter (a lookup `select` is safe).
                    if matches!(sym.name(), "=" | "distinct")
                        && args
                            .iter()
                            .any(|&arg| self.sort_is_nested_dt_array(self.ctx.terms.sort(arg)))
                    {
                        return false;
                    }
                    // A DISEQUALITY over a datatype-carrying array (`distinct`, or
                    // `(= X Y)` under a `not` below) is NOT modeled: the witness
                    // pass instantiates extensionality only POSITIVELY (`(= X Y) =>
                    // cells equal`), never the Skolem `X != Y => exists k.
                    // X[k] != Y[k]`, and a finite-cardinality element datatype makes
                    // `distinct A B C` a PIGEONHOLE the search never derives — a
                    // false SAT (adversarial audit, const-array pigeonhole). Keep
                    // the gate.
                    if sym.name() == "distinct"
                        && args.iter().any(|&arg| {
                            self.sort_is_datatype_carrying_array(self.ctx.terms.sort(arg))
                        })
                    {
                        return false;
                    }
                    stack.extend(args.iter().copied());
                }
                TermData::Not(inner) => {
                    if let TermData::App(s, a) = self.ctx.terms.get(*inner) {
                        if s.name() == "="
                            && a.iter().any(|&arg| {
                                self.sort_is_datatype_carrying_array(self.ctx.terms.sort(arg))
                            })
                        {
                            return false;
                        }
                    }
                    stack.push(*inner);
                }
                TermData::Ite(c, th, el) => {
                    stack.push(*c);
                    stack.push(*th);
                    stack.push(*el);
                }
                TermData::Let(bindings, body) => {
                    stack.push(*body);
                    for (_, v) in bindings {
                        stack.push(*v);
                    }
                }
                TermData::Forall(_, _, _) | TermData::Exists(_, _, _) => {
                    // No witness instances are emitted under a quantifier
                    // (bound-variable capture) — keep the gate whenever any
                    // datatype-carrying array appears there.
                    if self.term_has_datatype_carrying_array_sort(t) {
                        return false;
                    }
                }
                _ => {}
            }
        }
        true
    }

    /// ROUTE-INDEPENDENT bypass for the datatype-carrying-array degrade gate:
    /// the problem's datatype-array footprint is OBSERVATIONALLY COMPLETE —
    /// no assertion (or assumption) can observe the array encoding at all, so
    /// any model that passes strict validation is genuine regardless of which
    /// solve route produced it (no bridge axioms required).
    ///
    /// The walk accepts ONLY constructs that create no array-axiom obligation:
    ///   - datatype-carrying-array VARIABLES themselves (a bare variable is
    ///     unobservable; only its uses matter),
    ///   - at most ONE datatype-valued `select` per base array, the base a
    ///     plain variable with a datatype-free index sort (a single select is
    ///     a free opaque datatype value: no FC pair, no ROW, nothing relates
    ///     two array-dependent values),
    ///   - datatype-carrying arrays as arguments to a genuinely UNINTERPRETED
    ///     symbol applied at most ONCE (a single application is a free value;
    ///     only a second application would need congruence over array args).
    /// EVERYTHING else over the datatype-array fragment fails closed: stores,
    /// `=`/`distinct`, ITEs, constants/const-array/map/as-array/default,
    /// datatype-INDEXED arrays, nested datatype-array results, quantifiers.
    ///
    /// SOUNDNESS: under these rules no asserted atom's truth value depends on
    /// the array theory's treatment of the datatype-carrying arrays — each
    /// array-derived value is a fresh opaque term constrained only by the
    /// term-level DT axioms — so the encoding's array incompleteness cannot
    /// manufacture a spurious model for the asserted formula. Strict model
    /// validation still runs before the gate consults this bypass.
    ///
    /// If `select_term` is `(select <base> <idx>)` with a CONCRETE `<idx>` over a
    /// materialized store-chain / const-array whose store indices are all
    /// concrete, return the DETERMINISTICALLY-selected value (McCarthy fold):
    /// the value of the nearest store at the matching index, else the
    /// const-array default. `None` on a symbolic index, a symbolic store index,
    /// a non-store-chain base (Var / computed array), or depth exhaustion. Such
    /// a folded select is a deterministic read of an EXPLICITLY-stored value —
    /// NOT a symbolic observation of unmodeled array elements — so admitting it
    /// into the observational-completeness footprint introduces no
    /// constructor-injectivity-through-array hazard. SOUND by construction: it
    /// only ever returns a value the array literally holds at that concrete index.
    fn fold_dt_select_concrete(&self, select_term: TermId) -> Option<TermId> {
        let TermData::App(sym, args) = self.ctx.terms.get(select_term) else {
            return None;
        };
        if sym.name() != "select" || args.len() != 2 {
            return None;
        }
        let idx = args[1];
        if !matches!(self.ctx.terms.get(idx), TermData::Const(_)) {
            return None; // symbolic query index — could observe any element
        }
        let idx_const = self.ctx.terms.get(idx).clone();
        let mut cur = args[0];
        for _ in 0..64usize {
            match self.ctx.terms.get(cur) {
                TermData::App(s, a) if s.name() == "store" && a.len() == 3 => {
                    if !matches!(self.ctx.terms.get(a[1]), TermData::Const(_)) {
                        return None; // symbolic store index — fold not deterministic
                    }
                    if *self.ctx.terms.get(a[1]) == idx_const {
                        return Some(a[2]);
                    }
                    cur = a[0];
                }
                TermData::App(s, a) if s.name() == "const-array" && a.len() == 1 => {
                    return Some(a[0]);
                }
                _ => return None,
            }
        }
        None
    }

    pub(crate) fn dt_array_footprint_observationally_complete(&self, extra: &[TermId]) -> bool {
        if self.ctx.datatype_iter().next().is_none() {
            return true;
        }

        // GLOBAL aliasing pre-check (#dt-array-eq-components): every
        // datatype-element-array equality chain must be DEFINITIONAL (no two
        // distinct array constructions forced equal). This closes the
        // constructor-injectivity-through-array-equality hazard regardless of
        // per-atom visit order, so the per-construct walk below may admit a
        // definitional `(= v (store ...))` binding.
        if !self.dt_array_equalities_definitional(extra) {
            return false;
        }

        let mut dt_select_count_per_base: ay_core::kani_compat::DetHashMap<TermId, usize> =
            Default::default();
        let mut dt_array_uf_app_count: ay_core::kani_compat::DetHashMap<String, usize> =
            Default::default();

        let mut visited: ay_core::kani_compat::DetHashSet<TermId> = Default::default();
        let mut stack: Vec<TermId> = self.ctx.assertions.to_vec();
        stack.extend(extra.iter().copied());
        while let Some(t) = stack.pop() {
            if !visited.insert(t) {
                continue;
            }
            let s = self.ctx.terms.sort(t).clone();
            match self.ctx.terms.get(t) {
                TermData::App(sym, args) => {
                    let name = sym.name().to_string();
                    let args_v: Vec<TermId> = args.clone();
                    match name.as_str() {
                        "select" => {
                            if self.sort_carries_datatype(&s) {
                                // Result must be a plain (non-array) datatype
                                // value; nested datatype-array results are
                                // observable structure.
                                if self.sort_is_datatype_carrying_array(&s) {
                                    return false;
                                }
                                let Some(&arr_arg) = args_v.first() else {
                                    return false;
                                };
                                if matches!(self.ctx.terms.get(arr_arg), TermData::Var(_, _)) {
                                    // Bare-Var array base: at most ONE symbolic
                                    // datatype-valued select is observationally
                                    // complete (a fresh extensionality witness the
                                    // DT theory can model); index must be non-DT.
                                    if let Sort::Array(arr) = self.ctx.terms.sort(arr_arg) {
                                        if self.sort_carries_datatype(&arr.index_sort) {
                                            return false;
                                        }
                                    } else {
                                        return false;
                                    }
                                    let n =
                                        dt_select_count_per_base.entry(arr_arg).or_insert(0usize);
                                    *n += 1;
                                    if *n > 1 {
                                        return false;
                                    }
                                } else {
                                    // NON-Var base: admit ONLY when the select
                                    // FOLDS DETERMINISTICALLY at a CONCRETE index
                                    // over a materialized store-chain/const-array
                                    // to a specific stored constructor (McCarthy).
                                    // Such a select is a deterministic read of an
                                    // EXPLICITLY-stored value, NOT a symbolic
                                    // observation of unmodeled array elements, so
                                    // it creates NO constructor-injectivity-
                                    // through-array hazard. The folded value is
                                    // pushed so it is itself checked; the base
                                    // store-chain is walked via the default arg
                                    // extension below. A symbolic index or a
                                    // non-store-chain base still fails closed.
                                    // (#g4-concrete-dt-select-fold)
                                    match self.fold_dt_select_concrete(t) {
                                        Some(folded) => stack.push(folded),
                                        None => return false,
                                    }
                                }
                            } else if let Some(&arr_arg) = args_v.first() {
                                if let Sort::Array(arr) = self.ctx.terms.sort(arr_arg) {
                                    // DT-free-VALUE select over a DT-INDEXED array
                                    // is observationally complete when the index
                                    // is a FINITE ALL-NULLARY ENUM (e.g.
                                    // `Array(Color, Int)` read at ctor keys): NO
                                    // datatype VALUE flows through the array, so
                                    // the constructor-injectivity-through-array
                                    // hazard the gate guards cannot arise; the
                                    // ctor keys' pairwise distinctness is a
                                    // term-level DT fact, and the finite-enum
                                    // cardinality gate bounds phantom index
                                    // inhabitants. Any richer index datatype
                                    // (field-bearing, recursive) still fails
                                    // closed. Note the element is DT-free here
                                    // (we are in the non-DT-result branch).
                                    if self.sort_carries_datatype(&arr.index_sort)
                                        && !self.is_finite_nullary_enum_sort(&arr.index_sort)
                                    {
                                        return false;
                                    }
                                }
                            }
                        }
                        "store" => {
                            // A `store` is a WRITE, not an observation, so it
                            // creates no array-axiom obligation on its own — even
                            // when its result is a datatype-element array (the
                            // functional-update shape the VC encoder emits for
                            // `Vec::push`, packed straight into a constructor).
                            // The store's array value becomes OBSERVABLE only
                            // through a subsequent datatype-valued `select` (whose
                            // base is this store, NOT a bare Var, so the `select`
                            // arm fails closed) or an `=`/`distinct`/wrapper
                            // (dis)equality involving it (a store is not a bare
                            // Var, so those arms fail closed). Hence continue the
                            // DAG walk instead of failing closed; every genuine
                            // read/compare over the stored array is still gated by
                            // its own arm. In particular the two-STORES false-SAT
                            // shape `(= (store a i (C x)) (store b i (C (x+1))))`
                            // stays UNSAT/degrade because the `=` arm rejects a
                            // non-variable datatype-array operand.
                            // (#dt-array-store-walk)
                        }
                        "const-array" => {
                            // `(const-array default)` builds the constant array
                            // (the fresh-`Vec` backing store the encoder emits
                            // before any `push`). Like `store`/`ite` it is a
                            // construction, not an observation: its element is
                            // readable only via a datatype-valued `select` (base is
                            // this const-array, not a bare Var -> fails closed) or
                            // an `=` (a non-Var operand; two const-arrays with
                            // DISTINCT defaults are distinct TermIds and so two
                            // constructive nodes -> the definitional-component
                            // pre-pass fails closed). Continue the walk when the
                            // result is a BRIDGE-MODELED datatype array (non-dt
                            // index, plain-scalar dt element); nested / dt-indexed
                            // const-arrays stay unmodeled. (#dt-array-const-array)
                            if self.sort_is_datatype_carrying_array(&s)
                                && !self.is_bridge_modeled_dt_array_sort(&s)
                            {
                                return false;
                            }
                        }
                        "distinct" => {
                            // A `distinct` over any datatype-element-carrying array
                            // (direct or wrapper) is an array DISEQUALITY the
                            // definitional-component analysis does not cover; fail
                            // closed (these are rare and never appear in the
                            // fld_data functional-update fragment).
                            for &a in &args_v {
                                if self.sort_recursively_carries_dt_element_array(
                                    self.ctx.terms.sort(a),
                                ) {
                                    return false;
                                }
                            }
                        }
                        "=" => {
                            // A DIRECT datatype-carrying-array operand must be over
                            // a BRIDGE-MODELED sort (non-datatype index, plain-
                            // scalar-datatype element); nested / datatype-indexed
                            // arrays stay unmodeled and fail closed. The ALIASING
                            // hazard — two syntactically-distinct array
                            // constructions (e.g. two `store` chains) forced equal,
                            //   (= (store a i (C x)) (store b i (C (x+1)))) —
                            // is caught GLOBALLY by
                            // `dt_array_equalities_definitional` (checked once up
                            // front), so a definitional binding `(= v (store ...))`
                            // (one bare-var side, one construction) is admitted
                            // here while the two-STORES shape stays degraded.
                            // Wrapper-datatype (dis)equalities are likewise handled
                            // by that global pre-pass. (#dt-array-eq-components)
                            for &a in &args_v {
                                let sa = self.ctx.terms.sort(a).clone();
                                if self.sort_is_datatype_carrying_array(&sa)
                                    && !self.is_bridge_modeled_dt_array_sort(&sa)
                                {
                                    return false;
                                }
                            }
                        }
                        _ => {
                            let is_selector = self.is_declared_selector(&name);
                            let is_constructor = self.is_declared_constructor(&name);
                            // Result sort is a datatype-carrying array: fail
                            // closed UNLESS this is a datatype SELECTOR extracting
                            // a named field array (`fld_data`-style). The extracted
                            // array is merely NAMED here; its elements are
                            // observable only via a subsequent datatype-valued
                            // `select`, whose base is this selector app (NOT a bare
                            // Var) and which the `select` arm fails closed on — so
                            // the extraction opens no read path.
                            // (#dt-array-selector-extract)
                            if self.sort_is_datatype_carrying_array(&s) && !is_selector {
                                return false;
                            }
                            let has_dt_array_arg = args_v.iter().any(|&a| {
                                self.sort_is_datatype_carrying_array(self.ctx.terms.sort(a))
                            });
                            if has_dt_array_arg {
                                if matches!(
                                    name.as_str(),
                                    "const-array" | "as-array" | "map" | "default" | "eqrange"
                                ) {
                                    return false;
                                }
                                // Packing a datatype-element array into a declared
                                // CONSTRUCTOR is not an observation: constructor
                                // injectivity is observable only through an
                                // `=`/`distinct` over the wrapper, which the
                                // strengthened `=` arm gates. Only a genuinely
                                // UNINTERPRETED function applied MORE THAN ONCE
                                // would need congruence over its array arguments,
                                // so keep the app-count fail-closed only for
                                // non-constructor heads. (#dt-array-ctor-pack)
                                if !is_constructor {
                                    let n =
                                        dt_array_uf_app_count.entry(name.clone()).or_insert(0usize);
                                    *n += 1;
                                    if *n > 1 {
                                        return false;
                                    }
                                }
                            }
                        }
                    }
                    stack.extend(args_v);
                }
                TermData::Var(_, _) => {
                    // A bare datatype-carrying-array variable is unobservable.
                }
                TermData::Const(_) => {
                    if self.sort_is_datatype_carrying_array(&s) {
                        return false;
                    }
                }
                TermData::Ite(c, th, el) => {
                    // An `(ite g A B)` whose result is a datatype-element array is
                    // a CONDITIONAL construction (the SSA shape
                    // `(= v (ite g (store ...) v_init))` the encoder emits for a
                    // guarded `Vec::push`). Like a `store`/constructor it is a
                    // value, not an observation: its elements are observable only
                    // via a datatype-valued `select` (base is this ite, not a bare
                    // Var -> fails closed) or an `=` (a non-Var operand; the
                    // definitional-component pre-pass already counts the ite as a
                    // constructive node, so two distinct ites aliased together are
                    // caught there). Continue the walk instead of failing closed.
                    // (#dt-array-ite-construct)
                    stack.push(*c);
                    stack.push(*th);
                    stack.push(*el);
                }
                TermData::Not(inner) => {
                    stack.push(*inner);
                }
                TermData::Let(bindings, body) => {
                    stack.push(*body);
                    for (_, v) in bindings {
                        stack.push(*v);
                    }
                }
                TermData::Forall(_, _, _) | TermData::Exists(_, _, _) => {
                    if self.term_has_datatype_carrying_array_sort(t) {
                        return false;
                    }
                }
                _ => {}
            }
        }
        true
    }

    /// GLOBAL soundness pre-check for the observational-completeness bypass
    /// (#dt-array-eq-components).
    ///
    /// Builds a union-find over every term that appears as an operand of an `=`
    /// atom at least one of whose operands has a sort that RECURSIVELY carries a
    /// datatype-element array (a bare `Array(_, Datatype)` or a wrapper datatype
    /// like `Vec_PbTerm` packing one). Two operands of the same `=` are unioned.
    /// The check then requires every connected component to contain AT MOST ONE
    /// CONSTRUCTIVE (non-`Var`) node.
    ///
    /// SOUNDNESS. The bit-blast cannot model constructor injectivity THROUGH
    /// array equality, so the one hazard is two syntactically-DISTINCT array
    /// constructions forced equal, e.g.
    ///   (= (store a i (C x)) (store b i (C (x+1)))),
    /// which is UNSAT (the arrays must differ at `i`) yet the incomplete model
    /// satisfies it. Such a hazard makes two constructive nodes share a
    /// component, so this returns `false` (retain the degrade). When every
    /// component has at most one constructive node, all datatype-element-array
    /// equalities form pure definition chains `v_1 = v_2 = … = e` binding free
    /// array variables to a SINGLE value `e`: no independent array (dis)equality
    /// obligation exists, the array theory's element incompleteness cannot
    /// manufacture a spurious model, and (with the other arms still fail-closed
    /// on datatype-valued selects, nested arrays, quantifiers, …) any strictly-
    /// validated model is genuine. Terms are hash-consed, so two textually equal
    /// constructions are ONE node (a reflexive `(= e e)` is harmless).
    fn dt_array_equalities_definitional(&self, extra: &[TermId]) -> bool {
        use ay_core::kani_compat::{DetHashMap, DetHashSet};

        fn uf_find(parent: &mut DetHashMap<TermId, TermId>, x: TermId) -> TermId {
            let mut root = x;
            while let Some(&p) = parent.get(&root) {
                if p == root {
                    break;
                }
                root = p;
            }
            // Path-compress.
            let mut cur = x;
            while let Some(&p) = parent.get(&cur) {
                if p == cur {
                    break;
                }
                parent.insert(cur, root);
                cur = p;
            }
            root
        }

        // Collect the equality edges over datatype-element-array-carrying terms.
        let mut edges: Vec<(TermId, TermId)> = Vec::new();
        let mut visited: DetHashSet<TermId> = Default::default();
        let mut stack: Vec<TermId> = self.ctx.assertions.to_vec();
        stack.extend(extra.iter().copied());
        while let Some(t) = stack.pop() {
            if !visited.insert(t) {
                continue;
            }
            match self.ctx.terms.get(t) {
                TermData::App(sym, args) => {
                    if sym.name() == "=" && args.len() >= 2 {
                        let touches_dt_array = args.iter().any(|&a| {
                            self.sort_recursively_carries_dt_element_array(self.ctx.terms.sort(a))
                        });
                        if touches_dt_array {
                            for w in args.windows(2) {
                                edges.push((w[0], w[1]));
                            }
                        }
                    }
                    for &a in args {
                        stack.push(a);
                    }
                }
                TermData::Not(inner) => stack.push(*inner),
                TermData::Ite(c, th, el) => {
                    stack.push(*c);
                    stack.push(*th);
                    stack.push(*el);
                }
                TermData::Let(bindings, body) => {
                    stack.push(*body);
                    for (_, v) in bindings {
                        stack.push(*v);
                    }
                }
                TermData::Forall(_, body, _) | TermData::Exists(_, body, _) => stack.push(*body),
                _ => {}
            }
        }

        if edges.is_empty() {
            return true;
        }

        let mut parent: DetHashMap<TermId, TermId> = Default::default();
        for &(a, b) in &edges {
            parent.entry(a).or_insert(a);
            parent.entry(b).or_insert(b);
            let ra = uf_find(&mut parent, a);
            let rb = uf_find(&mut parent, b);
            if ra != rb {
                parent.insert(ra, rb);
            }
        }

        // Count constructive (non-variable) nodes per component; a component with
        // two or more forces two distinct array constructions to be equal.
        let nodes: Vec<TermId> = parent.keys().copied().collect();
        let mut constructive_per_root: DetHashMap<TermId, usize> = Default::default();
        for n in nodes {
            if !matches!(self.ctx.terms.get(n), TermData::Var(_, _)) {
                let r = uf_find(&mut parent, n);
                *constructive_per_root.entry(r).or_insert(0usize) += 1;
            }
        }
        constructive_per_root.values().all(|&c| c <= 1)
    }

    fn term_has_datatype_carrying_array_sort(&self, term: TermId) -> bool {
        stacker::maybe_grow(EVAL_STACK_RED_ZONE, EVAL_STACK_SIZE, || {
            if self.sort_is_datatype_carrying_array(self.ctx.terms.sort(term)) {
                return true;
            }
            match self.ctx.terms.get(term) {
                TermData::App(_, args) => args
                    .iter()
                    .any(|&arg| self.term_has_datatype_carrying_array_sort(arg)),
                TermData::Not(inner) => self.term_has_datatype_carrying_array_sort(*inner),
                TermData::Ite(c, t, e) => {
                    self.term_has_datatype_carrying_array_sort(*c)
                        || self.term_has_datatype_carrying_array_sort(*t)
                        || self.term_has_datatype_carrying_array_sort(*e)
                }
                TermData::Let(bindings, body) => {
                    bindings
                        .iter()
                        .any(|(_, bound)| self.term_has_datatype_carrying_array_sort(*bound))
                        || self.term_has_datatype_carrying_array_sort(*body)
                }
                TermData::Forall(_, body, _) | TermData::Exists(_, body, _) => {
                    self.term_has_datatype_carrying_array_sort(*body)
                }
                _ => false,
            }
        })
    }

    pub(in crate::executor::model) fn contains_internal_symbol(&self, term_id: TermId) -> bool {
        stacker::maybe_grow(EVAL_STACK_RED_ZONE, EVAL_STACK_SIZE, || {
            match self.ctx.terms.get(term_id) {
                TermData::App(sym, args) => {
                    if sym.name().starts_with("__ay_") {
                        return true;
                    }
                    args.iter().any(|&arg| self.contains_internal_symbol(arg))
                }
                TermData::Not(inner) => self.contains_internal_symbol(*inner),
                TermData::Ite(c, t, e) => {
                    self.contains_internal_symbol(*c)
                        || self.contains_internal_symbol(*t)
                        || self.contains_internal_symbol(*e)
                }
                TermData::Let(_, body) => self.contains_internal_symbol(*body),
                TermData::Forall(_, body, _) | TermData::Exists(_, body, _) => {
                    self.contains_internal_symbol(*body)
                }
                TermData::Const(_) | TermData::Var(_, _) => false,
                // All current TermData variants are handled above.
                // This arm is required by #[non_exhaustive] and catches future variants.
                other => unreachable!(
                    "unhandled TermData variant in contains_internal_symbol(): {other:?}"
                ),
            }
        })
    }

    /// Check whether a term tree contains a datatype-sorted subterm.
    ///
    /// Datatype symbols may be represented via uninterpreted sorts in the term
    /// store, so this check also uses frontend datatype symbol metadata.
    pub(in crate::executor::model) fn contains_datatype_term(&self, term_id: TermId) -> bool {
        fn is_declared_datatype_sort(executor: &Executor, sort: &Sort) -> bool {
            sort.is_datatype()
                || matches!(
                    sort,
                    Sort::Uninterpreted(name)
                        if executor
                            .ctx
                            .datatype_iter()
                            .any(|(dt, _)| dt == name.as_str())
                )
        }

        fn is_datatype_symbol_name(executor: &Executor, name: &str) -> bool {
            if executor.ctx.is_constructor(name).is_some() {
                return true;
            }
            if name
                .strip_prefix("is-")
                .is_some_and(|ctor| executor.ctx.is_constructor(ctor).is_some())
            {
                return true;
            }
            executor
                .ctx
                .ctor_selectors_iter()
                .any(|(_ctor, selectors)| selectors.iter().any(|sel| sel == name))
        }

        // Visited set: hash-consed DAG, else once-per-path (exponential; this
        // dominated post-solve validation on a 30M-clause BMC instance). Sound:
        // `any`/`||` short-circuit on the first `true`, so a continued-past node
        // evaluated `false`, fixed for this term table.
        let mut visited: ay_core::kani_compat::DetHashSet<TermId> = Default::default();
        self.contains_datatype_term_inner(
            term_id,
            &is_declared_datatype_sort,
            &is_datatype_symbol_name,
            &mut visited,
        )
    }

    #[allow(clippy::type_complexity)]
    fn contains_datatype_term_inner(
        &self,
        term_id: TermId,
        is_declared_datatype_sort: &dyn Fn(&Executor, &Sort) -> bool,
        is_datatype_symbol_name: &dyn Fn(&Executor, &str) -> bool,
        visited: &mut ay_core::kani_compat::DetHashSet<TermId>,
    ) -> bool {
        if !visited.insert(term_id) {
            return false;
        }
        stacker::maybe_grow(EVAL_STACK_RED_ZONE, EVAL_STACK_SIZE, || {
            if is_declared_datatype_sort(self, self.ctx.terms.sort(term_id)) {
                return true;
            }
            let recur =
                |exec: &Executor, t: TermId, v: &mut ay_core::kani_compat::DetHashSet<TermId>| {
                    exec.contains_datatype_term_inner(
                        t,
                        is_declared_datatype_sort,
                        is_datatype_symbol_name,
                        v,
                    )
                };
            match self.ctx.terms.get(term_id) {
                TermData::App(sym, args) => {
                    is_datatype_symbol_name(self, sym.name())
                        || args.iter().any(|&arg| recur(self, arg, visited))
                }
                TermData::Not(inner) => recur(self, *inner, visited),
                TermData::Ite(c, t, e) => {
                    recur(self, *c, visited) || recur(self, *t, visited) || recur(self, *e, visited)
                }
                TermData::Let(_, body) => recur(self, *body, visited),
                TermData::Forall(_, body, _) | TermData::Exists(_, body, _) => {
                    recur(self, *body, visited)
                }
                TermData::Var(name, _) => is_datatype_symbol_name(self, name),
                TermData::Const(_) => false,
                // All current TermData variants are handled above.
                // This arm is required by #[non_exhaustive] and catches future variants.
                other => unreachable!(
                    "unhandled TermData variant in contains_datatype_term(): {other:?}"
                ),
            }
        })
    }

    /// Flatten top-level conjunctions in the assertion list (#5585).
    ///
    /// The solve pipeline's `FlattenAnd` preprocessor splits conjunctions before
    /// Tseitin encoding, so individual conjuncts have SAT variable mappings but
    /// the parent conjunction node may not. This helper mirrors that flattening
    /// so `validate_model` can check each leaf assertion independently with its
    /// own term flags and SAT-fallback lookup.
    pub(crate) fn flatten_assertion_conjunctions(&self) -> Vec<TermId> {
        let mut result = Vec::with_capacity(self.ctx.assertions.len());
        let mut stack: Vec<TermId> = self.ctx.assertions.iter().rev().copied().collect();
        while let Some(term_id) = stack.pop() {
            match self.ctx.terms.get(term_id) {
                TermData::App(sym, args) if sym.name() == "and" => {
                    // Push children in reverse so they come out in order
                    for &arg in args.iter().rev() {
                        stack.push(arg);
                    }
                }
                _ => {
                    result.push(term_id);
                }
            }
        }
        result
    }

    /// Return whether an assertion is an arithmetic Boolean atom where a SAT
    /// truth assignment can be used as a conservative fallback when direct
    /// model evaluation is currently incomplete.
    pub(crate) fn is_arithmetic_boolean_assertion(&self, term_id: TermId) -> bool {
        let mut current = term_id;
        while let TermData::Not(inner) = self.ctx.terms.get(current) {
            current = *inner;
        }

        match self.ctx.terms.get(current) {
            TermData::App(sym, args) => match sym.name() {
                "<" | "<=" | ">" | ">=" => args.len() == 2,
                "=" | "distinct" if args.len() == 2 => {
                    matches!(self.ctx.terms.sort(args[0]), Sort::Int | Sort::Real)
                }
                _ => false,
            },
            _ => false,
        }
    }

    /// Return whether a Bool-sorted term contains arithmetic sub-expressions
    /// (Real or Int-sorted sub-terms). Such formulas are handled by Tseitin
    /// encoding at the SAT level but the LRA/LIA model may not properly
    /// reflect all the constraints created by ITE branching and Boolean
    /// connectives over arithmetic atoms (#8003, #8373).
    ///
    /// Examples:
    /// - `(ite (= x 1.0) (= y 0.0) (= y 1.0))` -- Bool ITE with arithmetic branches
    /// - `(or (and x_84 (= x_93 0.0)) (and x_66 (= x_96 1.0)))` -- mixed Bool+Arith disjunction
    #[allow(dead_code)]
    pub(in crate::executor::model) fn contains_arithmetic_subterm(&self, term_id: TermId) -> bool {
        stacker::maybe_grow(EVAL_STACK_RED_ZONE, EVAL_STACK_SIZE, || {
            let sort = self.ctx.terms.sort(term_id);
            if matches!(sort, Sort::Int | Sort::Real) {
                return true;
            }
            match self.ctx.terms.get(term_id) {
                TermData::Const(_) | TermData::Var(_, _) => false,
                TermData::Not(inner) => self.contains_arithmetic_subterm(*inner),
                TermData::Ite(c, t, e) => {
                    self.contains_arithmetic_subterm(*c)
                        || self.contains_arithmetic_subterm(*t)
                        || self.contains_arithmetic_subterm(*e)
                }
                TermData::App(_, args) => args
                    .iter()
                    .any(|&arg| self.contains_arithmetic_subterm(arg)),
                TermData::Let(_, body) => self.contains_arithmetic_subterm(*body),
                TermData::Forall(_, body, _) | TermData::Exists(_, body, _) => {
                    self.contains_arithmetic_subterm(*body)
                }
                other => unreachable!(
                    "unhandled TermData variant in contains_arithmetic_subterm(): {other:?}"
                ),
            }
        })
    }

    /// Whether a definitively-false arithmetic assertion could plausibly be a
    /// model-extraction gap instead of a hard semantic violation.
    ///
    /// This is intentionally narrower than the `Unknown` SAT-fallback path:
    /// ground arithmetic formulas like `(< 1 0)` must still validate as hard
    /// violations even if the SAT assignment says `true`.
    ///
    /// IMPORTANT: Do NOT widen this check to match Bool-sorted formulas that
    /// merely *contain* arithmetic subterms (e.g., via `contains_arithmetic_subterm`).
    /// `validation_term_is_ground` returns false for `TermData::Var` nodes, which
    /// are used for both quantifier-bound variables AND 0-ary `declare-fun`
    /// constants. In quantifier-free logics (QF_LRA, QF_LIA), ALL declared
    /// constants are `Var` nodes, so broadening the `is_arith` check causes
    /// SAT-fallback to trigger for essentially ALL assertions, masking real
    /// model violations and producing spurious SAT results on UNSAT formulas.
    /// See tgc_io-safe-13 soundness regression.
    pub(in crate::executor::model) fn arithmetic_false_may_be_model_extraction_gap(
        &self,
        model: &Model,
        term_id: TermId,
    ) -> bool {
        if !self.is_arithmetic_boolean_assertion(term_id) {
            return false;
        }
        if model.lia_model.is_none() && model.lra_model.is_none() {
            return false;
        }
        !self.validation_term_is_ground(term_id)
    }

    pub(in crate::executor::model) fn uf_arithmetic_false_may_be_model_extraction_gap(
        &self,
        model: &Model,
        term_id: TermId,
    ) -> bool {
        self.is_arithmetic_boolean_assertion(term_id)
            && model.euf_model.is_some()
            && (model.lia_model.is_some() || model.lra_model.is_some())
            && self.contains_uninterpreted_function_app(term_id)
            // (G3-obs748) A fully-ground UF+arith false atom is a genuine
            // violation, not a model-extraction gap — fail CLOSED. Mirrors
            // `arithmetic_false_may_be_model_extraction_gap` at the sibling call
            // site, which bakes this same ground-guard in.
            && !self.validation_term_is_ground(term_id)
    }

    pub(in crate::executor::model) fn contains_uninterpreted_function_app(
        &self,
        term_id: TermId,
    ) -> bool {
        // Visited set: hash-consed DAG, else once-per-path (exponential). Sound:
        // `any` short-circuits on the first `true`, so a continued-past node
        // evaluated `false`, fixed for this term table.
        let mut visited: ay_core::kani_compat::DetHashSet<TermId> = Default::default();
        self.contains_uninterpreted_function_app_inner(term_id, &mut visited)
    }

    fn contains_uninterpreted_function_app_inner(
        &self,
        term_id: TermId,
        visited: &mut ay_core::kani_compat::DetHashSet<TermId>,
    ) -> bool {
        if !visited.insert(term_id) {
            return false;
        }
        stacker::maybe_grow(EVAL_STACK_RED_ZONE, EVAL_STACK_SIZE, || {
            match self.ctx.terms.get(term_id) {
                TermData::Const(_) | TermData::Var(_, _) => false,
                TermData::App(sym, args) => {
                    let name = sym.name();
                    if matches!(
                        name,
                        "+" | "-"
                            | "*"
                            | "/"
                            | "div"
                            | "mod"
                            | "abs"
                            | "to_real"
                            | "to_int"
                            | "<"
                            | "<="
                            | ">"
                            | ">="
                            | "="
                            | "distinct"
                            | "and"
                            | "or"
                            | "not"
                            | "=>"
                            | "ite"
                            | "select"
                            | "store"
                    ) {
                        args.iter().any(|&arg| {
                            self.contains_uninterpreted_function_app_inner(arg, visited)
                        })
                    } else {
                        true
                    }
                }
                TermData::Not(inner) => {
                    self.contains_uninterpreted_function_app_inner(*inner, visited)
                }
                TermData::Ite(cond, then_term, else_term) => {
                    self.contains_uninterpreted_function_app_inner(*cond, visited)
                        || self.contains_uninterpreted_function_app_inner(*then_term, visited)
                        || self.contains_uninterpreted_function_app_inner(*else_term, visited)
                }
                TermData::Let(bindings, body) => {
                    bindings.iter().any(|(_, value)| {
                        self.contains_uninterpreted_function_app_inner(*value, visited)
                    }) || self.contains_uninterpreted_function_app_inner(*body, visited)
                }
                TermData::Forall(_, body, triggers) | TermData::Exists(_, body, triggers) => {
                    self.contains_uninterpreted_function_app_inner(*body, visited)
                        || triggers.iter().flatten().copied().any(|trigger| {
                            self.contains_uninterpreted_function_app_inner(trigger, visited)
                        })
                }
                _ => false,
            }
        })
    }

    /// Whether a term is a BV comparison predicate (bvult, bvsle, etc.)
    /// as opposed to a BV equality or other BV-flagged term.
    ///
    /// BV comparison predicates (bvult, bvule, bvugt, bvuge, bvslt, bvsle,
    /// bvsgt, bvsge) are evaluated by `evaluate_bv_comparison_predicate`,
    /// which only returns `Bool(false)` when BOTH operands resolve to
    /// concrete `BitVec` values. This makes the result definitive -- not a
    /// model extraction gap. BV equalities (`=` on BitVec), by contrast,
    /// can return `Bool(false)` from the general equality handler even when
    /// one side comes from an incomplete model extraction (ITE, UF, etc.).
    ///
    /// Used by validation (#8597) to distinguish definitively-false BV
    /// comparisons (real violations) from potentially-spurious BV equality
    /// failures (model extraction gaps).
    #[allow(dead_code)]
    pub(in crate::executor::model) fn is_bv_comparison_predicate(&self, term_id: TermId) -> bool {
        if let TermData::App(sym, _) = self.ctx.terms.get(term_id) {
            let name = sym.name();
            matches!(
                name,
                "bvult" | "bvule" | "bvugt" | "bvuge" | "bvslt" | "bvsle" | "bvsgt" | "bvsge"
            )
        } else {
            false
        }
    }

    /// Whether a definitively-false assertion containing ITE subterms could
    /// plausibly be a model-extraction gap (#8373).
    ///
    /// ITE terms create branch-dependent constraints that the LRA simplex
    /// model cannot reconstruct. For example:
    ///   `(ite (= x_92 7.0) (= x_63 x_93) (= x_57 x_93))`
    /// The LRA theory resolves ITE branches at parse time via
    /// `parse_linear_expr`, but the simplex model values may not satisfy the
    /// branch equality when the model evaluator picks a branch.
    ///
    /// This is STRICTLY narrower than the broad `contains_arithmetic_subterm`
    /// approach (which was reverted for soundness — see comment on
    /// `arithmetic_false_may_be_model_extraction_gap`). It only triggers when
    /// the assertion actually contains an `Ite` node, which creates the
    /// structural branch-dependency that the model evaluator cannot resolve.
    pub(in crate::executor::model) fn ite_false_may_be_model_extraction_gap(
        &self,
        model: &Model,
        term_id: TermId,
    ) -> bool {
        if model.lia_model.is_none() && model.lra_model.is_none() {
            return false;
        }
        if !self.contains_ite_subterm(term_id) {
            return false;
        }
        // SOUNDNESS (#919-class false-SAT): a PURE arithmetic/Boolean ITE
        // assertion — one built only from arithmetic ops, comparisons, Boolean
        // connectives, ITE, and Real/Int/Bool constants, with NO uninterpreted
        // functions, arrays, datatypes, etc. — is authoritatively evaluable from
        // the LRA/LIA + Boolean model. Every declared constant in QF_LRA/QF_LIA
        // has a model value, so the evaluator's concrete `Bool(false)` result is
        // definitive: the model genuinely violates the assertion. The
        // `fix_ite_model_values` pass already patches active-branch equalities
        // BEFORE validation runs; a remaining concrete-false on a pure
        // arithmetic ITE assertion means the simplex produced a spurious model,
        // not a model-extraction gap.
        //
        // Accepting SAT-fallback for such assertions let spurious LRA models
        // escape as wrong SAT (gasburner-prop3-{7,8,16}, pursuit-safety-3): e.g.
        // `(ite x_44 (= x_39 x_46) (= x_46 (+ x_39 x_41)))` with x_44=true forces
        // x_46 = x_39, but the model had x_46 = 121/40 ≠ x_39 = 3. We therefore
        // only treat ITE assertions that contain UNINTERPRETED content (where the
        // extracted theory model can legitimately be partial) as a possible
        // extraction gap. Keep the fail-closed behavior here.
        self.contains_uninterpreted_function_app(term_id)
    }

    /// Check whether a term tree contains an ITE subterm at any depth.
    pub(in crate::executor::model) fn contains_ite_subterm(&self, term_id: TermId) -> bool {
        // Visited set: the term store is a hash-consed DAG; without it this walk
        // is once-per-tree-PATH — exponential in sharing depth (the DAG->tree
        // pathology; it dominated post-solve validation on a 30M-clause BMC
        // instance). Sound: `any` short-circuits on the first `true`, so a
        // continued-past node evaluated `false`, fixed for this term table.
        let mut visited: ay_core::kani_compat::DetHashSet<TermId> = Default::default();
        self.contains_ite_subterm_inner(term_id, &mut visited)
    }

    fn contains_ite_subterm_inner(
        &self,
        term_id: TermId,
        visited: &mut ay_core::kani_compat::DetHashSet<TermId>,
    ) -> bool {
        if !visited.insert(term_id) {
            return false;
        }
        stacker::maybe_grow(EVAL_STACK_RED_ZONE, EVAL_STACK_SIZE, || {
            match self.ctx.terms.get(term_id) {
                TermData::Ite(_, _, _) => true,
                TermData::App(_, args) => args
                    .iter()
                    .any(|&arg| self.contains_ite_subterm_inner(arg, visited)),
                TermData::Not(inner) => self.contains_ite_subterm_inner(*inner, visited),
                TermData::Let(_, body) => self.contains_ite_subterm_inner(*body, visited),
                TermData::Forall(_, body, _) | TermData::Exists(_, body, _) => {
                    self.contains_ite_subterm_inner(*body, visited)
                }
                TermData::Const(_) | TermData::Var(_, _) => false,
                other => {
                    unreachable!("unhandled TermData variant in contains_ite_subterm(): {other:?}")
                }
            }
        })
    }

    fn validation_term_is_ground(&self, term_id: TermId) -> bool {
        // Visited set: hash-consed DAG, else once-per-path (exponential). Sound:
        // `all` short-circuits on the first `false`, so a continued-past node
        // evaluated `true`, fixed for this term table.
        let mut visited: ay_core::kani_compat::DetHashSet<TermId> = Default::default();
        self.validation_term_is_ground_inner(term_id, &mut visited)
    }

    fn validation_term_is_ground_inner(
        &self,
        term_id: TermId,
        visited: &mut ay_core::kani_compat::DetHashSet<TermId>,
    ) -> bool {
        if !visited.insert(term_id) {
            return true;
        }
        stacker::maybe_grow(EVAL_STACK_RED_ZONE, EVAL_STACK_SIZE, || {
            match self.ctx.terms.get(term_id) {
                TermData::Var(..)
                | TermData::Let(..)
                | TermData::Forall(..)
                | TermData::Exists(..) => false,
                TermData::Const(_) => true,
                TermData::App(_, args) => args
                    .iter()
                    .all(|&arg| self.validation_term_is_ground_inner(arg, visited)),
                TermData::Not(inner) => self.validation_term_is_ground_inner(*inner, visited),
                TermData::Ite(c, t, e) => [*c, *t, *e]
                    .into_iter()
                    .all(|id| self.validation_term_is_ground_inner(id, visited)),
                other => unreachable!(
                    "unhandled TermData variant in validation_term_is_ground(): {other:?}"
                ),
            }
        })
    }

    /// Return whether a Bool assertion is purely propositional.
    ///
    /// These formulas are justified directly by the SAT assignment when the
    /// evaluator cannot reconstruct intermediate Bool variable values. This is
    /// narrower than SAT-fallback for theory atoms: only Bool vars/constants,
    /// Boolean connectives, Boolean equality, and Bool ITE are accepted.
    pub(in crate::executor::model) fn is_pure_boolean_formula(&self, term_id: TermId) -> bool {
        stacker::maybe_grow(EVAL_STACK_RED_ZONE, EVAL_STACK_SIZE, || {
            if *self.ctx.terms.sort(term_id) != Sort::Bool {
                return false;
            }

            match self.ctx.terms.get(term_id) {
                TermData::Const(Constant::Bool(_)) => true,
                TermData::Var(_, _) => true,
                TermData::Not(inner) => self.is_pure_boolean_formula(*inner),
                TermData::Ite(cond, then_br, else_br) => {
                    self.is_pure_boolean_formula(*cond)
                        && self.is_pure_boolean_formula(*then_br)
                        && self.is_pure_boolean_formula(*else_br)
                }
                TermData::App(sym, args) => match sym.name() {
                    "and" | "or" | "xor" => {
                        !args.is_empty()
                            && args.iter().all(|&arg| self.is_pure_boolean_formula(arg))
                    }
                    "=>" => {
                        args.len() == 2
                            && self.is_pure_boolean_formula(args[0])
                            && self.is_pure_boolean_formula(args[1])
                    }
                    "=" => {
                        args.len() == 2
                            && *self.ctx.terms.sort(args[0]) == Sort::Bool
                            && *self.ctx.terms.sort(args[1]) == Sort::Bool
                            && self.is_pure_boolean_formula(args[0])
                            && self.is_pure_boolean_formula(args[1])
                    }
                    _ => false,
                },
                TermData::Const(_)
                | TermData::Forall(_, _, _)
                | TermData::Exists(_, _, _)
                | TermData::Let(_, _) => false,
                other => {
                    unreachable!(
                        "unhandled TermData variant in is_pure_boolean_formula(): {other:?}"
                    )
                }
            }
        })
    }

    /// Check whether a term tree contains a quantifier (Forall or Exists).
    ///
    /// Quantified assertions cannot be model-checked; Unknown is acceptable
    /// for these assertions since the theory solvers already verified SAT.
    pub(in crate::executor::model) fn contains_quantifier(&self, term_id: TermId) -> bool {
        stacker::maybe_grow(EVAL_STACK_RED_ZONE, EVAL_STACK_SIZE, || {
            match self.ctx.terms.get(term_id) {
                TermData::Forall(_, _, _) | TermData::Exists(_, _, _) => true,
                TermData::App(_, args) => args.iter().any(|&arg| self.contains_quantifier(arg)),
                TermData::Not(inner) => self.contains_quantifier(*inner),
                TermData::Ite(c, t, e) => {
                    self.contains_quantifier(*c)
                        || self.contains_quantifier(*t)
                        || self.contains_quantifier(*e)
                }
                TermData::Let(_, body) => self.contains_quantifier(*body),
                TermData::Const(_) | TermData::Var(_, _) => false,
                // All current TermData variants are handled above.
                // This arm is required by #[non_exhaustive] and catches future variants.
                other => {
                    unreachable!("unhandled TermData variant in contains_quantifier(): {other:?}")
                }
            }
        })
    }

    /// Check whether a term contains an array operation (select, store,
    /// const-array) or a variable of Array sort.
    ///
    /// Used to classify validation diagnostics for array-containing assertions.
    #[cfg(test)]
    pub(in crate::executor::model) fn contains_array_term(&self, term_id: TermId) -> bool {
        stacker::maybe_grow(EVAL_STACK_RED_ZONE, EVAL_STACK_SIZE, || {
            match self.ctx.terms.get(term_id) {
                TermData::App(sym, args) => {
                    let name = sym.name();
                    if name == "select" || name == "store" || name == "const-array" {
                        return true;
                    }
                    args.iter().any(|&arg| self.contains_array_term(arg))
                }
                TermData::Var(_, _) => matches!(self.ctx.terms.sort(term_id), Sort::Array(_)),
                TermData::Not(inner) => self.contains_array_term(*inner),
                TermData::Ite(c, t, e) => {
                    self.contains_array_term(*c)
                        || self.contains_array_term(*t)
                        || self.contains_array_term(*e)
                }
                TermData::Let(_, body) => self.contains_array_term(*body),
                TermData::Forall(_, body, _) | TermData::Exists(_, body, _) => {
                    self.contains_array_term(*body)
                }
                TermData::Const(_) => false,
                other => {
                    unreachable!("unhandled TermData variant in contains_array_term(): {other:?}")
                }
            }
        })
    }

    /// Precompute term classification flags for all terms in a single O(T) pass.
    ///
    /// Because TermIds are allocated sequentially and children always have lower
    /// IDs than parents, a single forward pass from 0..T propagates flags from
    /// children to parents correctly. This replaces 5 separate recursive tree
    /// walks per assertion in `validate_model`, avoiding exponential re-traversal
    /// on shared DAG subterms.
    pub(in crate::executor::model) fn precompute_term_flags(&self) -> Vec<u8> {
        let n = self.ctx.terms.len();
        let mut flags = vec![0u8; n];

        for idx in 0..n {
            let tid = TermId(idx as u32);
            let mut f = 0u8;

            match self.ctx.terms.get(tid) {
                TermData::App(sym, args) => {
                    let name = sym.name();
                    // Internal symbol check
                    if name.starts_with("__ay_") {
                        f |= TERM_FLAG_INTERNAL;
                    }
                    // Array term check
                    if name == "select" || name == "store" || name == "const-array" {
                        f |= TERM_FLAG_ARRAY;
                    }
                    // Seq term check (#5841, #5995): flag Seq operations for
                    // ground evaluation in validate_model.
                    if name.starts_with("seq.") || self.ctx.terms.sort(tid).is_seq() {
                        f |= TERM_FLAG_SEQ;
                    }
                    // String operation check (#4057): flag str.* operations.
                    // String model extraction only assigns values from EQC
                    // constants and may not reflect computed string operations
                    // (str.substr, str.replace, etc.). Model validation
                    // Bool(false) on string assertions is unreliable.
                    if name.starts_with("str.") {
                        f |= TERM_FLAG_STRING;
                    }
                    // FP operation check (#8456): flag fp.* operations.
                    if name.starts_with("fp.")
                        || name == "fp"
                        || name == "to_fp"
                        || name == "to_fp_unsigned"
                    {
                        f |= TERM_FLAG_FP;
                    }
                    // BV comparison check
                    if matches!(
                        name,
                        "bvult"
                            | "bvule"
                            | "bvugt"
                            | "bvuge"
                            | "bvslt"
                            | "bvsle"
                            | "bvsgt"
                            | "bvsge"
                    ) {
                        f |= TERM_FLAG_BV_CMP;
                    }
                    // BV equality check
                    if name == "="
                        && args.len() == 2
                        && matches!(self.ctx.terms.sort(args[0]), Sort::BitVec(_))
                    {
                        f |= TERM_FLAG_BV_CMP;
                    }
                    // Datatype symbol check (constructor, tester, selector)
                    if self.ctx.is_constructor(name).is_some()
                        || name
                            .strip_prefix("is-")
                            .is_some_and(|ctor| self.ctx.is_constructor(ctor).is_some())
                        || self
                            .ctx
                            .ctor_selectors_iter()
                            .any(|(_ctor, sels)| sels.iter().any(|sel| sel == name))
                    {
                        f |= TERM_FLAG_DATATYPE;
                    }
                    // Propagate children flags
                    for &arg in args {
                        f |= flags[arg.index()];
                    }
                }
                TermData::Var(name, _) => {
                    // Internal variable check: solver-generated Skolem witnesses
                    // (extensionality/store decomposition `__ay_*`)
                    // should be treated as internal for model validation (#6731).
                    //
                    // EXCEPTION (inc-14): `__ay_eqdv!*` difference variables
                    // from the EqDiffVar pass are ordinary Int variables with
                    // definitional constraints and full model values. Skipping
                    // them would (a) silently exclude every REWRITTEN assertion
                    // from validation coverage and (b) degrade trivially-sat
                    // queries to Unknown when ALL assertions mention one
                    // ("all assertions skipped" rejection). Validating them is
                    // strictly stronger and fail-closed: a missing model value
                    // fails validation, never fabricates a verdict.
                    //
                    // EXCEPTION (#assert-soft): `__ay_soft_*` relaxation and
                    // cardinality-counter variables introduced by the MaxSMT
                    // solve are ordinary Boolean SAT variables with full model
                    // values. They must be validated, not skipped: when the user
                    // supplied no hard constraints, every relaxation clause
                    // mentions one, and skipping them all degrades a genuine SAT
                    // to Unknown via the "all assertions skipped" rejection.
                    if name.starts_with("__ay_")
                        && !name.starts_with("__ay_eqdv")
                        && !name.starts_with("__ay_soft_")
                    {
                        f |= TERM_FLAG_INTERNAL;
                    }
                    // Array-sorted variables
                    if matches!(self.ctx.terms.sort(tid), Sort::Array(_)) {
                        f |= TERM_FLAG_ARRAY;
                    }
                    // Seq-sorted variables (#5841)
                    if self.ctx.terms.sort(tid).is_seq() {
                        f |= TERM_FLAG_SEQ;
                    }
                    // String-sorted variables (#4057)
                    if matches!(self.ctx.terms.sort(tid), Sort::String) {
                        f |= TERM_FLAG_STRING;
                    }
                    // FP-sorted variables (#8456)
                    if matches!(self.ctx.terms.sort(tid), Sort::FloatingPoint(..)) {
                        f |= TERM_FLAG_FP;
                    }
                    // Datatype-sorted variables or DT symbol names.
                    // DT sorts are stored as Sort::Uninterpreted("<name>") internally,
                    // so we also check if the uninterpreted sort name matches a declared
                    // datatype (dt_axioms.rs:468-470 documents this representation).
                    if self.ctx.terms.sort(tid).is_datatype()
                        || matches!(
                            self.ctx.terms.sort(tid),
                            Sort::Uninterpreted(ref s) if self.ctx.datatype_iter().any(|(dt, _)| dt == s.as_str())
                        )
                        || self.ctx.is_constructor(name).is_some()
                        || name
                            .strip_prefix("is-")
                            .is_some_and(|ctor| self.ctx.is_constructor(ctor).is_some())
                        || self
                            .ctx
                            .ctor_selectors_iter()
                            .any(|(_ctor, sels)| sels.iter().any(|sel| sel == name.as_str()))
                    {
                        f |= TERM_FLAG_DATATYPE;
                    }
                    // FP-sorted constants (#8456)
                    if matches!(self.ctx.terms.sort(tid), Sort::FloatingPoint(..)) {
                        f |= TERM_FLAG_FP;
                    }
                }
                TermData::Not(inner) => {
                    f |= flags[inner.index()];
                }
                TermData::Ite(c, t, e) => {
                    f |= flags[c.index()] | flags[t.index()] | flags[e.index()];
                }
                TermData::Let(_, body) => {
                    f |= flags[body.index()];
                }
                TermData::Forall(_, body, _) | TermData::Exists(_, body, _) => {
                    f |= TERM_FLAG_QUANTIFIER;
                    f |= flags[body.index()];
                }
                TermData::Const(_) => {
                    // Datatype sort on constants (including Uninterpreted representation)
                    if self.ctx.terms.sort(tid).is_datatype()
                        || matches!(
                            self.ctx.terms.sort(tid),
                            Sort::Uninterpreted(ref s) if self.ctx.datatype_iter().any(|(dt, _)| dt == s.as_str())
                        )
                    {
                        f |= TERM_FLAG_DATATYPE;
                    }
                }
                // All current TermData variants are handled above.
                // This arm is required by #[non_exhaustive] and catches future variants.
                other => {
                    unreachable!("unhandled TermData variant in precompute_term_flags(): {other:?}")
                }
            }

            flags[idx] = f;
        }

        flags
    }

    pub(in crate::executor::model) fn sat_term_assigned_true(
        &self,
        model: &Model,
        term: TermId,
    ) -> bool {
        self.term_value(&model.sat_model, &model.term_to_var, term)
            .is_some_and(|b| b)
    }

    pub(in crate::executor::model) fn sat_literal_assigned_true(
        &self,
        model: &Model,
        term: TermId,
    ) -> bool {
        if self.sat_term_assigned_true(model, term) {
            return true;
        }
        if let TermData::Not(inner) = self.ctx.terms.get(term) {
            return self
                .term_value(&model.sat_model, &model.term_to_var, *inner)
                .is_some_and(|b| !b);
        }
        false
    }

    pub(in crate::executor::model) fn sat_assumption_assigned_true(
        &self,
        model: &Model,
        assumption: TermId,
    ) -> bool {
        let has_sat_var = model
            .term_to_var
            .get(&assumption)
            .and_then(|&var_idx| model.sat_model.get(var_idx as usize))
            .copied()
            == Some(true);
        let has_negated_sat_var = if let TermData::Not(inner) = self.ctx.terms.get(assumption) {
            model
                .term_to_var
                .get(inner)
                .and_then(|&var_idx| model.sat_model.get(var_idx as usize))
                .copied()
                == Some(false)
        } else {
            false
        };
        if has_sat_var || has_negated_sat_var {
            return true;
        }
        // (#h10) An assumption Bool atom may have been ELIMINATED by
        // VariableSubstitution preprocessing (e.g. `(= p def)` substitutes
        // `p -> def`), so it has no direct SAT variable. The defining term
        // `def`, however, still carries a SAT-level assignment. Resolve the
        // assumption's polarity, follow the substitution chain to the defining
        // atom, and honor the SAT solver's authoritative truth value for it.
        //
        // This mirrors what the plain-check path already does for the
        // corresponding ground assertion `(= p def)` (whose array flag routes
        // its false evaluation to delegation): it confirms the SAT solver
        // GENUINELY satisfied the assumption even though the extracted concrete
        // model is internally incomplete (e.g. the array index model assigns
        // `i = j` while the select-disequality the SAT solver chose needs
        // `i != j`). Soundness: we only accept when the SAT solver's own
        // literal assignment satisfies the assumption — never inventing a value.
        self.assumption_satisfied_via_substitution(model, assumption)
    }

    /// Resolve an assumption's SAT-level truth by following preprocessing
    /// variable substitutions to the defining atom that still has a SAT
    /// variable, then applying the accumulated negation polarity.
    ///
    /// Returns `true` only when the SAT model's assignment for the resolved
    /// defining atom satisfies the assumption literal. Returns `false` when the
    /// chain dead-ends without a SAT-assigned atom (caller falls through to the
    /// evaluator). The chain is bounded by the number of recorded substitutions
    /// to guarantee termination on any (defensively-possible) cycle.
    fn assumption_satisfied_via_substitution(&self, model: &Model, assumption: TermId) -> bool {
        // Peel leading negations to recover the underlying atom and polarity.
        let mut atom = assumption;
        let mut want_true = true;
        while let TermData::Not(inner) = self.ctx.terms.get(atom) {
            atom = *inner;
            want_true = !want_true;
        }

        // Follow the substitution chain from the atom. At each hop, if the
        // current atom has a SAT variable, the SAT solver decided its truth and
        // that decision is authoritative for the assumption.
        let max_hops = self.recorded_var_substitutions.len() + 1;
        let mut current = atom;
        for _ in 0..max_hops {
            if let Some(&var) = model.term_to_var.get(&current) {
                if let Some(&assigned) = model.sat_model.get(var as usize) {
                    return assigned == want_true;
                }
            }
            // Hop to the substitution target, peeling any negations it carries.
            match self.recorded_var_substitutions.get(&current) {
                Some(&next) => {
                    let mut t = next;
                    while let TermData::Not(inner) = self.ctx.terms.get(t) {
                        t = *inner;
                        want_true = !want_true;
                    }
                    current = t;
                }
                None => break,
            }
        }
        false
    }
}
