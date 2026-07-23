// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Array evaluation helpers for model evaluation.
//!
//! Extracted from `mod.rs` to reduce file size (code-health split).
//! All methods are `impl Executor` — they share the same method namespace.

// #8529: Use deterministic hash sets in all builds.
use ay_core::kani_compat::DetHashSet as HashSet;
use ay_core::term::TermData;
use ay_core::{Sort, TermId};

use super::{EvalValue, Model, NormalizedArray, EVAL_STACK_RED_ZONE, EVAL_STACK_SIZE};

use super::Executor;

/// Collapse authoritative/newest-first interpretation stores to one semantic
/// entry per concrete index. Sorting before this step would make a shadowed
/// older value participate in normalized equality (and could expose it after a
/// redundant authoritative default-valued store is removed).
fn unique_authoritative_stores(stores: &[(String, String)]) -> Vec<(String, String)> {
    let mut seen = HashSet::default();
    stores
        .iter()
        .filter(|(index, _)| seen.insert(index.clone()))
        .cloned()
        .collect()
}

impl Executor {
    /// Return the typed scalar-model authority for one symbolic `(default a)`.
    ///
    /// The final model can carry assignments in SAT, arithmetic, BV, FP,
    /// String, Seq, EUF, or completion maps. Reusing the scalar leaf lookup
    /// keeps array-default evaluation independent of which theory owned the
    /// element sort.
    pub(super) fn evaluate_symbolic_array_default_scalar(
        &self,
        model: &Model,
        default_term: TermId,
    ) -> EvalValue {
        if let Some(euf) = model.euf_model.as_ref() {
            if let Some(&constant) = euf.func_app_const_terms.get(&default_term) {
                return self.evaluate_term(model, constant);
            }
        }
        self.evaluate_var(model, default_term, self.ctx.terms.sort(default_term))
    }

    /// Evaluate the scalar else-value of an array interpretation.
    ///
    /// Syntactic const/store forms are reduced structurally. Symbolic arrays
    /// read the committed default materialized in `ArrayModel`; a scalar model
    /// entry for the `default` term is a final compatibility fallback for
    /// solver paths whose array extraction has not yet mirrored that value.
    pub(in crate::executor) fn evaluate_array_default(
        &self,
        model: &Model,
        default_term: TermId,
        array: TermId,
    ) -> EvalValue {
        let mut current = array;
        let mut visited = HashSet::default();
        while visited.insert(current) {
            match self.ctx.terms.get(current) {
                TermData::App(sym, args) if sym.name() == "store" && args.len() == 3 => {
                    current = args[0];
                }
                TermData::App(sym, args) if sym.name() == "const-array" && args.len() == 1 => {
                    return self.evaluate_term(model, args[0]);
                }
                _ => break,
            }
        }

        if let Some(interp) = model
            .array_model
            .as_ref()
            .and_then(|arrays| arrays.array_values.get(&current))
        {
            if let Some(default) = interp.default.as_deref() {
                let value = self.parse_model_value_string(default, &interp.element_sort);
                if !matches!(value, EvalValue::Unknown) {
                    return value;
                }
            }
        }

        self.evaluate_symbolic_array_default_scalar(model, default_term)
    }

    /// Mirror committed symbolic array-default scalars into `ArrayModel`.
    ///
    /// Array-theory extraction historically consumed only EUF strings, while
    /// Bool/SAT, BV, FP, String, Seq, and completion values live in separate
    /// maps. This fill-only pass runs after those models exist and gives a
    /// missing array interpretation exactly the value already committed for
    /// `(default a)`. Validation and model output therefore consume one
    /// authority.  Unlike an extractor-supplied fallback default, the scalar
    /// value of an explicit `(default a)` term is semantic and therefore
    /// replaces a stale heuristic array default.
    pub(in crate::executor) fn materialize_symbolic_array_defaults(&mut self) -> bool {
        let Some(mut model) = self.last_model.take() else {
            return false;
        };
        let changed = self.materialize_symbolic_array_defaults_in_model(&mut model);
        self.last_model = Some(model);
        if changed {
            self.last_model_validated = false;
            super::eval_memo_clear();
        }
        changed
    }

    /// In-model implementation of [`Self::materialize_symbolic_array_defaults`].
    ///
    /// Model completion owns the model temporarily while it fills scalar leaves;
    /// this helper lets it mirror those newly-available `(default a)` values
    /// before choosing any canonical completion for still-partial arrays.
    pub(super) fn materialize_symbolic_array_defaults_in_model(&self, model: &mut Model) -> bool {
        self.materialize_symbolic_array_defaults_in_model_for(model, None)
    }

    /// Filterable implementation used by validation completion, which must not
    /// total arrays that are unrelated to the current assertion/assumption
    /// roots.  The outer output pass intentionally passes no filter so a
    /// queried declared array with an explicit `(default a)` value can still be
    /// rendered.
    pub(super) fn materialize_relevant_symbolic_array_defaults_in_model(
        &self,
        model: &mut Model,
        relevant: &HashSet<TermId>,
    ) -> bool {
        self.materialize_symbolic_array_defaults_in_model_for(model, Some(relevant))
    }

    fn materialize_symbolic_array_defaults_in_model_for(
        &self,
        model: &mut Model,
        relevant: Option<&HashSet<TermId>>,
    ) -> bool {
        let mut pending = Vec::new();
        for default_term in self.ctx.terms.term_ids() {
            let Some(array) = self.ctx.terms.get_array_default(default_term) else {
                continue;
            };
            if relevant.is_some_and(|terms| !terms.contains(&array)) {
                continue;
            }
            // A dropped conflicting read poisons the whole else region.  Even
            // a scalar assignment for `(default a)` cannot identify the
            // disputed cell, so mirroring it would accidentally total the
            // deliberately-partial interpretation.
            if model
                .array_model
                .as_ref()
                .is_some_and(|arrays| arrays.read_conflicted.contains(&array))
            {
                continue;
            }
            let value = self.evaluate_symbolic_array_default_scalar(model, default_term);
            if matches!(value, EvalValue::Unknown) {
                continue;
            }
            let Ok(rendered) = self.try_format_eval_value(&value, default_term) else {
                continue;
            };
            let Sort::Array(array_sort) = self.ctx.terms.sort(array) else {
                continue;
            };
            pending.push((
                array,
                rendered,
                array_sort.index_sort.clone(),
                array_sort.element_sort.clone(),
            ));
        }
        if pending.is_empty() {
            return false;
        }

        let arrays = model.array_model.get_or_insert_with(Default::default);
        let mut changed = false;
        for (array, value, index_sort, element_sort) in pending {
            let interp = arrays.array_values.entry(array).or_default();
            if interp.default.as_ref() != Some(&value)
                || interp.index_sort.as_ref() != Some(&index_sort)
                || interp.element_sort.as_ref() != Some(&element_sort)
            {
                interp.default = Some(value);
                interp.index_sort = Some(index_sort);
                interp.element_sort = Some(element_sort);
                changed = true;
            }
        }
        changed
    }

    /// Evaluate select(array, index) using array axioms (ROW1/ROW2).
    ///
    /// Recursively peels off `store` layers:
    /// - `select(store(a, i, v), j)` = if `i == j` then `v` else `select(a, j)`
    /// - For base arrays (variables), looks up in the array model.
    pub(in crate::executor) fn evaluate_select(
        &self,
        model: &Model,
        array: TermId,
        index: TermId,
    ) -> EvalValue {
        // Track the array variables whose definitional equality we have already
        // chased during this evaluation. A mutual/cyclic definition — e.g. the
        // extensionality equality `(= s s_pre)` injected for a two-array
        // pointwise forall, which `array_variable_definition` reads in BOTH
        // directions (s -> s_pre and s_pre -> s) — would otherwise drive the
        // `(= a <array-expr>)` resolution below into unbounded self-recursion
        // and overflow the stack. The guard breaks the cycle and falls back to
        // the base-array model lookup (a concrete value or `Unknown`, both of
        // which are sound for model completion).
        let mut def_visited = HashSet::default();
        self.evaluate_select_resolving_defs(model, array, index, &mut def_visited)
    }

    /// Inner implementation of [`Self::evaluate_select`] threading a
    /// definition-cycle guard (`def_visited`) through the array-variable
    /// definitional-equality recursion.
    fn evaluate_select_resolving_defs(
        &self,
        model: &Model,
        array: TermId,
        index: TermId,
        def_visited: &mut HashSet<TermId>,
    ) -> EvalValue {
        let index_val = self.evaluate_term(model, index);

        // Walk through store layers with visited-set cycle guard.
        // In a well-formed term DAG, this chain is structurally finite.
        let mut current_array = array;
        let mut visited = HashSet::default();
        loop {
            if !visited.insert(current_array) {
                break; // cycle detected in malformed term
            }
            let term = self.ctx.terms.get(current_array);
            match term {
                TermData::App(sym, args) if sym.name() == "store" && args.len() == 3 => {
                    let store_index = args[1];
                    let store_value = args[2];
                    let store_index_val = self.evaluate_term(model, store_index);

                    // ROW1/ROW2 require exact equality/disequality evidence for
                    // every index sort. Algebraic (and recursively Seq)
                    // comparisons can remain undecided at their refinement cap;
                    // that is evidence for neither row and must fail closed.
                    match Self::eval_values_equal_exact(&index_val, &store_index_val) {
                        Some(true) => return self.evaluate_term(model, store_value),
                        Some(false) => {}
                        None => return EvalValue::Unknown,
                    }

                    // Different concrete indices: peel this store and continue.
                    current_array = args[0];
                    continue;
                }
                TermData::App(sym, args) if sym.name() == "const-array" && args.len() == 1 => {
                    // const-array: all indices map to the same value
                    return self.evaluate_term(model, args[0]);
                }
                TermData::App(sym, args) if sym.name() == "lambda-array" && args.len() == 2 => {
                    // Runtime beta reduction. Term construction eagerly reduces
                    // `select(lambda, i)`, but model validation can expose a
                    // lambda only after chasing an asserted definition and
                    // peeling one or more stores:
                    //
                    //   select(arr, j), arr = store(lambda x. body, i, v)
                    //
                    // At j != i the evaluator reaches the lambda after the
                    // original select term has already been interned. Bind the
                    // lambda variable to the concrete index value for the body
                    // evaluation. The scoped override disables the ordinary
                    // term memo and restores every outer override on drop, so a
                    // body cached/evaluated at one index can never leak into a
                    // different read. An unresolved index remains fail-closed.
                    if matches!(index_val, EvalValue::Unknown) {
                        return EvalValue::Unknown;
                    }
                    return super::dt_model::with_scoped_term_override(
                        args[0],
                        index_val.clone(),
                        || self.evaluate_term(model, args[1]),
                    );
                }
                TermData::App(sym, args)
                    if sym.name() == "select"
                        && args.len() == 2
                        && matches!(self.ctx.terms.sort(current_array), Sort::Array(_)) =>
                {
                    // Nested-array read (#nested-array-row wrong-SAT, QF_AUFNIA):
                    // `current_array` is itself `(select B j)` whose ELEMENT
                    // sort is another array, so this select denotes an ARRAY
                    // value — the inner array `B[j]`. The store-walk above only
                    // reduces `store`/`const-array`/`lambda` heads, so without
                    // this arm the inner select is treated as an opaque base:
                    // `evaluate_select` returns Unknown and the caller's
                    // arith/BV-model fallback launders the solver's
                    // unconstrained opaque value for a read that the store
                    // structure actually FORCES (e.g. `select(select(store(m,b,
                    // store(a,o,V)),b),o)` is V, not free). Resolve the inner
                    // select to the concrete inner-array term it denotes and
                    // keep peeling. Resolution is exact-or-nothing: on any
                    // undecidable index it returns None and we fall through to
                    // the existing sound opaque handling.
                    match self.resolve_array_valued_select(model, args[0], args[1], def_visited) {
                        Some(inner) if inner != current_array => {
                            current_array = inner;
                            continue;
                        }
                        _ => break,
                    }
                }
                _ => break,
            }
        }

        // Resolve an explicit constructor definition `(= a <array-expr>)`
        // before consulting a reconstructed entry for `a`.  Completion may
        // install a total fallback entry for a defined variable; that entry is
        // not allowed to shadow the asserted store chain (storecomm otherwise
        // reads two empty fallback arrays and rejects a valid witness).  A
        // variable-to-variable alias is chased only when no model entry exists,
        // preserving the committed representative and avoiding alias cycles.
        // In pure QF_(A)LIA the array's value can live only in the committed
        // assertion (#5450).
        if matches!(self.ctx.terms.get(current_array), TermData::Var(_, _)) {
            let has_model_entry = model
                .array_model
                .as_ref()
                .is_some_and(|am| am.array_values.contains_key(&current_array));
            let definition = if has_model_entry {
                // A completed model entry may be bypassed only by one
                // unambiguous asserted constructor definition.  When a
                // variable has two different store definitions, choosing one
                // here can make completion alternate between incompatible
                // candidates instead of letting the fail-closed gate reject
                // the partial witness.
                self.unique_array_constructor_definition_excluding(current_array, def_visited)
            } else {
                self.array_variable_definition_excluding(current_array, def_visited)
            };
            if let Some(def) = definition {
                // The definition is an ambient assertion, not syntax under
                // the lambda binder. Following one that mentions an active
                // bound TermId would dynamically capture that unrelated
                // occurrence through the scoped override.
                // Chase each base variable's definition at most once. The
                // exclusion above already skips an already-visited variable
                // definition; recording `current_array` here guards the
                // remaining edges of any definitional cycle. On a revisit
                // we stop recursing and fall through to the base-array model
                // lookup, which yields a concrete value or `Unknown` — both
                // sound for model completion (never a false answer).
                if !super::dt_model::term_depends_on_scoped_binding(&self.ctx.terms, def)
                    && def != array
                    && def_visited.insert(current_array)
                {
                    return self.evaluate_select_resolving_defs(model, def, index, def_visited);
                }
            }
        }

        // Every remaining interpretation is keyed by `current_array`'s
        // ambient TermId. A binder-dependent array expression can denote a
        // different array at each beta instance, so no such entry is a valid
        // contextual fallback. Store/const/lambda structure was handled above.
        if super::dt_model::term_depends_on_scoped_binding(&self.ctx.terms, current_array) {
            return EvalValue::Unknown;
        }

        // Base array: first honor explicit model stores, then exact
        // bit-blasted select terms, and only then array defaults. QF_ABV array
        // extraction uses a zero default for model completion; letting that
        // default shadow the exact select term can turn an incomplete array
        // entry into a concrete false direct-select assertion.
        let store_result = self.lookup_array_model_store_entry(model, current_array, &index_val);
        if !matches!(store_result, EvalValue::Unknown) {
            return store_result;
        }

        let exact_select_result = self.bv_exact_select_fallback(model, current_array, index);
        if !matches!(exact_select_result, EvalValue::Unknown) {
            let array_result = self.lookup_array_model(model, current_array, &index_val);
            if !matches!(array_result, EvalValue::Unknown) {
                if matches!(
                    Self::eval_values_equal_exact(&exact_select_result, &array_result),
                    Some(true)
                ) {
                    return exact_select_result;
                }
                // A BV-backed exact select and the reconstructed array model
                // disagree. Treat that as incomplete model evidence rather than
                // letting SAT-side select bits mask an array-model conflict.
                return EvalValue::Unknown;
            }
            return exact_select_result;
        }

        // Base array: look up in array model, including defaults.
        let result = self.lookup_array_model(model, current_array, &index_val);
        if !matches!(result, EvalValue::Unknown) {
            return result;
        }

        // BV model fallback (#8510): when the array model has no entry for
        // this base array + index combination, scan the BV model for any
        // `select(current_array, idx)` term whose index evaluates to the
        // same concrete value. The BV model contains bit-blasted values for
        // ALL select terms (including those created by array axiom generation
        // and CEGAR FC refinement), so this resolves selects that
        // `extract_array_model_from_bv_model` missed — either because:
        // (a) the select was through a store chain (deliberately excluded
        //     from array model construction to avoid non-determinism), or
        // (b) the index is a UF application whose BV value wasn't formatted
        //     as a string key in the array model.
        self.bv_select_fallback(model, current_array, &index_val)
    }

    /// Resolve an ARRAY-valued `(select outer_arr outer_idx)` — a read of a
    /// nested array whose element sort is itself an array — to the concrete
    /// inner-array term it denotes under `model`.
    ///
    /// Peels `outer_arr`'s store chain at the model value of `outer_idx`
    /// (chasing array-variable definitional equalities and nested selects),
    /// and returns the stored array-valued term, or a `const-array`'s element
    /// array term. Resolution is exact-or-nothing: an unknown index, a
    /// non-exact index comparison, or an opaque base array-of-array variable
    /// with no structural definition all yield `None`, so the caller retains
    /// its existing sound opaque handling. Because a `Some` result is the
    /// array value FORCED by the store structure under the model, feeding it
    /// back into the select walk can only make a store-determined read
    /// concrete — never manufacture a value inconsistent with the stores.
    fn resolve_array_valued_select(
        &self,
        model: &Model,
        outer_arr: TermId,
        outer_idx: TermId,
        def_visited: &mut HashSet<TermId>,
    ) -> Option<TermId> {
        // A binder-dependent nested array denotes a different array per beta
        // instance; no ambient TermId resolution is valid then.
        if super::dt_model::scoped_term_binding_active()
            && super::dt_model::term_depends_on_scoped_binding(&self.ctx.terms, outer_arr)
        {
            return None;
        }
        let idx_val = self.evaluate_term(model, outer_idx);
        if matches!(idx_val, EvalValue::Unknown) {
            return None;
        }
        let mut arr = outer_arr;
        let mut visited = HashSet::default();
        loop {
            if !visited.insert(arr) {
                return None; // structural cycle in a malformed term DAG
            }
            match self.ctx.terms.get(arr) {
                TermData::App(sym, args) if sym.name() == "store" && args.len() == 3 => {
                    let store_idx_val = self.evaluate_term(model, args[1]);
                    match Self::eval_values_equal_exact(&idx_val, &store_idx_val) {
                        // ROW1: this write determines the read — its value is
                        // the inner array term.
                        Some(true) => return Some(args[2]),
                        // ROW2: distinct index — peel and continue.
                        Some(false) => {
                            arr = args[0];
                            continue;
                        }
                        // Undecided overwrite: cannot prove which cell wins.
                        None => return None,
                    }
                }
                TermData::App(sym, args) if sym.name() == "const-array" && args.len() == 1 => {
                    return Some(args[0]);
                }
                TermData::App(sym, args)
                    if sym.name() == "select"
                        && args.len() == 2
                        && matches!(self.ctx.terms.sort(arr), Sort::Array(_)) =>
                {
                    // A deeper nesting level: resolve it first, then continue
                    // peeling the array it denotes.
                    match self.resolve_array_valued_select(model, args[0], args[1], def_visited) {
                        Some(inner) if inner != arr => {
                            arr = inner;
                            continue;
                        }
                        _ => return None,
                    }
                }
                TermData::Var(_, _) => {
                    // Opaque array-of-array base: only a structural definition
                    // (`(= v (store ...))` / `(= v (const-array ...))`) pins the
                    // inner array. A genuinely free base has no concrete inner
                    // array, so return None (caller falls back soundly).
                    if !def_visited.insert(arr) {
                        return None; // definitional cycle
                    }
                    match self.array_variable_definition_excluding(arr, def_visited) {
                        Some(def) if def != arr => {
                            arr = def;
                            continue;
                        }
                        _ => return None,
                    }
                }
                _ => return None,
            }
        }
    }

    /// Return true when exact bit-blasted select evidence conflicts with the
    /// reconstructed array interpretation for the same base read.
    ///
    /// `evaluate_term(select(...))` has a later BV-cache fallback when
    /// `evaluate_select` returns `Unknown`. This predicate lets that outer
    /// fallback distinguish a missing model entry from contradictory model
    /// evidence.
    pub(in crate::executor) fn bv_exact_select_array_model_conflict(
        &self,
        model: &Model,
        array: TermId,
        index: TermId,
    ) -> bool {
        let index_val = self.evaluate_term(model, index);
        let mut current_array = array;
        let mut visited = HashSet::default();

        loop {
            if !visited.insert(current_array) {
                return false;
            }
            match self.ctx.terms.get(current_array) {
                TermData::App(sym, args) if sym.name() == "store" && args.len() == 3 => {
                    let store_index_val = self.evaluate_term(model, args[1]);
                    match Self::eval_values_equal_exact(&index_val, &store_index_val) {
                        Some(false) => current_array = args[0],
                        Some(true) | None => return false,
                    }
                }
                TermData::App(sym, args) if sym.name() == "const-array" && args.len() == 1 => {
                    return false;
                }
                _ => break,
            }
        }

        let store_result = self.lookup_array_model_store_entry(model, current_array, &index_val);
        if !matches!(store_result, EvalValue::Unknown) {
            return false;
        }

        let exact_select_result = self.bv_exact_select_fallback(model, current_array, index);
        if matches!(exact_select_result, EvalValue::Unknown) {
            return false;
        }

        let array_result = self.lookup_array_model(model, current_array, &index_val);
        !matches!(array_result, EvalValue::Unknown)
            && matches!(
                Self::eval_values_equal_exact(&exact_select_result, &array_result),
                Some(false)
            )
    }

    /// Look up only explicit array-model store entries.
    ///
    /// This lets direct select evaluation prefer authoritative stores without
    /// prematurely accepting model-completion defaults.
    fn lookup_array_model_store_entry(
        &self,
        model: &Model,
        array: TermId,
        index_val: &EvalValue,
    ) -> EvalValue {
        let Some(ref array_model) = model.array_model else {
            return EvalValue::Unknown;
        };
        let Some(interp) = array_model.array_values.get(&array) else {
            return EvalValue::Unknown;
        };

        for (stored_idx, stored_val) in &interp.stores {
            let parsed_idx = self.parse_model_value_string(stored_idx, &interp.index_sort);
            if matches!(parsed_idx, EvalValue::Unknown) {
                continue;
            }
            match Self::eval_values_equal_exact(index_val, &parsed_idx) {
                Some(true) => {
                    return self.parse_model_value_string(stored_val, &interp.element_sort);
                }
                Some(false) => {}
                None => return EvalValue::Unknown,
            }
        }

        EvalValue::Unknown
    }

    /// Look up a base array variable in the array model.
    ///
    /// Store entries are matched with typed comparisons so mixed AUFLIA/AUFLRA
    /// models can validate concrete `select` assertions. Once every parseable
    /// store index is proved distinct from the requested index, the committed
    /// default is the array's exact value at that index under every theory mix.
    fn lookup_array_model(&self, model: &Model, array: TermId, index_val: &EvalValue) -> EvalValue {
        let Some(ref array_model) = model.array_model else {
            return EvalValue::Unknown;
        };
        let Some(interp) = array_model.array_values.get(&array) else {
            return EvalValue::Unknown;
        };

        let mut has_unparseable_index = false;
        for (stored_idx, stored_val) in &interp.stores {
            let parsed_idx = self.parse_model_value_string(stored_idx, &interp.index_sort);
            if matches!(parsed_idx, EvalValue::Unknown) {
                has_unparseable_index = true;
                continue;
            }
            match Self::eval_values_equal_exact(index_val, &parsed_idx) {
                Some(true) => {
                    return self.parse_model_value_string(stored_val, &interp.element_sort);
                }
                Some(false) => {}
                None => return EvalValue::Unknown,
            }
        }

        if has_unparseable_index {
            return EvalValue::Unknown;
        }

        // Extraction deliberately leaves a read-conflicted interpretation
        // partial: at least one concrete cell was dropped because committed
        // reads disagreed.  A default would silently choose a value for that
        // poisoned cell, so it is not usable as miss evidence even when some
        // other phase happened to materialize one.  Exact explicit stores
        // above remain safe and continue to resolve.
        if array_model.read_conflicted.contains(&array) {
            return EvalValue::Unknown;
        }

        // Every store index above was parsed and compared with the fully
        // evaluated target index. `Some(false)` is exact disequality evidence;
        // `None` and unparseable keys already returned Unknown. Therefore a
        // complete miss means the interpretation's committed default is the
        // exact read value. Refusing it merely because LIA/LRA is present loses
        // valid unlisted-index reads and makes model minimization appear to
        // change semantics.
        if let Some(ref default) = interp.default {
            return self.parse_model_value_string(default, &interp.element_sort);
        }

        EvalValue::Unknown
    }

    /// BV model fallback for select evaluation (#8510).
    ///
    /// When `evaluate_select` walks a store chain to a base array variable
    /// and `lookup_array_model` returns Unknown, scan the BV model for any
    /// `select(base_array, idx)` term whose index evaluates to the same
    /// concrete value as the target index. Returns the BV model value for
    /// the matching select term, or Unknown if no match is found.
    ///
    /// This resolves the gap between the array model (built from direct
    /// `select(Var, idx)` terms only) and the BV model (which contains
    /// bit-blasted values for ALL select terms, including store-chain
    /// selects and CEGAR-generated selects).
    fn bv_select_fallback(
        &self,
        model: &Model,
        base_array: TermId,
        index_val: &EvalValue,
    ) -> EvalValue {
        let bv_model = match &model.bv_model {
            Some(m) => m,
            None => return EvalValue::Unknown,
        };
        let scoped_binding_active = super::dt_model::scoped_term_binding_active();

        // We need to find any select(base_array, idx) term in the BV model
        // where idx evaluates to the same concrete value as index_val.
        for (&term_id, val) in &bv_model.values {
            if scoped_binding_active
                && super::dt_model::term_depends_on_scoped_binding(&self.ctx.terms, term_id)
            {
                continue;
            }
            if let TermData::App(sym, args) = self.ctx.terms.get(term_id) {
                if sym.name() == "select" && args.len() == 2 && args[0] == base_array {
                    let candidate_idx_val = self.evaluate_term(model, args[1]);
                    match Self::eval_values_equal_exact(index_val, &candidate_idx_val) {
                        Some(true) => {
                            let sort = self.ctx.terms.sort(term_id);
                            if let Sort::BitVec(bv) = sort {
                                return EvalValue::BitVec {
                                    value: val.clone(),
                                    width: bv.width,
                                };
                            }
                        }
                        Some(false) => {}
                        None => return EvalValue::Unknown,
                    }
                }
            }
        }

        // Also check Bool-sorted selects in bool_overrides (#6047).
        for (&term_id, &val) in &bv_model.bool_overrides {
            if scoped_binding_active
                && super::dt_model::term_depends_on_scoped_binding(&self.ctx.terms, term_id)
            {
                continue;
            }
            if let TermData::App(sym, args) = self.ctx.terms.get(term_id) {
                if sym.name() == "select" && args.len() == 2 && args[0] == base_array {
                    let candidate_idx_val = self.evaluate_term(model, args[1]);
                    match Self::eval_values_equal_exact(index_val, &candidate_idx_val) {
                        Some(true) => return EvalValue::Bool(val),
                        Some(false) => {}
                        None => return EvalValue::Unknown,
                    }
                }
            }
        }

        // Datatype/uninterpreted-ELEMENT selects (#g4-dt-ce-select): the committed
        // element value of a DIRECT `(select base_array idx)` read lives in the EUF
        // model's `term_values`, NOT in the BV/Bool model, so the scans above miss
        // datatype-carrying arrays (Vec_PbConstraint::fld_data etc.). Return that
        // committed element so a downstream selector — e.g. `(fld_rhs (select a i))`
        // — composes via EUF congruence (find_congruent_bv_app) to the committed
        // field value. This closes the datatype-CE reconstruction gap: without it a
        // free datatype-element array read defaults/Unknowns and a subst-recovered
        // constraint (local_6_0) is mis-derived, invalidating the emitted model.
        // SOUND: only committed DIRECT reads (base_array is the reached base) are
        // used; conflicting committed reads at the same concrete index yield
        // `Unknown` (fail-closed), never a guessed element.
        if let Some(euf_model) = model.euf_model.as_ref() {
            let mut found: Option<&str> = None;
            for &term_id in euf_model.term_values.keys() {
                // `term_values` can carry non-term SENTINEL keys (e.g. the
                // `REPAIR_MARKER` = TermId(u32::MAX - 7) inserted by
                // `repair_asserted_array_read_pins`); `terms.get` on an
                // out-of-range id panics (index-out-of-bounds). Skip any key not
                // backed by a real term — the same guard eval_uf uses (#g4-dt-ce-select).
                if (term_id.0 as usize) >= self.ctx.terms.len() {
                    continue;
                }
                if scoped_binding_active
                    && super::dt_model::term_depends_on_scoped_binding(&self.ctx.terms, term_id)
                {
                    continue;
                }
                let TermData::App(sym, args) = self.ctx.terms.get(term_id) else {
                    continue;
                };
                if sym.name() != "select" || args.len() != 2 || args[0] != base_array {
                    continue;
                }
                if !matches!(self.ctx.terms.sort(term_id), Sort::Uninterpreted(_)) {
                    continue;
                }
                let candidate_idx_val = self.evaluate_term(model, args[1]);
                match Self::eval_values_equal_exact(index_val, &candidate_idx_val) {
                    Some(true) => {}
                    Some(false) => continue,
                    None => return EvalValue::Unknown,
                }
                let Some(elem) = euf_model.term_values.get(&term_id) else {
                    continue;
                };
                match found {
                    None => found = Some(elem.as_str()),
                    Some(prev) if prev != elem.as_str() => return EvalValue::Unknown, // conflict
                    _ => {}
                }
            }
            if let Some(elem) = found {
                return EvalValue::Element(elem.to_string());
            }
        }

        EvalValue::Unknown
    }

    /// Exact-syntax BV model fallback for a base-array select.
    ///
    /// This is deliberately narrower than `bv_select_fallback`: it only accepts
    /// the value of the exact term `(select base_array index)`. That is safe to
    /// prefer over array-model defaults while avoiding arbitrary choice among
    /// multiple same-concrete-index selects that may have conflicting
    /// unconstrained SAT bits.
    fn bv_exact_select_fallback(
        &self,
        model: &Model,
        base_array: TermId,
        index: TermId,
    ) -> EvalValue {
        if super::dt_model::scoped_term_binding_active()
            && (super::dt_model::term_depends_on_scoped_binding(&self.ctx.terms, base_array)
                || super::dt_model::term_depends_on_scoped_binding(&self.ctx.terms, index))
        {
            return EvalValue::Unknown;
        }
        let bv_model = match &model.bv_model {
            Some(m) => m,
            None => return EvalValue::Unknown,
        };

        for (&term_id, val) in &bv_model.values {
            if let TermData::App(sym, args) = self.ctx.terms.get(term_id) {
                if sym.name() == "select"
                    && args.len() == 2
                    && args[0] == base_array
                    && args[1] == index
                {
                    let sort = self.ctx.terms.sort(term_id);
                    if let Sort::BitVec(bv) = sort {
                        return EvalValue::BitVec {
                            value: val.clone(),
                            width: bv.width,
                        };
                    }
                }
            }
        }

        for (&term_id, &val) in &bv_model.bool_overrides {
            if let TermData::App(sym, args) = self.ctx.terms.get(term_id) {
                if sym.name() == "select"
                    && args.len() == 2
                    && args[0] == base_array
                    && args[1] == index
                {
                    return EvalValue::Bool(val);
                }
            }
        }

        EvalValue::Unknown
    }

    /// Compare evaluated values with exact, tri-state evidence.
    ///
    /// `None` means equality is undecidable (an unknown value, an algebraic
    /// refinement cap, or a sequence containing one). Callers may apply ROW1
    /// only on `Some(true)` and ROW2/difference reasoning only on `Some(false)`.
    pub(super) fn eval_values_equal_exact(a: &EvalValue, b: &EvalValue) -> Option<bool> {
        match (a, b) {
            (EvalValue::Unknown, _) | (_, EvalValue::Unknown) => None,
            (EvalValue::Bool(a), EvalValue::Bool(b)) => Some(a == b),
            (EvalValue::Element(a), EvalValue::Element(b)) => Some(a == b),
            (EvalValue::Rational(a), EvalValue::Rational(b)) => Some(a == b),
            (
                EvalValue::BitVec {
                    value: av,
                    width: aw,
                },
                EvalValue::BitVec {
                    value: bv,
                    width: bw,
                },
            ) => Some(av == bv && aw == bw),
            (EvalValue::Fp(a), EvalValue::Fp(b)) => Some(a.to_smtlib() == b.to_smtlib()),
            (EvalValue::String(a), EvalValue::String(b)) => Some(a == b),
            (EvalValue::Algebraic(a), EvalValue::Algebraic(b)) => a.eq_value(b),
            (EvalValue::Algebraic(a), EvalValue::Rational(b))
            | (EvalValue::Rational(b), EvalValue::Algebraic(a)) => a
                .cmp_rational(b)
                .map(|ordering| ordering == std::cmp::Ordering::Equal),
            (EvalValue::Seq(a), EvalValue::Seq(b)) => {
                if a.len() != b.len() {
                    return Some(false);
                }
                let mut undecided = false;
                for (a, b) in a.iter().zip(b) {
                    match Self::eval_values_equal_exact(a, b) {
                        Some(true) => {}
                        Some(false) => return Some(false),
                        None => undecided = true,
                    }
                }
                if undecided {
                    None
                } else {
                    Some(true)
                }
            }
            (EvalValue::Algebraic(_), _) | (_, EvalValue::Algebraic(_)) => Some(false),
            (EvalValue::Seq(_), _) | (_, EvalValue::Seq(_)) => Some(false),
            _ => Some(false),
        }
    }

    /// When `sort` is an ALL-NULLARY (enum) datatype, return its number of
    /// constructors — its exact (finite) inhabitant count. Resolves both the
    /// inline `Sort::Datatype` form and a bare `Sort::Uninterpreted(name)`
    /// against the declared-datatype registry. Returns `None` for any sort that
    /// is not a finite all-nullary datatype (a constructor with fields makes the
    /// domain unbounded). Used by the finite-index array extensionality oracle.
    pub(in crate::executor) fn enum_datatype_constructor_count(
        &self,
        sort: &Sort,
    ) -> Option<usize> {
        match sort {
            Sort::Datatype(dt) => {
                if dt.constructors.is_empty()
                    || !dt.constructors.iter().all(|c| c.fields.is_empty())
                {
                    return None;
                }
                Some(dt.constructors.len())
            }
            Sort::Uninterpreted(name) => {
                let ctors: Vec<String> = self
                    .ctx
                    .datatype_iter()
                    .find(|(dt_name, _)| dt_name == name)
                    .map(|(_, cs)| cs.to_vec())
                    .unwrap_or_default();
                if ctors.is_empty() {
                    return None;
                }
                let all_nullary = ctors.iter().all(|c| {
                    self.ctx
                        .constructor_selector_info(c)
                        .map_or(true, |f| f.is_empty())
                });
                if all_nullary {
                    Some(ctors.len())
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    /// both sides are reduced to (default, sorted-stores) and compared.
    /// Falls back to string comparison, then to SAT model when the evaluator
    /// cannot determine equality.
    pub(in crate::executor) fn evaluate_array_equality(
        &self,
        model: &Model,
        eq_term: TermId,
        args: &[TermId],
    ) -> EvalValue {
        // Try semantic comparison via normalized array models.
        if let Some(result) = self.compare_array_models_normalized(model, args[0], args[1]) {
            // BV-backed array interpretations are reconstructed from select/store
            // evidence plus completion defaults. A normalized mismatch is not an
            // extensional witness, so avoid turning partial extraction into a
            // definitive model-validation failure.
            if !result && self.is_bv_backed_array_equality(model, args) {
                return EvalValue::Unknown;
            }
            return EvalValue::Bool(result);
        }

        // Same-symbolic-base store chains (#qf-ax-swap-false-sat): two store
        // chains rooted at the SAME base term can be compared pointwise under
        // the model WITHOUT any interpretation for the base: indices written by
        // either chain compare by evaluated value (with select-through-base for
        // one-sided writes), and every unwritten index trivially agrees. This
        // is what decides the SMT-COMP QF_AX swap/storeinv shapes, where the
        // base array stays a free variable with no `array_model` entry and
        // `normalize_array_to_stores` therefore cannot produce a normal form —
        // previously falling through to the circular SAT-model fallback below,
        // which certified false SAT (40 conflicts in the 2026-07-02 sweep).
        if let Some(result) = self.compare_same_base_store_chains(model, args[0], args[1]) {
            // Only the EQUAL verdict is completion-robust (identical reads
            // under every completion of the free base). A DIFFERENT verdict
            // can hinge on completion-artifact values for otherwise-free
            // index variables (the #8871 shadowed-store shape), so it must
            // not become definitive evidence.
            if result {
                return EvalValue::Bool(true);
            }
        }

        // Definitional resolution (#qf-ax-swap-false-sat completeness
        // residue): an array VARIABLE with no reconstructed `array_model`
        // entry can still be FORCED to a concrete array value by an asserted
        // definitional equality `(= v <array-expr>)` — e.g. deductive-checks's
        // Map/Set `empty()` encodings assert `(= m (const-array d))` and the
        // lazy ArraySolver never materializes an entry for `m` when no select
        // constrains it. Removing the circular SAT-model fallback turned this
        // trivially-true equality into Unknown, downgrading genuinely-SAT
        // counterexample models to Unknown. Resolve both sides through their
        // definitional equalities and compare canonical forms. Only the EQUAL
        // verdict is used: every component of both normal forms evaluated
        // CONCRETELY under the model (`normalize_array_with_definitions`
        // aborts on Unknown components), and each definitional substitution
        // is an asserted equality that holds in every satisfying model, so
        // equal canonical forms mean this equality is true under the model —
        // no SAT-model circularity. A DIFFERENT verdict is deliberately NOT
        // used (mirrors the same-base-chain guard above).
        if let Some(true) = self.compare_array_var_definitions(model, args[0], args[1]) {
            return EvalValue::Bool(true);
        }

        // Fall back to string representation comparison.
        let lhs = self.format_array_term_value(model, args[0]);
        let rhs = self.format_array_term_value(model, args[1]);
        if let (Some(lhs), Some(rhs)) = (lhs, rhs) {
            if lhs == rhs {
                return EvalValue::Bool(true);
            }
            // Strings differ but this is unreliable for arrays (different syntax,
            // same semantics). Don't return false — fall through to SAT.
        }

        // SOUNDNESS (#as-array-ext): function-backed array terms — `(_ as-array
        // f)`, `map[g](...)`, `lambda-array` — do NOT normalize to store maps,
        // so neither `compare_array_models_normalized` nor
        // `format_array_term_value` can decide their equality. The SAT-model
        // fallback below would then launder the SAT solver's free truth value
        // for the equality literal into a "verified" result — circular
        // self-validation. For pure extensionality cases such as
        // `(= (_ as-array f) (_ as-array h))` with `f(3)=10`, `h(3)=20`, that
        // produced a provably-wrong SAT (z3: UNSAT). When either operand is a
        // function-backed array, first try to find a concrete index where the
        // backing functions disagree (definitive Bool(false)); otherwise return
        // Unknown rather than trusting the circular SAT value.
        if self.is_function_backed_array(args[0]) || self.is_function_backed_array(args[1]) {
            if let Some(false) = self.function_backed_array_equality(model, args[0], args[1]) {
                return EvalValue::Bool(false);
            }
            return EvalValue::Unknown;
        }

        // SOUNDNESS (#qf-ax-swap-false-sat): no semantic evidence either way.
        // The previous code fell back to the SAT model's truth value for the
        // equality literal — but the SAT model is the thing being validated, so
        // that laundered the solver's own guess into a "verified" verdict
        // (circular self-validation, the same hole #5499/#6282/#as-array-ext
        // closed elsewhere). Unknown is the only honest answer.
        let _ = eq_term;
        EvalValue::Unknown
    }

    /// Compare two store chains over the SAME symbolic base array, pointwise
    /// under the model, with SYMBOLIC element values.
    ///
    /// Element values resolve to either a concrete model value or a symbolic
    /// base read `BaseRead(base_term, index_key)` — an unconstrained read
    /// through an uninterpreted base array. Two identical `BaseRead`s denote
    /// the same value under EVERY completion of the free base, and two
    /// distinct concrete values differ under every completion, so:
    ///  - `Some(true)` (arrays equal — a definitive violation of an asserted
    ///    disequality) requires every written index to compare EQUAL
    ///    (concrete==concrete or identical base reads);
    ///  - `Some(false)` requires some index with two definitively-different
    ///    (concrete) values;
    ///  - anything indefinite (mixed concrete/symbolic, different reads)
    ///    degrades to `None` — never a verdict.
    /// This decides the SMT-COMP QF_AX swap/storeinv `_np_` shapes, where the
    /// base array is a free variable with NO model interpretation and all
    /// element values are selects that bottom out in reads of that base.
    /// Every returned verdict is forced by the model itself — no SAT-model
    /// circularity.
    pub(in crate::executor) fn compare_same_base_store_chains(
        &self,
        model: &Model,
        a: TermId,
        b: TermId,
    ) -> Option<bool> {
        #[derive(Clone, PartialEq, Eq, Debug)]
        enum SymVal {
            Concrete(String),
            /// A read of an uninterpreted base array at a concrete index key.
            BaseRead(TermId, String),
        }

        // Resolve an element-sorted term to a symbolic value under the model.
        fn resolve_value(
            ex: &Executor,
            model: &Model,
            term: TermId,
            depth: usize,
        ) -> Option<SymVal> {
            if depth == 0 {
                return None;
            }
            let v = ex.evaluate_term(model, term);
            if !matches!(v, EvalValue::Unknown) {
                return Some(SymVal::Concrete(ex.format_eval_value(&v, term)));
            }
            // Unknown: a select bottoming out in an uninterpreted base can
            // still resolve symbolically.
            let TermData::App(sym, args) = ex.ctx.terms.get(term) else {
                return None;
            };
            if sym.name() != "select" || args.len() != 2 {
                return None;
            }
            let (arr0, idx) = (args[0], args[1]);
            let idx_val = ex.evaluate_term(model, idx);
            if matches!(idx_val, EvalValue::Unknown) {
                return None;
            }
            let idx_key = ex.format_eval_value(&idx_val, idx);
            let mut arr = arr0;
            for _ in 0..256_usize {
                match ex.ctx.terms.get(arr) {
                    TermData::App(s, sargs) if s.name() == "store" && sargs.len() == 3 => {
                        let i_val = ex.evaluate_term(model, sargs[1]);
                        if matches!(i_val, EvalValue::Unknown) {
                            return None;
                        }
                        if ex.format_eval_value(&i_val, sargs[1]) == idx_key {
                            return resolve_value(ex, model, sargs[2], depth - 1);
                        }
                        arr = sargs[0];
                    }
                    TermData::App(s, sargs) if s.name() == "const-array" && sargs.len() == 1 => {
                        return resolve_value(ex, model, sargs[0], depth - 1);
                    }
                    _ => {
                        // Opaque base: a concrete model read if one exists,
                        // else a symbolic read of this exact base term.
                        let sel = ex.lookup_array_model(model, arr, &idx_val);
                        if !matches!(sel, EvalValue::Unknown) {
                            return Some(SymVal::Concrete(ex.format_eval_value(&sel, term)));
                        }
                        return Some(SymVal::BaseRead(arr, idx_key));
                    }
                }
            }
            None
        }

        // Read the shared base at a concrete index, symbolically.
        // `sort_ctx_term` is a term of the array's ELEMENT sort (the other
        // side's write-value term) so a concrete read formats with the same
        // sort context as the value it is compared against.
        let base_read = |base: TermId,
                         idx_term: TermId,
                         idx_key: &str,
                         sort_ctx_term: TermId|
         -> Option<SymVal> {
            match self.ctx.terms.get(base) {
                TermData::App(s, sargs) if s.name() == "const-array" && sargs.len() == 1 => {
                    resolve_value(self, model, sargs[0], 64)
                }
                _ => {
                    let idx_val = self.evaluate_term(model, idx_term);
                    if matches!(idx_val, EvalValue::Unknown) {
                        return None;
                    }
                    let sel = self.lookup_array_model(model, base, &idx_val);
                    if !matches!(sel, EvalValue::Unknown) {
                        return Some(SymVal::Concrete(
                            self.format_eval_value(&sel, sort_ctx_term),
                        ));
                    }
                    Some(SymVal::BaseRead(base, idx_key.to_string()))
                }
            }
        };

        // Peel a store chain into (base, outermost-wins write map keyed by the
        // MODEL value of each index).
        struct ChainWrite {
            idx_key: String,
            val: SymVal,
            idx_term: TermId,
            val_term: TermId,
        }
        let peel = |mut cur: TermId| -> Option<(TermId, Vec<ChainWrite>)> {
            let mut writes: Vec<ChainWrite> = Vec::new();
            // Definitional-equality resolution (the storecomm/storeinv `_sf_`
            // shape defines each chain link as `(= a_k (store a_{k-1} i v))`):
            // chase a VAR link to its defining array expression, with a cycle
            // guard, so syntactically-flat chains peel identically to nested
            // ones. Mirrors `evaluate_select_resolving_defs`.
            let mut def_visited: HashSet<TermId> = HashSet::default();
            for _ in 0..256_usize {
                match self.ctx.terms.get(cur) {
                    TermData::App(sym, args) if sym.name() == "store" && args.len() == 3 => {
                        let idx_val = self.evaluate_term(model, args[1]);
                        if matches!(idx_val, EvalValue::Unknown) {
                            return None; // map keys must be concrete
                        }
                        let idx_key = self.format_eval_value(&idx_val, args[1]);
                        let val = resolve_value(self, model, args[2], 64)?;
                        // Outermost store shadows inner writes at the same index.
                        if !writes.iter().any(|w| w.idx_key == idx_key) {
                            writes.push(ChainWrite {
                                idx_key,
                                val,
                                idx_term: args[1],
                                val_term: args[2],
                            });
                        }
                        cur = args[0];
                    }
                    TermData::Var(_, _) => {
                        if !def_visited.insert(cur) {
                            return Some((cur, writes)); // definition cycle: stop here
                        }
                        match self.array_variable_definition_excluding(cur, &def_visited) {
                            Some(def) if def != cur => cur = def,
                            _ => return Some((cur, writes)),
                        }
                    }
                    _ => return Some((cur, writes)),
                }
            }
            None // pathological depth; give up soundly
        };

        let (base_a, writes_a) = peel(a)?;
        let (base_b, writes_b) = peel(b)?;
        if base_a != base_b {
            return None; // different bases: no shared-base shortcut
        }
        if writes_a.is_empty() && writes_b.is_empty() {
            return Some(true);
        }

        // Tri-state pointwise comparison over the union of written indices.
        #[derive(PartialEq)]
        enum Cmp {
            Equal,
            Different,
            Indefinite,
        }
        let cmp = |x: &SymVal, y: &SymVal| -> Cmp {
            match (x, y) {
                (SymVal::Concrete(cx), SymVal::Concrete(cy)) => {
                    if cx == cy {
                        Cmp::Equal
                    } else {
                        Cmp::Different
                    }
                }
                (SymVal::BaseRead(bx, kx), SymVal::BaseRead(by, ky)) => {
                    if bx == by && kx == ky {
                        Cmp::Equal
                    } else {
                        Cmp::Indefinite // distinct free reads: unconstrained
                    }
                }
                _ => Cmp::Indefinite, // concrete vs free read: unconstrained
            }
        };

        let mut all_equal = true;
        for wa in &writes_a {
            let vb = match writes_b.iter().find(|wb| wb.idx_key == wa.idx_key) {
                Some(wb) => wb.val.clone(),
                None => base_read(base_a, wa.idx_term, &wa.idx_key, wa.val_term)?,
            };
            match cmp(&wa.val, &vb) {
                Cmp::Equal => {}
                Cmp::Different => return Some(false),
                Cmp::Indefinite => all_equal = false,
            }
        }
        for wb in &writes_b {
            if writes_a.iter().any(|wa| wa.idx_key == wb.idx_key) {
                continue; // already compared above
            }
            let va = base_read(base_a, wb.idx_term, &wb.idx_key, wb.val_term)?;
            match cmp(&va, &wb.val) {
                Cmp::Equal => {}
                Cmp::Different => return Some(false),
                Cmp::Indefinite => all_equal = false,
            }
        }
        if all_equal {
            Some(true)
        } else {
            None
        }
    }

    /// Resolve a `select` term to an UNCONSTRAINED read of a free base array
    /// under `model`: `(select A i)` where peeling `A`'s store chain (through
    /// definitional equalities, like [`Self::compare_same_base_store_chains`])
    /// at `i`'s concrete model value bottoms out at an opaque array variable
    /// with NO model-committed value at that index.
    ///
    /// Returns `(base_var, index_key)` — a read whose value is a free function
    /// of the base-array completion — or `None` when the read is determined by
    /// a chain write, a const-array default, a committed model entry, or any
    /// index along the chain does not evaluate concretely.
    ///
    /// Used by the strict validation oracle (#qf-ax-swap-sf-false-sat): two
    /// asserted equalities pinning the SAME free base read to two DIFFERENT
    /// concrete values cannot both hold under any completion of the base, so
    /// the candidate model is definitively invalid.
    pub(in crate::executor) fn resolve_free_base_read(
        &self,
        model: &Model,
        select_term: TermId,
    ) -> Option<(TermId, String)> {
        let TermData::App(sym, args) = self.ctx.terms.get(select_term) else {
            return None;
        };
        if sym.name() != "select" || args.len() != 2 {
            return None;
        }
        let idx_val = self.evaluate_term(model, args[1]);
        if matches!(idx_val, EvalValue::Unknown) {
            return None;
        }
        let idx_key = self.format_eval_value(&idx_val, args[1]);
        let mut arr = args[0];
        let mut def_visited: HashSet<TermId> = HashSet::default();
        for _ in 0..256_usize {
            match self.ctx.terms.get(arr) {
                TermData::App(s, sargs) if s.name() == "store" && sargs.len() == 3 => {
                    let i_val = self.evaluate_term(model, sargs[1]);
                    if matches!(i_val, EvalValue::Unknown) {
                        return None; // cannot prove the write does not shadow
                    }
                    if self.format_eval_value(&i_val, sargs[1]) == idx_key {
                        return None; // read determined by this chain write
                    }
                    arr = sargs[0];
                }
                TermData::Var(_, _) => {
                    if !def_visited.insert(arr) {
                        return None; // definitional cycle
                    }
                    match self.array_variable_definition_excluding(arr, &def_visited) {
                        Some(def) if def != arr => arr = def,
                        _ => {
                            // Opaque base: only a read the model does NOT pin
                            // is a free base read.
                            let sel = self.lookup_array_model(model, arr, &idx_val);
                            if !matches!(sel, EvalValue::Unknown) {
                                return None;
                            }
                            return Some((arr, idx_key));
                        }
                    }
                }
                // const-array default / as-array / anything else: determined
                // (or out of scope) — not a free base read.
                _ => return None,
            }
        }
        None
    }

    /// True when `term` denotes an array whose interpretation is given by a
    /// backing function/lambda rather than a store map: `(_ as-array f)`,
    /// `map[g](...)`, or `lambda-array(...)`. These never reduce to a
    /// `(default, stores)` normal form, so the array-model normalizer/printer
    /// cannot decide equality over them.
    pub(in crate::executor) fn is_function_backed_array(&self, term: TermId) -> bool {
        if self.ctx.terms.get_as_array_func(term).is_some() {
            return true;
        }
        matches!(
            self.ctx.terms.get(term),
            TermData::App(sym, _)
                if sym.name() == "lambda-array"
                    || (sym.name().starts_with("map[") && sym.name().ends_with(']'))
        )
    }

    /// True when `term` is a (possibly negated) `=`/`distinct` atom that has at
    /// least one function-backed array operand (`(_ as-array f)`, `map`,
    /// `lambda-array`). Such atoms cannot be soundly delegated back to the array
    /// theory during model validation: the eager `select(as-array f, i) -> f(i)`
    /// rewrite removes any `select` term, so `check_array_equality` never fires
    /// on the backing functions, and the array solver may report quiescent while
    /// the equality is actually inconsistent (#as-array-ext). The validation
    /// pipeline must fail closed (degrade SAT to Unknown) on these instead of
    /// counting the array theory's silence as verification evidence.
    pub(in crate::executor) fn equality_has_function_backed_array_operand(
        &self,
        term: TermId,
    ) -> bool {
        let inner = match self.ctx.terms.get(term) {
            TermData::Not(inner) => *inner,
            TermData::App(sym, args) if sym.name() == "not" && args.len() == 1 => args[0],
            _ => term,
        };
        let TermData::App(sym, args) = self.ctx.terms.get(inner) else {
            return false;
        };
        if !matches!(sym.name(), "=" | "distinct") {
            return false;
        }
        args.iter().any(|&arg| self.is_function_backed_array(arg))
    }

    /// Attempt to decide equality of two array terms where at least one is an
    /// `(_ as-array f)` term, by probing the backing functions at concrete
    /// indices that already appear as function applications in the term store.
    ///
    /// Returns `Some(false)` only when a concrete index is found at which the
    /// two arrays provably read different values under the model — a definitive
    /// extensionality violation. Returns `None` when no such witness is found
    /// (the caller must then fail closed to Unknown). Never returns
    /// `Some(true)`: a finite probe cannot prove agreement at all indices.
    fn function_backed_array_equality(
        &self,
        model: &Model,
        lhs: TermId,
        rhs: TermId,
    ) -> Option<bool> {
        // Collect, for each side, the set of concrete index values reachable as
        // existing reads (either `f(i)` for an as-array[f] term, or
        // `select(arr, i)`). Then probe shared indices for a disagreement.
        let read_at = |arr: TermId, idx: TermId| -> EvalValue {
            if let Some(func_name) = self.ctx.terms.get_as_array_func(arr) {
                // select(as-array[f], i) = f(i): look up an existing f(i) term.
                if let Some(app) = self
                    .ctx
                    .terms
                    .find_app(&ay_core::Symbol::named(func_name), &[idx])
                {
                    return self.evaluate_term(model, app);
                }
                return EvalValue::Unknown;
            }
            // Otherwise treat as a generic array term: select(arr, i).
            self.evaluate_select(model, arr, idx)
        };

        // Gather candidate index terms from function applications of the
        // backing functions: scan the term store for `f(i)` / `h(i)` apps whose
        // symbol matches an as-array backing function and collect their single
        // argument as a probe index.
        let backing_names: Vec<String> = [lhs, rhs]
            .iter()
            .filter_map(|&arr| self.ctx.terms.get_as_array_func(arr).map(str::to_string))
            .collect();
        if backing_names.is_empty() {
            return None;
        }
        let mut candidate_indices: Vec<TermId> = Vec::new();
        for term_id in self.ctx.terms.term_ids() {
            if let TermData::App(sym, app_args) = self.ctx.terms.get(term_id) {
                if app_args.len() == 1 && backing_names.iter().any(|n| n == sym.name()) {
                    let idx = app_args[0];
                    if !candidate_indices.contains(&idx) {
                        candidate_indices.push(idx);
                    }
                }
            }
        }

        for idx in candidate_indices {
            let lv = read_at(lhs, idx);
            let rv = read_at(rhs, idx);
            if matches!(lv, EvalValue::Unknown) || matches!(rv, EvalValue::Unknown) {
                continue;
            }
            if matches!(Self::eval_values_equal_exact(&lv, &rv), Some(false)) {
                return Some(false);
            }
        }
        None
    }

    fn is_bv_backed_array_equality(&self, model: &Model, args: &[TermId]) -> bool {
        model.bv_model.is_some()
            && args
                .iter()
                .any(|&term| Self::sort_contains_bitvec(self.ctx.terms.sort(term)))
    }

    fn sort_contains_bitvec(sort: &Sort) -> bool {
        match sort {
            Sort::BitVec(_) => true,
            Sort::Array(array_sort) => {
                Self::sort_contains_bitvec(&array_sort.index_sort)
                    || Self::sort_contains_bitvec(&array_sort.element_sort)
            }
            Sort::Seq(element_sort) => Self::sort_contains_bitvec(element_sort),
            Sort::Datatype(datatype_sort) => datatype_sort.constructors.iter().any(|constructor| {
                constructor
                    .fields
                    .iter()
                    .any(|field| Self::sort_contains_bitvec(&field.sort))
            }),
            _ => false,
        }
    }

    /// Normalize an array term to (default_value, sorted store map) for semantic comparison.
    ///
    /// Returns None if the array cannot be fully normalized.
    fn normalize_array_to_stores(&self, model: &Model, term_id: TermId) -> Option<NormalizedArray> {
        stacker::maybe_grow(EVAL_STACK_RED_ZONE, EVAL_STACK_SIZE, || {
            // A dropped conflicting read makes the interpretation partial at
            // an unknown cell.  Neither an attached default nor a surrounding
            // store/alias can turn that partial witness into an exact normal
            // form.  Completion propagates this marker through hard
            // dependencies, while structural store recursion below catches a
            // conflicted base directly.
            if model
                .array_model
                .as_ref()
                .is_some_and(|arrays| arrays.read_conflicted.contains(&term_id))
            {
                return None;
            }
            match self.ctx.terms.get(term_id) {
                TermData::Var(_, _) => {
                    let array_model = model.array_model.as_ref()?;
                    let interp = array_model.array_values.get(&term_id)?;
                    let mut stores = unique_authoritative_stores(&interp.stores);
                    stores.sort_by(|a, b| a.0.cmp(&b.0));
                    Some((interp.default.clone(), stores))
                }
                TermData::App(sym, args) if sym.name() == "store" && args.len() == 3 => {
                    let mut base = self.normalize_array_to_stores(model, args[0])?;
                    let index_val = self.evaluate_term(model, args[1]);
                    let value_val = self.evaluate_term(model, args[2]);
                    // SOUNDNESS (#qf-ax-swap-false-sat): an Unknown index or
                    // value formats to the SORT DEFAULT string, so two
                    // DIFFERENT unknown indices collide onto one map key and
                    // an unknown value masquerades as a concrete one —
                    // corrupting the normal form in either direction (false
                    // equal AND false different). No normal form is the only
                    // sound answer.
                    if matches!(index_val, EvalValue::Unknown)
                        || matches!(value_val, EvalValue::Unknown)
                    {
                        return None;
                    }
                    let index_str = self.format_eval_value(&index_val, args[1]);
                    let value_str = self.format_eval_value(&value_val, args[2]);

                    // Overwrite existing entry at this index if present.
                    if let Some(existing) = base.1.iter_mut().find(|(k, _)| *k == index_str) {
                        existing.1 = value_str;
                    } else {
                        base.1.push((index_str, value_str));
                        base.1.sort_by(|a, b| a.0.cmp(&b.0));
                    }
                    Some(base)
                }
                TermData::App(sym, args) if sym.name() == "const-array" && args.len() == 1 => {
                    let default_val = self.evaluate_term(model, args[0]);
                    // SOUNDNESS (#qf-ax-swap-false-sat): same Unknown-collapse
                    // hazard as the store case above.
                    if matches!(default_val, EvalValue::Unknown) {
                        return None;
                    }
                    let default_str = self.format_eval_value(&default_val, args[0]);
                    Some((Some(default_str), Vec::new()))
                }
                TermData::Let(bindings, body) if bindings.is_empty() => {
                    self.normalize_array_to_stores(model, *body)
                }
                TermData::Let(_, _) => None,
                TermData::Ite(cond, then_br, else_br) => match self.evaluate_term(model, *cond) {
                    EvalValue::Bool(true) => self.normalize_array_to_stores(model, *then_br),
                    EvalValue::Bool(false) => self.normalize_array_to_stores(model, *else_br),
                    _ => None,
                },
                // NOTE (#seq-array-uf-def, adversarial A/B finding): opaque
                // array-valued UF applications are deliberately NOT normalized
                // here from `array_model.array_values`. Those app-keyed
                // interpretations are reconstructed from PARTIAL select/store
                // evidence, and treating them as normal forms lets
                // `compare_array_models_normalized` hand out definitive
                // (incl. FALSE) verdicts that are not extensional ground
                // truth — live-measured on verification-consumer index_range, this flipped
                // the base solve into a pathological refutation/refinement
                // loop (248s hard-timeout; A/B: stores-arm alone reproduces,
                // removing it restores the pass). Opaque apps resolve ONLY
                // through the asserted-definitional path in
                // `normalize_array_with_definitions`, whose consumer uses the
                // EQUAL verdict alone.
                _ => None,
            }
        })
    }

    /// Whether `term` is an OPAQUE array-valued function application: an
    /// `App` of array sort whose symbol is NOT an interpreted array
    /// constructor/reader (`store`/`const-array`/`select`) and NOT
    /// function-backed (`as-array`/`map[..]`/`lambda-array`). The verification-consumer
    /// Seq-view carrier `(seq_array v)` is the motivating shape
    /// (#seq-array-uf-def).
    pub(in crate::executor) fn is_opaque_array_valued_app(&self, term: TermId) -> bool {
        if !matches!(self.ctx.terms.sort(term), Sort::Array(_)) {
            return false;
        }
        if self.is_function_backed_array(term) {
            return false;
        }
        match self.ctx.terms.get(term) {
            TermData::App(sym, _) => !matches!(sym.name(), "store" | "const-array" | "select"),
            _ => false,
        }
    }

    /// Compare two array terms by normalizing both to (default, sorted-stores)
    /// and checking structural equality.
    ///
    /// Returns Some(true) if provably equal, Some(false) if provably different,
    /// None if comparison cannot be determined.
    pub(in crate::executor) fn compare_array_models_normalized(
        &self,
        model: &Model,
        a: TermId,
        b: TermId,
    ) -> Option<bool> {
        let norm_a = self.normalize_array_to_stores(model, a)?;
        let norm_b = self.normalize_array_to_stores(model, b)?;
        Some(Self::normalized_arrays_equal(&norm_a, &norm_b))
    }

    /// Structural equality of two normalized arrays, treating any `(idx -> val)`
    /// store whose `val` equals that array's OWN default as REDUNDANT (it does
    /// not change the array's value at `idx`).
    ///
    /// Two reconstructions of the *same* array can differ only in such redundant
    /// stores when one side's base interpretation dropped stores equal to its
    /// already-committed default while the other side re-materializes that
    /// index through a `store` overlay. The
    /// `qf_ax_diamond_equality_sat` model is the canonical case: `b =
    /// store(a,i,v)` and `c = store(a,j,w)` both reduce to `a` once `v = a[i]`,
    /// `w = a[j]`, but `c`'s overlay re-adds `(j -> w)` which equals `a`'s
    /// committed default, so a raw `==` reported the two as different and the
    /// strict arrays oracle spuriously rejected a valid SAT model.
    ///
    /// Soundness: dropping `(idx -> val)` with `val == default` is EXACT — the
    /// array maps `idx` to `default` with or without the store — so the
    /// canonical form denotes the same array function. Genuinely-distinct arrays
    /// keep distinct canonical forms (a differing concrete store, or a differing
    /// default over the uncovered index space), so this never reports two
    /// different arrays as equal; it only removes the redundant-store artifact.
    fn normalized_arrays_equal(a: &NormalizedArray, b: &NormalizedArray) -> bool {
        fn canonicalize((default, stores): &NormalizedArray) -> NormalizedArray {
            let mut canon: Vec<(String, String)> = match default {
                Some(d) => stores.iter().filter(|(_, v)| v != d).cloned().collect(),
                None => stores.clone(),
            };
            canon.sort();
            (default.clone(), canon)
        }
        canonicalize(a) == canonicalize(b)
    }

    /// Compare two array *variables* by normalizing both, resolving each through
    /// its definitional equality in the assertion set when it has no
    /// reconstructed `array_model` entry.
    ///
    /// Returns Some(true) if provably equal, Some(false) if provably different,
    /// None if either side cannot be fully normalized.
    ///
    /// Soundness: a definitional equality `(= v <array-expr>)` is an assertion
    /// that holds in every satisfying model, so substituting `v` by
    /// `<array-expr>` preserves the variable's value under any model of the
    /// formula. We only ever return `Some(_)` when BOTH variables resolve to a
    /// fully-normalized form, so partial reconstruction never produces a
    /// spurious refutation. In QF_ABV with Int indices the const-array
    /// interpretation of `f`/`g` lives only in the assertions (`f = const(1)`,
    /// `g = const(2)`), so this resolution is what lets extensionality refute
    /// `(= f g)` (#8729).
    pub(in crate::executor) fn compare_array_var_definitions(
        &self,
        model: &Model,
        a: TermId,
        b: TermId,
    ) -> Option<bool> {
        let mut visited_a = HashSet::default();
        let mut visited_b = HashSet::default();
        let norm_a = self.normalize_array_with_definitions(model, a, &mut visited_a)?;
        let norm_b = self.normalize_array_with_definitions(model, b, &mut visited_b)?;
        Some(Self::normalized_arrays_equal(&norm_a, &norm_b))
    }

    /// Like [`normalize_array_to_stores`], but for an array *variable* with no
    /// `array_model` entry, fall back to its definitional equality
    /// `(= v <array-expr>)` (or `(= <array-expr> v)`) from the assertion set and
    /// normalize that expression instead.
    ///
    /// `visited` guards against definitional cycles (e.g. `(= f g) (= g f)` or a
    /// self-referential `(= f (store f ...))`): a variable already on the
    /// resolution path yields `None` rather than recursing forever.
    fn normalize_array_with_definitions(
        &self,
        model: &Model,
        term_id: TermId,
        visited: &mut HashSet<TermId>,
    ) -> Option<NormalizedArray> {
        stacker::maybe_grow(EVAL_STACK_RED_ZONE, EVAL_STACK_SIZE, || {
            match self.ctx.terms.get(term_id) {
                TermData::Var(_, _) => {
                    // Prefer a reconstructed array-model interpretation when present.
                    if let Some(norm) = self.normalize_array_to_stores(model, term_id) {
                        return Some(norm);
                    }
                    // Otherwise resolve through a definitional equality in the
                    // assertions. Mark this variable visited to break cycles.
                    if !visited.insert(term_id) {
                        return None;
                    }
                    let definition = self.array_variable_definition(term_id)?;
                    self.normalize_array_with_definitions(model, definition, visited)
                }
                TermData::App(sym, args) if sym.name() == "store" && args.len() == 3 => {
                    let mut base =
                        self.normalize_array_with_definitions(model, args[0], visited)?;
                    let index_val = self.evaluate_term(model, args[1]);
                    let value_val = self.evaluate_term(model, args[2]);
                    // SOUNDNESS (#qf-ax-swap-false-sat): an Unknown index or
                    // value has no concrete printed form, so it cannot key or
                    // fill a normal-form entry — no normal form is the only
                    // sound answer (mirrors `normalize_array_to_stores`).
                    if matches!(index_val, EvalValue::Unknown)
                        || matches!(value_val, EvalValue::Unknown)
                    {
                        return None;
                    }
                    let index_str = self.format_eval_value(&index_val, args[1]);
                    let value_str = self.format_eval_value(&value_val, args[2]);

                    if let Some(existing) = base.1.iter_mut().find(|(k, _)| *k == index_str) {
                        existing.1 = value_str;
                    } else {
                        base.1.push((index_str, value_str));
                        base.1.sort_by(|a, b| a.0.cmp(&b.0));
                    }
                    Some(base)
                }
                TermData::App(sym, args) if sym.name() == "const-array" && args.len() == 1 => {
                    let default_val = self.evaluate_term(model, args[0]);
                    // SOUNDNESS (#qf-ax-swap-false-sat): same Unknown-collapse
                    // hazard as the store case above.
                    if matches!(default_val, EvalValue::Unknown) {
                        return None;
                    }
                    let default_str = self.format_eval_value(&default_val, args[0]);
                    Some((Some(default_str), Vec::new()))
                }
                TermData::Let(bindings, body) if bindings.is_empty() => {
                    self.normalize_array_with_definitions(model, *body, visited)
                }
                TermData::Let(_, _) => None,
                TermData::Ite(cond, then_br, else_br) => match self.evaluate_term(model, *cond) {
                    EvalValue::Bool(true) => {
                        self.normalize_array_with_definitions(model, *then_br, visited)
                    }
                    EvalValue::Bool(false) => {
                        self.normalize_array_with_definitions(model, *else_br, visited)
                    }
                    _ => None,
                },
                // (#seq-array-uf-def) An OPAQUE array-valued UF application —
                // verification-consumer's Seq-view carrier `(seq_array v)` is the pinned
                // shape — resolves exactly like a bare array variable: prefer a
                // reconstructed interpretation, else fall back to a
                // definitional equality `(= (seq_array v) <array-expr>)` from
                // the assertion/assumption set (the verification-consumer base-consistency
                // assumption `(= (const-array 0) (seq_array v))` previously
                // evaluated to Unknown here and degraded a genuine sat to
                // unknown). Same visited-set cycle guard as the Var arm, PLUS a
                // CONGRUENCE guard (`opaque_app_congruent_definitions_agree`):
                // if any definitional equality binds the SAME function symbol
                // at argument values this model cannot distinguish from ours to
                // a DIFFERENT concrete array, resolution refuses (None) — a
                // per-assertion resolution there could validate a
                // congruence-inconsistent completion (e.g. `v = w`,
                // `seq_array(v) = const-array 0`, `seq_array(w) = const-array
                // 1`, jointly UNSAT), which would be a wrong-SAT vector. The
                // refusal degrades to Unknown, today's behaviour.
                TermData::App(_, _) if self.is_opaque_array_valued_app(term_id) => {
                    if let Some(norm) = self.normalize_array_to_stores(model, term_id) {
                        return Some(norm);
                    }
                    if !visited.insert(term_id) {
                        return None;
                    }
                    let definition = self.array_variable_definition(term_id)?;
                    let norm = self.normalize_array_with_definitions(model, definition, visited)?;
                    if !self.opaque_app_congruent_definitions_agree(model, term_id, &norm, visited)
                    {
                        return None;
                    }
                    Some(norm)
                }
                _ => None,
            }
        })
    }

    /// Congruence guard for opaque array-valued UF app resolution
    /// (#seq-array-uf-def).
    ///
    /// `app` was resolved to `norm` through one of its asserted definitional
    /// equalities. For the resolution to be admissible, every OTHER asserted
    /// definitional equality that binds an application of the SAME function
    /// symbol (same name, arity, and array sort — including further
    /// definitions of `app` itself) at argument values this model cannot
    /// PROVABLY distinguish from `app`'s must normalize to the SAME concrete
    /// array. Otherwise the definitions are (potentially) congruence-
    /// inconsistent and resolution must refuse, degrading validation to
    /// Unknown (fail-closed).
    ///
    /// "Provably distinguish" is deliberately conservative: only concrete
    /// scalar/element value pairs of the same kind count as different;
    /// Unknown or mixed-kind argument evaluations are treated as possibly
    /// equal. A candidate whose definition cannot be normalized concretely
    /// contributes no acceptance evidence here — but it also cannot make this
    /// model validate: its own defining assertion still evaluates through
    /// this same resolution path (Unknown at worst), so the model degrades
    /// there instead.
    fn opaque_app_congruent_definitions_agree(
        &self,
        model: &Model,
        app: TermId,
        norm: &NormalizedArray,
        visited: &HashSet<TermId>,
    ) -> bool {
        let (app_name, app_args) = match self.ctx.terms.get(app) {
            TermData::App(sym, args) => (sym.name().to_string(), args.clone()),
            _ => return true,
        };
        let app_sort = self.ctx.terms.sort(app).clone();
        let candidates: Vec<(TermId, TermId)> = self
            .definitional_constraint_terms()
            .filter_map(|assertion| {
                let TermData::App(sym, args) = self.ctx.terms.get(assertion) else {
                    return None;
                };
                if sym.name() != "=" || args.len() != 2 {
                    return None;
                }
                for (side, other) in [(args[0], args[1]), (args[1], args[0])] {
                    let TermData::App(s2, args2) = self.ctx.terms.get(side) else {
                        continue;
                    };
                    if s2.name() == app_name
                        && args2.len() == app_args.len()
                        && *self.ctx.terms.sort(side) == app_sort
                        && self.is_opaque_array_valued_app(side)
                        && self.is_array_definition_shape(other)
                        && !(side == app && other == side)
                    {
                        return Some((side, other));
                    }
                }
                None
            })
            .collect();
        for (side, other) in candidates {
            // A same-symbol app at PROVABLY different argument values cannot
            // be congruent with ours — no constraint from it.
            if side != app {
                let args2 = match self.ctx.terms.get(side) {
                    TermData::App(_, a) => a.clone(),
                    _ => continue,
                };
                let provably_different = app_args.iter().zip(args2.iter()).any(|(&a, &b)| {
                    let (va, vb) = (self.evaluate_term(model, a), self.evaluate_term(model, b));
                    match (&va, &vb) {
                        (EvalValue::Unknown, _) | (_, EvalValue::Unknown) => false,
                        _ => {
                            // Same-kind concrete values that differ are a
                            // definitive distinction under THIS model.
                            std::mem::discriminant(&va) == std::mem::discriminant(&vb) && va != vb
                        }
                    }
                });
                if provably_different {
                    continue;
                }
            }
            // Possibly congruent: its definition, when concretely
            // normalizable, must agree with ours.
            let mut probe_visited = visited.clone();
            probe_visited.insert(side);
            let Some(other_norm) =
                self.normalize_array_with_definitions(model, other, &mut probe_visited)
            else {
                continue;
            };
            if !Self::normalized_arrays_equal(norm, &other_norm) {
                return false;
            }
        }
        true
    }

    /// The hard constraints of the CURRENT query: the assertion set plus the
    /// active `check-sat-assuming` assumptions, if any.
    ///
    /// With `produce-unsat-cores`, named assertions are temporarily REMOVED
    /// from `ctx.assertions` and redirected through `check_sat_assuming` as
    /// assumptions (MiniSat-style core tracking), so a definitional equality
    /// `(= v <array-expr>)` that the user wrote as a named assertion lives in
    /// `last_assumptions` during that solve. Both sets are equally forced:
    /// any SAT answer for the current query certifies satisfiability of
    /// assertions AND assumptions together, so a definitional equality from
    /// either set holds in every model of the current query.
    fn definitional_constraint_terms(&self) -> impl Iterator<Item = TermId> + '_ {
        self.ctx
            .assertions
            .iter()
            .copied()
            .chain(self.last_assumptions.iter().flatten().copied())
    }

    /// Find a definitional equality `(= v rhs)` or `(= lhs v)` for the array
    /// variable `v` among the assertions (and active assumptions) and return
    /// the OTHER side.
    ///
    /// Only equalities whose other side is an array-constructor expression
    /// (`const-array`/`store`) or another array variable are eligible — those
    /// are the shapes `normalize_array_with_definitions` can reduce. Returns the
    /// first such definition; if a variable has several, any one is sound
    /// because all asserted equalities must hold simultaneously.
    pub(super) fn array_variable_definition(&self, var: TermId) -> Option<TermId> {
        for assertion in self.definitional_constraint_terms() {
            let TermData::App(sym, args) = self.ctx.terms.get(assertion) else {
                continue;
            };
            if sym.name() != "=" || args.len() != 2 {
                continue;
            }
            let (lhs, rhs) = (args[0], args[1]);
            let other = if lhs == var {
                rhs
            } else if rhs == var {
                lhs
            } else {
                continue;
            };
            if self.is_array_definition_shape(other) {
                return Some(other);
            }
        }
        None
    }

    /// Like [`Self::array_variable_definition`], but skips a candidate
    /// definition that is itself an array variable already present in
    /// `def_visited`.
    ///
    /// `array_variable_definition` reads an equality `(= a b)` in both
    /// directions, so a single mutual equality between two array variables is a
    /// definitional cycle (`a -> b -> a`). Excluding already-chased variables
    /// breaks that cycle while still allowing a concrete (`store` /
    /// `const-array`) definition of the same variable to be discovered.
    pub(super) fn array_variable_definition_excluding(
        &self,
        var: TermId,
        def_visited: &HashSet<TermId>,
    ) -> Option<TermId> {
        for assertion in self.definitional_constraint_terms() {
            let TermData::App(sym, args) = self.ctx.terms.get(assertion) else {
                continue;
            };
            if sym.name() != "=" || args.len() != 2 {
                continue;
            }
            let (lhs, rhs) = (args[0], args[1]);
            let other = if lhs == var {
                rhs
            } else if rhs == var {
                lhs
            } else {
                continue;
            };
            // Skip an array-variable definition we have already chased: that is
            // the back-edge of a definitional cycle.
            if matches!(self.ctx.terms.get(other), TermData::Var(_, _))
                && def_visited.contains(&other)
            {
                continue;
            }
            if self.is_array_definition_shape(other) {
                return Some(other);
            }
        }
        None
    }

    /// Return the sole non-variable constructor definition of `var`, or
    /// `None` when no such definition exists or competing definitions exist.
    ///
    /// A reconstructed model entry is authoritative when assertions give the
    /// same variable multiple distinct store/const/ite definitions.  Picking
    /// one arbitrary equality in that case can make model completion oscillate
    /// instead of failing closed.  A unique constructor definition, however,
    /// is safe to use ahead of a completion fallback entry.
    fn unique_array_constructor_definition_excluding(
        &self,
        var: TermId,
        def_visited: &HashSet<TermId>,
    ) -> Option<TermId> {
        let mut unique = None;
        for assertion in self.definitional_constraint_terms() {
            let TermData::App(sym, args) = self.ctx.terms.get(assertion) else {
                continue;
            };
            if sym.name() != "=" || args.len() != 2 {
                continue;
            }
            let (lhs, rhs) = (args[0], args[1]);
            let other = if lhs == var {
                rhs
            } else if rhs == var {
                lhs
            } else {
                continue;
            };
            if matches!(self.ctx.terms.get(other), TermData::Var(_, _)) {
                if def_visited.contains(&other) {
                    continue;
                }
                // Only explicit constructor definitions can supersede an
                // already materialized model entry.
                continue;
            }
            if !self.is_array_definition_shape(other) {
                continue;
            }
            match unique {
                Some(existing) if existing != other => return None,
                Some(_) => {}
                None => unique = Some(other),
            }
        }
        unique
    }

    /// Whether `term` is a shape `normalize_array_with_definitions` can reduce
    /// to a normalized array: an array constructor (`const-array`/`store`), an
    /// array variable, or `let`/`ite` wrapping one.
    fn is_array_definition_shape(&self, term: TermId) -> bool {
        match self.ctx.terms.get(term) {
            TermData::Var(_, _) => matches!(self.ctx.terms.sort(term), Sort::Array(_)),
            TermData::App(sym, args) => {
                matches!((sym.name(), args.len()), ("const-array", 1) | ("store", 3))
            }
            TermData::Let(bindings, body) => {
                bindings.is_empty() && self.is_array_definition_shape(*body)
            }
            TermData::Ite(_, then_br, else_br) => {
                self.is_array_definition_shape(*then_br) && self.is_array_definition_shape(*else_br)
            }
            _ => false,
        }
    }

    /// Return a concrete Int witness index where two array terms differ.
    ///
    /// AUFLIA benchmark families often encode extensionality witnesses as an
    /// uninterpreted `sk(A, B)` index and assert
    /// `(not (= (select A (sk A B)) (select B (sk A B))))`. EUF can make the
    /// disequality Boolean true while the model printer/evaluator still needs a
    /// concrete Int for `sk(A, B)`. Use the reconstructed array interpretations
    /// to choose an existing store index where the element values differ.
    pub(super) fn array_extensional_witness_index(
        &self,
        model: &Model,
        lhs: TermId,
        rhs: TermId,
    ) -> Option<EvalValue> {
        let Sort::Array(lhs_array_sort) = self.ctx.terms.sort(lhs) else {
            return None;
        };
        if !matches!(lhs_array_sort.index_sort, Sort::Int) {
            return None;
        }
        let Sort::Array(rhs_array_sort) = self.ctx.terms.sort(rhs) else {
            return None;
        };
        if rhs_array_sort.index_sort != lhs_array_sort.index_sort {
            return None;
        }

        let lhs_norm = self.normalize_array_to_stores(model, lhs)?;
        let rhs_norm = self.normalize_array_to_stores(model, rhs)?;
        let value_at = |norm: &NormalizedArray, key: &str| -> Option<String> {
            norm.1
                .iter()
                .find_map(|(idx, val)| (idx == key).then(|| val.clone()))
                .or_else(|| norm.0.clone())
        };

        let mut candidate_keys = Vec::new();
        for (idx, _) in lhs_norm.1.iter().chain(rhs_norm.1.iter()) {
            if !candidate_keys.iter().any(|seen| seen == idx) {
                candidate_keys.push(idx.clone());
            }
        }

        for key in candidate_keys {
            let lhs_value = value_at(&lhs_norm, &key)?;
            let rhs_value = value_at(&rhs_norm, &key)?;
            if lhs_value == rhs_value {
                continue;
            }
            let parsed = self.parse_model_value_string(&key, &Some(Sort::Int));
            if !matches!(parsed, EvalValue::Unknown) {
                return Some(parsed);
            }
        }

        None
    }
}

#[cfg(test)]
mod array_store_normalization_tests {
    use super::{unique_authoritative_stores, EvalValue, Executor};

    #[test]
    fn duplicate_indices_keep_only_authoritative_newest_entry() {
        let stores = vec![
            ("7".to_string(), "0".to_string()),
            ("7".to_string(), "5".to_string()),
            ("8".to_string(), "3".to_string()),
        ];
        assert_eq!(
            unique_authoritative_stores(&stores),
            vec![
                ("7".to_string(), "0".to_string()),
                ("8".to_string(), "3".to_string()),
            ]
        );
    }

    #[test]
    fn array_value_equality_keeps_nested_unknown_tristate() {
        let undecided = EvalValue::Seq(vec![EvalValue::Unknown]);
        let concrete = EvalValue::Seq(vec![EvalValue::String("x".to_string())]);
        assert_eq!(
            Executor::eval_values_equal_exact(&undecided, &concrete),
            None,
            "an unresolved sequence element is neither equality nor disequality evidence"
        );
        assert_eq!(
            Executor::eval_values_equal_exact(
                &EvalValue::Seq(vec![EvalValue::String("x".to_string())]),
                &concrete,
            ),
            Some(true)
        );
        assert_eq!(
            Executor::eval_values_equal_exact(
                &EvalValue::Seq(vec![EvalValue::String("y".to_string())]),
                &concrete,
            ),
            Some(false)
        );
    }
}
