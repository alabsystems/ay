// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Interpretations of store chains, constant arrays and substitution targets
//! under one BV/Bool assignment. Every entry is model data only; the complete
//! original-root validation is unchanged.

use super::*;

impl Executor {
    /// Build the interpretation of a `(const-array default)` term: a default
    /// value (resolved through `bv_model`, with the array reads and
    /// uninterpreted applications it mentions read from the model itself) and
    /// no stores. Returns `None` for non-BitVec-indexed or unsupported element
    /// sorts.
    pub(super) fn const_array_interp(
        terms: &TermStore,
        bv_model: &BvModel,
        const_array_term: TermId,
        default_term: TermId,
        array_model: &mut ArrayModel,
    ) -> Option<ArrayInterpretation> {
        let Sort::Array(arr_sort) = terms.sort(const_array_term) else {
            return None;
        };
        if !matches!(arr_sort.index_sort, Sort::BitVec(_)) {
            return None;
        }
        let TermData::App(ay_core::term::Symbol::Named(name), args) = terms.get(const_array_term)
        else {
            return None;
        };
        if name.as_ref() != "const-array"
            || args.as_slice() != [default_term]
            || terms.sort(default_term) != &arr_sort.element_sort
        {
            return None;
        }
        let mut memo = BvEvalMemo::default();
        Self::seed_definition_operand_leaves(terms, bv_model, default_term, array_model, &mut memo);
        let default =
            Self::store_chain_element_value(terms, bv_model, default_term, array_model, &mut memo)?;
        Some(ArrayInterpretation {
            index_sort: Some(arr_sort.index_sort.clone()),
            element_sort: Some(arr_sort.element_sort.clone()),
            default: Some(default),
            ..Default::default()
        })
    }

    /// Add array-model entries for array variables eliminated by variable substitution.
    ///
    /// QF_ABV preprocessing can rewrite `(= arr2 arr1)` by substituting
    /// `arr2 -> arr1`. The SAT/BV model is then built over the post-substitution
    /// terms, while validation runs over restored original assertions. Copying
    /// the resolved array interpretation back to substituted variables prevents
    /// strict validation from treating model-completion defaults as concrete
    /// counterexamples.
    ///
    /// The substitution *target* `to_term` is frequently a `store` chain rather
    /// than another array variable — e.g. `(= a2 (store a 0 5))` and `(= b a2)`
    /// both collapse to `b, a2 -> store(a, 0, 5)`. The store term has no
    /// `array_values` entry of its own (only variables that appear in select
    /// terms or in explicit `(= var store)` assertions get one), so a flat
    /// `array_values[to_term]` lookup misses it and the eliminated variables
    /// keep whatever stale select-derived entry their now-orphaned `select`
    /// terms produced (unconstrained bits → garbage). Because both `b` and `a2`
    /// alias the *same* store term, that left two asserted-equal arrays with
    /// divergent interpretations, which the strict array oracle then refuted —
    /// demoting a genuine SAT to `unknown`. Building the store-chain
    /// interpretation for such targets gives every variable aliasing the same
    /// target one identical, consistent interpretation. (#array-subst-store-target)
    pub(in crate::executor) fn populate_array_models_from_substitutions(
        terms: &TermStore,
        bv_model: &BvModel,
        substitutions: &[(TermId, TermId)],
        array_model: &mut ArrayModel,
    ) {
        if substitutions.is_empty() {
            return;
        }

        // Keep unresolved definitions separate from protected extraction
        // failures. Both withhold the old decoupled entry, but a late typed
        // recovery may discharge only its own birth-stamped definition.
        for &(from, to) in substitutions {
            if matches!(terms.sort(from), Sort::Array(_)) {
                if array_model.read_conflicted.contains(&to) {
                    array_model.read_conflicted.insert(from);
                } else {
                    array_model.defer_array_definition(terms, from, to);
                }
            }
        }

        // Fixpoint over the chain length so transitive substitutions
        // (`a2 -> b`, `b -> store(...)`) all resolve to the final target.
        for _ in 0..substitutions.len() {
            for &(from_var, to_term) in substitutions {
                if !matches!(terms.sort(from_var), Sort::Array(_))
                    || array_model.read_conflicted.contains(&from_var)
                {
                    continue;
                }
                if terms.sort(from_var) != terms.sort(to_term) {
                    continue;
                }
                if array_model.read_conflicted.contains(&to_term) {
                    array_model.read_conflicted.insert(from_var);
                    continue;
                }
                let Some(interp) =
                    Self::resolve_substitution_target_interp(terms, bv_model, to_term, array_model)
                else {
                    continue;
                };
                if array_model.discharge_array_definition(terms, from_var, to_term) {
                    array_model.array_values.insert(from_var, interp);
                }
            }
        }
    }

    /// Resolve the array interpretation of a substitution *target* term.
    ///
    /// Compound targets are reconstructed, never read from potentially dead
    /// bit-blast caches. A primitive free base may receive one explicit model
    /// choice, published under that same variable before any alias uses it.
    pub(super) fn resolve_substitution_target_interp(
        terms: &TermStore,
        bv_model: &BvModel,
        to_term: TermId,
        array_model: &mut ArrayModel,
    ) -> Option<ArrayInterpretation> {
        if array_model.is_withheld(&to_term) {
            return None;
        }
        match terms.get(to_term) {
            TermData::Var(_, _) => {
                let Sort::Array(sort) = terms.sort(to_term) else {
                    return None;
                };
                if !matches!(sort.index_sort, Sort::BitVec(_)) {
                    return None;
                }
                if let Some(interp) = array_model.array_values.get(&to_term) {
                    return (interp.index_sort.as_ref() == Some(&sort.index_sort)
                        && interp.element_sort.as_ref() == Some(&sort.element_sort)
                        && interp.default.is_some())
                    .then(|| interp.clone());
                }
                let default =
                    Self::select_scan_default(terms, bv_model, to_term, &sort.element_sort)?;
                let interp = ArrayInterpretation {
                    index_sort: Some(sort.index_sort.clone()),
                    element_sort: Some(sort.element_sort.clone()),
                    default: Some(default),
                    stores: Vec::new(),
                };
                array_model.array_values.insert(to_term, interp.clone());
                Some(interp)
            }
            TermData::App(sym, args) if sym.name() == "const-array" && args.len() == 1 => {
                Self::const_array_interp(terms, bv_model, to_term, args[0], array_model)
            }
            TermData::App(sym, _) if sym.name() == "store" => {
                Self::build_store_chain_interp(terms, bv_model, to_term, array_model)
            }
            TermData::App(sym, args) if sym.name() == "select" && args.len() == 2 => {
                Self::nested_read_target_interp(terms, bv_model, to_term, array_model)
            }
            _ => Self::published_field_target_interp(terms, to_term, array_model),
        }
    }

    /// Resolve the model value of a store-chain index or value operand.
    ///
    /// Constants are literal and compound terms are recomputed from their
    /// leaves. Cached interior-node bits can be unconstrained after substitution
    /// and must never become array cells (#store-chain-dead-node). The shared
    /// memo belongs to this immutable BV/Bool assignment, not an empty-Bool view.
    pub(super) fn store_chain_operand_value(
        terms: &TermStore,
        bv_model: &BvModel,
        t: TermId,
        memo: &mut BvEvalMemo,
    ) -> Option<BigInt> {
        let Sort::BitVec(sort) = terms.sort(t) else {
            return None;
        };
        let value = Self::evaluate_bv_expr_with_bools(
            terms,
            t,
            &bv_model.values,
            &bv_model.bool_overrides,
            memo,
        )?;
        (value.sign() != num_bigint::Sign::Minus && value.bits() <= u64::from(sort.width))
            .then_some(value)
    }

    fn store_chain_element_value(
        terms: &TermStore,
        bv_model: &BvModel,
        term: TermId,
        array_model: &mut ArrayModel,
        memo: &mut BvEvalMemo,
    ) -> Option<String> {
        match terms.sort(term) {
            Sort::BitVec(sort) => Self::store_chain_operand_value(terms, bv_model, term, memo)
                .map(|value| format_bitvec(&value, sort.width)),
            Sort::Bool => Self::evaluate_bool_substitution(
                terms,
                term,
                &bv_model.values,
                &bv_model.bool_overrides,
                memo,
            )
            .map(|value| value.to_string()),
            Sort::Array(_) => Self::array_cell_value(terms, bv_model, term, array_model, memo),
            _ => None,
        }
    }

    /// Build an [`ArrayInterpretation`] for a `store` chain term by resolving
    /// each stored (index, value) pair through `bv_model` and inheriting the
    /// base array's entry for indices the chain does not overwrite.
    ///
    /// Shared by direct definitions and substitution targets. Every typed cell
    /// and the base must resolve; partial/truncated chains never become total
    /// default-backed interpretations. The independent original-root gate still
    /// decides whether this complete candidate satisfies the source.
    pub(super) fn build_store_chain_interp(
        terms: &TermStore,
        bv_model: &BvModel,
        store_term: TermId,
        array_model: &mut ArrayModel,
    ) -> Option<ArrayInterpretation> {
        let Sort::Array(arr_sort) = terms.sort(store_term) else {
            return None;
        };
        let Sort::BitVec(idx_bv) = &arr_sort.index_sort else {
            return None;
        };
        if !Self::is_buildable_cell_sort(&arr_sort.element_sort) {
            return None;
        }
        let (chain_entries, base) = Self::collect_store_chain_entries(terms, store_term)?;
        if chain_entries.is_empty() {
            return None;
        }

        let mut index_to_value: HashMap<String, String> = HashMap::default();
        let mut memo = BvEvalMemo::default();
        for &(idx_term, val_term) in &chain_entries {
            for operand in [idx_term, val_term] {
                Self::seed_definition_operand_leaves(
                    terms,
                    bv_model,
                    operand,
                    array_model,
                    &mut memo,
                );
            }
        }

        // Store-chain entries (ground truth; outermost store wins).
        for (idx_term, val_term) in &chain_entries {
            let idx = Self::store_chain_operand_value(terms, bv_model, *idx_term, &mut memo)?;
            let value = Self::store_chain_element_value(
                terms,
                bv_model,
                *val_term,
                array_model,
                &mut memo,
            )?;
            index_to_value
                .entry(format_bitvec(&idx, idx_bv.width))
                .or_insert(value);
        }
        let mut interp =
            Self::resolve_substitution_target_interp(terms, bv_model, base, array_model)?;
        // Base entries are already newest-first; the first one at an index
        // wins unless an outer store has overwritten it.
        for (idx, value) in &interp.stores {
            index_to_value
                .entry(idx.clone())
                .or_insert_with(|| value.clone());
        }

        interp.stores = index_to_value.into_iter().collect();
        Some(interp)
    }

    /// The interpretation a ground array definition denotes: a `const-array`
    /// default, or a `store` chain over its resolved base. Both builders are
    /// complete or `None`; neither ever returns a partial interpretation.
    pub(super) fn ground_definition_interp(
        terms: &TermStore,
        bv_model: &BvModel,
        definition: TermId,
        array_model: &mut ArrayModel,
    ) -> Option<ArrayInterpretation> {
        match terms.get(definition) {
            TermData::App(sym, args) if sym.name() == "const-array" && args.len() == 1 => {
                Self::const_array_interp(terms, bv_model, definition, args[0], array_model)
            }
            _ => Self::build_store_chain_interp(terms, bv_model, definition, array_model),
        }
    }

    /// Walk a store chain and collect (index_term, value_term) pairs.
    ///
    /// Returns pairs in outermost-first order (last store first).
    /// Returns the actual terminal base. The unchanged 500-store bound refuses
    /// overflow rather than returning a prefix with a different, deeper base.
    pub(super) fn collect_store_chain_entries(
        terms: &TermStore,
        mut array_term: TermId,
    ) -> Option<(Vec<(TermId, TermId)>, TermId)> {
        let mut entries = Vec::new();
        let mut depth = 0;
        const MAX_DEPTH: usize = 500;

        loop {
            match terms.get(array_term) {
                TermData::App(sym, args) if sym.name() == "store" => {
                    let Sort::Array(sort) = terms.sort(array_term) else {
                        return None;
                    };
                    if depth >= MAX_DEPTH
                        || !matches!(sym, ay_core::term::Symbol::Named(_))
                        || args.len() != 3
                        || terms.sort(args[0]) != terms.sort(array_term)
                        || terms.sort(args[1]) != &sort.index_sort
                        || terms.sort(args[2]) != &sort.element_sort
                    {
                        return None;
                    }
                    entries.push((args[1], args[2])); // (index, value)
                    array_term = args[0]; // recurse into base
                    depth += 1;
                }
                _ => return Some((entries, array_term)),
            }
        }
    }

    /// Populate array model entries for variables defined via store chains (#8512).
    ///
    /// Scans `assertions` for `(= Var store_chain)` or `(= store_chain Var)`
    /// patterns. For each, walks the store chain to collect index/value pairs,
    /// resolves them through the BV model, and merges with the base array's
    /// model entries. A `(= Var const-array)` definition resolves its default
    /// the same way; its "base" is the const-array itself, never withheld. An
    /// unresolved store chain withholds its variable; an unresolved const-array
    /// default leaves the variable as it was (see the second pass).
    ///
    /// After variable substitution, `select(b, idx)` is rewritten to
    /// `select(store(a, i, v), idx)` and may be further simplified by
    /// `expand_select_store`. When assertions are restored, selects on `b`
    /// may not appear in the BV model at all. This function recovers the
    /// correct model by:
    /// 1. Extracting store chain entries (index/value pairs with ground truth)
    /// 2. Inheriting base array entries for indices not in the store chain
    /// 3. Removing any select-based entries that conflict with store chain values
    ///
    /// Returns the `(array_var, store_chain_base)` pairs whose chain resolved
    /// COMPLETELY — every (index, value) term in the chain came back concrete
    /// from the BV model. Only those interpretations cover every index the
    /// definition speaks to; a chain with even one unresolved pair leaves a hole
    /// that would read back as the array's `default`. The caller uses this to
    /// decide which nested-only definitions no longer need to be withheld as
    /// read-conflicted (see [`Self::extract_array_model_from_bv_model`]).
    pub(super) fn populate_store_chain_array_models(
        terms: &TermStore,
        bv_model: &BvModel,
        assertions: &[TermId],
        array_model: &mut ArrayModel,
    ) -> Vec<(TermId, TermId)> {
        // First pass: collect all (Var, store_chain_term, base_array) tuples.
        //
        // Store-chain definitions may be nested inside BV1 guards such as
        // `(ite (= arr (store ...)) #b1 #b0)`. Only trust nested definitions
        // reached through a top-level true assertion and model-forced true
        // BV1/Bool wrappers.
        let mut store_defs: Vec<(TermId, TermId, TermId)> = Vec::new();
        let mut seen_store_defs: HashSet<(TermId, TermId, TermId)> = HashSet::default();

        for &assertion in assertions {
            let mut visited: HashSet<(TermId, StoreChainTruth)> = HashSet::default();
            Self::collect_true_store_chain_defs(
                terms,
                bv_model,
                assertion,
                StoreChainTruth::BoolTrue,
                0,
                &mut visited,
                &mut seen_store_defs,
                &mut store_defs,
            );
        }

        if store_defs.is_empty() {
            return Vec::new();
        }

        Self::propagate_defined_array_read_pins(
            terms,
            bv_model,
            &store_defs,
            assertions,
            array_model,
        );

        // Second pass: build each definition once every definition of an array
        // it reads has been attempted (`definition_order.rs`).
        let (fully_resolved, failed) =
            Self::resolve_ground_definitions(terms, bv_model, assertions, &store_defs, array_model);
        // A second successful definition cannot erase an unresolved first one.
        for var_id in &failed {
            array_model.definition_authoritative.remove(var_id);
        }
        array_model.read_conflicted.extend(failed);
        fully_resolved
    }
}
