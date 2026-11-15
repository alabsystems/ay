// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Array models recovered from a BV model: the bit-blasted `select` scan,
//! ground array definitions and the definitional array equalities between them
//! (#5449). Store-chain and substitution-target interpretations are in
//! `store_chains.rs`; which store-chain definitions the model makes true is in
//! `true_store_chain_defs.rs`.

use super::*;

impl Executor {
    /// Extract array model from BV model for QF_ABV/QF_AUFBV (#5449).
    ///
    /// Scans bit-blasted select terms in the BV model to recover concrete
    /// index-value mappings for each root array variable. Without this,
    /// array models default to `((as const ...) 0)`.
    ///
    /// Also scans assertions for `(= array_var (store ...))` patterns to
    /// populate models for array variables defined by store chains. After
    /// variable substitution, selects on such variables are rewritten to
    /// selects on the store chain, so the select-scan alone misses them.
    pub(in crate::executor) fn extract_array_model_from_bv_model(
        terms: &TermStore,
        bv_model: &BvModel,
        assertions: &[TermId],
        substituted_vars: &HashSet<TermId>,
    ) -> ArrayModel {
        // Group select(array_var, index) terms by array variable.
        // Only collect selects where the array arg is a variable (Var), NOT a
        // store chain. Selects through stores give the post-store value, not the
        // root array's value — collecting them would cause non-deterministic
        // model output when a direct select and a store-chain select at the same
        // index map to the same root with different values.
        // ROW2 axioms ensure that store-chain selects at non-matching indices
        // have corresponding direct selects from the root array.
        //
        // #abv-select-congruence (wishlist#1): selects whose INDEX mentions a
        // substitution-eliminated variable are excluded. Their bit-blast values
        // are decoupled junk (the index components are free in the CNF), so a
        // pair derived from them either plants a garbage store entry at an
        // arbitrary index or #8510-conflicts with the authoritative
        // post-substitution read of the same array — masking a pinned read
        // with the default. The post-substitution counterpart of every such
        // read is present in the model and supplies the authoritative pair.
        let mut selects_by_array: HashMap<TermId, Vec<(TermId, TermId)>> = HashMap::default();
        // Memoized per index TERM: many selects share hash-consed index terms
        // on BMC instances, so the walk runs once per distinct index.
        let mut decoupled_memo: HashMap<TermId, bool> = HashMap::default();
        let mut decoupled = |idx: TermId| {
            !substituted_vars.is_empty()
                && *decoupled_memo
                    .entry(idx)
                    .or_insert_with(|| Self::term_mentions_any_var(terms, idx, substituted_vars))
        };

        // Scan BV-sorted select terms from bv_model.values
        for &term_id in bv_model.values.keys() {
            if let TermData::App(sym, args) = terms.get(term_id) {
                if sym.name() == "select"
                    && args.len() == 2
                    && matches!(terms.get(args[0]), TermData::Var(_, _))
                    && !decoupled(args[1])
                {
                    selects_by_array
                        .entry(args[0])
                        .or_default()
                        .push((args[1], term_id));
                }
            }
        }

        // #6047: Also scan Bool-sorted select terms from bool_overrides.
        // Arrays like (Array BV32 Bool) have Bool-element selects whose values
        // are in the SAT assignment (seeded into bool_overrides), not bv_model.values.
        // Without this, (Array BV Bool) arrays get default const(false) models
        // even when select(arr, idx) is asserted true.
        for &term_id in bv_model.bool_overrides.keys() {
            if let TermData::App(sym, args) = terms.get(term_id) {
                if sym.name() == "select"
                    && args.len() == 2
                    && matches!(terms.get(args[0]), TermData::Var(_, _))
                    && !decoupled(args[1])
                {
                    selects_by_array
                        .entry(args[0])
                        .or_default()
                        .push((args[1], term_id));
                }
            }
        }

        let hints = Self::array_default_hints(terms, bv_model, assertions);
        let mut array_values = HashMap::default();
        for (root_id, selects) in &selects_by_array {
            let Sort::Array(arr_sort) = terms.sort(*root_id) else {
                continue;
            };
            let Sort::BitVec(idx_bv) = &arr_sort.index_sort else {
                continue;
            };
            let idx_width = idx_bv.width;

            // Element sort determines how to format the default and store values.
            // (Array BV BV) → bitvec default/values
            // (Array BV Bool) → "false"/"true" default/values
            // The default agrees with the model's `(default ..)` values
            // (`model_defaults.rs`).
            let is_bool_elem = matches!(arr_sort.element_sort, Sort::Bool);
            let Some(default_val) = hints.get(root_id).cloned().or_else(|| {
                Self::select_scan_default(terms, bv_model, *root_id, &arr_sort.element_sort)
            }) else {
                continue;
            };

            let mut interp = ArrayInterpretation {
                index_sort: Some(arr_sort.index_sort.clone()),
                element_sort: Some(arr_sort.element_sort.clone()),
                default: Some(default_val),
                ..Default::default()
            };

            // Collect ALL (index, value) pairs, detecting conflicts (#8510).
            //
            // Multiple select terms at the same array index can have different
            // BV model values. This happens when the array axiom fixpoint or
            // FC axiom generation creates new select terms with fresh
            // unconstrained bits, while the original select term (from an
            // assertion like `(= #x00 (select arr idx))`) has constrained bits.
            //
            // HashMap iteration order is non-deterministic, so the first-seen
            // select term at any index may be the unconstrained one with
            // arbitrary bit values. When values conflict at an index, we remove
            // the store entry entirely and let the default value (typically
            // `#x00`) apply via `lookup_array_model`. This prevents false SAT
            // on QF_ABV benchmarks like csplit-query where ~2000 constant
            // selects share indices with FC-generated selects.
            let mut index_to_value: HashMap<String, String> = HashMap::default();
            let mut conflicted_indices: HashSet<String> = HashSet::default();

            for &(idx_id, sel_id) in selects {
                let idx_val = bv_model
                    .values
                    .get(&idx_id)
                    .cloned()
                    .or_else(|| Self::evaluate_bv_expr(terms, idx_id, &bv_model.values));

                // Element value: from BV model for BV elements, bool_overrides for Bool elements
                let elem_str = if is_bool_elem {
                    bv_model
                        .bool_overrides
                        .get(&sel_id)
                        .map(|&b| if b { "true" } else { "false" }.to_string())
                } else {
                    bv_model
                        .values
                        .get(&sel_id)
                        .cloned()
                        .or_else(|| Self::evaluate_bv_expr(terms, sel_id, &bv_model.values))
                        .map(|ev| {
                            let Sort::BitVec(elem_bv) = &arr_sort.element_sort else {
                                unreachable!(
                                    "BUG: BV array element sort is not BitVec in model extraction"
                                );
                            };
                            format_bitvec(&ev, elem_bv.width)
                        })
                };

                if let (Some(ref iv), Some(ref ev_str)) = (idx_val, &elem_str) {
                    let idx_str = format_bitvec(iv, idx_width);
                    match index_to_value.get(&idx_str) {
                        None => {
                            index_to_value.insert(idx_str, ev_str.clone());
                        }
                        Some(existing_val) if existing_val != ev_str => {
                            // Conflict: different select terms at the same index
                            // have different BV model values. One is constrained
                            // by an assertion, the other has unconstrained bits.
                            // Remove this index from the store so the default
                            // applies, avoiding non-deterministic wrong models.
                            conflicted_indices.insert(idx_str);
                        }
                        Some(_) => {
                            // Same value: no conflict, keep the existing entry
                        }
                    }
                }
            }

            // Build store entries, excluding conflicted indices
            for (idx_str, val_str) in index_to_value {
                if !conflicted_indices.contains(&idx_str) {
                    interp.stores.push((idx_str, val_str));
                }
            }

            array_values.insert(*root_id, interp);
        }
        // Bases no read reaches still take the else-value a definition passes
        // down (`model_defaults.rs`); arrays of arrays take their nested
        // reads, kept only if they end unwithheld (`nested_reads.rs`).
        Self::publish_unread_hinted_arrays(terms, &hints, &mut array_values);
        let nested = Self::publish_nested_reads(terms, bv_model, &mut decoupled, &mut array_values);

        // #8512: Scan assertions for `(= array_var (store ...))` patterns to
        // populate models for array variables defined by store chains.
        //
        // After variable substitution, `select(b, idx)` is rewritten to
        // `select(store(a, i, v), idx)`, then `expand_select_store` may
        // eliminate the select entirely (replacing it with an ITE or constant).
        // When assertions are restored before model extraction, the original
        // `(= b (store a #x01 #x42))` is present but `b` has no select terms
        // in the BV model. Walking the store chain and resolving index/value
        // pairs from the BV model fills the gap.
        //
        // This is needed for EXTERNAL_CODEGEN GPU/memory semantic encoding where array
        // variables represent memory states connected by store chains.
        let read_conflicted = Self::withheld_nested_definition_vars(terms, assertions);
        let mut array_model = ArrayModel {
            array_values,
            read_conflicted,
            store_chain_class_candidate: None,
            ..Default::default()
        };
        let store_chain_populated =
            Self::populate_store_chain_array_models(terms, bv_model, assertions, &mut array_model);

        // #array-def-equality: an array variable asserted equal — transitively
        // through `(= x y)` chains — to a const-array or store chain must adopt
        // that AUTHORITATIVE interpretation, even when select-derived extraction
        // gave it a divergent entry from orphaned/skolem `select` terms. Two
        // datatype-field arrays asserted equal but reconstructed independently
        // (e.g. `(= s!fld_data t!fld_osc_data!fld_data)`, one resolving via its
        // definition to `(const-array #xff)`, the other carrying a garbage
        // select-derived entry) otherwise disagree, and the strict array oracle
        // refutes the asserted equality — demoting a genuine model to `unknown`.
        //
        // Sound: the definitional equality is an assertion (ground truth in every
        // model), so overwriting with the definition's value can only make the
        // reported interpretation match what the formula already requires; any
        // OTHER assertion the definite value violates still fails its own oracle
        // check. Pure var↔var equalities with no const/store ground reachable are
        // deliberately left untouched, so genuinely spurious models (where the
        // bit-blaster left two asserted-equal arrays inconsistent) are still
        // refuted by comparing their independent entries.
        Self::propagate_definitional_array_equalities(
            terms,
            bv_model,
            assertions,
            &mut array_model,
        );

        // #8512-nested-def: an array variable whose ONLY definition is a
        // store-chain / const-array equality nested inside `or`/`ite`/`not`
        // cannot adopt that definition — a conditional equality is not
        // unconditionally asserted, so applying it would fabricate a value.
        // Its select-derived interpretation is published as it stands and
        // judged on its values by the independent gate; only a sort the select
        // scans do not interpret is withheld (`live_definitions.rs`).
        //
        // #8512-forced-or: when the model FORCES the arm the definition sits
        // in (every sibling disjunct is false), the chain was walked and every
        // (index, value) pair resolved concretely, so the definition's
        // interpretation is published instead.
        //
        // A refused base poisons dependent definitions transitively, including
        // ones visited before the failed base definition was discovered.
        for _ in 0..store_chain_populated.len() {
            let mut changed = false;
            for (var, base) in &store_chain_populated {
                if array_model.is_withheld(base) {
                    changed |= array_model.read_conflicted.insert(*var);
                }
            }
            if !changed {
                break;
            }
        }
        Self::align_model_true_array_equalities(terms, bv_model, assertions, &mut array_model);

        Self::drop_withheld_nested_reads(&nested, &mut array_model);
        array_model
    }

    /// Array variables that appear in a store-chain / const-array defining
    /// equality ONLY at a nested (non-top-level, non-top-level-`and`) position.
    ///
    /// `propagate_definitional_array_equalities` scans top-level `=` assertions
    /// only, so these variables never receive their authoritative interpretation
    /// and keep a partial select-derived one, which the gate judges on its
    /// values; only a sort the select scans skip is withheld (`live_definitions.rs`).
    pub(super) fn array_vars_defined_only_under_nested_equality(
        terms: &TermStore,
        assertions: &[TermId],
    ) -> HashSet<TermId> {
        // Definitions reachable unconditionally: top level, or a conjunct of a
        // top-level `and`. These ARE applied elsewhere, so exclude them.
        let mut unconditional: HashSet<TermId> = HashSet::default();
        let mut top: Vec<TermId> = assertions.to_vec();
        while let Some(t) = top.pop() {
            match terms.get(t) {
                TermData::App(sym, args) if sym.name() == "and" => top.extend(args.iter().copied()),
                TermData::App(sym, args) if sym.name() == "=" && args.len() == 2 => {
                    for (a, b) in [(args[0], args[1]), (args[1], args[0])] {
                        if matches!(terms.get(a), TermData::Var(_, _))
                            && matches!(terms.sort(a), Sort::Array(_))
                            && Self::is_array_ground_definition(terms, b)
                        {
                            unconditional.insert(a);
                        }
                    }
                }
                _ => {}
            }
        }
        // Every array-var store-chain definition anywhere in the formula.
        let mut nested: HashSet<TermId> = HashSet::default();
        let mut stack: Vec<TermId> = assertions.to_vec();
        let mut seen: HashSet<TermId> = HashSet::default();
        while let Some(t) = stack.pop() {
            if !seen.insert(t) {
                continue;
            }
            match terms.get(t) {
                TermData::App(sym, args) => {
                    if sym.name() == "=" && args.len() == 2 {
                        for (a, b) in [(args[0], args[1]), (args[1], args[0])] {
                            if matches!(terms.get(a), TermData::Var(_, _))
                                && matches!(terms.sort(a), Sort::Array(_))
                                && Self::is_array_ground_definition(terms, b)
                                && !unconditional.contains(&a)
                            {
                                nested.insert(a);
                            }
                        }
                    }
                    stack.extend(args.iter().copied());
                }
                TermData::Not(inner) => stack.push(*inner),
                TermData::Ite(c, x, y) => {
                    stack.push(*c);
                    stack.push(*x);
                    stack.push(*y);
                }
                _ => {}
            }
        }
        nested
    }

    /// Overwrite array-variable interpretations with the authoritative
    /// interpretation implied by a const-array / store-chain definitional
    /// equality reachable through asserted `(= x y)` chains. See the call site
    /// in [`Self::extract_array_model_from_bv_model`] for the rationale and the
    /// soundness argument. (#array-def-equality)
    fn propagate_definitional_array_equalities(
        terms: &TermStore,
        bv_model: &BvModel,
        assertions: &[TermId],
        array_model: &mut ArrayModel,
    ) {
        // Collect every array variable that appears in an asserted array
        // equality — those are the only ones a definition can speak to.
        let mut def_vars: Vec<TermId> = Vec::new();
        for &assertion in assertions {
            if let TermData::App(sym, args) = terms.get(assertion) {
                if sym.name() == "=" && args.len() == 2 {
                    for &side in &[args[0], args[1]] {
                        if matches!(terms.get(side), TermData::Var(_, _))
                            && matches!(terms.sort(side), Sort::Array(_))
                        {
                            def_vars.push(side);
                        }
                    }
                }
            }
        }
        def_vars.sort_by_key(|t| t.0);
        def_vars.dedup();

        for v in def_vars {
            let interp = {
                let mut visited = HashSet::default();
                Self::resolve_authoritative_array_interp(
                    terms,
                    bv_model,
                    assertions,
                    array_model,
                    v,
                    &mut visited,
                )
            };
            if let Some(interp) = interp {
                array_model.array_values.insert(v, interp);
            }
        }
    }

    /// Resolve an array variable to the AUTHORITATIVE interpretation implied by
    /// a const-array / store-chain definitional equality in `assertions`,
    /// following var→var definitional equalities transitively. Returns `None`
    /// when no const/store ground definition is reachable (the `visited` set
    /// breaks var↔var cycles), so the caller leaves the existing entry intact.
    fn resolve_authoritative_array_interp(
        terms: &TermStore,
        bv_model: &BvModel,
        assertions: &[TermId],
        array_model: &mut ArrayModel,
        var: TermId,
        visited: &mut HashSet<TermId>,
    ) -> Option<ArrayInterpretation> {
        if array_model.is_withheld(&var) || !visited.insert(var) {
            return None;
        }
        for &assertion in assertions {
            let TermData::App(sym, args) = terms.get(assertion) else {
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
            match terms.get(other) {
                TermData::App(s, a) if s.name() == "const-array" && a.len() == 1 => {
                    if let Some(interp) =
                        Self::const_array_interp(terms, bv_model, other, a[0], array_model)
                    {
                        return Some(interp);
                    }
                    array_model.read_conflicted.insert(var);
                }
                TermData::App(s, a) if s.name() == "store" && a.len() == 3 => {
                    // Resolve a known source definition of the base before
                    // inheriting it. Otherwise source order could leave this
                    // array holding a default that a later base pass replaces.
                    if let Some((_, base)) = Self::collect_store_chain_entries(terms, other) {
                        if matches!(terms.get(base), TermData::Var(_, _)) {
                            if let Some(interp) = Self::resolve_authoritative_array_interp(
                                terms,
                                bv_model,
                                assertions,
                                array_model,
                                base,
                                visited,
                            ) {
                                array_model.array_values.insert(base, interp);
                            }
                        }
                    }
                    if let Some(interp) =
                        Self::build_store_chain_interp(terms, bv_model, other, array_model)
                    {
                        return Some(interp);
                    }
                    array_model.read_conflicted.insert(var);
                }
                TermData::Var(_, _) if matches!(terms.sort(other), Sort::Array(_)) => {
                    if let Some(interp) = Self::resolve_authoritative_array_interp(
                        terms,
                        bv_model,
                        assertions,
                        array_model,
                        other,
                        visited,
                    ) {
                        return Some(interp);
                    }
                    if array_model.is_withheld(&other) {
                        array_model.read_conflicted.insert(var);
                    }
                }
                _ => {}
            }
        }
        None
    }
}
