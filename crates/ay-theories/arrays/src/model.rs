// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Model extraction for the array theory solver.
//!
//! Builds `ArrayInterpretation` from store chains, const-array terms, and
//! select-derived entries for use in satisfying model output.

use super::*;

impl ArraySolver<'_> {
    /// Extract an array model from the current solver state (#6047, #7022).
    ///
    /// Walks store chains, const-array terms, and select cache entries to build
    /// `ArrayInterpretation` for each tracked array. `term_values` maps term IDs
    /// to their string representations in the current model.
    ///
    /// Select-derived entries (#7022): For base arrays without stores, selects
    /// are the only source of index→value mappings. When EUF derives index
    /// equality (e.g., `x = y`), both `select(a, x)` and `select(a, y)` should
    /// resolve to the same value. By adding select-derived entries keyed by
    /// concrete index value, EUF-equal indices naturally deduplicate.
    pub fn extract_model(&mut self, term_values: &HashMap<TermId, String>) -> ArrayModel {
        // Model extraction relies on the current store/select caches and the
        // equality graph. If SAT assignments changed since the last array
        // check, alias arrays like `a1 = store(a0, 0, 11)` can otherwise miss
        // their propagated interpretation and leave validation with an
        // incomplete array model.
        self.populate_caches();
        // After rebuilding caches we also need a fresh equality/disequality
        // index so the equivalence-class propagation below sees alias edges
        // introduced by the most recent assignments (#8745).
        self.rebuild_assign_indices();

        let mut model = ArrayModel::default();

        // For each array term that has a store chain or const-array base,
        // reconstruct its interpretation.
        //
        // #qf-auflia-select-backfill: track which store entries carry a
        // CONCRETE (constant) written value. Concrete stores are hard
        // semantics and stay authoritative; a store whose value term is a
        // variable/opaque application only carries that term's (possibly
        // shadow-default) model value, and a select-derived entry pinned by an
        // ASSERTED read constraint is stronger evidence for the same index —
        // it may override below.
        let mut soft_store_indices: HashMap<TermId, std::collections::HashSet<String>> =
            HashMap::default();
        for (&arr_term, _) in &self.array_vars {
            let mut interp = ArrayInterpretation::default();
            if let Sort::Array(array_sort) = self.terms.sort(arr_term) {
                interp.index_sort = Some(array_sort.index_sort.clone());
                interp.element_sort = Some(array_sort.element_sort.clone());
            }
            let mut current = arr_term;

            // Walk the store chain backwards to collect stores
            while let Some(&(base, idx, val)) = self.store_cache.get(&current) {
                let idx_str = term_values.get(&idx).cloned().unwrap_or_default();
                let val_str = term_values.get(&val).cloned().unwrap_or_default();
                if std::env::var_os("AY_DEBUG_ARR_EXTRACT").is_some() {
                    eprintln!(
                        "[arr-extract] arr={} chain: base={} idx={}({idx_str}) val={}({val_str}) val_data={:?}",
                        arr_term.0, base.0, idx.0, val.0,
                        self.terms.get(val)
                    );
                }
                // (#nested-array-store-value) An ARRAY-sorted store value has no
                // element string — EUF names only uninterpreted-sort elements —
                // so `val_str` was empty and the store was DROPPED from the
                // interpretation entirely. Array-of-array models then lost every
                // nested store, making distinct inner arrays look identical and
                // leaving an asserted array disequality unwitnessable (the strict
                // `arrays-unwitnessed-diseq` oracle then degraded a genuine sat to
                // unknown: QF_AX nested store/extensionality, z3+cvc5 say sat).
                // Name such a value by its CONGRUENCE-CLASS representative: equal
                // arrays share a class hence a name, and distinct classes get
                // distinct names — so the store map records the value faithfully
                // without inventing a difference.
                let val_str =
                    if val_str.is_empty() && matches!(self.terms.sort(val), Sort::Array(_)) {
                        format!("@Arr!{}", self.shadow_uf.find(val).0)
                    } else {
                        val_str
                    };
                if !idx_str.is_empty() && !val_str.is_empty() {
                    if !matches!(self.terms.get(val), TermData::Const(_)) {
                        soft_store_indices
                            .entry(arr_term)
                            .or_default()
                            .insert(idx_str.clone());
                    }
                    interp.stores.push((idx_str, val_str));
                }
                current = base;
            }

            // Check for const-array default
            if let Some(&default_term) = self.const_array_cache.get(&current) {
                if let Some(val_str) = term_values.get(&default_term) {
                    interp.default = Some(val_str.clone());
                }
            }

            if !interp.stores.is_empty() || interp.default.is_some() {
                model.array_values.insert(arr_term, interp);
            }
        }

        // A symbolic array's `(default a)` is an ordinary scalar term in the
        // combined model. If that term has a committed value, it is exactly the
        // array interpretation's else value and must be carried into the array
        // model. Previously `default_cache` was wired only to const-array axiom
        // generation; extraction ignored it, leaving symbolic arrays partial and
        // making satisfiable constraints such as `(= (default a) x)` impossible
        // to validate or print coherently.
        for (&array, &default_term) in &self.default_cache {
            let Some(value) = term_values.get(&default_term).filter(|v| !v.is_empty()) else {
                continue;
            };
            let interp = model.array_values.entry(array).or_default();
            // A syntactic/propagated const-array default is semantic authority.
            // Never overwrite a disagreement with a speculative scalar value;
            // leaving it intact lets model validation reject the inconsistency.
            if interp.default.is_none() {
                interp.default = Some(value.clone());
            }
            if let Sort::Array(array_sort) = self.terms.sort(array) {
                interp.index_sort = Some(array_sort.index_sort.clone());
                interp.element_sort = Some(array_sort.element_sort.clone());
            }
        }

        // Add select-derived entries (#7022): for base arrays without explicit
        // stores, selects provide index→value mappings from the EUF model.
        //
        // #select-read-conflict-fail-closed: two select-derived entries for
        // ONE (base, index-value) cell that DISAGREE are an internally
        // inconsistent completion (e.g. a read at a symbolic index whose
        // merged completion value went stale against the read the constraints
        // pin). Baking either value in fabricates a winner the validators and
        // the independent model-check gate then treat as the model's
        // committed truth. Fail closed instead: drop the cell entirely (the
        // interpretation stays PARTIAL there) so downstream evaluation reads
        // the per-term committed select values — or degrades to the monitored
        // cannot-confirm posture — rather than refuting a fabricated cell.
        let mut select_derived: HashSet<(TermId, String)> = HashSet::default();
        let mut poisoned: HashSet<(TermId, String)> = HashSet::default();
        for (&select_term, &(array_term, index_term)) in &self.select_cache {
            let idx_str = match term_values.get(&index_term) {
                Some(s) if !s.is_empty() => s.clone(),
                _ => continue,
            };
            let val_str = match term_values.get(&select_term) {
                Some(s) if !s.is_empty() => s.clone(),
                _ => continue,
            };

            // Find the base array by peeling stores.
            //
            // #select-fold-miss-proof: `select(chain, i)` denotes a cell of the
            // BASE array only when `i` provably MISSES every peeled store
            // index. If `i` HITS a store (or a store index has no committed
            // value, so a hit cannot be excluded), the read observes the
            // chain's written cell — attributing it to the base fabricates a
            // base cell that no constraint pinned. Two folded reads through
            // DIFFERENT chains that legitimately differ at `i` then collide on
            // one (base, i) cell and manufacture a spurious
            // #select-read-conflict-fail-closed drop, poisoning the base (and,
            // via completion's dependency propagation, every chain over it):
            // wrong models stop being ground-refutable and genuine sats
            // degrade as unwitnessable (QF_AX read5 wrong-sat / storecomm
            // fail-close regression). Skipping the attribution is fail-closed:
            // the interpretation simply stays partial at that cell.
            let mut base = array_term;
            let mut provably_reaches_base = true;
            while let Some(&(inner_base, store_index, _)) = self.store_cache.get(&base) {
                match term_values.get(&store_index) {
                    Some(s) if !s.is_empty() && *s != idx_str => {}
                    _ => provably_reaches_base = false,
                }
                base = inner_base;
            }
            if std::env::var_os("AY_DEBUG_ARR_EXTRACT").is_some() {
                eprintln!(
                    "[arr-extract] select: sel={}({:?}) arr={} base={} idx={}({:?}) reaches_base={}",
                    select_term.0,
                    term_values.get(&select_term),
                    array_term.0,
                    base.0,
                    index_term.0,
                    term_values.get(&index_term),
                    provably_reaches_base
                );
            }
            if !provably_reaches_base {
                continue;
            }

            if poisoned.contains(&(base, idx_str.clone())) {
                continue; // cell dropped on a read conflict — never re-add
            }
            let interp = model.array_values.entry(base).or_default();
            if interp.index_sort.is_none() {
                if let Sort::Array(array_sort) = self.terms.sort(base) {
                    interp.index_sort = Some(array_sort.index_sort.clone());
                    interp.element_sort = Some(array_sort.element_sort.clone());
                }
            }
            // Concrete store entries are authoritative; SOFT store entries
            // (non-constant written value — see soft_store_indices above)
            // yield to a select-pinned value at the same index, since the
            // select entry reflects an asserted read constraint while the
            // soft store only echoes another term's possibly-default value.
            // Two SELECT-derived values that disagree drop the cell
            // (#select-read-conflict-fail-closed, see above).
            match interp.stores.iter().position(|(k, _)| k == &idx_str) {
                None => {
                    select_derived.insert((base, idx_str.clone()));
                    interp.stores.push((idx_str, val_str));
                }
                Some(pos) => {
                    if interp.stores[pos].1 != val_str {
                        if select_derived.contains(&(base, idx_str.clone())) {
                            interp.stores.remove(pos);
                            model.read_conflicted.insert(base);
                            poisoned.insert((base, idx_str));
                        } else if soft_store_indices
                            .get(&base)
                            .is_some_and(|soft| soft.contains(&idx_str))
                        {
                            interp.stores[pos].1 = val_str;
                            // The cell is now select-pinned: a later
                            // disagreeing read is a read conflict.
                            select_derived.insert((base, idx_str));
                        }
                    }
                }
            }
        }

        // #7435: Propagate interpretations across EUF equivalence classes.
        // When UF establishes equality between array terms (e.g.,
        // seq_array(seq_empty) = const_array(0)), terms in the same class
        // should share the same interpretation. Without this, a UF application
        // like seq_array(seq_empty) gets no interpretation even though its
        // EUF-equal partner const_array(0) has one with a default value.
        if !self.eq_adj.is_empty() && !self.assign_dirty {
            // NB (M2): this stays on the eager BFS cache. The interpretation
            // picked per class is `max_by_key` over the class members, whose
            // tie-break depends on member ITERATION ORDER; the union-find's
            // `non_singleton_classes()` sorts members while `equiv_classes`
            // keeps BFS insertion order, so switching the source here changes
            // which (equally-ranked) interpretation propagates and can emit a
            // different — and occasionally invalid — model. Model construction
            // is a once-per-solve cold path with no O(class) hot cost, so the
            // union-find brings no benefit that would justify that risk.
            self.build_equiv_class_cache();
            // For each equivalence class, find the richest interpretation
            // (prefer one with a default, then most stores) and propagate it
            // to all class members that lack one.
            for class in &self.equiv_classes {
                // Find the best interpretation in this class
                let best = class
                    .iter()
                    .filter_map(|t| model.array_values.get(t).map(|interp| (*t, interp)))
                    .max_by_key(|(_, interp)| {
                        (usize::from(interp.default.is_some()), interp.stores.len())
                    });
                if let Some((_, best_interp)) = best {
                    let best_interp = best_interp.clone();
                    for &member in class {
                        if !model.array_values.contains_key(&member) {
                            // Only propagate to array_vars members (tracked arrays)
                            if self.array_vars.contains_key(&member) {
                                model.array_values.insert(member, best_interp.clone());
                            }
                        }
                    }
                }
            }
        }

        model
    }
}
