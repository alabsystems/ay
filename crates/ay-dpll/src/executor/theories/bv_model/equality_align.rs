// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Alignment of array interpretations across var<->var equalities the
//! candidate makes true at nested positions. Completion only; the
//! complete original-root validation is unchanged.
use super::*;

/// Group variables into equality classes by union-find over pairs.
fn equality_classes(pairs: &[(TermId, TermId)]) -> Vec<Vec<TermId>> {
    fn find(parent: &mut HashMap<TermId, TermId>, v: TermId) -> TermId {
        let mut root = v;
        while let Some(&p) = parent.get(&root) {
            if p == root {
                break;
            }
            root = p;
        }
        let mut cur = v;
        while let Some(&p) = parent.get(&cur) {
            if p == root {
                break;
            }
            parent.insert(cur, root);
            cur = p;
        }
        root
    }
    let mut parent: HashMap<TermId, TermId> = HashMap::default();
    for &(a, b) in pairs {
        parent.entry(a).or_insert(a);
        parent.entry(b).or_insert(b);
        let (ra, rb) = (find(&mut parent, a), find(&mut parent, b));
        if ra != rb {
            parent.insert(ra, rb);
        }
    }
    let mut classes: HashMap<TermId, Vec<TermId>> = HashMap::default();
    for v in parent.keys().copied().collect::<Vec<_>>() {
        let root = find(&mut parent, v);
        classes.entry(root).or_default().push(v);
    }
    classes.into_values().collect()
}

impl Executor {
    /// Every var<->var array equality the candidate makes true
    /// anywhere in `assertions` (nested/reified positions included).
    pub(super) fn model_true_array_equality_pairs(
        terms: &TermStore,
        bv_model: &BvModel,
        assertions: &[TermId],
    ) -> Vec<(TermId, TermId)> {
        let mut pairs: Vec<(TermId, TermId)> = Vec::new();
        let mut stack: Vec<TermId> = assertions.to_vec();
        let mut seen: HashSet<TermId> = HashSet::default();
        while let Some(t) = stack.pop() {
            if !seen.insert(t) {
                continue;
            }
            match terms.get(t) {
                TermData::App(sym, args) => {
                    if sym.name() == "="
                        && args.len() == 2
                        && args[0] != args[1]
                        && [args[0], args[1]].iter().all(|&side| {
                            matches!(terms.get(side), TermData::Var(_, _))
                                && matches!(terms.sort(side), Sort::Array(_))
                        })
                        && Self::model_bool_value(terms, bv_model, t) == Some(true)
                    {
                        pairs.push((args[0], args[1]));
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
        pairs
    }

    /// Candidate-committed cells of selects occurring IN the
    /// assertions, per array var. These are the reads a completion
    /// must honor; pins from generated cross-selects that occur
    /// nowhere in the assertions may carry unlinked bits.
    pub(super) fn genuine_assertion_select_cells(
        terms: &TermStore,
        bv_model: &BvModel,
        assertions: &[TermId],
    ) -> HashMap<TermId, HashMap<String, String>> {
        let mut genuine: HashMap<TermId, HashMap<String, String>> = HashMap::default();
        let mut stack: Vec<TermId> = assertions.to_vec();
        let mut seen: HashSet<TermId> = HashSet::default();
        while let Some(t) = stack.pop() {
            if !seen.insert(t) {
                continue;
            }
            match terms.get(t) {
                TermData::App(sym, args) => {
                    if sym.name() == "select"
                        && args.len() == 2
                        && matches!(terms.get(args[0]), TermData::Var(_, _))
                    {
                        if let Some((idx, val)) =
                            Self::genuine_select_cell(terms, bv_model, args[0], args[1], t)
                        {
                            genuine.entry(args[0]).or_default().insert(idx, val);
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
        genuine
    }

    /// #model-true-array-equality: an array equality the candidate
    /// makes true at a NESTED position (reified under `ite`/BV1
    /// guards in the dwp idiom, e.g. `(ite (= mem_a mem_b) (= t #b1)
    /// (= t #b0))` inside an asserted conjunction) constrains the
    /// completion exactly as a top-level one does, but
    /// `propagate_definitional_array_equalities` only sees top-level
    /// assertions. Left unaligned, the sparse select-derived
    /// interpretation of the free side disagrees with the total
    /// definition-built interpretation of the other at the first
    /// unpinned index, and the gate falsifies an equality the
    /// candidate satisfied. Merge every model-true var<->var
    /// equality class into one shared interpretation (union of
    /// cells); a class whose cells conflict, whose defaults
    /// disagree, or that touches a withheld (`read_conflicted`)
    /// member is left alone — the gate then judges it as before.
    /// Completion is gate-validated, so alignment can only cost
    /// completeness, never soundness.
    pub(super) fn align_model_true_array_equalities(
        terms: &TermStore,
        bv_model: &BvModel,
        assertions: &[TermId],
        array_model: &mut ArrayModel,
    ) {
        let pairs = Self::model_true_array_equality_pairs(terms, bv_model, assertions);
        let genuine = Self::genuine_assertion_select_cells(terms, bv_model, assertions);
        if pairs.is_empty() {
            return;
        }
        for members in equality_classes(&pairs) {
            if members.iter().any(|v| array_model.is_withheld(v)) {
                continue;
            }
            if let Some(acc) = Self::merge_equality_class(array_model, &members, &genuine) {
                for v in members {
                    array_model.array_values.insert(v, acc.clone());
                }
            }
        }
    }

    /// The candidate's (index, value) cell for one in-assertion
    /// select, formatted exactly as the select scan formats pins.
    fn genuine_select_cell(
        terms: &TermStore,
        bv_model: &BvModel,
        array_var: TermId,
        idx_term: TermId,
        sel_term: TermId,
    ) -> Option<(String, String)> {
        let Sort::Array(arr_sort) = terms.sort(array_var) else {
            return None;
        };
        let Sort::BitVec(idx_bv) = &arr_sort.index_sort else {
            return None;
        };
        let idx_val = bv_model
            .values
            .get(&idx_term)
            .cloned()
            .or_else(|| Self::evaluate_bv_expr(terms, idx_term, &bv_model.values))?;
        let val = match &arr_sort.element_sort {
            Sort::BitVec(elem) => {
                let ev = bv_model
                    .values
                    .get(&sel_term)
                    .cloned()
                    .or_else(|| Self::evaluate_bv_expr(terms, sel_term, &bv_model.values))?;
                format_bitvec(&ev, elem.width)
            }
            Sort::Bool => if bv_model.bool_overrides.get(&sel_term).copied()? {
                "true"
            } else {
                "false"
            }
            .to_string(),
            _ => return None,
        };
        Some((format_bitvec(&idx_val, idx_bv.width), val))
    }

    /// Merge one model-true equality class into a single shared
    /// interpretation, or `None` when the class cannot be aligned
    /// (missing member interpretation, sort/default disagreement,
    /// two genuine assertion reads in conflict, or two
    /// definition-built members in conflict at an index no genuine
    /// read decides). Cell precedence: genuine in-assertion reads,
    /// then definition-built (authoritative) cells, then remaining
    /// select pins. A built interpretation's inherited cells are
    /// themselves pins of mixed provenance, so a genuine read
    /// outranks them; where a genuine read truly contradicts a
    /// definition-determined (store) cell, the candidate is not
    /// completable and the gate still falsifies the definition —
    /// alignment shifts which conjunct fails, never the verdict's
    /// soundness.
    fn merge_equality_class(
        array_model: &ArrayModel,
        members: &[TermId],
        genuine: &HashMap<TermId, HashMap<String, String>>,
    ) -> Option<ArrayInterpretation> {
        let mut interps: Vec<&ArrayInterpretation> = Vec::with_capacity(members.len());
        for v in members {
            interps.push(array_model.array_values.get(v)?);
        }
        let first = interps[0];
        if interps.iter().any(|interp| {
            interp.index_sort != first.index_sort
                || interp.element_sort != first.element_sort
                || interp.default != first.default
        }) {
            return None;
        }
        // Layer 1: genuine in-assertion reads (mutual contradiction
        // is unalignable — the candidate's own reads disagree).
        let mut cells: HashMap<String, String> = HashMap::default();
        for v in members {
            let Some(member_genuine) = genuine.get(v) else {
                continue;
            };
            for (idx, val) in member_genuine {
                match cells.get(idx) {
                    Some(existing) if existing != val => return None,
                    Some(_) => {}
                    None => {
                        cells.insert(idx.clone(), val.clone());
                    }
                }
            }
        }
        // Layer 2: authoritative (definition-built) cells fill the
        // indices no genuine read decided; two built members
        // disagreeing there is unalignable.
        let mut auth_cells: HashMap<String, String> = HashMap::default();
        for (&v, interp) in members.iter().zip(&interps) {
            if !array_model.definition_authoritative.contains(&v) {
                continue;
            }
            for (idx, val) in &interp.stores {
                match auth_cells.get(idx) {
                    Some(existing) if existing != val => {
                        if !cells.contains_key(idx) {
                            return None;
                        }
                    }
                    Some(_) => {}
                    None => {
                        auth_cells.insert(idx.clone(), val.clone());
                    }
                }
            }
        }
        for (idx, val) in auth_cells {
            cells.entry(idx).or_insert(val);
        }
        // Layer 3: remaining pins fill gaps only.
        for interp in &interps {
            for (idx, val) in &interp.stores {
                cells.entry(idx.clone()).or_insert_with(|| val.clone());
            }
        }
        let mut merged = first.clone();
        merged.stores = cells.into_iter().collect();
        Some(merged)
    }

    /// Array variables that appear in a store-chain / const-array defining
    /// equality ONLY at a nested (non-top-level, non-top-level-`and`) position.
    ///
    /// `propagate_definitional_array_equalities` scans top-level `=` assertions
    /// only, so these variables keep a partial select-derived interpretation.
    /// Listing them as read-conflicted withholds totality soundly.
    ///
    /// Exception: a variable whose nested definitions are ALL false
    /// under the BV model is not definition-constrained in this model
    /// (the dwp tag idiom's `#b0` branch), so its select-derived
    /// interpretation is legitimately total and is not withheld.
    pub(super) fn nested_only_defined_array_vars(
        terms: &TermStore,
        bv_model: &BvModel,
        assertions: &[TermId],
    ) -> HashSet<TermId> {
        fn is_array_ground_def(terms: &TermStore, t: TermId) -> bool {
            matches!(terms.get(t), TermData::App(sym, _)
                if sym.name() == "store" || sym.name() == "const-array")
        }
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
                            && is_array_ground_def(terms, b)
                        {
                            unconditional.insert(a);
                        }
                    }
                }
                _ => {}
            }
        }
        // Every array-var store-chain definition anywhere in the formula,
        // grouped by defined variable so model-falsified definitions can
        // be recognized below.
        let mut nested: HashMap<TermId, Vec<TermId>> = HashMap::default();
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
                                && is_array_ground_def(terms, b)
                                && !unconditional.contains(&a)
                            {
                                nested.entry(a).or_default().push(t);
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
        let falsified = |def: &TermId| Self::model_bool_value(terms, bv_model, *def) == Some(false);
        nested
            .into_iter()
            .filter(|(_, defs)| !defs.iter().all(|def| falsified(def)))
            .map(|(var, _)| var)
            .collect()
    }
}
