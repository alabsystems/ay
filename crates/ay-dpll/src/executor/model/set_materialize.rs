// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Materialize a self-consistent array interpretation for finite-set carriers
//! in a QF_SET / QF_SETLIA SAT model (#set-model-witness).
//!
//! Root cause this addresses: a set `s` of sort `(Set T)` is modelled on the
//! membership carrier `(Array T Bool)`. A membership atom `(set.member e s)`
//! is elaborated to the Boolean `select` term `(select s e)`, which the SAT
//! solver assigns directly. The combined Set+LIA solver does *not* reconstruct
//! an `ArrayInterpretation` for the carrier from those select literals, so the
//! model printer has no array-model entry for `s` and prints the bare default
//! const-array — `((as const (Array T Bool)) false)`, the EMPTY set. That
//! printed model contradicts the SAT-assigned membership: `(get-value ((select
//! s e)))` returns `true` (read from the SAT model) while `(get-model)` shows
//! `e` absent. get-model and get-value disagree, and the printed model does not
//! satisfy the asserted `(set.member e s)`.
//!
//! This module closes the gap by mirroring the string-witness materialization
//! approach (`string_materialize.rs`): for every set-carrier array variable, it
//! collects the membership reads `(select s e)` that appear in the assertions,
//! evaluates each read's Boolean value in the current model (the SAME value
//! `get-value` returns — `evaluate_select` followed by the SAT fallback), and
//! records a store entry `e -> true/false` plus a `false` default. The result
//! is committed into `model.array_model` so the printer emits a store chain
//! consistent with `get-value`.
//!
//! Soundness: the SAT/UNSAT verdict is already decided before this runs and is
//! never changed here — only the *printed array interpretation* is augmented to
//! agree with the per-atom Boolean membership values the model already carries.
//! Existing `ArrayInterpretation` store entries are never overwritten (they are
//! authoritative for `get-value`), so get-model and get-value stay in lockstep.
//! The materialized model is then re-checked by the normal validation pipeline,
//! so no `sat` can print a model that violates a `set.member` assertion.

use ay_arrays::{ArrayInterpretation, ArrayModel};
use ay_core::kani_compat::DetHashSet as HashSet;
use ay_core::term::TermData;
use ay_core::{Sort, TermId};

use super::{EvalValue, Executor};

impl Executor {
    /// Build/augment `ArrayInterpretation`s for finite-set carriers so the
    /// printed model agrees with `get-value` on every membership atom.
    ///
    /// Returns `true` unconditionally (it never fails closed): the values it
    /// records are exactly the ones the model already reports for the
    /// membership selects, so it cannot introduce an inconsistency. The
    /// surrounding pipeline still re-validates the model afterward.
    ///
    /// Only set-carrier array variables (`(Array T Bool)`) that participate in
    /// at least one membership read are touched; all other arrays and theory
    /// values are left untouched.
    pub(in crate::executor) fn materialize_set_witnesses(&mut self) -> bool {
        // Only relevant when there is a model to augment.
        if self.last_model.is_none() {
            return true;
        }

        // Collect (set-carrier variable, membership index) reads from the
        // assertions: `(select s e)` where `s` is a Bool-element array variable.
        let reads = self.collect_set_membership_reads();
        if reads.is_empty() {
            return true;
        }

        // For each distinct set variable, build the store entries from its
        // membership reads. We evaluate each read with the current model BEFORE
        // mutating `array_model`, so the values match what `get-value` reports.
        //
        // `entries`: set-var -> (index_sort, Vec<(formatted_index, "true"/"false")>).
        let mut planned: Vec<(TermId, Sort, Vec<(String, String)>)> = Vec::new();
        for &set_var in &reads.set_vars {
            let Sort::Array(array_sort) = self.ctx.terms.sort(set_var).clone() else {
                continue;
            };
            let index_sort = array_sort.index_sort.clone();

            // Existing store keys (if any) are authoritative for get-value, so
            // we must not add a conflicting entry for the same index. Snapshot
            // them up front.
            let existing_keys: HashSet<String> = self
                .last_model
                .as_ref()
                .and_then(|m| m.array_model.as_ref())
                .and_then(|am| am.array_values.get(&set_var))
                .map(|interp| interp.stores.iter().map(|(k, _)| k.clone()).collect())
                .unwrap_or_default();

            let mut stores: Vec<(String, String)> = Vec::new();
            let mut seen_keys: HashSet<String> = HashSet::default();
            for (idx, read_term) in reads.reads_for(set_var) {
                let model = self
                    .last_model
                    .as_ref()
                    .expect("model presence checked at entry");

                // Format the index using the model's value (the SAME formatting
                // the array-model lookup parses back, so store-key matching in
                // `evaluate_select` succeeds).
                let idx_val = self.evaluate_term(model, idx);
                if matches!(idx_val, EvalValue::Unknown) {
                    // No concrete index value: cannot key a store entry; leave
                    // it to the const-array default (sound — no concrete
                    // membership to materialize).
                    continue;
                }
                let key = self.format_eval_value(&idx_val, idx);

                // Skip indices already pinned by an existing store entry or by
                // an earlier read in this pass (first read wins, mirroring
                // `evaluate_select`'s first-match store lookup).
                if existing_keys.contains(&key) || !seen_keys.insert(key.clone()) {
                    continue;
                }

                // Evaluate the membership read's Boolean value — the exact value
                // `get-value ((select s idx))` returns.
                let member_val = match self.evaluate_term(model, read_term) {
                    EvalValue::Bool(b) => b,
                    _ => continue,
                };
                stores.push((key, if member_val { "true" } else { "false" }.to_string()));
            }

            if !stores.is_empty() {
                planned.push((set_var, index_sort, stores));
            }
        }

        if planned.is_empty() {
            return true;
        }

        // Commit: ensure an `ArrayModel` exists, then for each set variable
        // create/augment its interpretation. We never overwrite existing store
        // entries (preserving get-value), only add the new membership entries
        // and fill in a `false` default when none is present (a set is empty by
        // default; only explicit members deviate).
        let model = self
            .last_model
            .as_mut()
            .expect("model presence checked at entry");
        let array_model = model.array_model.get_or_insert_with(ArrayModel::default);
        for (set_var, index_sort, new_stores) in planned {
            let interp =
                array_model
                    .array_values
                    .entry(set_var)
                    .or_insert_with(|| ArrayInterpretation {
                        default: None,
                        stores: Vec::new(),
                        index_sort: Some(index_sort.clone()),
                        element_sort: Some(Sort::Bool),
                    });
            if interp.default.is_none() {
                interp.default = Some("false".to_string());
            }
            if interp.index_sort.is_none() {
                interp.index_sort = Some(index_sort);
            }
            if interp.element_sort.is_none() {
                interp.element_sort = Some(Sort::Bool);
            }
            interp.stores.extend(new_stores);
        }

        true
    }
}

/// Membership reads collected from the assertions, grouped per set variable.
struct SetMembershipReads {
    /// Distinct set-carrier variables that have at least one membership read.
    set_vars: Vec<TermId>,
    /// `(set_var, index, read_term)` membership records, where `read_term` is
    /// the membership atom itself (`(select set idx)` or `(set.member idx set)`)
    /// whose Boolean model value is the membership truth.
    records: Vec<(TermId, TermId, TermId)>,
}

impl SetMembershipReads {
    fn is_empty(&self) -> bool {
        self.records.is_empty()
    }

    /// All `(index, read_term)` records read against `set_var`.
    fn reads_for(&self, set_var: TermId) -> impl Iterator<Item = (TermId, TermId)> + '_ {
        self.records
            .iter()
            .filter(move |(s, _, _)| *s == set_var)
            .map(|(_, idx, read)| (*idx, *read))
    }
}

impl Executor {
    /// Collect `(select s e)` membership reads over set-carrier array variables
    /// from the assertion DAG.
    ///
    /// A set carrier is an array variable whose element sort is `Bool` (the
    /// `(Set T) = (Array T Bool)` membership encoding). Both the elaborated
    /// `select` shape and any residual raw `set.member` atom are recognised.
    fn collect_set_membership_reads(&self) -> SetMembershipReads {
        let mut set_vars: Vec<TermId> = Vec::new();
        let mut seen_vars: HashSet<TermId> = HashSet::default();
        let mut records: Vec<(TermId, TermId, TermId)> = Vec::new();
        let mut seen_pairs: HashSet<(TermId, TermId)> = HashSet::default();

        let mut stack: Vec<TermId> = self.ctx.assertions.clone();
        let mut visited: HashSet<TermId> = HashSet::default();
        while let Some(t) = stack.pop() {
            if !visited.insert(t) {
                continue;
            }
            match self.ctx.terms.get(t) {
                TermData::App(sym, args) => {
                    let name = sym.name();
                    // Elaborated membership: (select set elem) with a Bool-array
                    // operand. raw membership: (set.member elem set).
                    let membership = if name == "select" && args.len() == 2 {
                        Some((args[0], args[1]))
                    } else if name == "set.member" && args.len() == 2 {
                        Some((args[1], args[0]))
                    } else {
                        None
                    };
                    if let Some((set, elem)) = membership {
                        if self.is_set_carrier_var(set) && seen_pairs.insert((set, elem)) {
                            if seen_vars.insert(set) {
                                set_vars.push(set);
                            }
                            // `t` is the membership atom itself; its Boolean model
                            // value is the membership truth for (set, elem).
                            records.push((set, elem, t));
                        }
                    }
                    for &arg in args {
                        stack.push(arg);
                    }
                }
                TermData::Not(inner) => stack.push(*inner),
                TermData::Ite(c, th, e) => {
                    stack.push(*c);
                    stack.push(*th);
                    stack.push(*e);
                }
                TermData::Let(bindings, body) => {
                    for (_, value) in bindings.iter() {
                        stack.push(*value);
                    }
                    stack.push(*body);
                }
                _ => {}
            }
        }

        SetMembershipReads { set_vars, records }
    }

    /// Whether `term` is an array *variable* whose element sort is `Bool`
    /// (a finite-set membership carrier `(Array T Bool)`).
    fn is_set_carrier_var(&self, term: TermId) -> bool {
        matches!(self.ctx.terms.get(term), TermData::Var(_, _))
            && self
                .ctx
                .terms
                .sort(term)
                .array_element()
                .is_some_and(Sort::is_bool)
    }
}
