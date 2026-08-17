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
use ay_core::string_literal;
use ay_core::term::TermData;
use ay_core::{Sort, TermId};
use ay_set::OP_CARD;
use num_bigint::BigInt;
use num_traits::{Signed, ToPrimitive};

use crate::executor_format::{format_bigint, format_bitvec, format_model_atom, format_rational};

use super::{EvalValue, Executor, Model};

/// Upper bound on the number of fresh witness elements this module will invent
/// for one set carrier. A cardinality larger than this is not materialized —
/// the solve fails closed to `unknown` rather than printing a set whose size
/// contradicts the assertion (#set-card-model-witness).
const MAX_MATERIALIZED_SET_ELEMENTS: usize = 4096;

/// Search budget for fresh element candidates. Candidates are enumerated from
/// the index sort in a fixed order and skipped when they collide with an index
/// the model already pins, so the budget only has to exceed
/// `pinned + needed`.
const FRESH_ELEMENT_SEARCH_LIMIT: u64 = 1 << 20;

/// What [`Executor::plan_set_cardinality`] decided for one set-carrier
/// equivalence class.
enum SetCardPlan {
    /// No concrete cardinality is pinned for this class — nothing to enforce.
    Skip,
    /// The model cannot be made to exhibit the required cardinality soundly.
    /// The caller degrades `sat` to `unknown` (sound, incomplete).
    FailClosed,
    /// Commit `default = false` on every class member together with EXACTLY
    /// these cells (possibly none — the plan still pins the default, which is
    /// what turns a co-finite `((as const ..) true)` carrier into a finite one).
    Fix {
        cells: Vec<(String, String)>,
        index_sort: Sort,
    },
}

/// The membership facts a printed cardinality witness for one set-carrier
/// equivalence class has to respect.
///
/// Collected from the TOP-LEVEL POSITIVELY asserted atoms only — those are the
/// ones the query actually entails (#set-card-witness-constraints).
#[derive(Default)]
struct SetWitnessConstraints {
    /// Canonical keys that must be members of the witness.
    must_in: Vec<String>,
    /// Canonical keys that must NOT be members of the witness.
    must_out: Vec<String>,
    /// Upper bound: when `Some`, ONLY these keys may be members (an asserted
    /// `(set.subset class_var sup)` with a finite `sup`, or an asserted
    /// `(= class_var expr)` with a readable `expr`).
    allowed: Option<Vec<String>>,
    /// A class variable is defined by a top-level equality to a set expression
    /// whose model value has no structural reading here (an opaque set-valued
    /// application). Its cells are then exactly what the model already
    /// committed: nothing may be invented, nothing dropped.
    opaque_definition: bool,
}

impl SetWitnessConstraints {
    /// Require `key` to be a member. `None` when the model already requires the
    /// opposite — a self-contradictory assignment with no witness to print.
    fn require_in(&mut self, key: String) -> Option<()> {
        if self.must_out.contains(&key) {
            return None;
        }
        if !self.must_in.contains(&key) {
            self.must_in.push(key);
        }
        Some(())
    }

    /// Require `key` to be a non-member (dual of [`Self::require_in`]).
    fn require_out(&mut self, key: String) -> Option<()> {
        if self.must_in.contains(&key) {
            return None;
        }
        if !self.must_out.contains(&key) {
            self.must_out.push(key);
        }
        Some(())
    }

    /// Intersect the membership upper bound with `keys`.
    fn restrict_allowed(&mut self, keys: Vec<String>) {
        self.allowed = Some(match self.allowed.take() {
            None => keys,
            Some(prev) => prev.into_iter().filter(|k| keys.contains(k)).collect(),
        });
    }
}

impl Executor {
    /// The canonical store-key spelling of one index VALUE at `index_sort`.
    ///
    /// ROOT CAUSE this exists for (#set-card-neg-double-count): an
    /// `ArrayInterpretation`'s store keys are written by several producers that
    /// do NOT agree on how to spell a value. `format_eval_value` renders the
    /// integer −5 as the bare numeral `-5`; the array-witness path's
    /// `format_array_point_value` renders the SAME value as `(- 5)`. Every
    /// consumer in this module compares keys as STRINGS, so one member
    /// appeared as two cells: the carrier printed `{-5}` while the cell count —
    /// and therefore `(get-value ((set.card s)))` — said 2. The two-sided
    /// consequence was a wrong `sat` (model smaller than its own cardinality)
    /// and a spurious `unknown` (`(- 1) ∈ s ∧ |s| = 1` counted 2 members and
    /// failed closed).
    ///
    /// One value therefore gets exactly ONE key: every key this module writes
    /// or reads is routed through here first. The chosen dialect is the
    /// sort-directed one the array-witness printer already uses — negative Int
    /// `(- 5)`, Real `(- (/ 5 2))` / `5.0`, BitVec `#x…` — which is also the
    /// spelling the theory extractors already put in `stores`, so no existing
    /// key changes meaning. `None` for a value/sort with no canonical scalar
    /// spelling here (Fp, Seq, algebraic); callers then keep the raw key, which
    /// is no worse than before.
    fn set_index_key_for_value(&self, value: &EvalValue, index_sort: &Sort) -> Option<String> {
        match value {
            EvalValue::Rational(r) => Some(match index_sort {
                Sort::Real => format_rational(r),
                _ => format_bigint(r.numer()),
            }),
            EvalValue::Bool(b) => Some(if *b { "true" } else { "false" }.to_string()),
            EvalValue::BitVec { value, width } => Some(format_bitvec(value, *width)),
            EvalValue::String(s) => Some(string_literal(s)),
            EvalValue::Element(elem) => Some(format_model_atom(index_sort, elem)),
            _ => None,
        }
    }

    /// Canonical key for the membership index `idx` under `model`, or `None`
    /// when the index has no concrete model value (nothing to key a cell with).
    fn set_index_key(&self, model: &Model, idx: TermId) -> Option<String> {
        let value = self.evaluate_term(model, idx);
        if matches!(value, EvalValue::Unknown) {
            return None;
        }
        self.set_index_key_for_value(&value, self.ctx.terms.sort(idx))
    }

    /// Re-spell a store key some OTHER producer wrote into this module's
    /// canonical dialect, so string comparison is value comparison.
    ///
    /// An unparseable or exotic key is returned verbatim: it then still
    /// compares equal only to itself, exactly as before.
    fn canonical_set_index_key(&self, raw: &str, index_sort: &Option<Sort>) -> String {
        let Some(sort) = index_sort.as_ref() else {
            return raw.to_string();
        };
        let parsed = self.parse_model_value_string(raw, index_sort);
        self.set_index_key_for_value(&parsed, sort)
            .unwrap_or_else(|| raw.to_string())
    }

    /// The canonical (key, value) cells of `var`'s printed interpretation, with
    /// duplicate spellings of one index collapsed (first/authoritative wins).
    fn canonical_interp_cells(&self, model: &Model, var: TermId) -> Vec<(String, String)> {
        let Some(interp) = model
            .array_model
            .as_ref()
            .and_then(|am| am.array_values.get(&var))
        else {
            return Vec::new();
        };
        let mut out: Vec<(String, String)> = Vec::new();
        for (key, value) in &interp.stores {
            let key = self.canonical_set_index_key(key, &interp.index_sort);
            if out.iter().any(|(k, _)| *k == key) {
                continue;
            }
            out.push((key, value.clone()));
        }
        out
    }

    /// Make the printed model of every finite-set carrier a real witness.
    ///
    /// Two passes:
    /// 1. [`materialize_set_membership_witnesses`](Self::materialize_set_membership_witnesses)
    ///    — pin every membership atom's Boolean value as an explicit store
    ///    entry, so get-model and get-value agree on membership.
    /// 2. [`materialize_set_cardinality_witnesses`](Self::materialize_set_cardinality_witnesses)
    ///    — make the carrier exhibit exactly the cardinality the model assigns
    ///    to its `set.card` term.
    ///
    /// Returns `false` when a valid witness could not be constructed; the
    /// caller then degrades `sat` to `unknown` rather than print an invalid
    /// model.
    pub(in crate::executor) fn materialize_set_witnesses(&mut self) -> bool {
        self.materialize_set_membership_witnesses();
        self.materialize_set_cardinality_witnesses()
    }

    /// Build/augment `ArrayInterpretation`s for finite-set carriers so the
    /// printed model agrees with `get-value` on every membership atom.
    ///
    /// Never fails closed: the values it records are exactly the ones the model
    /// already reports for the membership selects, so it cannot introduce an
    /// inconsistency. The surrounding pipeline still re-validates the model
    /// afterward.
    ///
    /// Only set-carrier array variables (`(Array T Bool)`) that participate in
    /// at least one membership read are touched; all other arrays and theory
    /// values are left untouched.
    fn materialize_set_membership_witnesses(&mut self) -> bool {
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
            // them up front, in the canonical spelling — a differently-spelled
            // duplicate of an existing key is the negative-element
            // double-count bug (#set-card-neg-double-count).
            let existing_keys: HashSet<String> = self
                .last_model
                .as_ref()
                .map(|m| {
                    self.canonical_interp_cells(m, set_var)
                        .into_iter()
                        .map(|(k, _)| k)
                        .collect()
                })
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
                //
                // No concrete index value: cannot key a store entry; leave it
                // to the const-array default (sound — no concrete membership to
                // materialize).
                let Some(key) = self.set_index_key(model, idx) else {
                    continue;
                };

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

    /// The membership index of `atom`, when `atom` is itself a membership read
    /// against `set_var`.
    fn index_of_read(&self, atom: TermId, set_var: TermId) -> Option<TermId> {
        self.records
            .iter()
            .find(|(s, _, read)| *s == set_var && *read == atom)
            .map(|(_, idx, _)| *idx)
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

// ---------------------------------------------------------------------------
// Cardinality witnesses (#set-card-model-witness)
// ---------------------------------------------------------------------------

impl Executor {
    /// Read the set carrier `array` **exactly as the model prints it**: the
    /// membership of every index not listed explicitly (`default`), plus the
    /// explicitly-listed cells in first-occurrence order (which is what
    /// read-over-write and the array-model lookup both use).
    ///
    /// Returns `None` (fail-closed, never a guess) when the carrier has no
    /// structural reading under this model: a base variable with no
    /// `ArrayInterpretation` or a non-Boolean default, a store index or stored
    /// value that does not evaluate, an opaque set-valued application, or a
    /// cyclic term.
    fn set_model_reading(
        &self,
        model: &Model,
        array: TermId,
    ) -> Option<(bool, Vec<(String, bool)>)> {
        // (index key, membership) in first-occurrence order.
        let mut cells: Vec<(String, bool)> = Vec::new();
        let push_cell = |cells: &mut Vec<(String, bool)>, key: String, member: bool| {
            if !cells.iter().any(|(k, _)| *k == key) {
                cells.push((key, member));
            }
        };

        let mut cur = array;
        let mut visited: HashSet<TermId> = HashSet::default();
        let default = loop {
            if !visited.insert(cur) {
                // Cyclic term structure: no finite reading.
                return None;
            }
            match self.ctx.terms.get(cur) {
                TermData::App(sym, args) if sym.name() == "store" && args.len() == 3 => {
                    let key = self.set_index_key(model, args[1])?;
                    let member = match self.evaluate_term(model, args[2]) {
                        EvalValue::Bool(b) => b,
                        _ => return None,
                    };
                    push_cell(&mut cells, key, member);
                    cur = args[0];
                }
                TermData::App(sym, args) if sym.name() == "const-array" && args.len() == 1 => {
                    match self.evaluate_term(model, args[0]) {
                        EvalValue::Bool(b) => break b,
                        _ => return None,
                    }
                }
                TermData::Var(_, _) => {
                    let interp = model.array_model.as_ref()?.array_values.get(&cur)?;
                    let default = match interp.default.as_deref() {
                        Some("true") => true,
                        Some("false") => false,
                        _ => return None,
                    };
                    // Canonical keys: two spellings of one index must count as
                    // ONE cell (#set-card-neg-double-count).
                    for (key, value) in self.canonical_interp_cells(model, cur) {
                        let member = match value.as_str() {
                            "true" => true,
                            "false" => false,
                            _ => return None,
                        };
                        push_cell(&mut cells, key, member);
                    }
                    break default;
                }
                // Anything else (an opaque set-valued application, a lambda
                // carrier, an ite over arrays) has no structural reading here.
                _ => return None,
            }
        };

        Some((default, cells))
    }

    /// Count the members of the set carrier `array` **as the model prints it**.
    ///
    /// This is the model-side meaning of `set.card`, and it is what both
    /// `(get-value ((set.card s)))` and model validation use — so the printed
    /// carrier and the reported cardinality cannot disagree.
    ///
    /// `None` (fail-closed) when the carrier has no structural reading, or when
    /// its default membership is `true`: `((as const ..) true)` is the universal
    /// set, infinite over an infinite index sort, and AY carries no domain-size
    /// fact for the finite ones.
    pub(super) fn set_card_model_count(&self, model: &Model, array: TermId) -> Option<BigInt> {
        let (default, cells) = self.set_model_reading(model, array)?;
        if default {
            return None;
        }
        Some(BigInt::from(cells.iter().filter(|(_, m)| *m).count()))
    }

    /// Whether `sub ⊆ sup` holds under the model as printed, or `None` when the
    /// question is not decidable from the printed carriers (either has no
    /// structural reading, or `sub` is co-finite while `sup` is finite — that
    /// needs a domain-size fact AY does not carry).
    fn subset_holds_in_model(&self, model: &Model, sub: TermId, sup: TermId) -> Option<bool> {
        let (sub_default, sub_cells) = self.set_model_reading(model, sub)?;
        let (sup_default, sup_cells) = self.set_model_reading(model, sup)?;
        if sub_default && !sup_default {
            // `sub` holds every index it does not list; `sup` holds only the
            // ones it does. Over an INFINITE index sort there is always such an
            // index, so the subset definitively fails. Over a finite one it
            // fails as soon as some index of the domain is unlisted by both.
            match self.index_sort_is_infinite(sub) {
                Some(true) => return Some(false),
                Some(false) => {
                    let mut listed: Vec<&String> = sub_cells.iter().map(|(k, _)| k).collect();
                    for (k, _) in &sup_cells {
                        if !listed.contains(&k) {
                            listed.push(k);
                        }
                    }
                    match self.index_domain_size(sub) {
                        Some(size) if BigInt::from(listed.len()) < size => return Some(false),
                        Some(_) => {}
                        None => return None,
                    }
                }
                None => return None,
            }
        }
        let member_of = |cells: &[(String, bool)], key: &str, default: bool| -> bool {
            cells
                .iter()
                .find(|(k, _)| k == key)
                .map_or(default, |(_, m)| *m)
        };
        // Explicit members of `sub` must be members of `sup`.
        for (key, member) in &sub_cells {
            if *member && !member_of(&sup_cells, key, sup_default) {
                return Some(false);
            }
        }
        if sub_default {
            // `sub` also contains every index `sup` lists as a non-member,
            // unless `sub` itself lists it as a non-member.
            for (key, member) in &sup_cells {
                if !*member && member_of(&sub_cells, key, true) {
                    return Some(false);
                }
            }
        }
        // Unlisted indices: either `sub` excludes them, or `sup_default` holds.
        Some(true)
    }

    /// Whether the index sort of the set carrier `array` is infinite
    /// (`Some(true)`), finite (`Some(false)`), or not classifiable here
    /// (`None` — an uninterpreted or datatype domain).
    fn index_sort_is_infinite(&self, array: TermId) -> Option<bool> {
        match self.ctx.terms.sort(array).array_index()? {
            Sort::Int | Sort::Real | Sort::String => Some(true),
            Sort::Bool | Sort::BitVec(_) => Some(false),
            _ => None,
        }
    }

    /// The number of values in the index sort of the set carrier `array`, when
    /// that sort is finite and small enough to reason about.
    fn index_domain_size(&self, array: TermId) -> Option<BigInt> {
        match self.ctx.terms.sort(array).array_index()? {
            Sort::Bool => Some(BigInt::from(2u32)),
            Sort::BitVec(bv) => Some(BigInt::from(2u32).pow(bv.width)),
            _ => None,
        }
    }

    /// Top-level `set.subset` assertions the printed model definitively
    /// violates, as `(sub, sup, expected_truth)`.
    fn violated_subset_assertions(&self) -> Vec<(TermId, TermId, bool)> {
        let Some(model) = self.last_model.as_ref() else {
            return Vec::new();
        };
        let mut out = Vec::new();
        for &assertion in &self.ctx.assertions {
            let (atom, expected) = match self.ctx.terms.get(assertion) {
                TermData::Not(inner) => (*inner, false),
                _ => (assertion, true),
            };
            let TermData::App(sym, args) = self.ctx.terms.get(atom) else {
                continue;
            };
            if sym.name() != ay_set::OP_SUBSET || args.len() != 2 {
                continue;
            }
            if let Some(holds) = self.subset_holds_in_model(model, args[0], args[1]) {
                if holds != expected {
                    out.push((args[0], args[1], expected));
                }
            }
        }
        out
    }

    /// Re-check — and where possible repair — every top-level `set.subset`
    /// assertion against the carriers as just materialized.
    ///
    /// Shrinking a carrier to its exact cardinality can invalidate a subset atom
    /// that the don't-care universal default happened to satisfy (e.g.
    /// `t ⊆ s ∧ |s| = 1`, where `t` is printed as the universal set and `s` is
    /// now the one-element witness). `set.subset` is an opaque predicate to the
    /// evaluator, so ordinary model validation would not notice.
    ///
    /// The repair is a model-completion choice, not a guess: a carrier whose
    /// membership is *entirely* pinned by explicit cells has a free default, and
    /// picking `false` for the subset side is the choice that keeps the atom
    /// true. It is only applied to a carrier that occurs in no set-sorted
    /// equality (where flipping the default could break the other side) and
    /// whose every membership probe is already pinned.
    ///
    /// Returns `false` when a violation remains, and the caller fails closed.
    fn repair_and_check_set_subset_assertions(&mut self) -> bool {
        for _ in 0..4 {
            let violated = self.violated_subset_assertions();
            if violated.is_empty() {
                return true;
            }
            let mut changed = false;
            for (sub, _sup, expected) in violated {
                // Only a positively-asserted subset can be repaired by shrinking
                // its left side; a negated one needs a witness, not a smaller set.
                if !expected {
                    continue;
                }
                if self.is_set_carrier_var(sub)
                    && self.set_carrier_default_is_true(sub)
                    && self.set_carrier_membership_fully_pinned(sub)
                    && !self.set_var_in_any_set_equality(sub)
                {
                    self.force_set_carrier_default_false(sub);
                    changed = true;
                }
            }
            if !changed {
                return false;
            }
        }
        self.violated_subset_assertions().is_empty()
    }

    /// Whether the model prints `var` with the universal (`true`) default.
    fn set_carrier_default_is_true(&self, var: TermId) -> bool {
        self.last_model
            .as_ref()
            .and_then(|m| m.array_model.as_ref())
            .and_then(|am| am.array_values.get(&var))
            .and_then(|i| i.default.as_deref())
            == Some("true")
    }

    /// Whether every membership probe against `var` in the assertions resolves
    /// to a concrete index that the model already pins with an explicit cell —
    /// the precondition for choosing `var`'s default freely.
    fn set_carrier_membership_fully_pinned(&self, var: TermId) -> bool {
        let Some(model) = self.last_model.as_ref() else {
            return false;
        };
        let keys: Vec<String> = self
            .canonical_interp_cells(model, var)
            .into_iter()
            .map(|(k, _)| k)
            .collect();
        let reads = self.collect_set_membership_reads();
        for (idx, _read) in reads.reads_for(var) {
            let Some(key) = self.set_index_key(model, idx) else {
                return false;
            };
            if !keys.contains(&key) {
                return false;
            }
        }
        true
    }

    /// Whether `var` occurs in any asserted set-sorted equality (either
    /// polarity, either side). Such a carrier's default is tied to the other
    /// side and must not be flipped independently.
    fn set_var_in_any_set_equality(&self, var: TermId) -> bool {
        let mut stack: Vec<TermId> = self.ctx.assertions.clone();
        let mut visited: HashSet<TermId> = HashSet::default();
        while let Some(t) = stack.pop() {
            if !visited.insert(t) {
                continue;
            }
            match self.ctx.terms.get(t) {
                TermData::App(sym, args) => {
                    if sym.name() == "="
                        && args.len() == 2
                        && (args[0] == var || args[1] == var)
                        && self.ctx.terms.sort(args[0]).is_array()
                    {
                        return true;
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
        false
    }

    /// Commit `default = false` for `var`'s printed interpretation.
    fn force_set_carrier_default_false(&mut self, var: TermId) {
        if let Some(interp) = self
            .last_model
            .as_mut()
            .and_then(|m| m.array_model.as_mut())
            .and_then(|am| am.array_values.get_mut(&var))
        {
            interp.default = Some("false".to_string());
        }
    }

    /// Make every set carrier whose `set.card` the model pins to a concrete `k`
    /// actually exhibit `k` distinct members.
    ///
    /// Without this a free `(Set Int)` variable constrained only by
    /// `(= 1 (set.card s))` printed as `((as const (Array Int Bool)) false)` —
    /// the EMPTY set — while `(get-value ((set.card s)))` answered `1`: a `sat`
    /// whose own model falsifies the assertion. Membership atoms alone cannot
    /// fix it, because a bare cardinality constraint probes no membership.
    ///
    /// Returns `false` when no valid witness can be constructed, so the caller
    /// degrades `sat` to `unknown` (sound and incomplete) instead of printing an
    /// invalid model.
    fn materialize_set_cardinality_witnesses(&mut self) -> bool {
        if self.last_model.is_none() {
            return true;
        }
        let classes = self.set_carrier_equality_classes();
        if classes.is_empty() {
            return true;
        }
        let mut committed = false;
        for class in classes {
            match self.plan_set_cardinality(&class) {
                SetCardPlan::Skip => {}
                SetCardPlan::FailClosed => return false,
                SetCardPlan::Fix { cells, index_sort } => {
                    self.commit_set_cardinality(&class, &index_sort, &cells);
                    committed = true;
                }
            }
        }
        // Pinning a carrier to its exact size can break a `set.subset` atom that
        // the don't-care universal default satisfied. `set.subset` is opaque to
        // the evaluator, so nothing downstream would catch it — check it here.
        !committed || self.repair_and_check_set_subset_assertions()
    }

    /// Group the set-carrier variables that carry a `set.card` term into
    /// equivalence classes joined by asserted set equalities `(= a b)` over two
    /// set-carrier variables.
    ///
    /// Equated carriers must print the SAME set, so a cardinality witness has to
    /// be committed to the whole class at once — materializing `s = {0}` while
    /// leaving `t` empty under an asserted `(= s t)` would just trade one
    /// invalid model for another.
    fn set_carrier_equality_classes(&self) -> Vec<Vec<TermId>> {
        let card_vars = self.collect_set_card_carrier_vars();
        if card_vars.is_empty() {
            return Vec::new();
        }
        // Seed one class per card-constrained carrier, then merge on equalities.
        let mut classes: Vec<Vec<TermId>> = card_vars.iter().map(|&v| vec![v]).collect();
        // Equality atoms asserted NEGATIVELY at the top level (`(not (= s t))`)
        // state that the two carriers are DIFFERENT. Merging on those forced
        // one shared witness onto both and falsified the disequality — the
        // committed model then failed validation and a satisfiable query
        // answered `unknown` (#set-card-equality-polarity, the class-merge
        // twin of the `set_var_equated_to_expression` hole).
        let refuted: HashSet<TermId> = self
            .top_level_literals()
            .into_iter()
            .filter(|(_, polarity)| !polarity)
            .map(|(atom, _)| atom)
            .collect();
        let mut stack: Vec<TermId> = self.ctx.assertions.clone();
        let mut visited: HashSet<TermId> = HashSet::default();
        let mut pairs: Vec<(TermId, TermId)> = Vec::new();
        while let Some(t) = stack.pop() {
            if !visited.insert(t) {
                continue;
            }
            match self.ctx.terms.get(t) {
                TermData::App(sym, args) => {
                    if sym.name() == "="
                        && args.len() == 2
                        && self.is_set_carrier_var(args[0])
                        && self.is_set_carrier_var(args[1])
                        && args[0] != args[1]
                        && !refuted.contains(&t)
                        && !self.set_equality_refuted_by_model(t)
                    {
                        pairs.push((args[0], args[1]));
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
        // NOTE: this still merges on an occurrence of `(= a b)` nested inside a
        // disjunction whose truth the model leaves undetermined. That direction
        // is conservative — one shared set is the stricter witness — as long as
        // the equality is not actually REFUTED, which the filter above ensures.
        for (a, b) in pairs {
            let ia = classes.iter().position(|c| c.contains(&a));
            let ib = classes.iter().position(|c| c.contains(&b));
            match (ia, ib) {
                (Some(ia), Some(ib)) if ia != ib => {
                    let merged = classes.remove(ib.max(ia));
                    classes[ib.min(ia)].extend(merged);
                }
                (Some(ia), None) => classes[ia].push(b),
                (None, Some(ib)) => classes[ib].push(a),
                _ => {}
            }
        }
        for class in &mut classes {
            class.sort_unstable();
            class.dedup();
        }
        classes
    }

    /// Whether the model already decides the set equality `atom` to be FALSE.
    ///
    /// Such carriers must print DIFFERENT sets, so they may not be merged into
    /// one cardinality-witness class.
    fn set_equality_refuted_by_model(&self, atom: TermId) -> bool {
        let Some(model) = self.last_model.as_ref() else {
            return false;
        };
        matches!(self.evaluate_term(model, atom), EvalValue::Bool(false))
    }

    /// Every set-carrier VARIABLE that appears as the argument of a `set.card`
    /// application in the assertions (deduplicated, DAG order).
    fn collect_set_card_carrier_vars(&self) -> Vec<TermId> {
        let mut out: Vec<TermId> = Vec::new();
        let mut seen: HashSet<TermId> = HashSet::default();
        let mut stack: Vec<TermId> = self.ctx.assertions.clone();
        let mut visited: HashSet<TermId> = HashSet::default();
        while let Some(t) = stack.pop() {
            if !visited.insert(t) {
                continue;
            }
            match self.ctx.terms.get(t) {
                TermData::App(sym, args) => {
                    if sym.name() == OP_CARD
                        && args.len() == 1
                        && self.is_set_carrier_var(args[0])
                        && seen.insert(args[0])
                    {
                        out.push(args[0]);
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
        out
    }

    /// Decide what (if anything) has to be added to the carriers of one
    /// equivalence class so their printed size matches the cardinality the
    /// solver assigned.
    fn plan_set_cardinality(&mut self, class: &[TermId]) -> SetCardPlan {
        let Some(model) = self.last_model.as_ref() else {
            return SetCardPlan::Skip;
        };
        let Some(&first) = class.first() else {
            return SetCardPlan::Skip;
        };
        let Some(index_sort) = self.ctx.terms.sort(first).array_index().cloned() else {
            return SetCardPlan::Skip;
        };

        // The cardinality the SOLVER assigned. Read through the opaque-UF path
        // on purpose: `evaluate_term` now DERIVES `set.card` from the printed
        // carrier, which is exactly the number we are about to make true — using
        // it here would be circular and would enforce nothing.
        let mut target: Option<BigInt> = None;
        for &var in class {
            let Some(card_term) = self.existing_card_term(var) else {
                continue;
            };
            let TermData::App(card_symbol, _) = self.ctx.terms.get(card_term) else {
                continue;
            };
            let assigned =
                self.evaluate_uninterpreted_app(model, card_symbol, &[var], &Sort::Int, card_term);
            let EvalValue::Rational(ref r) = assigned else {
                continue;
            };
            if !r.is_integer() {
                return SetCardPlan::FailClosed;
            }
            let k = r.to_integer();
            if k.is_negative() {
                // `card >= 0` is asserted for every card term, so this cannot
                // come from a consistent model. Refuse to print one.
                return SetCardPlan::FailClosed;
            }
            match target {
                // Equated carriers with disagreeing cardinalities: the model is
                // self-contradictory, so there is no witness to print.
                Some(ref prev) if *prev != k => return SetCardPlan::FailClosed,
                Some(_) => {}
                None => target = Some(k),
            }
        }
        let Some(target) = target else {
            // No concrete cardinality pinned — nothing to enforce.
            return SetCardPlan::Skip;
        };
        let Some(target) = target.to_usize() else {
            return SetCardPlan::FailClosed;
        };

        // Two attempts. The first keeps the solver's DON'T-CARE membership
        // choices (a `(select s e)` the model assigned inside a theory axiom
        // rather than at the top level) so the printed witness stays as close
        // to the found model as possible. When those choices leave no witness
        // — `s ⊆ {1} ∧ |s| = 1` with the axiom probe `1 ∉ s` assigned false —
        // the second attempt drops them: they are not entailed by any
        // assertion, and every candidate is re-validated against the full
        // assertion set anyway, so overriding one can only lose an already
        // lost answer.
        for honor_preferences in [true, false] {
            match self.plan_set_cardinality_for_target(
                model,
                class,
                &index_sort,
                target,
                honor_preferences,
            ) {
                SetCardPlan::FailClosed if honor_preferences => continue,
                plan => return plan,
            }
        }
        SetCardPlan::FailClosed
    }

    /// One attempt of [`Self::plan_set_cardinality`] at a fixed `target`.
    fn plan_set_cardinality_for_target(
        &self,
        model: &Model,
        class: &[TermId],
        index_sort: &Sort,
        target: usize,
        honor_preferences: bool,
    ) -> SetCardPlan {
        let index_sort = index_sort.clone();
        // What the query ENTAILS about this class's membership. Collected from
        // the top-level positive atoms only (#set-card-witness-constraints):
        // membership atoms, a defining equality, and `set.subset` bounds. The
        // witness is then built to satisfy them instead of inheriting whatever
        // don't-care cells model completion happened to leave behind — those
        // cells made `|s| = 1 ∧ s ≠ {2}` print `s = {2}` and fail closed.
        let Some(constraints) = self.set_class_witness_constraints(model, class, honor_preferences)
        else {
            return SetCardPlan::FailClosed;
        };

        // Exact sets an asserted DISEQUALITY forbids the witness from being.
        // Checked at every `Fix` exit below (#set-card-diseq-witness).
        let forbidden = self.set_class_forbidden_witnesses(model, class);

        if constraints.opaque_definition {
            // The definition is not readable here, so the committed cells are
            // the only witness available: accept it when it already has the
            // required size, otherwise fail closed. Inventing or dropping a
            // member would falsify the defining equality.
            let mut pinned: Vec<(String, String)> = Vec::new();
            for &var in class {
                for (key, value) in self.canonical_interp_cells(model, var) {
                    match pinned.iter().find(|(k, _)| *k == key) {
                        Some((_, prev)) if *prev != value => return SetCardPlan::FailClosed,
                        Some(_) => {}
                        None => pinned.push((key, value)),
                    }
                }
            }
            if pinned.iter().filter(|(_, v)| v == "true").count() != target {
                return SetCardPlan::FailClosed;
            }
            if Self::witness_is_forbidden(&forbidden, &pinned) {
                return SetCardPlan::FailClosed;
            }
            return SetCardPlan::Fix {
                cells: pinned,
                index_sort,
            };
        }

        if let Some(allowed) = constraints.allowed.as_ref() {
            if constraints.must_in.iter().any(|k| !allowed.contains(k)) {
                // A forced member is outside the asserted upper bound: the
                // assignment is self-contradictory, so there is no witness.
                return SetCardPlan::FailClosed;
            }
        }

        let members = constraints.must_in.len();
        if members > target {
            // More distinct members are already forced than the cardinality
            // allows — no witness exists for this assignment.
            return SetCardPlan::FailClosed;
        }
        let needed = target - members;
        if needed > MAX_MATERIALIZED_SET_ELEMENTS {
            return SetCardPlan::FailClosed;
        }

        let fresh = match constraints.allowed.as_ref() {
            // Bounded above: the padding elements have to come FROM the bound.
            Some(allowed) => {
                let pool: Vec<String> = allowed
                    .iter()
                    .filter(|k| {
                        !constraints.must_in.contains(k) && !constraints.must_out.contains(k)
                    })
                    .cloned()
                    .collect();
                if pool.len() < needed {
                    return SetCardPlan::FailClosed;
                }
                pool[..needed].to_vec()
            }
            // Unbounded: draw from the index sort, avoiding both the forced
            // keys and every index value the assertions actually mention. An
            // element the formula never names cannot make an asserted atom
            // change truth value except through `set.card` itself, which is
            // exactly what we are fixing; picking a mentioned one is what made
            // `|s| = 1 ∧ s ≠ {2}` land on `{2}`. If the sort is too small to
            // avoid the mentioned values (Bool, a narrow BitVec), fall back to
            // the forced keys alone and let validation judge the result.
            None => {
                let mut avoid = constraints.must_in.clone();
                avoid.extend(constraints.must_out.iter().cloned());
                let mut avoid_mentioned = avoid.clone();
                for key in self.assertion_index_keys(model, &index_sort) {
                    if !avoid_mentioned.contains(&key) {
                        avoid_mentioned.push(key);
                    }
                }
                match self
                    .fresh_set_element_keys(&index_sort, needed, &avoid_mentioned)
                    .or_else(|| self.fresh_set_element_keys(&index_sort, needed, &avoid))
                {
                    Some(fresh) => fresh,
                    None => return SetCardPlan::FailClosed,
                }
            }
        };

        // The witness: exactly the forced members plus the padding, with every
        // forced NON-member spelled out so `get-value` reads it from the same
        // cells `get-model` prints.
        let mut cells: Vec<(String, String)> = Vec::new();
        for key in constraints.must_in {
            cells.push((key, "true".to_string()));
        }
        for key in fresh {
            if !cells.iter().any(|(k, _)| *k == key) {
                cells.push((key, "true".to_string()));
            }
        }
        for key in constraints.must_out {
            if !cells.iter().any(|(k, _)| *k == key) {
                cells.push((key, "false".to_string()));
            }
        }
        // A candidate that IS one of the forbidden sets falsifies its own
        // assertion. Under `honor_preferences` this is the common case and it is
        // repairable: the offending member came from a NON-entailed `(select s
        // e)` probe (a don't-care the theory happened to assign), so the caller's
        // retry drops those preferences and pads with an element the assertions
        // never mention. Reporting `FailClosed` here is what routes it there.
        // If the preference-free attempt still lands on a forbidden set the
        // members are entailed, there is no witness to print, and `FailClosed`
        // is the honest answer (#set-card-diseq-witness).
        if Self::witness_is_forbidden(&forbidden, &cells) {
            return SetCardPlan::FailClosed;
        }
        SetCardPlan::Fix { cells, index_sort }
    }

    /// The top-level asserted LITERALS of the query, as `(atom, polarity)`.
    ///
    /// Only these are entailed. The former `set_var_equated_to_expression`
    /// walked the WHOLE assertion DAG and matched `(= var expr)` under any
    /// polarity, so a DISequality `(not (= s (set.singleton 2)))` was read as a
    /// DEFINING equality and blocked the witness — `|s| = 1 ∧ s ≠ {2}` failed
    /// closed although `s = {0}` witnesses it
    /// (#set-card-equality-polarity). Conjunction is transparent (every
    /// conjunct of an asserted `and` is itself asserted) and `not` flips the
    /// polarity; a disjunction, an `ite` condition and a quantifier body are
    /// NOT entailed and are not descended into.
    fn top_level_literals(&self) -> Vec<(TermId, bool)> {
        let mut out: Vec<(TermId, bool)> = Vec::new();
        let mut stack: Vec<(TermId, bool)> =
            self.ctx.assertions.iter().map(|&a| (a, true)).collect();
        let mut visited: HashSet<(TermId, bool)> = HashSet::default();
        while let Some((t, polarity)) = stack.pop() {
            if !visited.insert((t, polarity)) {
                continue;
            }
            match self.ctx.terms.get(t) {
                TermData::Not(inner) => stack.push((*inner, !polarity)),
                TermData::App(sym, args) if sym.name() == "and" && polarity => {
                    for &arg in args {
                        stack.push((arg, true));
                    }
                }
                _ => out.push((t, polarity)),
            }
        }
        out
    }

    /// The exact member-key sets the printed witness may NOT equal, read off the
    /// top-level NEGATED set equalities `(not (= class_var expr))`.
    ///
    /// This is the WITNESS-CONTENT twin of the two `#set-card-equality-polarity`
    /// holes already fixed in this module (the defining-equality read in
    /// [`Self::set_class_witness_constraints`] and the class merge in
    /// [`Self::set_carrier_equality_classes`]). Both of those stopped a
    /// disequality from being MISREAD as an equality; neither made the witness
    /// actually RESPECT it. A disequality is a real constraint on the printed
    /// set: `|s| = 1 ∧ s ≠ {2}` is satisfiable, but only by a witness that is
    /// not `{2}`.
    ///
    /// Only a `expr` with a readable FINITE reading (`default = false`)
    /// constrains anything: a committed witness always has the `false` default,
    /// so it can never equal a co-finite set, and an unreadable `expr` yields no
    /// key set to compare against. Set-carrier VARIABLES are excluded on the
    /// same ground as the positive case — their own interpretation may not have
    /// been materialized yet, so reading one here would be order-dependent.
    /// Those stay covered by the (fail-closed) model gate.
    fn set_class_forbidden_witnesses(&self, model: &Model, class: &[TermId]) -> Vec<Vec<String>> {
        let mut out: Vec<Vec<String>> = Vec::new();
        for (atom, polarity) in self.top_level_literals() {
            if polarity {
                continue;
            }
            let TermData::App(sym, args) = self.ctx.terms.get(atom) else {
                continue;
            };
            if sym.name() != "=" || args.len() != 2 || !self.ctx.terms.sort(args[0]).is_array() {
                continue;
            }
            for (var, expr) in [(args[0], args[1]), (args[1], args[0])] {
                if !class.contains(&var) || self.is_set_carrier_var(expr) {
                    continue;
                }
                if let Some((false, cells)) = self.set_model_reading(model, expr) {
                    let mut members: Vec<String> = cells
                        .into_iter()
                        .filter(|(_, m)| *m)
                        .map(|(k, _)| k)
                        .collect();
                    members.sort();
                    members.dedup();
                    if !out.contains(&members) {
                        out.push(members);
                    }
                }
            }
        }
        out
    }

    /// Whether the witness `cells` denote exactly one of the `forbidden` sets,
    /// i.e. the plan would print a set an asserted disequality rules out.
    fn witness_is_forbidden(forbidden: &[Vec<String>], cells: &[(String, String)]) -> bool {
        if forbidden.is_empty() {
            return false;
        }
        let mut members: Vec<String> = cells
            .iter()
            .filter(|(_, v)| v == "true")
            .map(|(k, _)| k.clone())
            .collect();
        members.sort();
        members.dedup();
        forbidden.iter().any(|f| *f == members)
    }

    /// Gather what the query entails about the membership of one set-carrier
    /// equivalence class. `None` means the entailed facts are contradictory —
    /// the caller fails closed.
    ///
    /// `honor_preferences` additionally freezes the membership values the model
    /// assigned to `(select s e)` reads that are NOT top-level literals (theory
    /// axiom probes). Those are don't-cares, so the caller re-plans without
    /// them when they admit no witness.
    fn set_class_witness_constraints(
        &self,
        model: &Model,
        class: &[TermId],
        honor_preferences: bool,
    ) -> Option<SetWitnessConstraints> {
        let mut cons = SetWitnessConstraints::default();
        let literals = self.top_level_literals();

        // (1) Membership literals asserted at the top level are entailed: the
        // witness MUST exhibit them.
        let reads = self.collect_set_membership_reads();
        for (atom, polarity) in &literals {
            for &var in class {
                let Some(idx) = reads.index_of_read(*atom, var) else {
                    continue;
                };
                let key = self.set_index_key(model, idx)?;
                if *polarity {
                    cons.require_in(key)?;
                } else {
                    cons.require_out(key)?;
                }
            }
        }

        // (2) Top-level positive structural atoms.
        for (atom, polarity) in &literals {
            if !polarity {
                continue;
            }
            let TermData::App(sym, args) = self.ctx.terms.get(*atom) else {
                continue;
            };
            let name = sym.name();
            if name == "=" && args.len() == 2 && self.ctx.terms.sort(args[0]).is_array() {
                for (var, expr) in [(args[0], args[1]), (args[1], args[0])] {
                    if !class.contains(&var) || self.is_set_carrier_var(expr) {
                        continue;
                    }
                    // A defining equality fixes the set exactly.
                    match self.set_model_reading(model, expr) {
                        Some((false, cells)) => {
                            let members: Vec<String> = cells
                                .iter()
                                .filter(|(_, m)| *m)
                                .map(|(k, _)| k.clone())
                                .collect();
                            for key in &members {
                                cons.require_in(key.clone())?;
                            }
                            cons.restrict_allowed(members);
                        }
                        // Co-finite or unreadable definition: keep whatever the
                        // model committed, unchanged.
                        _ => cons.opaque_definition = true,
                    }
                }
                continue;
            }
            if name == ay_set::OP_SUBSET && args.len() == 2 {
                let (sub, sup) = (args[0], args[1]);
                // `sub ⊆ class` — every member of `sub` must be in the witness.
                if class.contains(&sup) && sub != sup {
                    if let Some((false, cells)) = self.set_model_reading(model, sub) {
                        for (key, member) in cells {
                            if member {
                                cons.require_in(key)?;
                            }
                        }
                    }
                }
                // `class ⊆ sup` — the witness may only use `sup`'s members.
                if class.contains(&sub) && !class.contains(&sup) {
                    match self.set_model_reading(model, sup) {
                        Some((false, cells)) => cons.restrict_allowed(
                            cells
                                .into_iter()
                                .filter(|(_, m)| *m)
                                .map(|(k, _)| k)
                                .collect(),
                        ),
                        Some((true, cells)) => {
                            for (key, member) in cells {
                                if !member {
                                    cons.require_out(key)?;
                                }
                            }
                        }
                        None => {}
                    }
                }
            }
        }

        // (3) Non-entailed membership probes: keep the model's own choice when
        // it is compatible, so the printed witness stays close to the model the
        // search actually found.
        if honor_preferences {
            for &var in class {
                for (idx, read) in reads.reads_for(var) {
                    let Some(key) = self.set_index_key(model, idx) else {
                        continue;
                    };
                    if cons.must_in.contains(&key) || cons.must_out.contains(&key) {
                        continue;
                    }
                    match self.evaluate_term(model, read) {
                        EvalValue::Bool(true) => {
                            if cons
                                .allowed
                                .as_ref()
                                .is_none_or(|allowed| allowed.contains(&key))
                            {
                                cons.require_in(key)?;
                            }
                        }
                        EvalValue::Bool(false) => cons.require_out(key)?,
                        _ => {}
                    }
                }
            }
        }

        Some(cons)
    }

    /// Canonical keys of every index value the ASSERTIONS mention: the model
    /// values of the index-sorted constants and variables occurring in them.
    ///
    /// Padding a cardinality witness with one of these can flip an asserted
    /// atom (`s ≠ {2}` is falsified by choosing 2); an unmentioned element
    /// cannot. Bounded by the assertion DAG, and only constants/variables are
    /// evaluated, so this is cheap.
    fn assertion_index_keys(&self, model: &Model, index_sort: &Sort) -> Vec<String> {
        let mut out: Vec<String> = Vec::new();
        let mut stack: Vec<TermId> = self.ctx.assertions.clone();
        let mut visited: HashSet<TermId> = HashSet::default();
        while let Some(t) = stack.pop() {
            if !visited.insert(t) {
                continue;
            }
            if matches!(
                self.ctx.terms.get(t),
                TermData::Const(_) | TermData::Var(_, _)
            ) && self.ctx.terms.sort(t) == index_sort
            {
                if let Some(key) = self.set_index_key(model, t) {
                    if !out.contains(&key) {
                        out.push(key);
                    }
                }
            }
            match self.ctx.terms.get(t) {
                TermData::App(_, args) => {
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
        out
    }

    /// The interned `(set.card v)` term, if the assertions contain one.
    ///
    /// Looked up rather than constructed: a fresh term would have no solver
    /// assignment to read.
    fn existing_card_term(&self, var: TermId) -> Option<TermId> {
        self.ctx.terms.find_app_named(OP_CARD, &[var])
    }

    /// Produce `needed` fresh index keys of `index_sort` that avoid every key in
    /// `used`, formatted exactly the way the array model stores and the model
    /// printer spell index values.
    ///
    /// `None` when the index sort has no enumerable concrete constants (an
    /// uninterpreted or datatype domain — AY has no committed universe to draw a
    /// distinct element from) or is too small to supply `needed` fresh values.
    /// The caller then fails closed.
    fn fresh_set_element_keys(
        &self,
        index_sort: &Sort,
        needed: usize,
        used: &[String],
    ) -> Option<Vec<String>> {
        let mut out: Vec<String> = Vec::with_capacity(needed);
        let mut candidate: u64 = 0;
        while out.len() < needed {
            if candidate >= FRESH_ELEMENT_SEARCH_LIMIT {
                return None;
            }
            let key = self.index_constant_key(index_sort, candidate)?;
            candidate += 1;
            if used.iter().any(|u| *u == key) || out.contains(&key) {
                continue;
            }
            out.push(key);
        }
        Some(out)
    }

    /// The printed spelling of the `n`-th concrete constant of `index_sort`, or
    /// `None` when the sort has no `n`-th constant (domain exhausted) or no
    /// enumerable constants at all.
    fn index_constant_key(&self, index_sort: &Sort, n: u64) -> Option<String> {
        let value = match index_sort {
            Sort::Int => EvalValue::Rational(num_rational::BigRational::from(BigInt::from(n))),
            Sort::Real => EvalValue::Rational(num_rational::BigRational::from(BigInt::from(n))),
            Sort::Bool => {
                if n > 1 {
                    return None;
                }
                EvalValue::Bool(n == 1)
            }
            Sort::BitVec(bv) => {
                let width = bv.width;
                if width < 64 && n >= (1u64 << width) {
                    return None;
                }
                EvalValue::BitVec {
                    value: BigInt::from(n),
                    width,
                }
            }
            // Uninterpreted / datatype / array / string / sequence index sorts:
            // AY carries no enumerable universe of distinct constants for them
            // here, so no witness element can be invented honestly.
            _ => return None,
        };
        self.set_index_key_for_value(&value, index_sort)
    }

    /// Commit the cardinality witness: every carrier in the class gets the
    /// `false` default (a FINITE set — this is what turns a co-finite
    /// `((as const ..) true)` carrier into a printable one) and the fresh
    /// members, on top of the membership entries already pinned.
    fn commit_set_cardinality(
        &mut self,
        class: &[TermId],
        index_sort: &Sort,
        cells: &[(String, String)],
    ) {
        let Some(model) = self.last_model.as_mut() else {
            return;
        };
        let array_model = model.array_model.get_or_insert_with(ArrayModel::default);
        // Every carrier in the class denotes the same set, so they all get the
        // same cells — in the canonical key spelling, so one index can never
        // occupy two cells (#set-card-neg-double-count).
        let shared: Vec<(String, String)> = cells.to_vec();
        for &var in class {
            let interp =
                array_model
                    .array_values
                    .entry(var)
                    .or_insert_with(|| ArrayInterpretation {
                        default: None,
                        stores: Vec::new(),
                        index_sort: Some(index_sort.clone()),
                        element_sort: Some(Sort::Bool),
                    });
            interp.default = Some("false".to_string());
            interp.stores = shared.clone();
            if interp.index_sort.is_none() {
                interp.index_sort = Some(index_sort.clone());
            }
            if interp.element_sort.is_none() {
                interp.element_sort = Some(Sort::Bool);
            }
        }
    }
}
