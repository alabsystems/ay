// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Materialized witnesses for the free datatype-element array residual.

use std::collections::HashMap;

use ay_core::{DatatypeSort, Sort, TermId, TermStore};
use num_bigint::BigInt;
use num_rational::BigRational;

use crate::dt_axiom::DtResolve;
use crate::{
    confirm_completed_model, value_eq, ArrayValue, Evaluator, GateVerdict, ModelValue, ModelView,
    ProjectionLookupError, ProvenUnconstrainedKind,
};

use super::path::metadata;
mod accounting;
mod completion;
mod requirements;
pub(super) use accounting::{account_entry_values, account_path_index};
pub use completion::{ArrayCompletion, CompletedArrayAssignment, ModelConfirmation};

/// Maximum formula/pin requirements admitted by one residual witness.
pub(crate) const MAX_WITNESS_ENTRIES: usize = 512;

/// Maximum semantic index comparisons across outer groups and inner arrays.
const MAX_INDEX_COMPARISONS: usize = 131_072;

/// Maximum value nodes inspected or synthesized for one completed witness.
pub(crate) const MAX_WITNESS_VALUE_WORK: usize = 8192;

/// Maximum nesting depth of a synthesized canonical inhabitant.
const MAX_WITNESS_VALUE_DEPTH: usize = 128;

/// Which slot of an array element an entry constrains.
#[derive(Clone)]
pub(super) enum Slot {
    /// The whole element: `(= <ground> (select a i))` or a pinned select.
    Whole,
    /// One selector field: `(= <ground> (fld (select a i)))` or a pinned
    /// selector-chain read.
    Field(String),
    /// Root-to-leaf selectors, authenticated at every original source step.
    Path(Vec<String>),
    /// Exact selector/index steps inside the selected outer datatype element.
    Access(Vec<AccessStep>),
}

/// One typed, source-authenticated step; index values come from the candidate
/// evaluator, never from an invented interpretation of an unpinned key.
#[derive(Clone)]
pub(super) enum AccessStep {
    Field(String),
    Index(ModelValue),
}

/// One entry of the joint constraint map: `(array, index-value, slot) ->
/// value`, from either a residual requirement or a pinned read.
pub(super) struct Entry {
    pub(super) array: TermId,
    pub(super) index: ModelValue,
    pub(super) slot: Slot,
    pub(super) value: ModelValue,
}

/// Shared, monotone work meter for materializing one witness.
#[derive(Default)]
struct WitnessBudget {
    index_comparisons: usize,
    value_work: usize,
}

impl WitnessBudget {
    fn compare_index(&mut self) -> bool {
        let Some(next) = self.index_comparisons.checked_add(1) else {
            return false;
        };
        if next > MAX_INDEX_COMPARISONS {
            return false;
        }
        self.index_comparisons = next;
        true
    }

    fn spend_value_node(&mut self) -> bool {
        self.spend_value_nodes(1)
    }

    fn spend_value_nodes(&mut self, amount: usize) -> bool {
        let Some(next) = self.value_work.checked_add(amount) else {
            return false;
        };
        if next > MAX_WITNESS_VALUE_WORK {
            return false;
        }
        self.value_work = next;
        true
    }

    fn pending_values_fit(&self, pending: usize, additional: usize) -> bool {
        self.value_work
            .checked_add(pending)
            .and_then(|count| count.checked_add(additional))
            .is_some_and(|count| count <= MAX_WITNESS_VALUE_WORK)
    }

    fn spend_scalar_payload(&mut self, value: &ModelValue) -> bool {
        let Some(payload_work) = scalar_payload_work(value) else {
            return false;
        };
        self.spend_value_nodes(payload_work)
    }

    /// Account the complete shape before any model-provided value is copied
    /// into the witness. The walk is iterative so hostile nesting cannot grow
    /// the native stack before the independent replay gets a chance to refuse.
    fn account_value(&mut self, value: &ModelValue) -> bool {
        let mut stack = vec![(value, 0usize)];
        while let Some((current, depth)) = stack.pop() {
            if depth > MAX_WITNESS_VALUE_DEPTH {
                return false;
            }
            if !self.spend_value_node() {
                return false;
            }
            if !self.spend_scalar_payload(current) {
                return false;
            }
            match current {
                ModelValue::Array(array) => {
                    let Some(child_depth) = depth.checked_add(1) else {
                        return false;
                    };
                    if child_depth > MAX_WITNESS_VALUE_DEPTH {
                        return false;
                    }
                    let Some(store_nodes) = array.store.len().checked_mul(2) else {
                        return false;
                    };
                    let Some(child_count) = store_nodes.checked_add(1) else {
                        return false;
                    };
                    if !self.pending_values_fit(stack.len(), child_count) {
                        return false;
                    }
                    stack.push((&array.default, child_depth));
                    for (index, element) in &array.store {
                        stack.push((index, child_depth));
                        stack.push((element, child_depth));
                    }
                }
                ModelValue::Seq(elements) if !elements.is_empty() => {
                    let Some(child_depth) = depth.checked_add(1) else {
                        return false;
                    };
                    if child_depth > MAX_WITNESS_VALUE_DEPTH {
                        return false;
                    }
                    if !self.pending_values_fit(stack.len(), elements.len()) {
                        return false;
                    }
                    stack.extend(elements.iter().map(|element| (element, child_depth)));
                }
                ModelValue::Datatype { args, .. } if !args.is_empty() => {
                    let Some(child_depth) = depth.checked_add(1) else {
                        return false;
                    };
                    if child_depth > MAX_WITNESS_VALUE_DEPTH {
                        return false;
                    }
                    if !self.pending_values_fit(stack.len(), args.len()) {
                        return false;
                    }
                    stack.extend(args.iter().map(|argument| (argument, child_depth)));
                }
                _ => {}
            }
        }
        true
    }
}

fn scalar_payload_work(value: &ModelValue) -> Option<usize> {
    fn bigint_bytes(value: &BigInt) -> Option<usize> {
        usize::try_from(value.bits().checked_add(7)? / 8).ok()
    }

    fn rational_bytes(value: &BigRational) -> Option<usize> {
        bigint_bytes(value.numer())?.checked_add(bigint_bytes(value.denom())?)
    }

    fn algebraic_bytes(value: &crate::algebraic::Algebraic) -> Option<usize> {
        let mut work = 0usize;
        for coefficient in value
            .minimal_polynomial()
            .iter()
            .chain(value.representation())
        {
            work = work
                .checked_add(1)?
                .checked_add(rational_bytes(coefficient)?)?;
        }
        let (lower, upper) = value.interval();
        for endpoint in [lower, upper] {
            work = work
                .checked_add(1)?
                .checked_add(rational_bytes(endpoint)?)?;
        }
        Some(work)
    }

    match value {
        ModelValue::Bool(_) | ModelValue::Array(_) | ModelValue::Seq(_) => Some(0),
        ModelValue::Int(value) => bigint_bytes(value),
        ModelValue::Real(value) => rational_bytes(value),
        ModelValue::BitVec { width, value } => {
            let width_bytes = usize::try_from((u64::from(*width).checked_add(7)?) / 8).ok()?;
            Some(width_bytes.max(bigint_bytes(value)?))
        }
        ModelValue::FloatingPoint {
            exponent_bits,
            significand_bits,
            ..
        } => {
            let total_bits = u64::from(*exponent_bits)
                .checked_add(u64::from(*significand_bits))?
                .checked_add(1)?;
            usize::try_from(total_bits.checked_add(7)? / 8).ok()
        }
        value @ ModelValue::FloatingPointExact { .. } => crate::fp_exact::bytes(value).ok(),
        ModelValue::Str(value) | ModelValue::Uninterpreted(value) => Some(value.len()),
        ModelValue::Algebraic(value) => algebraic_bytes(value),
        ModelValue::Datatype { ctor, .. } => Some(ctor.len()),
    }
}

/// Read-only overlay used only for the final replay. Every member of one alias
/// class resolves to the exact same materialized array; every other model
/// surface is delegated unchanged to the solver-provided view.
struct CompletedModel<'a> {
    base: &'a dyn ModelView,
    admission_refused: std::cell::Cell<bool>,
    member_roots: HashMap<TermId, TermId>,
    arrays: HashMap<TermId, ModelValue>,
}

impl ModelView for CompletedModel<'_> {
    fn has_evaluation_admission(&self) -> bool {
        self.base.has_evaluation_admission()
    }

    fn refuse_evaluation_work(&self, reason: &str) {
        self.admission_refused.set(true);
        self.base.refuse_evaluation_work(reason);
    }

    fn admit_evaluation_work(&self, work: usize, bytes: usize) -> Result<(), String> {
        if self.admission_refused.get() {
            return Err("completed-model payload admission previously refused".to_owned());
        }
        if !self.has_evaluation_admission() {
            return Ok(());
        }
        self.base
            .admit_evaluation_work(work, bytes)
            .map_err(|reason| {
                self.refuse_evaluation_work(&reason);
                reason
            })
    }

    fn exact_fp_interrupted(&self) -> bool {
        self.admission_refused.get() || self.base.exact_fp_interrupted()
    }

    fn charge_exact_fp_work(&self, amount: usize) -> Result<(), String> {
        if self.admission_refused.get() {
            return Err("completed-model exact FP admission previously refused".to_owned());
        }
        self.base.charge_exact_fp_work(amount).map_err(|reason| {
            self.refuse_evaluation_work(&reason);
            reason
        })
    }

    fn admit_exact_fp_work(&self, work: usize, bytes: usize) -> Result<(), String> {
        if self.admission_refused.get() {
            return Err("completed-model exact FP admission previously refused".to_owned());
        }
        self.base
            .admit_exact_fp_work(work, bytes)
            .map_err(|reason| {
                self.refuse_evaluation_work(&reason);
                reason
            })
    }

    fn leaf_value(&self, term: TermId) -> Option<ModelValue> {
        match self.member_roots.get(&term) {
            Some(root) => {
                let value = self.arrays.get(root)?;
                if self.has_evaluation_admission() {
                    if let Err(reason) = crate::admit_model_value_work(value, &mut |work, bytes| {
                        self.admit_evaluation_work(work, bytes)
                    }) {
                        self.refuse_evaluation_work(&reason);
                        return None;
                    }
                }
                Some(value.clone())
            }
            None => self.base.leaf_value(term),
        }
    }

    fn projection_argument(&self, term: TermId) -> Result<Option<usize>, ProjectionLookupError> {
        self.base.projection_argument(term)
    }

    fn datatype_def(&self, name: &str) -> Option<DatatypeSort> {
        self.base.datatype_def(name)
    }

    fn uf_app_value(&self, term: TermId) -> Option<ModelValue> {
        self.base.uf_app_value(term)
    }

    fn unconstrained_app_value(&self, term: TermId) -> Option<ModelValue> {
        self.base.unconstrained_app_value(term)
    }

    fn proven_unconstrained_app_value(
        &self,
        term: TermId,
        kind: ProvenUnconstrainedKind,
    ) -> Option<ModelValue> {
        self.base.proven_unconstrained_app_value(term, kind)
    }

    fn uf_app_value_at(&self, term: TermId, arguments: &[ModelValue]) -> Option<ModelValue> {
        self.base.uf_app_value_at(term, arguments)
    }

    fn array_select_value(&self, term: TermId) -> Option<ModelValue> {
        self.base.array_select_value(term)
    }
}

/// Materialize one concrete `(default, finite-store)` value per alias class and
/// grant it authority only after a fresh residual-disabled replay succeeds.
pub(super) fn materialize_and_replay<'a>(
    terms: &'a TermStore,
    model: &'a dyn ModelView,
    evaluator: &Evaluator<'_>,
    assertions: &'a [TermId],
    resolve: &DtResolve<'_>,
    member_roots: HashMap<TermId, TermId>,
    entries: Vec<Entry>,
    entry_value_work: usize,
) -> Option<ArrayCompletion<'a>> {
    if entry_value_work > MAX_WITNESS_VALUE_WORK {
        return None;
    }
    let mut budget = WitnessBudget {
        index_comparisons: 0,
        value_work: entry_value_work,
    };

    let Some(mut class_arrays) = build_class_arrays(terms, resolve, &member_roots, &mut budget)
    else {
        return None;
    };
    if !populate_class_arrays(
        terms,
        resolve,
        &member_roots,
        &entries,
        &mut class_arrays,
        &mut budget,
    ) {
        return None;
    }

    let arrays = class_arrays
        .into_iter()
        .map(|(root, array)| (root, ModelValue::Array(Box::new(array))))
        .collect();
    for (&root, array) in &arrays {
        if evaluator
            .ensure_value_inhabits_sort(array, terms.sort(root))
            .is_err()
        {
            return None;
        }
    }
    let completed = CompletedModel {
        base: model,
        admission_refused: std::cell::Cell::new(false),
        member_roots,
        arrays,
    };
    if !matches!(
        confirm_completed_model(terms, &completed, assertions),
        GateVerdict::ConfirmedSat
    ) {
        return None;
    }
    Some(ArrayCompletion::new(terms, assertions, completed, budget))
}

fn build_class_arrays(
    terms: &TermStore,
    resolve: &DtResolve<'_>,
    member_roots: &HashMap<TermId, TermId>,
    budget: &mut WitnessBudget,
) -> Option<HashMap<TermId, ArrayValue>> {
    let mut arrays = HashMap::new();
    let mut members: Vec<(TermId, TermId)> = member_roots
        .iter()
        .map(|(&member, &root)| (member, root))
        .collect();
    members.sort_unstable();
    for (member, root) in members {
        if arrays.contains_key(&root) {
            continue;
        }
        let Sort::Array(array_sort) = terms.sort(member) else {
            return None;
        };
        metadata::datatype(&array_sort.element_sort, resolve, &mut |n| {
            budget.spend_value_nodes(n)
        })?;
        let default = canonical_inhabitant(
            &array_sort.element_sort,
            resolve,
            &mut Vec::new(),
            budget,
            0,
        )?;
        if !budget.spend_value_node() {
            return None;
        }
        arrays.insert(
            root,
            ArrayValue {
                default,
                store: Vec::new(),
            },
        );
    }
    Some(arrays)
}

fn populate_class_arrays(
    terms: &TermStore,
    resolve: &DtResolve<'_>,
    member_roots: &HashMap<TermId, TermId>,
    entries: &[Entry],
    arrays: &mut HashMap<TermId, ArrayValue>,
    budget: &mut WitnessBudget,
) -> bool {
    let mut keyed = Vec::with_capacity(entries.len());
    for entry in entries {
        let Some(&root) = member_roots.get(&entry.array) else {
            return false;
        };
        keyed.push((root, entry));
    }
    let mut done = vec![false; keyed.len()];
    for group_index in 0..keyed.len() {
        if done[group_index] {
            continue;
        }
        let (root, first) = keyed[group_index];
        let Some(group) = gather_index_group(root, first, &keyed, &mut done, budget) else {
            return false;
        };
        let Sort::Array(array_sort) = terms.sort(root) else {
            return false;
        };
        let element = if group
            .iter()
            .any(|entry| matches!(entry.slot, Slot::Path(_) | Slot::Access(_)))
        {
            requirements::materialize(&array_sort.element_sort, &group, resolve, budget)
        } else {
            legacy_element(&array_sort.element_sort, &group, resolve, budget)
        };
        let Some(element) = element else {
            return false;
        };
        let Some(array) = arrays.get_mut(&root) else {
            return false;
        };
        array.store.push((first.index.clone(), element));
    }
    true
}

fn legacy_element(
    sort: &Sort,
    group: &[&Entry],
    resolve: &DtResolve<'_>,
    budget: &mut WitnessBudget,
) -> Option<ModelValue> {
    let (whole, fields) = reconcile_group(group)?;
    let datatype = metadata::datatype(sort, resolve, &mut |n| budget.spend_value_nodes(n))?;
    materialize_element(&datatype, whole, &fields, resolve, budget)
}

fn gather_index_group<'a>(
    root: TermId,
    first: &'a Entry,
    keyed: &[(TermId, &'a Entry)],
    done: &mut [bool],
    budget: &mut WitnessBudget,
) -> Option<Vec<&'a Entry>> {
    let mut group = Vec::new();
    let mut matched_indices = Vec::new();
    for (candidate_index, &(candidate_root, candidate)) in keyed.iter().enumerate() {
        if candidate_root != root {
            continue;
        }
        if !budget.compare_index() {
            return None;
        }
        match value_eq(&first.index, &candidate.index) {
            Ok(true) => {
                group.push(candidate);
                matched_indices.push(candidate_index);
            }
            Ok(false) => {}
            Err(_) => return None,
        }
    }
    for candidate_index in matched_indices {
        done[candidate_index] = true;
    }
    Some(group)
}

fn reconcile_group<'a>(
    group: &[&'a Entry],
) -> Option<(Option<&'a ModelValue>, Vec<(&'a str, &'a ModelValue)>)> {
    let mut whole: Option<&'a ModelValue> = None;
    let mut fields: Vec<(&'a str, &'a ModelValue)> = Vec::new();
    for entry in group {
        match &entry.slot {
            Slot::Whole => match whole {
                None => whole = Some(&entry.value),
                Some(previous) if matches!(value_eq(previous, &entry.value), Ok(true)) => {}
                Some(_) => return None,
            },
            Slot::Field(field) => {
                if let Some((_, previous)) =
                    fields.iter().find(|(candidate, _)| *candidate == field)
                {
                    if !matches!(value_eq(previous, &entry.value), Ok(true)) {
                        return None;
                    }
                } else {
                    fields.push((field.as_str(), &entry.value));
                }
            }
            Slot::Path(_) | Slot::Access(_) => return None,
        }
    }
    Some((whole, fields))
}

/// Turn the consistent requirements for one `(class, index)` into a concrete
/// datatype element.
fn materialize_element(
    datatype: &DatatypeSort,
    whole: Option<&ModelValue>,
    fields: &[(&str, &ModelValue)],
    resolve: &DtResolve<'_>,
    budget: &mut WitnessBudget,
) -> Option<ModelValue> {
    if let Some(value) = whole {
        if fields.is_empty() {
            return Some(value.clone());
        }
        let ModelValue::Datatype { ctor, args } = value else {
            return None;
        };
        let constructor = datatype
            .constructors
            .iter()
            .find(|candidate| candidate.name == *ctor)?;
        for (name, expected) in fields {
            let position = constructor
                .fields
                .iter()
                .position(|field| field.name == *name)?;
            let actual = args.get(position)?;
            if !matches!(value_eq(actual, expected), Ok(true)) {
                return None;
            }
        }
        return Some(value.clone());
    }

    for constructor in &datatype.constructors {
        if !fields
            .iter()
            .all(|(name, _)| constructor.fields.iter().any(|field| field.name == *name))
        {
            continue;
        }
        if !budget.spend_value_node() {
            return None;
        }
        if !budget.spend_value_nodes(constructor.fields.len())
            || !budget.spend_value_nodes(constructor.name.len())
        {
            return None;
        }
        let mut active_datatypes = vec![datatype.name.clone()];
        let mut args = Vec::with_capacity(constructor.fields.len());
        let mut complete = true;
        for field in &constructor.fields {
            if let Some((_, value)) = fields.iter().find(|(name, _)| *name == field.name) {
                args.push((*value).clone());
                continue;
            }
            let Some(value) =
                canonical_inhabitant(&field.sort, resolve, &mut active_datatypes, budget, 1)
            else {
                complete = false;
                break;
            };
            args.push(value);
        }
        if complete {
            return Some(ModelValue::Datatype {
                ctor: constructor.name.clone(),
                args,
            });
        }
    }
    None
}

/// Construct one deterministic, well-founded inhabitant of `sort` under hard
/// depth/work bounds. Unsupported carriers and recursive cycles without a base
/// case fail closed.
fn canonical_inhabitant(
    sort: &Sort,
    resolve: &DtResolve<'_>,
    active_datatypes: &mut Vec<String>,
    budget: &mut WitnessBudget,
    depth: usize,
) -> Option<ModelValue> {
    if depth > MAX_WITNESS_VALUE_DEPTH || !budget.spend_value_node() {
        return None;
    }

    if let Some(datatype) =
        metadata::datatype_shape(sort, resolve, &mut |n| budget.spend_value_nodes(n))?
    {
        if active_datatypes.iter().any(|name| name == &datatype.name) {
            return None;
        }
        active_datatypes.push(datatype.name.clone());
        let mut result = None;
        for constructor in &datatype.constructors {
            if !budget.spend_value_nodes(constructor.fields.len())
                || !budget.spend_value_nodes(constructor.name.len())
            {
                active_datatypes.pop();
                return None;
            }
            let mut args = Vec::with_capacity(constructor.fields.len());
            let mut complete = true;
            for field in &constructor.fields {
                let Some(value) =
                    canonical_inhabitant(&field.sort, resolve, active_datatypes, budget, depth + 1)
                else {
                    complete = false;
                    break;
                };
                args.push(value);
            }
            if complete {
                result = Some(ModelValue::Datatype {
                    ctor: constructor.name.clone(),
                    args,
                });
                break;
            }
        }
        active_datatypes.pop();
        return result;
    }

    match sort {
        Sort::Bool => Some(ModelValue::Bool(false)),
        Sort::Int => Some(ModelValue::Int(BigInt::from(0))),
        Sort::Real => Some(ModelValue::Real(BigRational::from_integer(BigInt::from(0)))),
        Sort::BitVec(bitvec) => {
            let width_bytes =
                usize::try_from((u64::from(bitvec.width).checked_add(7)?) / 8).ok()?;
            budget
                .spend_value_nodes(width_bytes)
                .then(|| ModelValue::bitvec(BigInt::from(0), bitvec.width))
        }
        Sort::Array(array) => {
            let default = canonical_inhabitant(
                &array.element_sort,
                resolve,
                active_datatypes,
                budget,
                depth + 1,
            )?;
            Some(ModelValue::Array(Box::new(ArrayValue {
                default,
                store: Vec::new(),
            })))
        }
        Sort::String => Some(ModelValue::Str(String::new())),
        Sort::RegLan => None,
        Sort::FloatingPoint(exponent_bits, significand_bits)
            if *exponent_bits >= 2 && *significand_bits >= 2 =>
        {
            if !crate::fp::data_format_supported(*exponent_bits, *significand_bits) {
                let value = ModelValue::floating_point_exact(
                    false,
                    0u8.into(),
                    0u8.into(),
                    *exponent_bits,
                    *significand_bits,
                )?;
                return budget
                    .spend_value_nodes(crate::fp_exact::bytes(&value).ok()?)
                    .then_some(value);
            }
            let total_bits = u64::from(*exponent_bits)
                .checked_add(u64::from(*significand_bits))?
                .checked_add(1)?;
            let payload_bytes = usize::try_from(total_bits.checked_add(7)? / 8).ok()?;
            budget
                .spend_value_nodes(payload_bytes)
                .then_some(ModelValue::FloatingPoint {
                    sign: false,
                    exponent: 0,
                    significand: 0,
                    exponent_bits: *exponent_bits,
                    significand_bits: *significand_bits,
                })
        }
        Sort::Uninterpreted(name) => {
            const PREFIX: &str = "@ay-residual-inhabitant:uninterpreted:";
            let bytes = PREFIX.len().checked_add(name.len())?;
            budget
                .spend_value_nodes(bytes)
                .then(|| ModelValue::Uninterpreted(format!("{PREFIX}{name}")))
        }
        Sort::Datatype(_) => None,
        Sort::Seq(_) => Some(ModelValue::Seq(Vec::new())),
        Sort::Char => Some(ModelValue::Int(BigInt::from(0))),
        Sort::FiniteDomain(_, size) if *size > 0 => Some(ModelValue::Int(BigInt::from(0))),
        Sort::TypeVar(name) => {
            const PREFIX: &str = "@ay-residual-inhabitant:type-var:";
            let bytes = PREFIX.len().checked_add(name.len())?;
            budget
                .spend_value_nodes(bytes)
                .then(|| ModelValue::Uninterpreted(format!("{PREFIX}{name}")))
        }
        _ => None,
    }
}

#[cfg(test)]
mod bound_tests {
    use super::*;

    #[test]
    fn index_grouping_exhaustion_leaves_completion_state_unchanged() {
        let mut terms = TermStore::new();
        let root = terms.mk_var("array", Sort::array(Sort::Int, Sort::Bool));
        let first = Entry {
            array: root,
            index: ModelValue::Int(BigInt::from(0)),
            slot: Slot::Whole,
            value: ModelValue::Bool(false),
        };
        let second = Entry {
            array: root,
            index: ModelValue::Int(BigInt::from(1)),
            slot: Slot::Whole,
            value: ModelValue::Bool(true),
        };
        let keyed = vec![(root, &first), (root, &second)];
        let mut done = vec![false; keyed.len()];
        let mut budget = WitnessBudget {
            index_comparisons: MAX_INDEX_COMPARISONS - 1,
            value_work: 0,
        };

        assert!(gather_index_group(root, &first, &keyed, &mut done, &mut budget).is_none());
        assert_eq!(budget.index_comparisons, MAX_INDEX_COMPARISONS);
        assert_eq!(done, vec![false; keyed.len()]);
    }

    #[test]
    fn model_value_accounting_fails_closed_at_the_work_cap() {
        let value = ModelValue::Datatype {
            ctor: "pair".to_string(),
            args: vec![ModelValue::Bool(false), ModelValue::Bool(true)],
        };
        let mut budget = WitnessBudget {
            index_comparisons: 0,
            value_work: MAX_WITNESS_VALUE_WORK - 1,
        };

        assert!(!budget.account_value(&value));
        assert_eq!(budget.value_work, MAX_WITNESS_VALUE_WORK);
    }

    #[test]
    fn model_value_accounting_rejects_hostile_width_before_enqueuing_it() {
        let value = ModelValue::Datatype {
            ctor: "wide".to_string(),
            args: vec![ModelValue::Bool(false); MAX_WITNESS_VALUE_WORK],
        };
        let mut budget = WitnessBudget::default();

        assert!(!budget.account_value(&value));
        assert_eq!(budget.value_work, 1 + "wide".len());
    }

    #[test]
    fn oversized_single_node_payloads_fail_before_entry_retention() {
        let oversized_integer = BigInt::from(1u8) << (MAX_WITNESS_VALUE_WORK * 8);
        let oversized_text = "x".repeat(MAX_WITNESS_VALUE_WORK);
        let values = vec![
            ModelValue::Int(oversized_integer.clone()),
            ModelValue::Real(BigRational::from_integer(oversized_integer)),
            ModelValue::BitVec {
                width: u32::try_from(MAX_WITNESS_VALUE_WORK * 8 + 1).expect("test width fits u32"),
                value: BigInt::from(0),
            },
            ModelValue::Str(oversized_text.clone()),
            // Uninterpreted values are the gate's opaque-token carrier.
            ModelValue::Uninterpreted(oversized_text.clone()),
            ModelValue::Datatype {
                ctor: oversized_text,
                args: Vec::new(),
            },
        ];

        for value in values {
            let mut retained_work = 0;
            assert!(!account_entry_values(
                &mut retained_work,
                &ModelValue::Bool(false),
                &value,
                &Slot::Whole,
            ));
            assert_eq!(
                retained_work, 0,
                "a rejected scalar must not consume retained-entry capacity"
            );
        }
    }

    #[test]
    fn model_value_accounting_enforces_the_nested_depth_cap() {
        fn nested_sequence(depth: usize) -> ModelValue {
            let mut value = ModelValue::Bool(false);
            for _ in 0..depth {
                value = ModelValue::Seq(vec![value]);
            }
            value
        }

        let mut at_limit_budget = WitnessBudget::default();
        assert!(at_limit_budget.account_value(&nested_sequence(MAX_WITNESS_VALUE_DEPTH)));

        let mut over_limit_budget = WitnessBudget::default();
        assert!(!over_limit_budget.account_value(&nested_sequence(MAX_WITNESS_VALUE_DEPTH + 1)));
    }

    #[test]
    fn canonical_inhabitant_enforces_the_nested_value_depth_cap() {
        fn nested_array_sort(depth: usize) -> Sort {
            let mut sort = Sort::Bool;
            for _ in 0..depth {
                sort = Sort::array(Sort::Int, sort);
            }
            sort
        }

        let resolve = |_: &str| None;
        let mut at_limit_budget = WitnessBudget::default();
        assert!(canonical_inhabitant(
            &nested_array_sort(MAX_WITNESS_VALUE_DEPTH),
            &resolve,
            &mut Vec::new(),
            &mut at_limit_budget,
            0,
        )
        .is_some());

        let mut over_limit_budget = WitnessBudget::default();
        assert!(canonical_inhabitant(
            &nested_array_sort(MAX_WITNESS_VALUE_DEPTH + 1),
            &resolve,
            &mut Vec::new(),
            &mut over_limit_budget,
            0,
        )
        .is_none());
    }
}

#[cfg(test)]
mod evaluation_admission_tests {
    use super::*;
    use std::cell::Cell;

    #[test]
    fn completed_model_forwards_admission_and_debits_its_own_payload() {
        struct Owner {
            refused: Cell<bool>,
            calls: Cell<usize>,
        }
        impl ModelView for Owner {
            fn has_evaluation_admission(&self) -> bool {
                true
            }
            fn refuse_evaluation_work(&self, _: &str) {
                self.refused.set(true);
            }
            fn leaf_value(&self, _: TermId) -> Option<ModelValue> {
                None
            }
            fn admit_evaluation_work(&self, _: usize, bytes: usize) -> Result<(), String> {
                self.calls.set(self.calls.get() + 1);
                if self.refused.get() || bytes > 512 {
                    self.refused.set(true);
                    Err("owner payload limit".to_owned())
                } else {
                    Ok(())
                }
            }
        }
        let mut terms = TermStore::new();
        let term = terms.mk_var("array", Sort::array(Sort::Int, Sort::String));
        let owner = Owner {
            refused: Cell::new(false),
            calls: Cell::new(0),
        };
        let view = CompletedModel {
            base: &owner,
            admission_refused: Cell::new(false),
            member_roots: HashMap::from([(term, term)]),
            arrays: HashMap::from([(
                term,
                ModelValue::Array(Box::new(ArrayValue {
                    default: ModelValue::Str("x".repeat(4096)),
                    store: Vec::new(),
                })),
            )]),
        };
        assert!(matches!(
            Evaluator::new(&terms, &view).evaluate(term),
            crate::EvalOutcome::Unevaluable(_)
        ));
        assert!(owner.refused.get());
        assert!(owner.calls.get() > 1);
        assert!(view.admit_evaluation_work(0, 0).is_err());
    }
    #[test]
    fn completed_overlay_preserves_dedicated_fp_counter_without_generic_admission() {
        use std::cell::Cell;
        struct Owner {
            left: Cell<usize>,
            refused: Cell<bool>,
        }
        impl ModelView for Owner {
            fn leaf_value(&self, _: TermId) -> Option<ModelValue> {
                None
            }
            fn exact_fp_interrupted(&self) -> bool {
                self.refused.get()
            }
            fn charge_exact_fp_work(&self, amount: usize) -> Result<(), String> {
                if self.refused.get() {
                    return Err("original FP counter refused".into());
                }
                let Some(left) = self.left.get().checked_sub(amount) else {
                    self.refused.set(true);
                    return Err("original FP counter exhausted".into());
                };
                self.left.set(left);
                Ok(())
            }
        }
        let owner = Owner {
            left: Cell::new(4096),
            refused: Cell::new(false),
        };
        let mut terms = ay_core::TermStore::new();
        let root = terms.mk_var(
            "overlay_exact",
            ay_core::Sort::array(ay_core::Sort::Int, ay_core::Sort::FloatingPoint(8, 200)),
        );
        let zero = terms.mk_int(num_bigint::BigInt::from(0));
        let selected = terms.mk_app(
            ay_core::Symbol::named("select"),
            &[root, zero],
            ay_core::Sort::FloatingPoint(8, 200),
        );
        let value = ModelValue::floating_point_exact(
            false,
            127u32.into(),
            (num_bigint::BigUint::from(1u8) << 198usize) + 1u8,
            8,
            200,
        )
        .unwrap();
        let view = CompletedModel {
            base: &owner,
            admission_refused: Cell::new(false),
            member_roots: [(root, root)].into_iter().collect(),
            arrays: [(
                root,
                ModelValue::Array(Box::new(crate::ArrayValue {
                    default: value,
                    store: Vec::new(),
                })),
            )]
            .into_iter()
            .collect(),
        };
        assert!(
            !view.has_evaluation_admission(),
            "generic admission deliberately absent"
        );
        assert!(matches!(
            crate::evaluate_term(&terms, &view, root),
            crate::EvalOutcome::Value(_)
        ));
        assert_eq!(
            owner.left.get(),
            4096,
            "retained aggregate DATA consumes no FP field work"
        );
        let evaluator = crate::Evaluator::new(&terms, &view);
        assert!(matches!(
            evaluator.evaluate(root),
            crate::EvalOutcome::Value(_)
        ));
        assert!(matches!(
            evaluator.evaluate(selected),
            crate::EvalOutcome::Value(_)
        ));
        assert!(
            owner.left.get() < 4096,
            "actual select spent the base FP counter"
        );
        assert!(view.charge_exact_fp_work(4097).is_err());
        assert!(owner.exact_fp_interrupted());
        assert!(matches!(
            evaluator.evaluate(selected),
            crate::EvalOutcome::Unevaluable(_)
        ));
        let fresh = crate::Evaluator::new(&terms, &view);
        assert!(matches!(fresh.evaluate(root), crate::EvalOutcome::Value(_)));
        assert!(matches!(
            fresh.evaluate(selected),
            crate::EvalOutcome::Unevaluable(_)
        ));
    }
}
