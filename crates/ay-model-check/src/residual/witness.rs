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
    confirm_completed_model, value_eq, ArrayValue, GateVerdict, ModelValue, ModelView,
    ProjectionLookupError, ProvenUnconstrainedKind,
};

use super::element_dt;

/// Maximum formula/pin requirements admitted by one residual witness.
pub(crate) const MAX_WITNESS_ENTRIES: usize = 512;

/// Maximum semantic index comparisons while forming `(class, index)` groups.
const MAX_INDEX_COMPARISONS: usize = 131_072;

/// Maximum value nodes inspected or synthesized for one completed witness.
const MAX_WITNESS_VALUE_WORK: usize = 8192;

/// Maximum nesting depth of a synthesized canonical inhabitant.
const MAX_WITNESS_VALUE_DEPTH: usize = 128;

/// Which slot of an array element an entry constrains.
#[derive(Clone, PartialEq, Eq)]
pub(super) enum Slot {
    /// The whole element: `(= <ground> (select a i))` or a pinned select.
    Whole,
    /// One selector field: `(= <ground> (fld (select a i)))` or a pinned
    /// selector-chain read.
    Field(String),
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
        self.index_comparisons = next;
        next <= MAX_INDEX_COMPARISONS
    }

    fn spend_value_node(&mut self) -> bool {
        let Some(next) = self.value_work.checked_add(1) else {
            return false;
        };
        self.value_work = next;
        next <= MAX_WITNESS_VALUE_WORK
    }

    /// Account the complete shape before any model-provided value is copied
    /// into the witness. The walk is iterative so hostile nesting cannot grow
    /// the native stack before the independent replay gets a chance to refuse.
    fn account_value(&mut self, value: &ModelValue) -> bool {
        let mut stack = vec![value];
        while let Some(current) = stack.pop() {
            if !self.spend_value_node() {
                return false;
            }
            match current {
                ModelValue::Array(array) => {
                    stack.push(&array.default);
                    for (index, element) in &array.store {
                        stack.push(index);
                        stack.push(element);
                    }
                }
                ModelValue::Seq(elements) => stack.extend(elements),
                ModelValue::Datatype { args, .. } => stack.extend(args),
                _ => {}
            }
        }
        true
    }
}

/// Read-only overlay used only for the final replay. Every member of one alias
/// class resolves to the exact same materialized array; every other model
/// surface is delegated unchanged to the solver-provided view.
struct CompletedModel<'a> {
    base: &'a dyn ModelView,
    member_roots: HashMap<TermId, TermId>,
    arrays: HashMap<TermId, ModelValue>,
}

impl ModelView for CompletedModel<'_> {
    fn leaf_value(&self, term: TermId) -> Option<ModelValue> {
        match self.member_roots.get(&term) {
            Some(root) => self.arrays.get(root).cloned(),
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
pub(super) fn materialize_and_replay(
    terms: &TermStore,
    model: &dyn ModelView,
    assertions: &[TermId],
    resolve: &DtResolve<'_>,
    member_roots: HashMap<TermId, TermId>,
    entries: Vec<Entry>,
) -> bool {
    let mut budget = WitnessBudget::default();
    for entry in &entries {
        if !budget.account_value(&entry.index) || !budget.account_value(&entry.value) {
            return false;
        }
    }

    let Some(mut class_arrays) = build_class_arrays(terms, resolve, &member_roots, &mut budget)
    else {
        return false;
    };
    if !populate_class_arrays(
        terms,
        resolve,
        &member_roots,
        &entries,
        &mut class_arrays,
        &mut budget,
    ) {
        return false;
    }

    let arrays = class_arrays
        .into_iter()
        .map(|(root, array)| (root, ModelValue::Array(Box::new(array))))
        .collect();
    let completed = CompletedModel {
        base: model,
        member_roots,
        arrays,
    };
    matches!(
        confirm_completed_model(terms, &completed, assertions),
        GateVerdict::ConfirmedSat
    )
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
        element_dt(&array_sort.element_sort, resolve)?;
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
        let Some((whole, fields)) = reconcile_group(&group) else {
            return false;
        };
        let Sort::Array(array_sort) = terms.sort(root) else {
            return false;
        };
        let Some(datatype) = element_dt(&array_sort.element_sort, resolve) else {
            return false;
        };
        let Some(element) = materialize_element(&datatype, whole, &fields, resolve, budget) else {
            return false;
        };
        let Some(array) = arrays.get_mut(&root) else {
            return false;
        };
        array.store.push((first.index.clone(), element));
    }
    true
}

fn gather_index_group<'a>(
    root: TermId,
    first: &'a Entry,
    keyed: &[(TermId, &'a Entry)],
    done: &mut [bool],
    budget: &mut WitnessBudget,
) -> Option<Vec<&'a Entry>> {
    let mut group = Vec::new();
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
                done[candidate_index] = true;
            }
            Ok(false) => {}
            Err(_) => return None,
        }
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

    if let Some(datatype) = element_dt(sort, resolve) {
        if active_datatypes.iter().any(|name| name == &datatype.name) {
            return None;
        }
        active_datatypes.push(datatype.name.clone());
        let mut result = None;
        for constructor in &datatype.constructors {
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
        Sort::BitVec(bitvec) => Some(ModelValue::bitvec(BigInt::from(0), bitvec.width)),
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
            if (2..=64).contains(exponent_bits) && (2..=65).contains(significand_bits) =>
        {
            Some(ModelValue::FloatingPoint {
                sign: false,
                exponent: 0,
                significand: 0,
                exponent_bits: *exponent_bits,
                significand_bits: *significand_bits,
            })
        }
        Sort::Uninterpreted(name) => Some(ModelValue::Uninterpreted(format!(
            "@ay-residual-inhabitant:uninterpreted:{name}"
        ))),
        Sort::Datatype(_) => None,
        Sort::Seq(_) => Some(ModelValue::Seq(Vec::new())),
        Sort::Char => Some(ModelValue::Int(BigInt::from(0))),
        Sort::FiniteDomain(_, size) if *size > 0 => Some(ModelValue::Int(BigInt::from(0))),
        Sort::TypeVar(name) => Some(ModelValue::Uninterpreted(format!(
            "@ay-residual-inhabitant:type-var:{name}"
        ))),
        _ => None,
    }
}
