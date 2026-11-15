// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Typed finite-array evidence normalization.

use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::{ArraySort, Sort};
use ay_model_check::{ArrayValue, ModelValue};
use num_bigint::BigInt;
use num_rational::BigRational;

use super::super::dt_construct::dt_canonical_string;
use super::super::rendered_dt_guard::RenderedDatatypeGuard;
use super::super::rendered_dt_limits::{
    model_value_work, SchemaSourceBudget, MAX_RENDERED_DT_BYTES, MAX_RENDERED_DT_DEPTH,
    MAX_RENDERED_DT_NODES,
};

const MAX_SEMANTIC_NORMALIZATION_WORK: usize = 4 * MAX_RENDERED_DT_BYTES;

#[derive(Clone, Default)]
pub(super) struct ArrayAccumulator {
    default: Option<ModelValue>,
    points: HashMap<ScalarValue, (ModelValue, ModelValue)>,
    observed: bool,
    work: SemanticNormalizationBudget,
}

impl ArrayAccumulator {
    pub(super) fn merge_point(&mut self, key: ModelValue, value: ModelValue) -> bool {
        if !self.work.charge_value(&key) {
            return false;
        }
        let Some(token) = scalar_value(&key) else {
            return false;
        };
        let Some(normalized) = normalize_datatype_array_value(&value, &mut self.work) else {
            return false;
        };
        match self.points.get(&token) {
            Some((_, current)) => {
                normalize_datatype_array_value(current, &mut self.work).as_ref()
                    == Some(&normalized)
            }
            None => {
                self.points.insert(token, (key, value));
                self.observed = true;
                true
            }
        }
    }

    /// Merge one authoritative/newest-first interpretation. Shadowed older
    /// entries are local representation history, not conflicting evidence.
    pub(super) fn merge_interpretation(
        &mut self,
        default: Option<ModelValue>,
        stores: Vec<(ModelValue, ModelValue)>,
    ) -> bool {
        let Some(default) = default else {
            return false;
        };
        if stores.len() > super::MAX_EXACT_ARRAY_FIELD_TERMS {
            return false;
        }
        let Some(normalized_default) = normalize_datatype_array_value(&default, &mut self.work)
        else {
            return false;
        };
        if self.default.as_ref().is_some_and(|current| {
            normalize_datatype_array_value(current, &mut self.work).as_ref()
                != Some(&normalized_default)
        }) {
            return false;
        }
        let mut local = HashMap::default();
        for (key, value) in stores {
            if !self.work.charge_value(&key) {
                return false;
            }
            let Some(token) = scalar_value(&key) else {
                return false;
            };
            let Some(normalized) = normalize_datatype_array_value(&value, &mut self.work) else {
                return false;
            };
            if !local.contains_key(&token) {
                local.insert(token, (key, value, normalized));
            }
        }
        if local.iter().any(|(token, (_, _, normalized))| {
            self.points.get(token).is_some_and(|(_, current)| {
                normalize_datatype_array_value(current, &mut self.work).as_ref() != Some(normalized)
            })
        }) {
            return false;
        }
        if self.default.is_none() {
            self.default = Some(default);
        }
        for (token, (key, value, _)) in local {
            self.points.entry(token).or_insert((key, value));
        }
        self.observed = true;
        true
    }

    pub(super) fn finish(mut self, element_sort: &Sort) -> Option<ModelValue> {
        if !self.observed {
            return None;
        }
        let default = self
            .default
            .take()
            .or_else(|| canonical_scalar_value(element_sort))?;
        // Keep the legacy deterministic printed-key order, while the map
        // itself identifies scalar keys semantically (including rationals).
        let mut points: Vec<_> = self
            .points
            .into_values()
            .map(|point| (dt_canonical_string(&point.0), point))
            .collect();
        points.sort_by(|(left, _), (right, _)| left.cmp(right));
        let store = points.into_iter().map(|(_, point)| point).collect();
        Some(ModelValue::Array(Box::new(ArrayValue { default, store })))
    }
}

fn canonical_scalar_value(sort: &Sort) -> Option<ModelValue> {
    match sort {
        Sort::Bool => Some(ModelValue::Bool(false)),
        Sort::Int => Some(ModelValue::Int(BigInt::from(0))),
        Sort::Real => Some(ModelValue::Real(BigRational::from_integer(BigInt::from(0)))),
        Sort::BitVec(bitvec) => Some(ModelValue::bitvec(BigInt::from(0), bitvec.width)),
        Sort::String => Some(ModelValue::Str(String::new())),
        _ => None,
    }
}

pub(super) fn same_value(left: &ModelValue, right: &ModelValue) -> bool {
    let mut budget = SemanticNormalizationBudget::new();
    match (
        normalize_datatype_array_value(left, &mut budget),
        normalize_datatype_array_value(right, &mut budget),
    ) {
        (Some(left), Some(right)) => left == right,
        _ => false,
    }
}

pub(super) fn typed_array_value(
    value: &ArrayValue,
    sort: &ArraySort,
    guard: &RenderedDatatypeGuard,
) -> bool {
    let mut schema = SchemaSourceBudget::new();
    aggregate_work(AggregateRoot::Array(value)).is_some()
        && schema.charge_array_sort(&sort.index_sort, &sort.element_sort)
        && typed_array_inner(value, sort, guard)
}

fn typed_scalar_value(value: &ModelValue, sort: &Sort) -> bool {
    match (value, sort) {
        (ModelValue::Bool(_), Sort::Bool)
        | (ModelValue::Int(_), Sort::Int)
        | (ModelValue::Str(_), Sort::String) => true,
        (ModelValue::Real(value), Sort::Real) => value.denom() > &BigInt::from(0),
        (ModelValue::BitVec { width, value }, Sort::BitVec(bitvec)) => {
            *width > 0
                && *width == bitvec.width
                && value.sign() != num_bigint::Sign::Minus
                && value.bits() <= u64::from(bitvec.width)
        }
        _ => false,
    }
}

pub(super) fn typed_datatype_array_value(
    root: &ModelValue,
    root_sort: &Sort,
    guard: &RenderedDatatypeGuard,
) -> bool {
    let mut schema = SchemaSourceBudget::new();
    aggregate_work(AggregateRoot::Value(root)).is_some()
        && schema.charge_sort(root_sort)
        && typed_value_inner(root, root_sort, guard)
}

// Both public entrypoints preflight the WHOLE value before this recursion.
// Child sorts come only from the bounded root descriptor or exact registry.
fn typed_value_inner(value: &ModelValue, sort: &Sort, guard: &RenderedDatatypeGuard) -> bool {
    match (value, sort) {
        (ModelValue::Datatype { ctor, args }, _) => {
            let Some((_, fields)) = guard.constructor(sort, ctor) else {
                return false;
            };
            fields.len() == args.len()
                && args
                    .iter()
                    .zip(fields)
                    .all(|(value, sort)| typed_value_inner(value, sort, guard))
        }
        (ModelValue::Array(array), Sort::Array(sort)) => typed_array_inner(array, sort, guard),
        _ => typed_scalar_value(value, sort),
    }
}

fn typed_array_inner(value: &ArrayValue, sort: &ArraySort, guard: &RenderedDatatypeGuard) -> bool {
    scalar_sort(&sort.index_sort)
        && typed_value_inner(&value.default, &sort.element_sort, guard)
        && value.store.iter().all(|(key, value)| {
            typed_scalar_value(key, &sort.index_sort)
                && typed_value_inner(value, &sort.element_sort, guard)
        })
}

fn scalar_sort(sort: &Sort) -> bool {
    matches!(sort, Sort::Bool | Sort::Int | Sort::Real | Sort::String)
        || matches!(sort, Sort::BitVec(width) if width.width > 0)
}

#[cfg(test)]
pub(super) fn same_array_value(left: &ArrayValue, right: &ArrayValue) -> bool {
    let mut budget = SemanticNormalizationBudget::new();
    let (Some(left), Some(right)) = (
        normalize_array_value(left, &mut budget),
        normalize_array_value(right, &mut budget),
    ) else {
        return false;
    };
    left == right
}

/// Compare two bounded, typed values in the concrete W6 fragment. Datatype
/// structure is exact; arrays are compared recursively so redundant
/// and shadowed stores do not create a second encoding of one model value.
#[cfg(test)]
pub(super) fn same_datatype_array_value(left: &ModelValue, right: &ModelValue) -> bool {
    same_value(left, right)
}

#[derive(Clone, Eq, Hash, Ord, PartialEq, PartialOrd)]
enum ScalarValue {
    Bool(bool),
    Int(BigInt),
    Real(BigRational),
    BitVec(u32, BigInt),
    Str(String),
}

fn scalar_value(value: &ModelValue) -> Option<ScalarValue> {
    match value {
        ModelValue::Bool(value) => Some(ScalarValue::Bool(*value)),
        ModelValue::Int(value) => Some(ScalarValue::Int(value.clone())),
        ModelValue::Real(value) if value.denom() > &BigInt::from(0) => {
            Some(ScalarValue::Real(value.clone()))
        }
        ModelValue::BitVec { width, value }
            if *width > 0
                && value.sign() != num_bigint::Sign::Minus
                && value.bits() <= u64::from(*width) =>
        {
            Some(ScalarValue::BitVec(*width, value.clone()))
        }
        ModelValue::Str(value) => Some(ScalarValue::Str(value.clone())),
        _ => None,
    }
}

#[derive(Clone)]
pub(in crate::executor::model) struct SemanticNormalizationBudget {
    work: usize,
    aggregate: Option<super::super::recovery_admission::RecoveryAdmission>,
}

impl Default for SemanticNormalizationBudget {
    fn default() -> Self {
        Self::new()
    }
}

impl SemanticNormalizationBudget {
    pub(in crate::executor::model) fn new() -> Self {
        Self {
            work: 0,
            aggregate: super::super::recovery_admission::RecoveryAdmission::current(),
        }
    }

    fn charge(&mut self, amount: usize) -> bool {
        if self
            .aggregate
            .as_ref()
            .is_some_and(|budget| !budget.pay(amount, amount))
        {
            return false;
        }
        match self.work.checked_add(amount) {
            Some(next) if next <= MAX_SEMANTIC_NORMALIZATION_WORK => {
                self.work = next;
                true
            }
            _ => {
                super::super::recovery_admission::refuse_current();
                false
            }
        }
    }

    pub(super) fn charge_value(&mut self, value: &ModelValue) -> bool {
        let admitted =
            aggregate_work(AggregateRoot::Value(value)).is_some_and(|work| self.charge(work));
        if !admitted {
            super::super::recovery_admission::refuse_current();
        }
        admitted
    }

    fn charge_array(&mut self, value: &ArrayValue) -> bool {
        let admitted =
            aggregate_work(AggregateRoot::Array(value)).is_some_and(|work| self.charge(work));
        if !admitted {
            super::super::recovery_admission::refuse_current();
        }
        admitted
    }
}

#[derive(Eq, Hash, PartialEq)]
pub(super) struct NormalizedArrayValue {
    default: Box<NormalizedValue>,
    points: Vec<(ScalarValue, NormalizedValue)>,
}

pub(super) fn normalize_array_value(
    value: &ArrayValue,
    budget: &mut SemanticNormalizationBudget,
) -> Option<NormalizedArrayValue> {
    if !budget.charge_array(value) {
        return None;
    }
    build_normalized_array(value)
}

fn build_normalized_array(value: &ArrayValue) -> Option<NormalizedArrayValue> {
    let default = Box::new(build_normalized_value(&value.default)?);
    let mut seen = HashSet::default();
    let mut points = Vec::new();
    for (key, cell) in value.store.iter().rev() {
        let key = scalar_value(key)?;
        // Validate even shadowed cells: an unsupported old payload is not
        // authority merely because the current point hides it.
        let cell = build_normalized_value(cell)?;
        if seen.insert(key.clone()) && cell != *default {
            points.push((key, cell));
        }
    }
    points.sort_unstable_by(|left, right| left.0.cmp(&right.0));
    Some(NormalizedArrayValue { default, points })
}

impl NormalizedArrayValue {
    pub(super) fn matches_point(
        &self,
        key: &ModelValue,
        actual: &ModelValue,
        budget: &mut SemanticNormalizationBudget,
    ) -> bool {
        if !budget.charge_value(key) || !budget.charge_value(actual) {
            return false;
        }
        let Some(key) = scalar_value(key) else {
            return false;
        };
        let expected = self
            .points
            .binary_search_by(|(candidate, _)| candidate.cmp(&key))
            .ok()
            .map_or(self.default.as_ref(), |index| &self.points[index].1);
        build_normalized_value(actual).as_ref() == Some(expected)
    }
}

#[derive(Eq, Hash, PartialEq)]
pub(in crate::executor::model) struct NormalizedDatatypeArrayValue(NormalizedValue);

#[derive(Eq, Hash, PartialEq)]
enum NormalizedValue {
    Scalar(ScalarValue),
    Array(NormalizedArrayValue),
    Datatype {
        ctor: String,
        args: Vec<NormalizedValue>,
    },
}

pub(in crate::executor::model) fn normalize_datatype_array_value(
    value: &ModelValue,
    budget: &mut SemanticNormalizationBudget,
) -> Option<NormalizedDatatypeArrayValue> {
    if !budget.charge_value(value) {
        return None;
    }
    build_normalized_value(value).map(NormalizedDatatypeArrayValue)
}

fn build_normalized_value(value: &ModelValue) -> Option<NormalizedValue> {
    match value {
        ModelValue::Datatype { ctor, args } => {
            let args = args
                .iter()
                .map(build_normalized_value)
                .collect::<Option<Vec<_>>>()?;
            Some(NormalizedValue::Datatype {
                ctor: ctor.clone(),
                args,
            })
        }
        ModelValue::Array(value) => build_normalized_array(value).map(NormalizedValue::Array),
        _ => scalar_value(value).map(NormalizedValue::Scalar),
    }
}

enum AggregateRoot<'a> {
    Value(&'a ModelValue),
    Array(&'a ArrayValue),
}

/// Borrowed preflight for either root form, with ONE node/depth/payload
/// envelope across all siblings and nested arrays. No synthetic value clone
/// precedes the debit; all later recursive building, equality and hashing see
/// only a depth-bounded tree.
fn aggregate_work(root: AggregateRoot<'_>) -> Option<usize> {
    if !super::super::recovery_admission::pay_current(
        0,
        std::mem::size_of::<(AggregateRoot<'_>, usize)>(),
    ) {
        return None;
    }
    let mut stack = vec![(root, 0usize)];
    let mut nodes = 0usize;
    let mut bytes = 0usize;
    while let Some((root, depth)) = stack.pop() {
        if !super::super::recovery_admission::pay_current(1, std::mem::size_of::<ModelValue>()) {
            return None;
        }
        nodes = nodes.checked_add(1)?;
        if depth > MAX_RENDERED_DT_DEPTH || nodes > MAX_RENDERED_DT_NODES {
            return None;
        }
        let root = match root {
            AggregateRoot::Value(ModelValue::Array(array)) => AggregateRoot::Array(array),
            root => root,
        };
        let payload = match root {
            AggregateRoot::Array(array) => {
                let children = array.store.len().checked_mul(2)?.checked_add(1)?;
                if stack.len().checked_add(children)? > MAX_RENDERED_DT_NODES - nodes {
                    return None;
                }
                if !super::super::recovery_admission::pay_current(
                    children,
                    children.checked_mul(std::mem::size_of::<(AggregateRoot<'_>, usize)>())?,
                ) {
                    return None;
                }
                stack.push((AggregateRoot::Value(&array.default), depth + 1));
                for (key, cell) in &array.store {
                    stack.push((AggregateRoot::Value(key), depth + 1));
                    stack.push((AggregateRoot::Value(cell), depth + 1));
                }
                1
            }
            AggregateRoot::Value(ModelValue::Datatype { ctor, args }) => {
                if stack.len().checked_add(args.len())? > MAX_RENDERED_DT_NODES - nodes {
                    return None;
                }
                if !super::super::recovery_admission::pay_current(
                    args.len(),
                    args.len()
                        .checked_mul(std::mem::size_of::<(AggregateRoot<'_>, usize)>())?,
                ) {
                    return None;
                }
                stack.extend(
                    args.iter()
                        .map(|arg| (AggregateRoot::Value(arg), depth + 1)),
                );
                ctor.len().checked_add(2)?
            }
            AggregateRoot::Value(
                value @ (ModelValue::Bool(_)
                | ModelValue::Int(_)
                | ModelValue::Real(_)
                | ModelValue::BitVec { .. }
                | ModelValue::Str(_)),
            ) => model_value_work(value)?.checked_sub(1)?,
            _ => return None,
        };
        if !super::super::recovery_admission::pay_current(payload, 0) {
            return None;
        }
        bytes = bytes.checked_add(payload)?;
        if bytes > MAX_RENDERED_DT_BYTES {
            return None;
        }
    }
    bytes.checked_add(nodes)
}

#[cfg(test)]
mod tests;
