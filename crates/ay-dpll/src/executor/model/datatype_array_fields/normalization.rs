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
    model_value_work, MAX_RENDERED_DT_BYTES, MAX_RENDERED_DT_NODES,
};

const MAX_SEMANTIC_NORMALIZATION_WORK: usize = 4 * MAX_RENDERED_DT_BYTES;

#[derive(Clone, Default)]
pub(super) struct ArrayAccumulator {
    default: Option<ModelValue>,
    points: HashMap<String, (ModelValue, ModelValue)>,
    observed: bool,
}

impl ArrayAccumulator {
    pub(super) fn merge_point(&mut self, key: ModelValue, value: ModelValue) -> bool {
        let token = dt_canonical_string(&key);
        match self.points.get(&token) {
            Some((_, current)) => same_value(current, &value),
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
        if stores.len() > super::MAX_EXACT_ARRAY_FIELD_TERMS
            || self
                .default
                .as_ref()
                .is_some_and(|current| !same_value(current, &default))
        {
            return false;
        }
        let mut local = HashMap::default();
        for (key, value) in stores {
            let token = dt_canonical_string(&key);
            if !local.contains_key(&token) {
                local.insert(token, (key, value));
            }
        }
        if local.iter().any(|(token, (_, value))| {
            self.points
                .get(token)
                .is_some_and(|(_, current)| !same_value(current, value))
        }) {
            return false;
        }
        if self.default.is_none() {
            self.default = Some(default);
        }
        for (token, point) in local {
            self.points.entry(token).or_insert(point);
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
        let mut points: Vec<_> = self.points.into_iter().collect();
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
    dt_canonical_string(left) == dt_canonical_string(right)
}

pub(super) fn typed_array_value(value: &ArrayValue, sort: &ArraySort) -> bool {
    typed_scalar_value(&value.default, &sort.element_sort)
        && value.store.iter().all(|(key, element)| {
            typed_scalar_value(key, &sort.index_sort)
                && typed_scalar_value(element, &sort.element_sort)
        })
}

fn typed_scalar_value(value: &ModelValue, sort: &Sort) -> bool {
    match (value, sort) {
        (ModelValue::Bool(_), Sort::Bool)
        | (ModelValue::Int(_), Sort::Int)
        | (ModelValue::Real(_), Sort::Real)
        | (ModelValue::Str(_), Sort::String) => true,
        (ModelValue::BitVec { width, value }, Sort::BitVec(bitvec)) => {
            *width == bitvec.width
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
    let mut stack = vec![(root, root_sort)];
    let mut nodes = 0usize;
    while let Some((value, sort)) = stack.pop() {
        nodes += 1;
        if nodes > MAX_RENDERED_DT_NODES {
            return false;
        }
        match (value, sort) {
            (ModelValue::Datatype { ctor, args }, _) if guard.datatype_name(sort).is_some() => {
                let Some((_, fields)) = guard.constructor(sort, ctor) else {
                    return false;
                };
                if fields.len() != args.len()
                    || stack
                        .len()
                        .checked_add(args.len())
                        .is_none_or(|pending| pending > MAX_RENDERED_DT_NODES.saturating_sub(nodes))
                {
                    return false;
                }
                stack.extend(args.iter().zip(fields));
            }
            (ModelValue::Array(array), Sort::Array(sort)) if typed_array_value(array, sort) => {}
            _ if typed_scalar_value(value, sort) => {}
            _ => return false,
        }
    }
    true
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
/// structure is exact; scalar arrays are compared extensionally so redundant
/// and shadowed stores do not create a second encoding of one model value.
#[cfg(test)]
pub(super) fn same_datatype_array_value(left: &ModelValue, right: &ModelValue) -> bool {
    let mut budget = SemanticNormalizationBudget::new();
    match (
        normalize_datatype_array_value(left, &mut budget),
        normalize_datatype_array_value(right, &mut budget),
    ) {
        (Some(left), Some(right)) => left == right,
        _ => false,
    }
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
        ModelValue::Real(value) => Some(ScalarValue::Real(value.clone())),
        ModelValue::BitVec { width, value } => Some(ScalarValue::BitVec(*width, value.clone())),
        ModelValue::Str(value) => Some(ScalarValue::Str(value.clone())),
        _ => None,
    }
}

fn scalar_matches(value: &ScalarValue, candidate: &ModelValue) -> bool {
    match (value, candidate) {
        (ScalarValue::Bool(left), ModelValue::Bool(right)) => left == right,
        (ScalarValue::Int(left), ModelValue::Int(right)) => left == right,
        (ScalarValue::Real(left), ModelValue::Real(right)) => left == right,
        (ScalarValue::BitVec(left_width, left), ModelValue::BitVec { width, value }) => {
            left_width == width && left == value
        }
        (ScalarValue::Str(left), ModelValue::Str(right)) => left == right,
        _ => false,
    }
}

pub(in crate::executor::model) struct SemanticNormalizationBudget {
    work: usize,
}

impl SemanticNormalizationBudget {
    pub(in crate::executor::model) fn new() -> Self {
        Self { work: 0 }
    }

    fn charge(&mut self, amount: usize) -> bool {
        match self.work.checked_add(amount) {
            Some(next) if next <= MAX_SEMANTIC_NORMALIZATION_WORK => {
                self.work = next;
                true
            }
            _ => false,
        }
    }

    pub(super) fn charge_value(&mut self, value: &ModelValue) -> bool {
        model_value_work(value).is_some_and(|work| self.charge(work))
    }

    fn charge_array(&mut self, value: &ArrayValue) -> bool {
        let Some(nodes) = value
            .store
            .len()
            .checked_mul(2)
            .and_then(|nodes| nodes.checked_add(1))
        else {
            return false;
        };
        if nodes > MAX_RENDERED_DT_NODES || !self.charge_value(&value.default) {
            return false;
        }
        value
            .store
            .iter()
            .all(|(key, cell)| self.charge_value(key) && self.charge_value(cell))
    }
}

#[derive(Eq, Hash, PartialEq)]
pub(super) struct NormalizedArrayValue {
    default: ScalarValue,
    points: Vec<(ScalarValue, ScalarValue)>,
}

pub(super) fn normalize_array_value(
    value: &ArrayValue,
    budget: &mut SemanticNormalizationBudget,
) -> Option<NormalizedArrayValue> {
    if !budget.charge_array(value) {
        return None;
    }
    let default = scalar_value(&value.default)?;
    let mut seen = HashSet::default();
    let mut points = Vec::new();
    for (key, cell) in value.store.iter().rev() {
        let key = scalar_value(key)?;
        let cell = scalar_value(cell)?;
        if seen.insert(key.clone()) && cell != default {
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
            .map_or(&self.default, |index| &self.points[index].1);
        scalar_matches(expected, actual)
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
        ModelValue::Array(value) => {
            let default = scalar_value(&value.default)?;
            let mut seen = HashSet::default();
            let mut points = Vec::new();
            for (key, cell) in value.store.iter().rev() {
                let key = scalar_value(key)?;
                let cell = scalar_value(cell)?;
                if seen.insert(key.clone()) && cell != default {
                    points.push((key, cell));
                }
            }
            points.sort_unstable_by(|left, right| left.0.cmp(&right.0));
            Some(NormalizedValue::Array(NormalizedArrayValue {
                default,
                points,
            }))
        }
        _ => scalar_value(value).map(NormalizedValue::Scalar),
    }
}
