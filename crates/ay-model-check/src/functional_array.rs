// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Complete immutable finite, BV64 range and periodic integer array data.
//! A range or residue quotient denotes its entire domain;
//! neither construction nor equality samples or enumerates the written range.

use std::sync::Arc;

use ay_core::Sort;
use num_bigint::BigInt;
use num_traits::{One, Signed};

use crate::{value_eq, ArrayValue, ModelValue};

mod partition;
pub(crate) mod periodic;
mod recipe;
mod scalar_data;
use scalar_data::{compose, scalar, scalar_cost};
pub(crate) mod topology;
pub use recipe::{
    recognize_fill_lambda, recognize_identity_lambda, recognize_int_scalar_lambda,
    recognize_range_lambda, FillInterval, FillLambda, IdentityLambda, IntScalarLambda, RangeLambda,
};

#[derive(Debug, thiserror::Error)]
pub enum FunctionalArrayError {
    #[error("functional array work or depth budget exceeded")]
    Resource,
    #[error("functional array requires BV64 Bool/BV cells or integer Bool/Int cells")]
    Sort,
    #[error("functional array contains an invalid captured value")]
    Value,
    #[error("functional array allocation was refused")]
    Allocation,
}

#[derive(Clone, Debug)]
pub struct ArraySnapshot {
    sort: Sort,
    depth: usize,
    node: Node,
}

#[derive(Clone, Debug)]
enum Node {
    Finite(ArrayValue),
    Periodic(Vec<ModelValue>),
    Store {
        base: Arc<ArraySnapshot>,
        index: ModelValue,
        value: ModelValue,
    },
    Range {
        destination: Arc<ArraySnapshot>,
        source: Arc<ArraySnapshot>,
        lo: BigInt,
        hi: BigInt,
        source_lo: BigInt,
    },
}

fn charge(work: &mut usize, amount: usize) -> Result<(), FunctionalArrayError> {
    let Some(left) = work.checked_sub(amount) else {
        *work = 0;
        return Err(FunctionalArrayError::Resource);
    };
    *work = left;
    Ok(())
}

fn key(value: &ModelValue) -> Result<&BigInt, FunctionalArrayError> {
    match value {
        ModelValue::BitVec { width: 64, value } if !value.is_negative() && value.bits() <= 64 => {
            Ok(value)
        }
        _ => Err(FunctionalArrayError::Sort),
    }
}

fn cell(value: &ModelValue, sort: &Sort) -> Result<(), FunctionalArrayError> {
    match (value, sort) {
        (ModelValue::Bool(_), Sort::Bool) | (ModelValue::Int(_), Sort::Int) => Ok(()),
        (ModelValue::BitVec { width, value }, Sort::BitVec(expected))
            if *width == expected.width
                && *width > 0
                && !value.is_negative()
                && value.bits() <= u64::from(*width) =>
        {
            Ok(())
        }
        _ => Err(FunctionalArrayError::Value),
    }
}

fn supported_sort(sort: &Sort) -> bool {
    matches!(sort, Sort::Array(array) if
        (array.index_sort == Sort::Int && matches!(&array.element_sort, Sort::Bool | Sort::Int))
        || (matches!(&array.index_sort, Sort::BitVec(index) if index.width == 64)
            && matches!(&array.element_sort, Sort::Bool | Sort::BitVec(_))))
}

fn array_key<'a>(value: &'a ModelValue, sort: &Sort) -> Result<&'a BigInt, FunctionalArrayError> {
    match (value, sort) {
        (ModelValue::Int(value), Sort::Array(array)) if array.index_sort == Sort::Int => Ok(value),
        (_, Sort::Array(array)) if matches!(&array.index_sort, Sort::BitVec(index) if index.width == 64) => {
            key(value)
        }
        _ => Err(FunctionalArrayError::Sort),
    }
}

impl ArraySnapshot {
    pub fn finite(
        value: ArrayValue,
        sort: &Sort,
        work: &mut usize,
    ) -> Result<Arc<Self>, FunctionalArrayError> {
        charge(work, 1 + value.store.len())?;
        let Sort::Array(array) = sort else {
            return Err(FunctionalArrayError::Sort);
        };
        if !supported_sort(sort) {
            return Err(FunctionalArrayError::Sort);
        }
        cell(&value.default, &array.element_sort)?;
        charge(work, scalar_cost(&value.default)?)?;
        for (index, value) in &value.store {
            array_key(index, sort)?;
            cell(value, &array.element_sort)?;
            charge(
                work,
                scalar_cost(index)?
                    .checked_add(scalar_cost(value)?)
                    .ok_or(FunctionalArrayError::Resource)?,
            )?;
        }
        Ok(Arc::new(Self {
            sort: sort.clone(),
            depth: 1,
            node: Node::Finite(value),
        }))
    }

    pub fn range_copy(
        destination: Arc<Self>,
        source: Arc<Self>,
        lo: &ModelValue,
        hi: &ModelValue,
        source_lo: &ModelValue,
        work: &mut usize,
    ) -> Result<Arc<Self>, FunctionalArrayError> {
        charge(work, 1)?;
        let (lo, hi, source_lo) = (key(lo)?, key(hi)?, key(source_lo)?);
        if destination.sort != source.sort
            || !matches!(&destination.sort, Sort::Array(sort) if matches!(&sort.index_sort, Sort::BitVec(index) if index.width == 64))
        {
            return Err(FunctionalArrayError::Sort);
        }
        // Exact unsigned interval semantics: no index can satisfy lo <= i < hi.
        if lo >= hi {
            return Ok(destination);
        }
        let depth = destination.depth.max(source.depth) + 1;
        if depth > 64 {
            return Err(FunctionalArrayError::Resource);
        }
        let node = Node::Range {
            destination: Arc::clone(&destination),
            source,
            lo: lo.clone(),
            hi: hi.clone(),
            source_lo: source_lo.clone(),
        };
        Ok(Arc::new(Self {
            sort: destination.sort.clone(),
            depth,
            node,
        }))
    }

    pub fn store(
        base: Arc<Self>,
        index: &ModelValue,
        value: &ModelValue,
        work: &mut usize,
    ) -> Result<Arc<Self>, FunctionalArrayError> {
        charge(
            work,
            scalar_cost(index)?
                .checked_add(scalar_cost(value)?)
                .and_then(|cost| cost.checked_add(1))
                .ok_or(FunctionalArrayError::Resource)?,
        )?;
        array_key(index, &base.sort)?;
        let Sort::Array(sort) = &base.sort else {
            return Err(FunctionalArrayError::Sort);
        };
        cell(value, &sort.element_sort)?;
        if let Node::Finite(finite) = &base.node {
            // This is exact finite-store normalization, not an expansion of a
            // range. It makes the closed printed capture reparse identically.
            charge(work, finite.store.len() + scalar_cost(&finite.default)?)?;
            for (index, value) in &finite.store {
                charge(
                    work,
                    scalar_cost(index)?
                        .checked_add(scalar_cost(value)?)
                        .ok_or(FunctionalArrayError::Resource)?,
                )?;
            }
            let mut copied = finite.clone();
            copied
                .store
                .try_reserve(1)
                .map_err(|_| FunctionalArrayError::Allocation)?;
            copied.store.push((index.clone(), value.clone()));
            return Self::finite(copied, &base.sort, work);
        }
        let depth = base.depth + 1;
        if depth > 64 {
            return Err(FunctionalArrayError::Resource);
        }
        Ok(Arc::new(Self {
            sort: base.sort.clone(),
            depth,
            node: Node::Store {
                base,
                index: index.clone(),
                value: value.clone(),
            },
        }))
    }

    pub fn sort(&self) -> &Sort {
        &self.sort
    }

    pub fn finite_value(
        &self,
        work: &mut usize,
    ) -> Result<Option<ModelValue>, FunctionalArrayError> {
        charge(work, 1)?;
        match &self.node {
            Node::Finite(value) => {
                charge(work, value.store.len() + scalar_cost(&value.default)?)?;
                for (index, value) in &value.store {
                    charge(
                        work,
                        scalar_cost(index)?
                            .checked_add(scalar_cost(value)?)
                            .ok_or(FunctionalArrayError::Resource)?,
                    )?;
                }
                Ok(Some(ModelValue::Array(Box::new(value.clone()))))
            }
            Node::Range { .. } | Node::Store { .. } | Node::Periodic(_) => Ok(None),
        }
    }

    pub fn read(
        &self,
        index: &ModelValue,
        work: &mut usize,
    ) -> Result<ModelValue, FunctionalArrayError> {
        self.read_with_stop(index, work, &mut || false)
    }

    pub fn read_with_stop(
        &self,
        index: &ModelValue,
        work: &mut usize,
        stop: &mut dyn FnMut() -> bool,
    ) -> Result<ModelValue, FunctionalArrayError> {
        if stop() {
            return Err(FunctionalArrayError::Resource);
        }
        charge(work, 1)?;
        let index_value = array_key(index, &self.sort)?;
        match &self.node {
            Node::Periodic(values) => periodic::read(values, index_value, work),
            Node::Finite(value) => {
                charge(
                    work,
                    value
                        .store
                        .len()
                        .checked_add(scalar_cost(&value.default)?)
                        .ok_or(FunctionalArrayError::Resource)?,
                )?;
                for (stored, datum) in value.store.iter().rev() {
                    if stop() {
                        return Err(FunctionalArrayError::Resource);
                    }
                    charge(
                        work,
                        scalar_cost(stored)?
                            .checked_add(scalar_cost(index)?)
                            .ok_or(FunctionalArrayError::Resource)?,
                    )?;
                    if array_key(stored, &self.sort)? == index_value {
                        charge(work, scalar_cost(datum)?)?;
                        return Ok(datum.clone());
                    }
                }
                Ok(value.default.clone())
            }
            Node::Store {
                base,
                index: stored,
                value,
            } => {
                charge(
                    work,
                    scalar_cost(stored)?
                        .checked_add(scalar_cost(index)?)
                        .ok_or(FunctionalArrayError::Resource)?,
                )?;
                if array_key(stored, &self.sort)? == index_value {
                    charge(work, scalar_cost(value)?)?;
                    Ok(value.clone())
                } else {
                    base.read_with_stop(index, work, stop)
                }
            }
            Node::Range {
                destination,
                source,
                lo,
                hi,
                source_lo,
            } => {
                if lo <= index_value && index_value < hi {
                    let modulus = BigInt::one() << 64;
                    let shifted = (index_value - lo + source_lo) % modulus;
                    source.read_with_stop(&ModelValue::bitvec(shifted, 64), work, stop)
                } else {
                    destination.read_with_stop(index, work, stop)
                }
            }
        }
    }

    /// True proves equal complete functions. False means only that this
    /// structural comparison did not establish equality, never disequality.
    pub fn same_function(
        &self,
        other: &Self,
        work: &mut usize,
    ) -> Result<bool, FunctionalArrayError> {
        self.same_function_with_stop(other, work, &mut || false)
    }

    pub fn same_function_with_stop(
        &self,
        other: &Self,
        work: &mut usize,
        stop: &mut dyn FnMut() -> bool,
    ) -> Result<bool, FunctionalArrayError> {
        Ok(self.equality_with_stop(other, work, stop)? == Some(true))
    }

    /// Integer arrays have an exact comparison over every residue and finite
    /// exception. A mismatch between two BV range programs can be inconclusive.
    pub(crate) fn equality_with_stop(
        &self,
        other: &Self,
        work: &mut usize,
        stop: &mut dyn FnMut() -> bool,
    ) -> Result<Option<bool>, FunctionalArrayError> {
        if stop() {
            return Err(FunctionalArrayError::Resource);
        }
        charge(work, 1)?;
        if self.sort != other.sort {
            return Err(FunctionalArrayError::Sort);
        }
        if matches!(&self.sort, Sort::Array(sort) if sort.index_sort == Sort::Int) {
            return periodic::same_function(self, other, work, stop).map(Some);
        }
        let established = match (&self.node, &other.node) {
            (Node::Finite(left), Node::Finite(right)) => {
                for (index, _) in left.store.iter().chain(&right.store) {
                    let left = self.read_with_stop(index, work, stop)?;
                    let right = other.read_with_stop(index, work, stop)?;
                    if !value_eq(&left, &right).map_err(|_| FunctionalArrayError::Value)? {
                        return Ok(None);
                    }
                }
                if value_eq(&left.default, &right.default)
                    .map_err(|_| FunctionalArrayError::Value)?
                {
                    true
                } else {
                    return Err(FunctionalArrayError::Value);
                }
            }
            (
                Node::Store {
                    base: lb,
                    index: li,
                    value: lv,
                },
                Node::Store {
                    base: rb,
                    index: ri,
                    value: rv,
                },
            ) => {
                value_eq(li, ri).map_err(|_| FunctionalArrayError::Value)?
                    && value_eq(lv, rv).map_err(|_| FunctionalArrayError::Value)?
                    && lb.same_function_with_stop(rb, work, stop)?
            }
            (
                Node::Range {
                    destination: ld,
                    source: ls,
                    lo: ll,
                    hi: lh,
                    source_lo: lx,
                },
                Node::Range {
                    destination: rd,
                    source: rs,
                    lo: rl,
                    hi: rh,
                    source_lo: rx,
                },
            ) => {
                ll == rl
                    && lh == rh
                    && lx == rx
                    && ld.same_function_with_stop(rd, work, stop)?
                    && ls.same_function_with_stop(rs, work, stop)?
            }
            _ => false,
        };
        Ok(established.then_some(true))
    }

    pub fn to_smtlib(&self, work: &mut usize) -> Result<String, FunctionalArrayError> {
        self.to_smtlib_with_stop(work, &mut || false)
    }

    pub fn to_smtlib_with_stop(
        &self,
        work: &mut usize,
        stop: &mut dyn FnMut() -> bool,
    ) -> Result<String, FunctionalArrayError> {
        if stop() {
            return Err(FunctionalArrayError::Resource);
        }
        charge(work, 1)?;
        let Sort::Array(sort) = &self.sort else {
            return Err(FunctionalArrayError::Sort);
        };
        match &self.node {
            Node::Periodic(values) => periodic::render(values, work, stop),
            Node::Finite(value) => {
                let element = match &sort.element_sort {
                    Sort::Bool => "Bool".to_owned(),
                    Sort::Int => "Int".to_owned(),
                    Sort::BitVec(bv) => format!("(_ BitVec {})", bv.width),
                    _ => return Err(FunctionalArrayError::Sort),
                };
                let index_sort = if sort.index_sort == Sort::Int {
                    "Int"
                } else {
                    "(_ BitVec 64)"
                };
                let default = scalar(&value.default, work)?;
                let mut output = compose(
                    work,
                    &[
                        "((as const (Array ",
                        index_sort,
                        " ",
                        &element,
                        ")) ",
                        &default,
                        ")",
                    ],
                )?;
                for (index, value) in &value.store {
                    if stop() {
                        return Err(FunctionalArrayError::Resource);
                    }
                    let index = scalar(index, work)?;
                    let value = scalar(value, work)?;
                    output = compose(work, &["(store ", &output, " ", &index, " ", &value, ")"])?;
                }
                Ok(output)
            }
            Node::Store { base, index, value } => {
                let base = base.to_smtlib_with_stop(work, stop)?;
                let index = scalar(index, work)?;
                let value = scalar(value, work)?;
                compose(work, &["(store ", &base, " ", &index, " ", &value, ")"])
            }
            Node::Range {
                destination,
                source,
                lo,
                hi,
                source_lo,
            } => {
                let destination = destination.to_smtlib_with_stop(work, stop)?;
                let source = source.to_smtlib_with_stop(work, stop)?;
                // Captured bounds are BV64 values (at most 20 decimal digits).
                let prefix = format!(
                    "(lambda ((ay!model!index (_ BitVec 64))) (ite (and (bvule (_ bv{lo} 64) ay!model!index) (bvult ay!model!index (_ bv{hi} 64))) (select "
                );
                let offset = format!(
                    " (bvadd (bvsub ay!model!index (_ bv{lo} 64)) (_ bv{source_lo} 64))) (select "
                );
                compose(
                    work,
                    &[
                        &prefix,
                        &source,
                        &offset,
                        &destination,
                        " ay!model!index)))",
                    ],
                )
            }
        }
    }
}

#[cfg(test)]
mod tests;
