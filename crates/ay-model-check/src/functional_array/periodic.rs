// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Complete integer functions over a finite residue quotient. Euclidean mod is
//! specified at https://smt-lib.org/theories-Ints.shtml. Every integer belongs
//! to exactly one residue, including negative integers.

use num_integer::Integer;
use num_traits::ToPrimitive;

use super::*;

impl ArraySnapshot {
    /// Own every residue of a positive integer period as immutable MODEL DATA.
    /// The vector length is the period. No query identity or SAT grant is made.
    pub fn periodic(
        values: &[ModelValue],
        sort: &Sort,
        work: &mut usize,
    ) -> Result<Arc<Self>, FunctionalArrayError> {
        charge(
            work,
            values
                .len()
                .checked_add(1)
                .ok_or(FunctionalArrayError::Resource)?,
        )?;
        let Sort::Array(array) = sort else {
            return Err(FunctionalArrayError::Sort);
        };
        if array.index_sort != Sort::Int
            || !matches!(&array.element_sort, Sort::Bool | Sort::Int)
            || values.is_empty()
        {
            return Err(FunctionalArrayError::Sort);
        }
        charge(
            work,
            values
                .len()
                .checked_mul(std::mem::size_of::<ModelValue>())
                .ok_or(FunctionalArrayError::Resource)?,
        )?;
        for value in values {
            cell(value, &array.element_sort)?;
            charge(work, scalar_cost(value)?)?;
        }
        let mut owned = Vec::new();
        owned
            .try_reserve_exact(values.len())
            .map_err(|_| FunctionalArrayError::Allocation)?;
        owned.extend_from_slice(values);
        Ok(Arc::new(Self {
            sort: sort.clone(),
            depth: 1,
            node: Node::Periodic(owned),
        }))
    }
}

pub(super) fn read(
    values: &[ModelValue],
    index: &BigInt,
    work: &mut usize,
) -> Result<ModelValue, FunctionalArrayError> {
    if values.is_empty() {
        return Err(FunctionalArrayError::Value);
    }
    let bits = usize::try_from(index.bits().max(1)).map_err(|_| FunctionalArrayError::Resource)?;
    charge(
        work,
        bits.checked_mul(std::mem::size_of::<usize>() * 8)
            .ok_or(FunctionalArrayError::Resource)?,
    )?;
    let residue = index
        .mod_floor(&BigInt::from(values.len()))
        .to_usize()
        .ok_or(FunctionalArrayError::Value)?;
    let value = values.get(residue).ok_or(FunctionalArrayError::Value)?;
    charge(work, scalar_cost(value)?)?;
    Ok(value.clone())
}

/// Bound the entire common quotient before allocating or enumerating it.
/// A refusal spends the existing remaining work; it creates no partial table.
pub(crate) fn common_period(
    left: usize,
    right: usize,
    work: &mut usize,
) -> Result<usize, FunctionalArrayError> {
    if left == 0 || right == 0 {
        return Err(FunctionalArrayError::Value);
    }
    charge(work, 128)?;
    let period = left
        .checked_div(left.gcd(&right))
        .and_then(|n| n.checked_mul(right))
        .ok_or(FunctionalArrayError::Resource)?;
    if period > *work {
        *work = 0;
        return Err(FunctionalArrayError::Resource);
    }
    Ok(period)
}

struct Base<'a> {
    values: &'a [ModelValue],
    exceptions: Vec<&'a ModelValue>,
}

fn base<'a>(
    snapshot: &'a ArraySnapshot,
    work: &mut usize,
    stop: &mut dyn FnMut() -> bool,
) -> Result<Base<'a>, FunctionalArrayError> {
    let mut current = snapshot;
    let mut exceptions = Vec::new();
    loop {
        if stop() {
            return Err(FunctionalArrayError::Resource);
        }
        charge(work, 1)?;
        match &current.node {
            Node::Periodic(values) => return Ok(Base { values, exceptions }),
            Node::Store { base, index, .. } => {
                charge(
                    work,
                    (exceptions.len() + 1)
                        .checked_mul(std::mem::size_of::<&ModelValue>())
                        .ok_or(FunctionalArrayError::Resource)?,
                )?;
                exceptions
                    .try_reserve_exact(1)
                    .map_err(|_| FunctionalArrayError::Allocation)?;
                exceptions.push(index);
                current = base;
            }
            Node::Finite(value) => {
                charge(
                    work,
                    value
                        .store
                        .len()
                        .checked_add(exceptions.len())
                        .and_then(|n| n.checked_mul(std::mem::size_of::<&ModelValue>()))
                        .ok_or(FunctionalArrayError::Resource)?,
                )?;
                exceptions
                    .try_reserve_exact(value.store.len())
                    .map_err(|_| FunctionalArrayError::Allocation)?;
                exceptions.extend(value.store.iter().map(|(index, _)| index));
                return Ok(Base {
                    values: std::slice::from_ref(&value.default),
                    exceptions,
                });
            }
            Node::Range { .. } => return Err(FunctionalArrayError::Sort),
        }
    }
}

pub(super) fn same_function(
    left: &ArraySnapshot,
    right: &ArraySnapshot,
    work: &mut usize,
    stop: &mut dyn FnMut() -> bool,
) -> Result<bool, FunctionalArrayError> {
    let left_base = base(left, work, stop)?;
    let right_base = base(right, work, stop)?;
    let period = common_period(left_base.values.len(), right_base.values.len(), work)?;
    // Outside finitely many stores, both functions equal their periodic base.
    // Every residue has infinitely many representatives, so base agreement and
    // equality at every written exception are necessary and sufficient.
    for residue in 0..period {
        if stop() {
            return Err(FunctionalArrayError::Resource);
        }
        let a = &left_base.values[residue % left_base.values.len()];
        let b = &right_base.values[residue % right_base.values.len()];
        charge(
            work,
            scalar_cost(a)?
                .checked_add(scalar_cost(b)?)
                .and_then(|n| n.checked_add(1))
                .ok_or(FunctionalArrayError::Resource)?,
        )?;
        if !value_eq(a, b).map_err(|_| FunctionalArrayError::Value)? {
            return Ok(false);
        }
    }
    for index in left_base.exceptions.iter().chain(&right_base.exceptions) {
        let a = left.read_with_stop(index, work, stop)?;
        let b = right.read_with_stop(index, work, stop)?;
        charge(
            work,
            scalar_cost(&a)?
                .checked_add(scalar_cost(&b)?)
                .ok_or(FunctionalArrayError::Resource)?,
        )?;
        if !value_eq(&a, &b).map_err(|_| FunctionalArrayError::Value)? {
            return Ok(false);
        }
    }
    Ok(true)
}

pub(super) fn render(
    values: &[ModelValue],
    work: &mut usize,
    stop: &mut dyn FnMut() -> bool,
) -> Result<String, FunctionalArrayError> {
    let Some(last) = values.last() else {
        return Err(FunctionalArrayError::Value);
    };
    charge(work, 128)?;
    let period = values.len().to_string();
    let mut body = scalar(last, work)?;
    for (residue, value) in values[..values.len() - 1].iter().enumerate().rev() {
        if stop() {
            return Err(FunctionalArrayError::Resource);
        }
        charge(work, 128)?;
        let index = residue.to_string();
        let value = scalar(value, work)?;
        body = compose(
            work,
            &[
                "(ite (= (mod ay!model!index ",
                &period,
                ") ",
                &index,
                ") ",
                &value,
                " ",
                &body,
                ")",
            ],
        )?;
    }
    compose(work, &["(lambda ((ay!model!index Int)) ", &body, ")"])
}
