// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use ay_core::{ArraySort, DatatypeConstructor, DatatypeField, DatatypeSort};
use std::mem::size_of;

pub(super) fn optional(
    source: Option<&Sort>,
    work: &mut WorkBudget<'_>,
) -> Result<Option<Sort>, QueryError> {
    source.map(|value| copy(value, 0, work)).transpose()
}

fn copy(source: &Sort, depth: usize, work: &mut WorkBudget<'_>) -> Result<Sort, QueryError> {
    if depth >= 56 {
        return Err(work.refuse_exhaustion());
    }
    // Includes fixed header moves, nested box requests and cleanup visits.
    let bytes = owned::checked(
        size_of::<Sort>()
            .checked_mul(8)
            .and_then(|n| n.checked_add(4 * size_of::<ArraySort>())),
        work,
    )?;
    work.admit(16, bytes)?;
    let result = match source {
        Sort::Bool => Sort::Bool,
        Sort::Int => Sort::Int,
        Sort::Real => Sort::Real,
        Sort::BitVec(value) => Sort::BitVec(value.clone()),
        Sort::String => Sort::String,
        Sort::RegLan => Sort::RegLan,
        Sort::Char => Sort::Char,
        Sort::FloatingPoint(exponent, significand) => Sort::FloatingPoint(*exponent, *significand),
        Sort::Uninterpreted(name) => Sort::Uninterpreted(owned::text(name, work)?),
        Sort::TypeVar(name) => Sort::TypeVar(owned::text(name, work)?),
        Sort::FiniteDomain(name, cardinality) => {
            Sort::FiniteDomain(owned::text(name, work)?, *cardinality)
        }
        Sort::Array(value) => {
            let index_sort = copy(&value.index_sort, depth + 1, work)?;
            let element_sort = copy(&value.element_sort, depth + 1, work)?;
            Sort::Array(Box::new(ArraySort {
                index_sort,
                element_sort,
            }))
        }
        Sort::Seq(value) => Sort::Seq(Box::new(copy(value, depth + 1, work)?)),
        Sort::Datatype(value) => Sort::Datatype(datatype(value, depth + 1, work)?),
        _ => return Err(work.refuse_exhaustion()),
    };
    work.charge(0)?;
    Ok(result)
}

fn datatype(
    source: &DatatypeSort,
    depth: usize,
    work: &mut WorkBudget<'_>,
) -> Result<DatatypeSort, QueryError> {
    let name = owned::text(&source.name, work)?;
    let mut constructors = owned::reserve_vec(source.constructors.len(), work)?;
    for constructor in &source.constructors {
        work.charge(1)?;
        let name = owned::text(&constructor.name, work)?;
        let mut fields = owned::reserve_vec(constructor.fields.len(), work)?;
        for field in &constructor.fields {
            work.charge(1)?;
            fields.push(DatatypeField {
                name: owned::text(&field.name, work)?,
                sort: copy(&field.sort, depth, work)?,
            });
        }
        constructors.push(DatatypeConstructor { name, fields });
    }
    work.charge(0)?;
    Ok(DatatypeSort { name, constructors })
}
