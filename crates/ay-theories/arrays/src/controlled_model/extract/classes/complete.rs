// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Complete sibling only: retain authenticated scalar components in legacy order.

use super::*;
use std::mem::size_of;

mod order;

#[derive(Clone, Copy, PartialEq, Eq)]
enum Scalar {
    Bool,
    Bv(u32),
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Signature {
    Scalar(Scalar),
    Array(Scalar, Scalar),
}

pub(super) fn prepare(
    solver: &ArraySolver<'_>,
    work: &mut WorkBudget<'_>,
) -> Result<Plan, QueryError> {
    // Complete shape admission has already authenticated every current edge.
    // Do not filter scalar components: that could change later class order.
    order::prepare(solver, work)
}

fn scalar(source: &Sort, work: &mut WorkBudget<'_>) -> Result<Scalar, QueryError> {
    work.charge(16)?;
    match source {
        Sort::Bool => Ok(Scalar::Bool),
        Sort::BitVec(bits) if (1..=128).contains(&bits.width) => Ok(Scalar::Bv(bits.width)),
        _ => Err(work.refuse_exhaustion()),
    }
}

fn signature(
    solver: &ArraySolver<'_>,
    term: TermId,
    work: &mut WorkBudget<'_>,
) -> Result<Signature, QueryError> {
    scan::live(solver, term, work)?;
    if let Some(scope) = &solver.registered_term_scope {
        let bound = owned::checked(
            scope
                .allocation_size()
                .checked_div(size_of::<(TermId, ())>())
                .and_then(|n| n.checked_add(32)),
            work,
        )?;
        owned::table_insert(bound, work)?;
        if !solver.term_in_scope(term) {
            return Err(work.refuse_exhaustion());
        }
    }
    // A cached member must be an actual vertex, not an extra same-sort term.
    let neighbors =
        scan::lookup(&solver.eq_adj, term, work)?.ok_or_else(|| work.refuse_exhaustion())?;
    let visits = owned::checked(size_of::<Signature>().checked_mul(4), work)?;
    work.charge(visits)?;
    match solver.terms.sort(term) {
        Sort::Array(sort) => Ok(Signature::Array(
            scalar(&sort.index_sort, work)?,
            scalar(&sort.element_sort, work)?,
        )),
        sort => {
            if neighbors.is_empty() {
                return Err(work.refuse_exhaustion());
            }
            Ok(Signature::Scalar(scalar(sort, work)?))
        }
    }
}
