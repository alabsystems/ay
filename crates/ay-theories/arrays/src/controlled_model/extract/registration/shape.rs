// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

pub(super) fn source(
    source: &ArraySolver<'_>,
    work: &mut WorkBudget<'_>,
) -> Result<(), QueryError> {
    work.charge(32)?;
    // Legacy dirty rebuild clears merge history, then needs the actual complete
    // assignment rebuild. Refuse a partly-maintained old graph/cache era.
    if !source.assign_dirty
        || !source.eq_adj.is_empty()
        || !source.equiv_classes.is_empty()
        || !source.external_eqs.is_empty()
        || source.populated_terms > source.terms.len()
    {
        return Err(work.refuse_exhaustion());
    }
    if let Some(scope) = &source.registered_term_scope {
        owned::scan_table::<(TermId, ())>(scope.allocation_size(), work)?;
        for &term in scope {
            scan::live(source, term, work)?;
        }
    }
    Ok(())
}

pub(super) fn scoped(
    source: &ArraySolver<'_>,
    term: TermId,
    work: &mut WorkBudget<'_>,
) -> Result<bool, QueryError> {
    if let Some(scope) = &source.registered_term_scope {
        let bound = owned::checked(
            scope
                .allocation_size()
                .checked_div(size_of::<(TermId, ())>())
                .and_then(|n| n.checked_add(32)),
            work,
        )?;
        owned::table_insert(bound, work)?;
    } else {
        work.charge(1)?;
    }
    Ok(source.term_in_scope(term))
}

pub(super) fn child(
    source: &ArraySolver<'_>,
    term: TermId,
    work: &mut WorkBudget<'_>,
) -> Result<(), QueryError> {
    scan::live(source, term, work)?;
    if !scoped(source, term, work)? {
        return Err(work.refuse_exhaustion());
    }
    work.charge(1)?;
    flat(source.terms.sort(term), work)
}

pub(super) fn term(
    source: &ArraySolver<'_>,
    term: TermId,
    work: &mut WorkBudget<'_>,
) -> Result<(), QueryError> {
    scan::live(source, term, work)?;
    work.charge(1)?;
    let sort = source.terms.sort(term);
    flat(sort, work)?;
    match source.terms.get(term) {
        TermData::Var(_, _) | TermData::Const(_) if !matches!(sort, Sort::Array(_)) => Ok(()),
        TermData::Var(_, _) if matches!(sort, Sort::Array(_)) => Ok(()),
        TermData::App(symbol, args) => app(source, term, symbol, args, work),
        TermData::Not(value) if *sort == Sort::Bool => child(source, *value, work),
        TermData::Ite(c, t, e) if !matches!(sort, Sort::Array(_)) => {
            child(source, *c, work)?;
            child(source, *t, work)?;
            child(source, *e, work)
        }
        _ => Err(work.refuse_exhaustion()),
    }
}

fn flat(sort: &Sort, work: &mut WorkBudget<'_>) -> Result<(), QueryError> {
    work.charge(1)?;
    if let Sort::Array(array) = sort {
        scalar(&array.index_sort, work)?;
        scalar(&array.element_sort, work)
    } else {
        scalar(sort, work)
    }
}

fn scalar(sort: &Sort, work: &mut WorkBudget<'_>) -> Result<(), QueryError> {
    work.charge(1)?;
    match sort {
        Sort::Bool | Sort::Int | Sort::Real => Ok(()),
        Sort::BitVec(bits) if (1..=128).contains(&bits.width) => Ok(()),
        _ => Err(work.refuse_exhaustion()),
    }
}

fn app(
    source: &ArraySolver<'_>,
    term: TermId,
    symbol: &Symbol,
    args: &[TermId],
    work: &mut WorkBudget<'_>,
) -> Result<(), QueryError> {
    work.charge(1)?;
    let name = symbol.name();
    // Prepay ALL borrowed argument scalar fetches before iteration, plus the
    // bounded flat-sort/header comparisons performed by this dispatch.
    let visits = owned::checked(
        name.len()
            .checked_add(32)
            .and_then(|n| n.checked_add(args.len())),
        work,
    )?;
    work.charge(visits)?;
    for &arg in args {
        child(source, arg, work)?;
    }
    let sort = source.terms.sort(term);
    match name {
        "store" | "lambda-array" => Err(work.refuse_exhaustion()),
        name if name.starts_with("map[") || name.starts_with("as-array[") => {
            Err(work.refuse_exhaustion())
        }
        "select" => {
            require(args.len() == 2, work)?;
            let Sort::Array(array) = source.terms.sort(args[0]) else {
                return Err(work.refuse_exhaustion());
            };
            require(
                source.terms.sort(args[1]) == &array.index_sort && sort == &array.element_sort,
                work,
            )
        }
        "const-array" => {
            require(args.len() == 1, work)?;
            let Sort::Array(array) = sort else {
                return Err(work.refuse_exhaustion());
            };
            require(source.terms.sort(args[0]) == &array.element_sort, work)
        }
        "default" => {
            require(args.len() == 1, work)?;
            let Sort::Array(array) = source.terms.sort(args[0]) else {
                return Err(work.refuse_exhaustion());
            };
            require(sort == &array.element_sort, work)
        }
        "=" => {
            require(args.len() == 2 && *sort == Sort::Bool, work)?;
            require(
                source.terms.sort(args[0]) == source.terms.sort(args[1]),
                work,
            )
        }
        _ if !matches!(sort, Sort::Array(_)) => Ok(()),
        _ => Err(work.refuse_exhaustion()),
    }
}

fn require(condition: bool, work: &mut WorkBudget<'_>) -> Result<(), QueryError> {
    work.charge(1)?;
    if condition {
        Ok(())
    } else {
        Err(work.refuse_exhaustion())
    }
}
