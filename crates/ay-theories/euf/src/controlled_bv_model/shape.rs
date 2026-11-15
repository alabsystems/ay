// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[derive(Clone, Copy, PartialEq, Eq)]
enum Scalar {
    Bool,
    Bv(u32),
}
#[derive(Clone, Copy, PartialEq, Eq)]
enum Key {
    Scalar(Scalar),
    Array(Scalar, Scalar),
}

pub(super) fn prepared(
    source: &EufSolver<'_>,
    work: &mut WorkBudget<'_>,
) -> Result<(), QueryError> {
    work.charge(128)?;
    let n = source.terms.len();
    if source.poisoned
        || source.dirty
        || source.egraph_requeue_needed
        || !source.enodes_init
        || source.enodes.len() != n
        || source.uf.parent.len() != n
        || source.uf_full_sync_needed
        || !source.uf_dirty_nodes.is_empty()
        || !source.to_merge.is_empty()
        || !source.bool_merge_pending.is_empty()
        || source.pending_conflict.is_some()
    {
        return Err(work.refuse_exhaustion());
    }
    Ok(())
}

pub(super) fn live(
    source: &EufSolver<'_>,
    term: TermId,
    work: &mut WorkBudget<'_>,
) -> Result<(), QueryError> {
    work.charge(16)?;
    if (term.0 as usize) < source.terms.len() {
        Ok(())
    } else {
        Err(work.refuse_exhaustion())
    }
}

fn scalar(sort: &Sort, work: &mut WorkBudget<'_>) -> Result<Scalar, QueryError> {
    work.charge(16)?;
    match sort {
        Sort::Bool => Ok(Scalar::Bool),
        Sort::BitVec(bits) if (1..=128).contains(&bits.width) => Ok(Scalar::Bv(bits.width)),
        _ => Err(work.refuse_exhaustion()),
    }
}

fn key(source: &EufSolver<'_>, term: TermId, work: &mut WorkBudget<'_>) -> Result<Key, QueryError> {
    live(source, term, work)?;
    work.charge(16)?;
    match source.terms.sort(term) {
        Sort::Array(array) => Ok(Key::Array(
            scalar(&array.index_sort, work)?,
            scalar(&array.element_sort, work)?,
        )),
        sort => Ok(Key::Scalar(scalar(sort, work)?)),
    }
}

pub(super) fn arena(source: &EufSolver<'_>, work: &mut WorkBudget<'_>) -> Result<(), QueryError> {
    // Complete arena validation also covers search-created assignments and
    // class constants outside the authored-root inventory. Never a dead lookup.
    for index in 0..source.terms.len() {
        work.charge(32)?;
        let id = u32::try_from(index).map_err(|_| work.refuse_exhaustion())?;
        term(source, TermId(id), work)?;
    }
    work.charge(64)?;
    let _ = owned::scan_table::<(TermId, bool)>(source.assigns.allocation_size(), work)?;
    for &id in source.assigns.keys() {
        live(source, id, work)?;
    }
    Ok(())
}

fn term(source: &EufSolver<'_>, id: TermId, work: &mut WorkBudget<'_>) -> Result<(), QueryError> {
    let sort = key(source, id, work)?;
    work.charge(32)?;
    match source.terms.get(id) {
        TermData::Var(..) => Ok(()),
        TermData::Const(Constant::Bool(_)) if sort == Key::Scalar(Scalar::Bool) => Ok(()),
        TermData::Const(Constant::BitVec { value, width })
            if sort == Key::Scalar(Scalar::Bv(*width)) =>
        {
            literal::magnitude(value, *width, work).map(|_| ())
        }
        TermData::Not(child) if sort == Key::Scalar(Scalar::Bool) => {
            require(key(source, *child, work)? == sort, work)
        }
        TermData::Ite(c, t, e) if matches!(sort, Key::Scalar(_)) => {
            require(key(source, *c, work)? == Key::Scalar(Scalar::Bool), work)?;
            require(
                key(source, *t, work)? == sort && key(source, *e, work)? == sort,
                work,
            )
        }
        TermData::App(Symbol::Named(name), args) => app(source, name, args, sort, work),
        _ => Err(work.refuse_exhaustion()),
    }
}

fn app(
    source: &EufSolver<'_>,
    name: &str,
    args: &[TermId],
    sort: Key,
    work: &mut WorkBudget<'_>,
) -> Result<(), QueryError> {
    let names = owned::checked(
        name.len().checked_mul(16).and_then(|n| n.checked_add(64)),
        work,
    )?;
    work.charge(names)?;
    let visits = owned::checked(args.len().checked_mul(16), work)?;
    work.charge(visits)?;
    for &arg in args {
        let _ = key(source, arg, work)?;
    }
    match name {
        "and" | "or" => {
            require(sort == Key::Scalar(Scalar::Bool), work)?;
            for &arg in args {
                require(key(source, arg, work)? == sort, work)?;
            }
            Ok(())
        }
        "=" | "distinct" => {
            require(sort == Key::Scalar(Scalar::Bool) && args.len() >= 2, work)?;
            if name == "=" {
                require(args.len() == 2, work)?;
            }
            let first = key(source, args[0], work)?;
            for &arg in args {
                require(key(source, arg, work)? == first, work)?;
            }
            Ok(())
        }
        "select" if args.len() == 2 => {
            let Key::Array(index, element) = key(source, args[0], work)? else {
                return Err(work.refuse_exhaustion());
            };
            require(
                key(source, args[1], work)? == Key::Scalar(index) && sort == Key::Scalar(element),
                work,
            )
        }
        "store" if args.len() == 3 => {
            let Key::Array(index, element) = sort else {
                return Err(work.refuse_exhaustion());
            };
            require(key(source, args[0], work)? == sort, work)?;
            require(key(source, args[1], work)? == Key::Scalar(index), work)?;
            require(key(source, args[2], work)? == Key::Scalar(element), work)
        }
        "const-array" if args.len() == 1 => {
            let Key::Array(_, element) = sort else {
                return Err(work.refuse_exhaustion());
            };
            require(key(source, args[0], work)? == Key::Scalar(element), work)
        }
        "default" if args.len() == 1 => {
            let Key::Array(_, element) = key(source, args[0], work)? else {
                return Err(work.refuse_exhaustion());
            };
            require(sort == Key::Scalar(element), work)
        }
        _ => Err(work.refuse_exhaustion()),
    }
}

fn require(ok: bool, work: &mut WorkBudget<'_>) -> Result<(), QueryError> {
    work.charge(8)?;
    if ok {
        Ok(())
    } else {
        Err(work.refuse_exhaustion())
    }
}

pub(super) fn representative(
    source: &EufSolver<'_>,
    term: TermId,
    work: &mut WorkBudget<'_>,
) -> Result<u32, QueryError> {
    live(source, term, work)?;
    let mut current = term.0;
    for _ in 0..source.enodes.len() {
        work.charge(64)?;
        let Some(node) = source.enodes.get(current as usize) else {
            return Err(work.refuse_exhaustion());
        };
        if node.root == current {
            if source.uf.parent.get(term.0 as usize).copied() != Some(current) {
                return Err(work.refuse_exhaustion());
            }
            return Ok(current);
        }
        current = node.root;
    }
    Err(work.refuse_exhaustion())
}
