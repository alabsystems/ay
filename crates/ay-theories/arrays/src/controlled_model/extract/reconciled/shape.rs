// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use ay_core::term::TermStoreSnapshotStamp;

mod caches;

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
    source: &ArraySolver<'_>,
    work: &mut WorkBudget<'_>,
) -> Result<(), QueryError> {
    work.charge(64)?;
    if source.dirty
        || source.var_layer_dirty
        || source.assign_dirty
        || source.shadow_uf_stale
        || source.populated_terms != source.terms.len()
        || !source.pending_registered_equalities.is_empty()
        || source.array_var_merge_log.len() != source.array_var_merge_undo.len()
        || !source.map_cache.is_empty()
        || !source.as_array_cache.is_empty()
    {
        return Err(work.refuse_exhaustion());
    }
    let scope_bound = if let Some(scope) = &source.registered_term_scope {
        owned::scan_table::<(TermId, ())>(scope.allocation_size(), work)?;
        for &term in scope {
            scan::live(source, term, work)?;
        }
        owned::checked(
            scope
                .allocation_size()
                .checked_div(size_of::<(TermId, ())>())
                .and_then(|n| n.checked_add(32)),
            work,
        )?
    } else {
        0
    };
    for index in 0..source.terms.len() {
        work.charge(32)?;
        let term = TermId(u32::try_from(index).map_err(|_| work.refuse_exhaustion())?);
        if scope_bound != 0 {
            owned::table_insert(scope_bound, work)?;
        }
        if source.term_in_scope(term) {
            validate(source, term, work)?;
        }
    }
    caches::validate(source, work)?;
    work.charge(0)
}

fn scalar(sort: &Sort, work: &mut WorkBudget<'_>) -> Result<Scalar, QueryError> {
    work.charge(16)?;
    match sort {
        Sort::Bool => Ok(Scalar::Bool),
        Sort::BitVec(bits) if (1..=128).contains(&bits.width) => Ok(Scalar::Bv(bits.width)),
        _ => Err(work.refuse_exhaustion()),
    }
}

fn key(
    source: &ArraySolver<'_>,
    term: TermId,
    work: &mut WorkBudget<'_>,
) -> Result<Key, QueryError> {
    scan::live(source, term, work)?;
    if let Some(scope) = &source.registered_term_scope {
        let bound = owned::checked(
            scope
                .allocation_size()
                .checked_div(size_of::<(TermId, ())>())
                .and_then(|n| n.checked_add(32)),
            work,
        )?;
        owned::table_insert(bound, work)?;
        if !source.term_in_scope(term) {
            return Err(work.refuse_exhaustion());
        }
    }
    work.charge(16)?;
    match source.terms.sort(term) {
        Sort::Array(sort) => Ok(Key::Array(
            scalar(&sort.index_sort, work)?,
            scalar(&sort.element_sort, work)?,
        )),
        sort => Ok(Key::Scalar(scalar(sort, work)?)),
    }
}

fn validate(
    source: &ArraySolver<'_>,
    term: TermId,
    work: &mut WorkBudget<'_>,
) -> Result<(), QueryError> {
    let sort = key(source, term, work)?;
    work.charge(32)?;
    match source.terms.get(term) {
        TermData::Var(..) => Ok(()),
        TermData::Const(Constant::Bool(_)) if sort == Key::Scalar(Scalar::Bool) => Ok(()),
        TermData::Const(Constant::BitVec { width, .. })
            if sort == Key::Scalar(Scalar::Bv(*width)) =>
        {
            Ok(())
        }
        TermData::Not(value) if sort == Key::Scalar(Scalar::Bool) => {
            require(key(source, *value, work)? == sort, work)
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
    source: &ArraySolver<'_>,
    name: &str,
    args: &[TermId],
    sort: Key,
    work: &mut WorkBudget<'_>,
) -> Result<(), QueryError> {
    let visits = owned::checked(
        name.len()
            .checked_mul(16)
            .and_then(|n| args.len().checked_mul(16).and_then(|a| n.checked_add(a)))
            .and_then(|n| n.checked_add(64)),
        work,
    )?;
    work.charge(visits)?;
    for &arg in args {
        let _ = key(source, arg, work)?;
    }
    match name {
        "and" | "or" | "=" | "distinct" => boolean(source, name, args, sort, work),
        _ => array(source, name, args, sort, work),
    }
}

fn boolean(
    source: &ArraySolver<'_>,
    name: &str,
    args: &[TermId],
    sort: Key,
    work: &mut WorkBudget<'_>,
) -> Result<(), QueryError> {
    require(sort == Key::Scalar(Scalar::Bool), work)?;
    let expected = match name {
        "and" | "or" => sort,
        _ => {
            require(args.len() >= 2 && (name != "=" || args.len() == 2), work)?;
            key(source, args[0], work)?
        }
    };
    for &arg in args {
        require(key(source, arg, work)? == expected, work)?;
    }
    Ok(())
}

fn array(
    source: &ArraySolver<'_>,
    name: &str,
    args: &[TermId],
    sort: Key,
    work: &mut WorkBudget<'_>,
) -> Result<(), QueryError> {
    match name {
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
            require(
                key(source, args[0], work)? == sort
                    && key(source, args[1], work)? == Key::Scalar(index)
                    && key(source, args[2], work)? == Key::Scalar(element),
                work,
            )
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

pub(super) struct Binding {
    terms: TermStoreSnapshotStamp,
    metadata: u64,
    versions: (u64, u64),
    scope: Option<(usize, usize)>,
}

impl Binding {
    pub(super) fn capture(
        source: &ArraySolver<'_>,
        work: &mut WorkBudget<'_>,
    ) -> Result<Self, QueryError> {
        work.admit(64, 8 * size_of::<Self>())?;
        Ok(Self {
            terms: source.terms.snapshot_stamp(),
            metadata: source.terms.checker_visible_metadata_generation(),
            versions: (source.eq_adj_version, source.propagate_state_version),
            scope: source
                .registered_term_scope
                .as_ref()
                .map(|s| (s.len(), s.allocation_size())),
        })
    }

    pub(super) fn verify(
        &self,
        source: &ArraySolver<'_>,
        work: &mut WorkBudget<'_>,
    ) -> Result<(), QueryError> {
        work.admit(64, 8 * size_of::<TermStoreSnapshotStamp>())?;
        let current = source.terms.snapshot_stamp();
        let valid = self.terms == current
            && self.metadata == source.terms.checker_visible_metadata_generation()
            && self.versions == (source.eq_adj_version, source.propagate_state_version)
            && self.scope
                == source
                    .registered_term_scope
                    .as_ref()
                    .map(|s| (s.len(), s.allocation_size()));
        drop(current);
        require(valid, work)
    }
}
