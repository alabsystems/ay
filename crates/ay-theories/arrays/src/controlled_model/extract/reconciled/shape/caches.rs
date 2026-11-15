// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

pub(super) fn validate(
    source: &ArraySolver<'_>,
    work: &mut WorkBudget<'_>,
) -> Result<(), QueryError> {
    owned::scan_table::<(TermId, (TermId, TermId, TermId))>(
        source.store_cache.allocation_size(),
        work,
    )?;
    for (&term, &(base, index, value)) in &source.store_cache {
        work.charge(128)?;
        application(source, term, "store", &[base, index, value], work)?;
        let _ = scan::chain(source, term, work)?;
    }
    owned::scan_table::<(TermId, (TermId, TermId))>(source.select_cache.allocation_size(), work)?;
    for (&term, &(array, index)) in &source.select_cache {
        work.charge(128)?;
        application(source, term, "select", &[array, index], work)?;
    }
    owned::scan_table::<(TermId, TermId)>(source.const_array_cache.allocation_size(), work)?;
    for (&term, &value) in &source.const_array_cache {
        work.charge(128)?;
        application(source, term, "const-array", &[value], work)?;
    }
    owned::scan_table::<(TermId, TermId)>(source.default_cache.allocation_size(), work)?;
    for (&array, &term) in &source.default_cache {
        work.charge(128)?;
        application(source, term, "default", &[array], work)?;
    }
    owned::scan_table::<(TermId, crate::ArrayVarData)>(source.array_vars.allocation_size(), work)?;
    for &term in source.array_vars.keys() {
        if !matches!(key(source, term, work)?, Key::Array(..)) {
            return Err(work.refuse_exhaustion());
        }
    }
    owned::scan_table::<(TermId, (TermId, TermId))>(source.equality_cache.allocation_size(), work)?;
    for (&term, &(left, right)) in &source.equality_cache {
        work.charge(128)?;
        application(source, term, "=", &[left, right], work)?;
    }
    adjacency(source, work)?;
    Ok(())
}

fn adjacency(source: &ArraySolver<'_>, work: &mut WorkBudget<'_>) -> Result<(), QueryError> {
    owned::scan_table::<(TermId, Vec<(TermId, TermId)>)>(source.eq_adj.allocation_size(), work)?;
    for (&term, neighbors) in &source.eq_adj {
        let sort = key(source, term, work)?;
        // Scalar vertices must come from real current equality/origin edges.
        // In particular an orphan inserted with an empty Vec is NOT admitted.
        work.charge(8)?;
        if matches!(sort, Key::Scalar(_)) && neighbors.is_empty() {
            return Err(work.refuse_exhaustion());
        }
        let visits = owned::checked(neighbors.len().checked_mul(32), work)?;
        work.charge(visits)?;
        for &(other, reason) in neighbors {
            require(key(source, other, work)? == sort, work)?;
            if reason == TermId::SENTINEL {
                // External equalities are ordered fixed-key rows, not a hash
                // table. Prepay each complete active-row membership scan.
                let visits = owned::checked(
                    source
                        .external_eqs
                        .len()
                        .checked_mul(32)
                        .and_then(|n| n.checked_add(64)),
                    work,
                )?;
                work.charge(visits)?;
                let forward = source.external_eqs.contains(&(term, other));
                work.charge(visits)?;
                require(
                    forward || source.external_eqs.contains(&(other, term)),
                    work,
                )?;
            } else {
                let &(left, right) = scan::lookup(&source.equality_cache, reason, work)?
                    .ok_or_else(|| work.refuse_exhaustion())?;
                require(
                    (left == term && right == other) || (left == other && right == term),
                    work,
                )?;
                require(
                    scan::lookup(&source.assigns, reason, work)?.copied() == Some(true),
                    work,
                )?;
            }
        }
    }
    Ok(())
}

fn application(
    source: &ArraySolver<'_>,
    term: TermId,
    name: &str,
    expected: &[TermId],
    work: &mut WorkBudget<'_>,
) -> Result<(), QueryError> {
    super::validate(source, term, work)?;
    work.charge(128)?;
    let TermData::App(Symbol::Named(actual), args) = source.terms.get(term) else {
        return Err(work.refuse_exhaustion());
    };
    let cost = owned::checked(
        actual
            .len()
            .checked_add(args.len())
            .and_then(|n| n.checked_mul(16)),
        work,
    )?;
    work.charge(cost)?;
    require(actual.as_str() == name && args.as_slice() == expected, work)
}
