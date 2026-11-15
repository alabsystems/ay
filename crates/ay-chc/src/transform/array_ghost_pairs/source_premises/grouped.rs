// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Cartesian, simultaneous instances of one original lexical binder group.

use super::*;

pub(super) fn instances(
    premise: &UniversalPremise,
    terms: &[ChcExpr],
    control: &SourceControl<'_>,
    out: &mut Vec<ChcExpr>,
) -> Option<()> {
    // The immutable source admits at most eight binders. Defend this private
    // seam before allocating, too; it is also used by solver-free tests.
    if premise.binder_count() > crate::quantified::MAX_PREMISE_BINDERS {
        control.stopped.set(true);
        return None;
    }
    control.charge(premise.binder_count().checked_mul(3)?)?;
    let binders: Vec<_> = premise.binders().collect();
    let mut choices = Vec::new();
    choices.try_reserve_exact(binders.len()).ok()?;
    let mut count = 1usize;
    for binder in &binders {
        control.charge(terms.len())?;
        let mut matching = Vec::new();
        matching.try_reserve_exact(terms.len()).ok()?;
        for term in terms {
            control.poll()?;
            if term.sort() == binder.sort {
                matching.push(term);
            }
        }
        count = match count.checked_mul(matching.len()) {
            Some(count) => count,
            None => {
                control.stopped.set(true);
                return None;
            }
        };
        choices.push(matching);
    }
    // Precharge tuple selection before any expansion. Each recursively copied
    // matrix/replacement is additionally charged against the same live ledger.
    let Some(work) = count.checked_mul(binders.len()) else {
        control.stopped.set(true);
        return None;
    };
    control.charge(work)?;
    let mut indices = vec![0; binders.len()];
    let mut bindings = Vec::new();
    bindings.try_reserve_exact(binders.len()).ok()?;
    for _ in 0..count {
        control.poll()?;
        bindings.clear();
        for ((binder, choices), index) in binders.iter().zip(&choices).zip(&indices) {
            bindings.push((*binder, *choices.get(*index)?));
        }
        let instance = substitute(premise.matrix(), &bindings, 0, control)?;
        out.try_reserve(1).ok()?;
        out.push(instance);
        // Last binder varies fastest, preserving source term order and
        // duplicates independently at every dimension.
        for position in (0..indices.len()).rev() {
            indices[position] += 1;
            if indices[position] < choices[position].len() {
                break;
            }
            indices[position] = 0;
        }
    }
    control.poll()
}
