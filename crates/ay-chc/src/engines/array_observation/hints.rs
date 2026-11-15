// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Static hints are candidates, not proof or transformation authority.
//! Scan the entire borrowed batch before copying formulas. Only canonical
//! retained scalar arguments cross the authenticated projection map. No
//! array hint, provider, cache or shared lemma state is silently discarded.

use super::super::array_projection::expression::checked_sort_with_bound;
use super::{
    admission::{bounded_sort, Scan, MAX_ARITY},
    map,
    projection::Projection,
};
use crate::problem::ArrayScalarizedArg;
use crate::{ChcExpr, ChcSort, ChcVar, LemmaHint};

mod rewrite;

pub(super) const MAX_HINTS: usize = 128;

/// A whole-batch occurrence/depth/fanout/text admission, borrowing all input.
/// Finite candidate caps decline to original PDR, not a process RSS guarantee.
pub(super) struct Admitted<'a> {
    hints: &'a [LemmaHint],
}

struct Binding {
    original: ChcVar,
    reduced: ChcVar,
}

fn scalar(sort: &ChcSort) -> bool {
    bounded_sort(sort) && !matches!(sort, ChcSort::Array(..))
}

impl<'a> Admitted<'a> {
    pub(super) fn new(hints: &'a [LemmaHint], poll: &mut dyn FnMut() -> bool) -> Option<Self> {
        if !poll() || hints.len() > MAX_HINTS {
            return None;
        }
        let mut scan = Scan::default();
        for hint in hints {
            if !poll() {
                return None;
            }
            scan.text(hint.source)?;
            scan.expression(&hint.formula, poll)?;
        }
        poll().then_some(Self { hints })
    }

    pub(super) fn rebase(
        self,
        projected: &Projection<'_>,
        poll: &mut dyn FnMut() -> bool,
    ) -> Option<Vec<LemmaHint>> {
        map::authenticate(projected, poll)?;
        if !poll() {
            return None;
        }
        let mut rebased = Vec::new();
        rebased.try_reserve_exact(self.hints.len()).ok()?;
        for hint in self.hints {
            if !poll() {
                return None;
            }
            let bindings = bindings(projected, hint, poll)?;
            closed(&hint.formula, &bindings, original_variable, poll)?;
            let formula = rewrite::expression(&hint.formula, &bindings, poll)?;
            closed(&formula, &bindings, reduced_variable, poll)?;
            if !poll() {
                return None;
            }
            rebased.push(LemmaHint::new(
                hint.predicate,
                formula,
                hint.priority,
                hint.source,
            ));
        }
        poll().then_some(rebased)
    }
}

fn bindings(
    projected: &Projection<'_>,
    hint: &LemmaHint,
    poll: &mut dyn FnMut() -> bool,
) -> Option<Vec<Binding>> {
    let original = projected.original.get_predicate(hint.predicate)?;
    let reduced = projected.reduced.get_predicate(hint.predicate)?;
    if !poll()
        || original.id != hint.predicate
        || reduced.id != hint.predicate
        || original.name != reduced.name
        || original.arg_sorts.len() > MAX_ARITY
        || reduced.arg_sorts.len() > MAX_ARITY
    {
        return None;
    }
    let mappings = projected.map.pred_args.get(&hint.predicate)?;
    let mut bindings = Vec::new();
    bindings.try_reserve_exact(original.arg_sorts.len()).ok()?;
    for (new_position, mapping) in mappings.iter().enumerate() {
        if !poll() {
            return None;
        }
        let ArrayScalarizedArg::Original(old_position) = mapping else {
            continue;
        };
        let old_sort = original.arg_sorts.get(*old_position)?;
        if !scalar(old_sort) {
            continue;
        }
        if reduced.arg_sorts.get(new_position)? != old_sort {
            return None;
        }
        bindings.push(Binding {
            original: ChcVar::new(
                crate::canonical_var_name(hint.predicate, *old_position),
                old_sort.clone(),
            ),
            reduced: ChcVar::new(
                crate::canonical_var_name(hint.predicate, new_position),
                old_sort.clone(),
            ),
        });
    }
    poll().then_some(bindings)
}

fn original_variable(binding: &Binding) -> &ChcVar {
    &binding.original
}

fn reduced_variable(binding: &Binding) -> &ChcVar {
    &binding.reduced
}

fn closed(
    formula: &ChcExpr,
    bindings: &[Binding],
    variable: fn(&Binding) -> &ChcVar,
    poll: &mut dyn FnMut() -> bool,
) -> Option<()> {
    let actual = checked_sort_with_bound(
        formula,
        poll,
        &mut |var| bindings.iter().any(|binding| variable(binding) == var),
        &mut scalar,
    )?;
    (actual == ChcSort::Bool && poll()).then_some(())
}
