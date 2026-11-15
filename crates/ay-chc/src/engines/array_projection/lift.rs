// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Checked, one-way lifting of a reduced candidate. No validation flags or
//! Unsafe witness machinery are copied from the search model.

use ay_core::kani_compat::{DetHashMap, DetHashSet};

use super::expression::checked_sort;
use super::projection::{Columns, Projection};
use crate::pdr::PredicateInterpretation;
use crate::{ChcSort, ChcVar, InvariantModel};

impl Projection {
    pub(super) fn lift(
        &self,
        model: &InvariantModel,
        poll: &mut dyn FnMut() -> bool,
    ) -> Option<InvariantModel> {
        if !poll() || model.len() != self.columns.len() {
            return None;
        }
        let mut lifted = InvariantModel::new();
        for column in &self.columns {
            if !poll() {
                return None;
            }
            let interpretation = model.get(&column.id)?;
            let variables = lift_variables(column, interpretation, poll)?;
            lifted.set(
                column.id,
                PredicateInterpretation::new(variables, interpretation.formula.clone()),
            );
        }
        // Count equality plus a required lookup for every original ID excludes
        // both missing and extra interpretations, including sparse foreign IDs.
        poll().then_some(lifted)
    }
}

fn lift_variables(
    column: &Columns,
    interpretation: &PredicateInterpretation,
    poll: &mut dyn FnMut() -> bool,
) -> Option<Vec<ChcVar>> {
    if interpretation.vars.len() != column.kept.len() {
        return None;
    }
    let mut names = DetHashSet::default();
    let mut bindings = DetHashMap::default();
    for (variable, &position) in interpretation.vars.iter().zip(&column.kept) {
        if !poll()
            || &variable.sort != column.original.get(position)?
            || !names.insert(variable.name.clone())
        {
            return None;
        }
        bindings.insert(variable.name.as_str(), &variable.sort);
    }
    let formula_sort = checked_sort(&interpretation.formula, poll, &mut |variable| {
        bindings
            .get(variable.name.as_str())
            .is_some_and(|sort| *sort == &variable.sort)
    })?;
    drop(bindings);
    if formula_sort != ChcSort::Bool {
        return None;
    }

    let mut variables = Vec::new();
    variables.try_reserve_exact(column.original.len()).ok()?;
    let mut retained = 0;
    for (position, sort) in column.original.iter().enumerate() {
        if !poll() {
            return None;
        }
        if column.kept.get(retained) == Some(&position) {
            variables.push(interpretation.vars.get(retained)?.clone());
            retained += 1;
        } else {
            let name = fresh_name(column, position, &mut names, poll)?;
            variables.push(ChcVar::new(name, sort.clone()));
        }
    }
    drop(names);
    poll().then_some(variables)
}

fn fresh_name(
    column: &Columns,
    position: usize,
    names: &mut DetHashSet<String>,
    poll: &mut dyn FnMut() -> bool,
) -> Option<String> {
    let mut suffix = 0usize;
    loop {
        if !poll() {
            return None;
        }
        let name = format!(
            "__ay_array_projection_{}_{position}_{suffix}",
            column.id.index()
        );
        if names.insert(name.clone()) {
            return Some(name);
        }
        suffix = suffix.checked_add(1)?;
    }
}
