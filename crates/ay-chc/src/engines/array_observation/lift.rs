// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Typed closed-formal substitution into original array observations. A fresh
//! model deliberately drops search flags/certificates; all source clauses must
//! still pass the ordinary verifier before publication.

use super::super::array_projection::expression::checked_sort_with_bound;
use super::{
    admission::{bounded_sort, Scan},
    map,
    projection::Projection,
};
use crate::problem::ArrayScalarizedArg;
use crate::{ChcExpr, ChcSort, ChcVar, InvariantModel, PredicateInterpretation};
use ay_core::kani_compat::{DetHashMap, DetHashSet};

impl Projection<'_> {
    pub(super) fn lift(
        &self,
        candidate: &InvariantModel,
        poll: &mut dyn FnMut() -> bool,
    ) -> Option<InvariantModel> {
        map::authenticate(self, poll)?;
        if !poll()
            || candidate.len() != self.original.predicates().len()
            || candidate.has_quantified_array_certificate()
        {
            return None;
        }
        let mut scan = Scan::default();
        let mut lifted = InvariantModel::new();
        for (old, reduced) in self
            .original
            .predicates()
            .iter()
            .zip(self.reduced.predicates())
        {
            if !poll() {
                return None;
            }
            let interpretation = candidate.get(&old.id)?;
            if interpretation.vars.len() != reduced.arg_sorts.len() {
                return None;
            }
            scan.expression(&interpretation.formula, poll)?;
            closed(
                &interpretation.vars,
                &reduced.arg_sorts,
                &interpretation.formula,
                &mut scan,
                poll,
            )?;
            let mut variables = Vec::new();
            variables.try_reserve_exact(old.arg_sorts.len()).ok()?;
            for (position, sort) in old.arg_sorts.iter().enumerate() {
                if !poll() {
                    return None;
                }
                variables.push(ChcVar::new(
                    crate::canonical_var_name(old.id, position),
                    sort.clone(),
                ));
            }
            let mappings = self.map.pred_args.get(&old.id)?;
            let replacements = substitutions(&interpretation.vars, &variables, mappings, poll)?;
            if !poll() {
                return None;
            }
            // Existing substitution is opaque, with admitted depth/occurrences.
            // Do not simplify away source observations or copy model flags.
            let formula = interpretation.formula.substitute(&replacements);
            if !poll() {
                return None;
            }
            scan.expression(&formula, poll)?;
            closed(&variables, &old.arg_sorts, &formula, &mut scan, poll)?;
            lifted.set(old.id, PredicateInterpretation::new(variables, formula));
        }
        // Count equality + each exact source ID lookup excludes foreign IDs.
        poll().then_some(lifted)
    }
}

fn closed(
    variables: &[ChcVar],
    sorts: &[ChcSort],
    formula: &ChcExpr,
    scan: &mut Scan,
    poll: &mut dyn FnMut() -> bool,
) -> Option<()> {
    if variables.len() != sorts.len() {
        return None;
    }
    let mut names = DetHashSet::default();
    let mut bindings = DetHashMap::default();
    for (variable, sort) in variables.iter().zip(sorts) {
        scan.text(&variable.name)?;
        if !poll()
            || !bounded_sort(&variable.sort)
            || &variable.sort != sort
            || !names.insert(variable.name.as_str())
        {
            return None;
        }
        bindings.insert(variable.name.as_str(), &variable.sort);
    }
    let actual = checked_sort_with_bound(
        formula,
        poll,
        &mut |var| {
            bindings
                .get(var.name.as_str())
                .is_some_and(|sort| *sort == &var.sort)
        },
        &mut |sort| bounded_sort(sort),
    )?;
    (actual == ChcSort::Bool && poll()).then_some(())
}

fn substitutions(
    reduced: &[ChcVar],
    original: &[ChcVar],
    mappings: &[ArrayScalarizedArg],
    poll: &mut dyn FnMut() -> bool,
) -> Option<Vec<(ChcVar, ChcExpr)>> {
    if reduced.len() != mappings.len() {
        return None;
    }
    let mut substitutions = Vec::new();
    substitutions.try_reserve_exact(mappings.len()).ok()?;
    for (variable, mapping) in reduced.iter().zip(mappings) {
        if !poll() {
            return None;
        }
        let replacement = match mapping {
            ArrayScalarizedArg::Original(position) => {
                ChcExpr::var(original.get(*position)?.clone())
            }
            ArrayScalarizedArg::Select {
                original_arg,
                index,
            } => ChcExpr::select(
                ChcExpr::var(original.get(*original_arg)?.clone()),
                index.clone(),
            ),
        };
        substitutions.push((variable.clone(), replacement));
    }
    poll().then_some(substitutions)
}
