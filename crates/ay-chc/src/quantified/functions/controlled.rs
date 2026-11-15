// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Bounded copies of the authenticated source registry, never inferred UFs.

use super::{Functions, QuantifiedChcFunction};
use crate::quantified::QuantifiedChcProblem;
use crate::transform::array_ghost_pairs::source_premises::SourceControl;
use crate::ChcSort;

mod types;
pub(crate) use types::expression_sort;
#[cfg(test)]
mod tests;

/// An owned immutable declaration snapshot for source-preserving transforms.
#[derive(Debug)]
pub(crate) struct RetainedFunctions(Functions);

fn debit(functions: &Functions, copies: usize, control: &SourceControl<'_>) -> Option<()> {
    control.poll()?;
    control.charge(functions.work().checked_mul(copies)?)?;
    control.bytes(functions.copy_bytes().checked_mul(copies)?)
}

pub(crate) fn retain(
    problem: &QuantifiedChcProblem,
    control: &SourceControl<'_>,
) -> Option<RetainedFunctions> {
    debit(&problem.functions, 1, control)?;
    let retained = RetainedFunctions(problem.functions.clone());
    control.poll()?;
    Some(retained)
}

#[cfg(test)]
fn copy_declarations(
    problem: &QuantifiedChcProblem,
    control: &SourceControl<'_>,
) -> Option<Vec<QuantifiedChcFunction>> {
    copy(&problem.functions, control)
}

fn copy(functions: &Functions, control: &SourceControl<'_>) -> Option<Vec<QuantifiedChcFunction>> {
    // Ordered public copy, registry rebuild and canonical declaration output.
    // Other source/schema work remains the transform caller's responsibility.
    debit(functions, 3, control)?;
    let mut declarations = Vec::new();
    declarations
        .try_reserve_exact(functions.declarations().len())
        .ok()?;
    declarations.extend(functions.declarations().iter().cloned());
    control.poll()?;
    Some(declarations)
}

/// Includes unused names. The debit covers an owned namespace insertion too.
pub(crate) fn names<'a>(
    problem: &'a QuantifiedChcProblem,
    control: &SourceControl<'_>,
) -> Option<impl Iterator<Item = &'a str>> {
    debit(&problem.functions, 1, control)?;
    Some(problem.functions.names())
}

/// Emit each complete ordered declaration once, still UNINTERPRETED.
pub(crate) fn declarations_smtlib(
    problem: &QuantifiedChcProblem,
    control: &SourceControl<'_>,
) -> Option<String> {
    debit(&problem.functions, 1, control)?;
    let output = problem.functions.declarations_smtlib().ok()?;
    control.poll()?;
    Some(output)
}

impl RetainedFunctions {
    pub(crate) fn declarations(
        &self,
        control: &SourceControl<'_>,
    ) -> Option<Vec<QuantifiedChcFunction>> {
        copy(&self.0, control)
    }

    pub(crate) fn contains(&self, name: &str, control: &SourceControl<'_>) -> Option<bool> {
        lookup_cost(&self.0, name, control)?;
        Some(self.0.contains(name))
    }

    pub(crate) fn application(
        &self,
        name: &str,
        args: &[ChcSort],
        recorded: &ChcSort,
        control: &SourceControl<'_>,
    ) -> Option<ChcSort> {
        application(&self.0, name, args, recorded, control)
    }
}

fn lookup_cost(functions: &Functions, name: &str, control: &SourceControl<'_>) -> Option<()> {
    if name.len() > super::super::records::MAX_NAME_BYTES {
        return None;
    }
    // Bound comparisons by the complete admitted inventory, not a guessed
    // tree height: a B-tree node can compare several keys at each level.
    let count = functions.declarations().len();
    control.charge((1 + name.len().div_ceil(64)).checked_mul(count)?)?;
    control.bytes(name.len().checked_mul(count)?)
}

fn application(
    functions: &Functions,
    name: &str,
    args: &[ChcSort],
    recorded: &ChcSort,
    control: &SourceControl<'_>,
) -> Option<ChcSort> {
    lookup_cost(functions, name, control)?;
    control.charge(args.len().checked_add(1)?)?;
    if !super::admission::scalar(recorded) || args.iter().any(|s| !super::admission::scalar(s)) {
        return None;
    }
    for sort in args.iter().chain(std::iter::once(recorded)) {
        control.bytes(super::super::records::sort_bytes(sort)?)?;
    }
    let actual = functions.application(name, args).ok()?;
    if &actual != recorded {
        return None;
    }
    control.poll()?;
    Some(actual)
}
