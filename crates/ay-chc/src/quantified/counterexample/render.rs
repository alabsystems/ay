// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Exact satisfiability obligations for a selected original occurrence tree.
//! This renderer selects no tree and grants no verdict. Universal premises are
//! retained, not instantiated; each clause occurrence has its own free values.

use super::SourceControl;
#[cfg(test)]
use super::MAX_PATH_CLAUSES;
use crate::quantified::records::{registry_bytes, Registry};
use crate::quantified::{QuantifiedChcProblem, UniversalPremise};
use crate::{ChcExpr, ChcVar, ClauseHead, HornClause};

mod array_definitions;
mod census;

#[derive(Clone, Copy)]
enum Rendering {
    Original,
    Advice,
}
mod complete;
use complete::Payloads;
pub(super) use complete::{names as complete_names, render as render_complete, CompleteRendered};
mod functions;
mod manifest;
mod output;
use census::Names;
pub(super) use manifest::Rendered;
use output::Output;

#[cfg(test)]
mod deep_tests;
#[cfg(test)]
mod tests;
#[cfg(test)]
mod tree_tests;

type Result<T> = std::result::Result<T, crate::ChcError>;
const MAX_OUTPUT_BYTES: usize = 8 * 1024 * 1024;

fn refused() -> crate::ChcError {
    crate::ChcError::Verification("quantified counterexample rendering refused".to_owned())
}

#[cfg(test)]
pub(super) fn render(
    problem: &QuantifiedChcProblem,
    path: &[usize],
    control: &SourceControl<'_>,
) -> Result<String> {
    if path.is_empty() || path.len() > MAX_PATH_CLAUSES {
        return Err(refused());
    }
    control
        .bytes(
            path.len()
                .checked_mul(
                    std::mem::size_of::<Vec<usize>>()
                        .checked_add(std::mem::size_of::<usize>())
                        .ok_or_else(refused)?,
                )
                .ok_or_else(refused)?,
        )
        .ok_or_else(refused)?;
    let mut premises = Vec::new();
    premises
        .try_reserve_exact(path.len())
        .map_err(|_| refused())?;
    for step in 0..path.len() {
        control.charge(1).ok_or_else(refused)?;
        premises.push(if step == 0 { vec![] } else { vec![step - 1] });
    }
    render_derivation(problem, path, &premises, control)
}

pub(super) fn render_derivation(
    problem: &QuantifiedChcProblem,
    indices: &[usize],
    premise_steps: &[Vec<usize>],
    control: &SourceControl<'_>,
) -> Result<String> {
    let (result, scopes, _) = render_inner(
        problem,
        indices,
        premise_steps,
        control,
        &mut Payloads::None,
    )?;
    drop(scopes);
    // Registry, scopes and all source-census scratch were destroyed first.
    control.poll().ok_or_else(refused)?;
    Ok(result)
}

/// Retain every occurrence-local declaration without changing the obligation.
/// Bound universal variables are not assignments; the lexical source census
/// excludes them while retaining variables used only in premise matrices.
pub(super) fn render_with_bindings<'a>(
    problem: &'a QuantifiedChcProblem,
    indices: &[usize],
    premise_steps: &[Vec<usize>],
    control: &SourceControl<'_>,
) -> Result<Rendered<'a>> {
    let (obligation, scopes, function_declarations) = render_inner(
        problem,
        indices,
        premise_steps,
        control,
        &mut Payloads::None,
    )?;
    let result = manifest::retain(obligation, scopes, function_declarations, control)?;
    // All source census, registry and scope-iteration scratch has been dropped.
    control.poll().ok_or_else(refused)?;
    Ok(result)
}

/// Search-only equivalent equations. This output is never a canonical
/// obligation, assertion-range manifest, base counterexample or pin authority.
pub(super) fn render_advice(
    problem: &QuantifiedChcProblem,
    indices: &[usize],
    premise_steps: &[Vec<usize>],
    control: &SourceControl<'_>,
) -> Result<String> {
    let (result, scopes, _) = render_inner_mode(
        problem,
        indices,
        premise_steps,
        control,
        &mut Payloads::None,
        Rendering::Advice,
    )?;
    drop(scopes);
    control.poll().ok_or_else(refused)?;
    Ok(result)
}

fn render_inner<'a>(
    problem: &'a QuantifiedChcProblem,
    path: &[usize],
    premise_steps: &[Vec<usize>],
    control: &SourceControl<'_>,
    payloads: &mut Payloads,
) -> Result<(String, Vec<Scope<'a>>, std::ops::Range<usize>)> {
    render_inner_mode(
        problem,
        path,
        premise_steps,
        control,
        payloads,
        Rendering::Original,
    )
}

fn render_inner_mode<'a>(
    problem: &'a QuantifiedChcProblem,
    path: &[usize],
    premise_steps: &[Vec<usize>],
    control: &SourceControl<'_>,
    payloads: &mut Payloads,
    rendering: Rendering,
) -> Result<(String, Vec<Scope<'a>>, std::ops::Range<usize>)> {
    super::derivation::validate(problem, path, premise_steps, control)?;
    let source = problem.source_problem();
    // Three allowances cover registry construction, declaration rendering and
    // its retained output copy. These are conservative charges, not RSS bounds.
    let registry_cost = registry_bytes(source)
        .and_then(|bytes| bytes.checked_mul(3))
        .ok_or_else(refused)?;
    control.bytes(registry_cost).ok_or_else(refused)?;
    let registry = Registry::new(source).map_err(|_| refused())?;
    let mut names = Names::new(problem, control)?;
    let mut output = Output::new(control);
    output.push("(set-logic ALL)\n")?;
    let declarations = registry.declarations_smtlib().map_err(|_| refused())?;
    output.push(&declarations)?;
    let functions_start = output.len();
    functions::render(problem, &mut output, control)?;
    let function_declarations = functions_start..output.len();
    control
        .bytes(
            path.len()
                .checked_mul(std::mem::size_of::<Scope<'_>>())
                .ok_or_else(refused)?,
        )
        .ok_or_else(refused)?;
    let mut scopes = Vec::new();
    scopes
        .try_reserve_exact(path.len())
        .map_err(|_| refused())?;
    for &index in path {
        control.poll().ok_or_else(refused)?;
        let variables = census::free_variables(
            &source.clauses()[index],
            &problem.premises()[index],
            control,
        )?;
        let scope = Scope::new(variables, &mut names, &mut output, control)?;
        scopes.push(scope);
    }
    // A nullary unconstrained path is satisfiable too, but still supplies one
    // explicit hard assertion to the native query boundary.
    let start = output.len();
    output.push("(assert true)\n")?;
    payloads.retain(start, output.len(), control)?;
    for (step, &index) in path.iter().enumerate() {
        control.poll().ok_or_else(refused)?;
        clause_payloads(
            problem,
            path,
            premise_steps,
            &scopes,
            step,
            index,
            &mut output,
            payloads,
            control,
            rendering,
        )?;
    }
    output.push("(check-sat)\n")?;
    Ok((output.finish(), scopes, function_declarations))
}

fn clause_payloads(
    problem: &QuantifiedChcProblem,
    path: &[usize],
    edges: &[Vec<usize>],
    scopes: &[Scope<'_>],
    step: usize,
    index: usize,
    output: &mut Output<'_, '_>,
    payloads: &mut Payloads,
    control: &SourceControl<'_>,
    rendering: Rendering,
) -> Result<()> {
    let source = problem.source_problem();
    let clause = &source.clauses()[index];
    if let Some(constraint) = &clause.body.constraint {
        let start = output.len();
        assertion(output, &scopes[step], constraint, None, rendering, control)?;
        payloads.retain(start, output.len(), control)?;
    }
    for premise in &problem.premises()[index] {
        let start = output.len();
        assertion(
            output,
            &scopes[step],
            premise.matrix(),
            Some(premise),
            rendering,
            control,
        )?;
        payloads.retain(start, output.len(), control)?;
    }
    for ((_, current), &previous_step) in clause.body.predicates.iter().zip(&edges[step]) {
        control.charge(1).ok_or_else(refused)?;
        let ClauseHead::Predicate(_, previous) = &source.clauses()[path[previous_step]].head else {
            return Err(refused());
        };
        for (current, previous) in current.iter().zip(previous) {
            let start = output.len();
            output.push("(assert (= ")?;
            scopes[step].expression(output, current)?;
            output.push(" ")?;
            scopes[previous_step].expression(output, previous)?;
            output.push("))\n")?;
            payloads.retain(start, output.len(), control)?;
        }
    }
    Ok(())
}

struct Scope<'a> {
    variables: Vec<(&'a ChcVar, String)>,
}

impl<'a> Scope<'a> {
    fn new(
        variables: Vec<&'a ChcVar>,
        names: &mut Names<'_>,
        output: &mut Output<'_, '_>,
        control: &SourceControl<'_>,
    ) -> Result<Self> {
        control
            .bytes(
                variables
                    .len()
                    .checked_mul(std::mem::size_of::<(&ChcVar, String)>())
                    .ok_or_else(refused)?,
            )
            .ok_or_else(refused)?;
        let mut bindings = Vec::new();
        bindings
            .try_reserve_exact(variables.len())
            .map_err(|_| refused())?;
        for variable in variables {
            let name = names.fresh(control)?;
            output.push("(declare-const ")?;
            output.push(&name)?;
            output.push(" ")?;
            output.sort(&variable.sort)?;
            output.push(")\n")?;
            bindings.push((variable, name));
        }
        Ok(Self {
            variables: bindings,
        })
    }

    fn open(&self, output: &mut Output<'_, '_>) -> Result<()> {
        if self.variables.is_empty() {
            return Ok(());
        }
        output.push("(let (")?;
        for (variable, value) in &self.variables {
            output.push("(")?;
            output.symbol(&variable.name)?;
            output.push(" ")?;
            output.push(value)?;
            output.push(")")?;
        }
        output.push(") ")
    }

    fn close(&self, output: &mut Output<'_, '_>) -> Result<()> {
        if self.variables.is_empty() {
            Ok(())
        } else {
            output.push(")")
        }
    }

    fn expression(&self, output: &mut Output<'_, '_>, expression: &ChcExpr) -> Result<()> {
        self.open(output)?;
        output.expression(expression)?;
        self.close(output)
    }
}

fn assertion(
    output: &mut Output<'_, '_>,
    scope: &Scope<'_>,
    expression: &ChcExpr,
    premise: Option<&UniversalPremise>,
    rendering: Rendering,
    control: &SourceControl<'_>,
) -> Result<()> {
    output.push("(assert ")?;
    scope.open(output)?;
    if let (Rendering::Advice, Some(premise)) = (rendering, premise) {
        if let Some(definition) = array_definitions::recognize(premise, control)? {
            definition.write(output)?;
            scope.close(output)?;
            return output.push(")\n");
        }
    }
    if let Some(premise) = premise {
        output.push("(forall (")?;
        for binder in premise.binders() {
            output.push("(")?;
            output.symbol(&binder.name)?;
            output.push(" ")?;
            output.sort(&binder.sort)?;
            output.push(")")?;
        }
        output.push(") ")?;
    }
    output.expression(expression)?;
    if premise.is_some() {
        output.push(")")?;
    }
    scope.close(output)?;
    output.push(")\n")
}
