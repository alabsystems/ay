// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::smt::executor_adapter::sort_to_smtlib;

pub(super) struct Input<'a> {
    pub(super) clause: &'a HornClause,
    pub(super) premises: &'a [crate::quantified::UniversalPremise],
    pub(super) variables: &'a [ChcVar],
    pub(super) head_axes: &'a [ChcVar],
    pub(super) bodies: &'a [pullback::Body],
    pub(super) hints: &'a [ChcExpr],
    pub(super) head: Option<&'a ChcExpr>,
}

pub(super) fn render(
    problem: &QuantifiedChcProblem,
    registry: &Registry,
    input: Input<'_>,
    control: &SourceControl<'_>,
) -> Option<String> {
    let Input {
        clause,
        premises,
        variables,
        head_axes,
        bodies,
        hints,
        head,
    } = input;
    let mut out = String::new();
    push(&mut out, "(set-logic ALL)\n", control)?;
    let declarations = registry.declarations_smtlib().ok()?;
    push(&mut out, &declarations, control)?;
    let functions =
        crate::quantified::functions::controlled::declarations_smtlib(problem, control)?;
    push(&mut out, &functions, control)?;
    if !problem.function_declarations().is_empty()
        || super::super::classify::source(problem, control)? == super::super::classify::Shape::Wide
    {
        for expression in clause
            .body
            .constraint
            .iter()
            .chain(head)
            .chain(hints)
            .chain(
                premises
                    .iter()
                    .map(crate::quantified::UniversalPremise::matrix),
            )
            .chain(bodies.iter().map(|(_, body)| body))
        {
            if crate::quantified::functions::controlled::expression_sort(
                problem, registry, expression, control,
            )? != ChcSort::Bool
            {
                return None;
            }
        }
    }
    for var in variables.iter().chain(head_axes) {
        registry.validate_sort(&var.sort).ok()?;
        control.bytes(
            var.name
                .len()
                .checked_mul(4)?
                .checked_add(sort_bytes(&var.sort)?)?,
        )?;
        push(
            &mut out,
            &format!(
                "(declare-const {} {})\n",
                ay_core::quote_symbol(&var.name),
                sort_to_smtlib(&var.sort)
            ),
            control,
        )?;
    }
    if let Some(constraint) = &clause.body.constraint {
        assertion(&mut out, constraint, control)?;
    }
    for premise in premises {
        let names = source_premises::binder_list(premise, Some(control))?;
        quantified(&mut out, &names, premise.matrix(), control)?;
    }
    for (axes, formula) in bodies {
        if axes.is_empty() {
            assertion(&mut out, formula, control)?;
            continue;
        }
        let mut names = Vec::new();
        for var in axes {
            control.bytes(var.name.len().checked_mul(4)?.checked_add(256)?)?;
            names.push(format!(
                "({} {})",
                ay_core::quote_symbol(&var.name),
                sort_to_smtlib(&var.sort)
            ));
        }
        quantified(&mut out, &names.join(" "), formula, control)?;
    }
    for hint in hints {
        assertion(&mut out, hint, control)?;
    }
    if let Some(head) = head {
        assertion(&mut out, head, control)?;
    }
    push(&mut out, "(check-sat)\n", control)?;
    control.poll()?;
    Some(out)
}

fn quantified(
    out: &mut String,
    names: &str,
    expr: &ChcExpr,
    control: &SourceControl<'_>,
) -> Option<()> {
    source_premises::preflight(expr, control, &mut 0)?;
    let expr = InvariantModel::expr_to_smtlib(expr);
    push(
        out,
        &format!("(assert (forall ({names}) {expr}))\n"),
        control,
    )
}

fn assertion(out: &mut String, expr: &ChcExpr, control: &SourceControl<'_>) -> Option<()> {
    source_premises::preflight(expr, control, &mut 0)?;
    let expr = InvariantModel::expr_to_smtlib(expr);
    push(out, &format!("(assert {expr})\n"), control)
}

fn push(out: &mut String, text: &str, control: &SourceControl<'_>) -> Option<()> {
    if out.len().checked_add(text.len())? > MAX_REPLAY_BYTES {
        return None;
    }
    control.bytes(text.len())?;
    out.try_reserve(text.len()).ok()?;
    out.push_str(text);
    Some(())
}
