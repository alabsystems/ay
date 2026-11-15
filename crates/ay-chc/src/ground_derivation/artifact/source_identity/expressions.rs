// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates

//! Cooperative polling inside the existing bounded source occurrence walks.

use super::*;

fn push_source_identity_expr<'a>(
    control: &mut GroundValidationControl<'_>,
    stack: &mut Vec<(&'a ChcExpr, usize, bool)>,
    expression: &'a ChcExpr,
    depth: usize,
    work: usize,
    bound_body: bool,
) -> Result<(), ChcGroundDerivationArtifactError> {
    control.poll().map_err(interruption_error)?;
    let limit = whole_source_work_limit(control);
    if depth > CHC_GROUND_DERIVATION_MAX_SOURCE_DEPTH
        || work
            .checked_add(stack.len())
            .is_none_or(|projected| projected >= limit)
    {
        return Err(source_identity_error(
            "whole-problem source expression exceeds depth/work bound",
        ));
    }
    stack.push((expression, depth, bound_body));
    Ok(())
}

pub(super) fn preflight_expressions(
    control: &mut GroundValidationControl<'_>,
    problem: &ChcProblem,
    work: &mut usize,
    priced: &mut PricedDatatypes,
) -> Result<usize, ChcGroundDerivationArtifactError> {
    let mut expression_nodes = 0usize;
    let mut bounded_expression_sorts = Vec::new();
    let mut stack = Vec::new();
    for clause in problem.clauses() {
        charge_source_identity_work(control, work, 64)?;
        charge_source_identity_work(
            control,
            work,
            clause
                .body
                .predicates
                .len()
                .checked_mul(2)
                .ok_or_else(|| source_identity_error("clause structure work overflow"))?,
        )?;
        if let Some(action_name) = clause
            .action_id
            .and_then(|action| problem.action_name(action))
        {
            charge_source_identity_work(
                control,
                work,
                action_name
                    .len()
                    .checked_mul(2)
                    .ok_or_else(|| source_identity_error("clause action work overflow"))?,
            )?;
        }
        if let Some(constraint) = &clause.body.constraint {
            push_source_identity_expr(control, &mut stack, constraint, 1, *work, false)?;
        }
        for (_, arguments) in &clause.body.predicates {
            control.poll().map_err(interruption_error)?;
            for argument in arguments {
                push_source_identity_expr(control, &mut stack, argument, 1, *work, false)?;
            }
        }
        if let crate::ClauseHead::Predicate(_, arguments) = &clause.head {
            for argument in arguments {
                push_source_identity_expr(control, &mut stack, argument, 1, *work, false)?;
            }
        }
        while let Some((expression, depth, bound_body)) = stack.pop() {
            expression_nodes = expression_nodes
                .checked_add(1)
                .ok_or_else(|| source_identity_error("source expression count overflow"))?;
            let depth_work = depth
                .checked_mul(2)
                .ok_or_else(|| source_identity_error("source identity depth work overflow"))?;
            // The wire identity renders every node's ancestry, so each node
            // and name costs its depth. Native validation renders nothing (see
            // `NATIVE_WHOLE_SOURCE_WORK`): a node costs the 128-unit floor that
            // keeps the native ceiling at ~2M occurrences, plus its depth for
            // the recursive sort derivation below, and a name its length.
            // Pricing native nodes as rendered ancestry refused a 200k-node
            // vmt transition (`kbfiltr_simpl2_BUG`) at ~1 G.
            let (identity_multiplier, node_work) = if control.native_whole_source() {
                (2, depth_work.checked_add(128))
            } else {
                (depth_work, 64usize.checked_mul(depth_work))
            };
            charge_source_identity_work(
                control,
                work,
                node_work.ok_or_else(|| source_identity_error("source node work overflow"))?,
            )?;
            bounded_expression_sorts.push((expression, identity_multiplier));
            if bound_body && matches!(expression, ChcExpr::FuncApp(..)) {
                return Err(error(
                    ChcGroundDerivationArtifactErrorReason::InvalidSourceProblem,
                    "native lambda replay does not admit bound-code function observations",
                ));
            }
            preflight_expression_identity(control, expression, identity_multiplier, work, priced)?;
            push_children(control, expression, depth, *work, bound_body, &mut stack)?;
        }
    }
    validate_expression_sorts(control, bounded_expression_sorts, work)?;
    Ok(expression_nodes)
}

fn preflight_expression_identity(
    control: &mut GroundValidationControl<'_>,
    expression: &ChcExpr,
    identity_multiplier: usize,
    work: &mut usize,
    priced: &mut PricedDatatypes,
) -> Result<(), ChcGroundDerivationArtifactError> {
    match expression {
        ChcExpr::ArrayLambda(lambda) => {
            if !control.is_native() {
                return Err(source_identity_error(
                    "array lambdas remain unsupported in ground wire artifacts",
                ));
            }
            for formal in std::iter::once(lambda.binder()).chain(lambda.formals()) {
                charge_source_identity_work(
                    control,
                    work,
                    formal
                        .name
                        .len()
                        .checked_mul(identity_multiplier)
                        .ok_or_else(|| source_identity_error("lambda name work overflow"))?,
                )?;
                preflight_source_identity_sort_multiplied(
                    control,
                    &formal.sort,
                    work,
                    identity_multiplier,
                    priced,
                )?;
            }
        }
        ChcExpr::Var(variable) => {
            charge_source_identity_work(
                control,
                work,
                variable
                    .name
                    .len()
                    .checked_mul(identity_multiplier)
                    .ok_or_else(|| source_identity_error("variable name work overflow"))?,
            )?;
            preflight_source_identity_sort_multiplied(
                control,
                &variable.sort,
                work,
                identity_multiplier,
                priced,
            )?;
        }
        ChcExpr::FuncApp(name, return_sort, _) => {
            charge_source_identity_work(
                control,
                work,
                name.len()
                    .checked_mul(identity_multiplier)
                    .ok_or_else(|| source_identity_error("function name work overflow"))?,
            )?;
            preflight_source_identity_sort_multiplied(
                control,
                return_sort,
                work,
                identity_multiplier,
                priced,
            )?;
        }
        ChcExpr::PredicateApp(name, _, _) | ChcExpr::IsTesterMarker(name) => {
            charge_source_identity_work(
                control,
                work,
                name.len()
                    .checked_mul(identity_multiplier)
                    .ok_or_else(|| source_identity_error("source name work overflow"))?,
            )?;
        }
        ChcExpr::ConstArray(sort, _) | ChcExpr::ConstArrayMarker(sort) => {
            preflight_source_identity_sort_multiplied(
                control,
                sort,
                work,
                identity_multiplier,
                priced,
            )?;
        }
        ChcExpr::Bool(_)
        | ChcExpr::Int(_)
        | ChcExpr::Real(_, _)
        | ChcExpr::BitVec(_, _)
        | ChcExpr::Op(_, _) => {}
    }
    Ok(())
}

fn push_children<'a>(
    control: &mut GroundValidationControl<'_>,
    expression: &'a ChcExpr,
    depth: usize,
    work: usize,
    bound_body: bool,
    stack: &mut Vec<(&'a ChcExpr, usize, bool)>,
) -> Result<(), ChcGroundDerivationArtifactError> {
    let children: &[std::sync::Arc<ChcExpr>] = match expression {
        ChcExpr::ArrayLambda(lambda) => {
            push_source_identity_expr(
                control,
                stack,
                lambda.body(),
                depth
                    .checked_add(1)
                    .ok_or_else(|| source_identity_error("lambda depth overflow"))?,
                work,
                true,
            )?;
            lambda.captures()
        }
        ChcExpr::Op(_, arguments)
        | ChcExpr::PredicateApp(_, _, arguments)
        | ChcExpr::FuncApp(_, _, arguments) => arguments,
        ChcExpr::ConstArray(_, value) => std::slice::from_ref(value),
        ChcExpr::Bool(_)
        | ChcExpr::Int(_)
        | ChcExpr::Real(_, _)
        | ChcExpr::BitVec(_, _)
        | ChcExpr::Var(_)
        | ChcExpr::ConstArrayMarker(_)
        | ChcExpr::IsTesterMarker(_) => &[],
    };
    let child_depth = depth
        .checked_add(1)
        .ok_or_else(|| source_identity_error("whole-problem source expression depth overflow"))?;
    for child in children {
        push_source_identity_expr(control, stack, child, child_depth, work, bound_body)?;
    }
    Ok(())
}

fn validate_expression_sorts(
    control: &mut GroundValidationControl<'_>,
    bounded_expression_sorts: Vec<(&ChcExpr, usize)>,
    work: &mut usize,
) -> Result<(), ChcGroundDerivationArtifactError> {
    // Recursive operator-sort derivation is safe only after the complete
    // iterative expression/sort preflight has accepted every live clause.
    for (expression, identity_multiplier) in bounded_expression_sorts {
        control.poll().map_err(interruption_error)?;
        let expression_sort = catch_unwind(AssertUnwindSafe(|| expression.sort()));
        control.poll().map_err(interruption_error)?;
        let expression_sort = expression_sort.map_err(|_| {
            source_identity_error("whole-problem expression sort derivation panicked")
        })?;
        if let ChcSort::BitVec(width) = expression_sort {
            charge_source_identity_work(
                control,
                work,
                source_bitvector_width_work(width)?
                    .checked_mul(identity_multiplier)
                    .ok_or_else(|| {
                        source_identity_error("source bitvector expression work overflow")
                    })?,
            )?;
        }
    }
    Ok(())
}
