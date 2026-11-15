// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates

#![cfg(test)]

//! Frozen pre-progress source validator, retained only as an independent oracle.

use super::*;

fn source_identity_error(message: impl Into<String>) -> ChcGroundDerivationArtifactError {
    error(
        ChcGroundDerivationArtifactErrorReason::SourceWorkLimitExceeded,
        message,
    )
}

fn charge_source_identity_work(
    work: &mut usize,
    amount: usize,
) -> Result<(), ChcGroundDerivationArtifactError> {
    *work = work
        .checked_add(amount)
        .filter(|work| *work <= CHC_GROUND_DERIVATION_MAX_SOURCE_WORK)
        .ok_or_else(|| source_identity_error("whole-problem source identity exceeds work bound"))?;
    Ok(())
}

fn source_bitvector_width_work(width: u32) -> Result<usize, ChcGroundDerivationArtifactError> {
    if width == 0 || width > crate::MAX_BITVECTOR_WIDTH {
        return Err(source_identity_error(format!(
            "source bitvector width {width} is outside 1..={}",
            crate::MAX_BITVECTOR_WIDTH
        )));
    }
    // Whole-problem identity and namespace passes render only this bounded
    // decimal width; they never allocate a `width`-bit value or mask. Selected
    // ground replay charges ceil(width/8) separately before evaluation.
    Ok(16)
}

fn preflight_source_identity_sort(
    root: &ChcSort,
    work: &mut usize,
) -> Result<(), ChcGroundDerivationArtifactError> {
    let mut stack = vec![(root, 1usize)];
    while let Some((sort, depth)) = stack.pop() {
        if depth > CHC_GROUND_DERIVATION_MAX_SOURCE_DEPTH {
            return Err(source_identity_error(
                "whole-problem source sort exceeds depth bound",
            ));
        }
        // `normalized_sort` constructs child strings bottom-up. Weight every
        // node and name by its sort-ancestor depth so a deep sort's repeated
        // copying is admitted only when the fixed envelope dominates it.
        charge_source_identity_work(
            work,
            32usize
                .checked_mul(depth)
                .ok_or_else(|| source_identity_error("source sort node work overflow"))?,
        )?;
        match sort {
            ChcSort::Array(index, value) => {
                charge_source_identity_work(
                    work,
                    2usize
                        .checked_mul(depth)
                        .ok_or_else(|| source_identity_error("source array sort work overflow"))?,
                )?;
                let child_depth = depth.checked_add(1).ok_or_else(|| {
                    source_identity_error("whole-problem source sort depth overflow")
                })?;
                stack.push((index, child_depth));
                stack.push((value, child_depth));
            }
            ChcSort::Uninterpreted(name) => charge_source_identity_work(
                work,
                name.len().checked_mul(depth).ok_or_else(|| {
                    source_identity_error("source uninterpreted-sort name work overflow")
                })?,
            )?,
            ChcSort::Datatype { name, constructors } => {
                charge_source_identity_work(
                    work,
                    name.len()
                        .checked_add(constructors.len())
                        .and_then(|amount| amount.checked_mul(depth))
                        .ok_or_else(|| {
                            source_identity_error("source datatype identity work overflow")
                        })?,
                )?;
                let child_depth = depth.checked_add(1).ok_or_else(|| {
                    source_identity_error("whole-problem datatype depth overflow")
                })?;
                for constructor in constructors.iter() {
                    charge_source_identity_work(
                        work,
                        constructor
                            .name
                            .len()
                            .checked_add(constructor.selectors.len())
                            .and_then(|amount| amount.checked_mul(depth))
                            .ok_or_else(|| {
                                source_identity_error("source constructor work overflow")
                            })?,
                    )?;
                    for selector in &constructor.selectors {
                        charge_source_identity_work(
                            work,
                            selector.name.len().checked_mul(depth).ok_or_else(|| {
                                source_identity_error("source selector work overflow")
                            })?,
                        )?;
                        stack.push((&selector.sort, child_depth));
                    }
                }
            }
            ChcSort::BitVec(width) => charge_source_identity_work(
                work,
                source_bitvector_width_work(*width)?
                    .checked_mul(depth)
                    .ok_or_else(|| source_identity_error("source bitvector sort work overflow"))?,
            )?,
            ChcSort::Bool | ChcSort::Int | ChcSort::Real => {}
        }
    }
    Ok(())
}

fn preflight_source_identity_sort_multiplied(
    root: &ChcSort,
    work: &mut usize,
    multiplier: usize,
) -> Result<(), ChcGroundDerivationArtifactError> {
    let starting_work = *work;
    preflight_source_identity_sort(root, work)?;
    let sort_work = work
        .checked_sub(starting_work)
        .ok_or_else(|| source_identity_error("whole-problem sort work underflow"))?;
    let additional = multiplier
        .checked_sub(1)
        .and_then(|multiplier| sort_work.checked_mul(multiplier))
        .ok_or_else(|| source_identity_error("whole-problem sort identity work overflow"))?;
    charge_source_identity_work(work, additional)
}

fn push_source_identity_expr<'a>(
    stack: &mut Vec<(&'a ChcExpr, usize)>,
    expression: &'a ChcExpr,
    depth: usize,
    work: usize,
) -> Result<(), ChcGroundDerivationArtifactError> {
    if depth > CHC_GROUND_DERIVATION_MAX_SOURCE_DEPTH
        || work
            .checked_add(stack.len())
            .is_none_or(|projected| projected >= CHC_GROUND_DERIVATION_MAX_SOURCE_WORK)
    {
        return Err(source_identity_error(
            "whole-problem source expression exceeds depth/work bound",
        ));
    }
    stack.push((expression, depth));
    Ok(())
}

pub(super) fn preflight_problem_source_identity(
    problem: &ChcProblem,
) -> Result<(), ChcGroundDerivationArtifactError> {
    let mut work = 0usize;
    let mut expression_nodes = 0usize;
    let mut bounded_expression_sorts = Vec::new();
    for predicate in problem.predicates() {
        charge_source_identity_work(&mut work, 64)?;
        charge_source_identity_work(
            &mut work,
            predicate
                .name
                .len()
                .checked_mul(2)
                .ok_or_else(|| source_identity_error("predicate name work overflow"))?,
        )?;
        charge_source_identity_work(
            &mut work,
            predicate
                .arg_sorts
                .len()
                .checked_mul(2)
                .ok_or_else(|| source_identity_error("predicate signature work overflow"))?,
        )?;
        for sort in &predicate.arg_sorts {
            preflight_source_identity_sort_multiplied(sort, &mut work, 2)?;
        }
    }
    for action_name in problem.action_names() {
        charge_source_identity_work(&mut work, 32)?;
        charge_source_identity_work(
            &mut work,
            action_name
                .len()
                .checked_mul(2)
                .ok_or_else(|| source_identity_error("action name work overflow"))?,
        )?;
    }
    for (datatype_name, constructors) in problem.datatype_defs() {
        charge_source_identity_work(&mut work, 64)?;
        charge_source_identity_work(
            &mut work,
            datatype_name
                .len()
                .checked_mul(2)
                .ok_or_else(|| source_identity_error("datatype name work overflow"))?,
        )?;
        for (constructor_name, selectors) in constructors {
            charge_source_identity_work(
                &mut work,
                constructor_name
                    .len()
                    .checked_mul(2)
                    .ok_or_else(|| source_identity_error("constructor name work overflow"))?,
            )?;
            for (selector_name, sort) in selectors {
                charge_source_identity_work(
                    &mut work,
                    selector_name
                        .len()
                        .checked_mul(2)
                        .ok_or_else(|| source_identity_error("selector name work overflow"))?,
                )?;
                preflight_source_identity_sort_multiplied(sort, &mut work, 2)?;
            }
        }
    }

    let mut stack = Vec::new();
    for clause in problem.clauses() {
        charge_source_identity_work(&mut work, 64)?;
        charge_source_identity_work(
            &mut work,
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
                &mut work,
                action_name
                    .len()
                    .checked_mul(2)
                    .ok_or_else(|| source_identity_error("clause action work overflow"))?,
            )?;
        }
        if let Some(constraint) = &clause.body.constraint {
            push_source_identity_expr(&mut stack, constraint, 1, work)?;
        }
        for (_, arguments) in &clause.body.predicates {
            for argument in arguments {
                push_source_identity_expr(&mut stack, argument, 1, work)?;
            }
        }
        if let crate::ClauseHead::Predicate(_, arguments) = &clause.head {
            for argument in arguments {
                push_source_identity_expr(&mut stack, argument, 1, work)?;
            }
        }
        while let Some((expression, depth)) = stack.pop() {
            expression_nodes = expression_nodes
                .checked_add(1)
                .ok_or_else(|| source_identity_error("source expression count overflow"))?;
            let identity_multiplier = depth
                .checked_mul(2)
                .ok_or_else(|| source_identity_error("source identity depth work overflow"))?;
            charge_source_identity_work(
                &mut work,
                64usize
                    .checked_mul(identity_multiplier)
                    .ok_or_else(|| source_identity_error("source node work overflow"))?,
            )?;
            bounded_expression_sorts.push((expression, identity_multiplier));
            match expression {
                ChcExpr::ArrayLambda(_) => {
                    return Err(source_identity_error(
                        "historical oracle has no array-lambda grammar",
                    ))
                }
                ChcExpr::Var(variable) => {
                    charge_source_identity_work(
                        &mut work,
                        variable
                            .name
                            .len()
                            .checked_mul(identity_multiplier)
                            .ok_or_else(|| source_identity_error("variable name work overflow"))?,
                    )?;
                    preflight_source_identity_sort_multiplied(
                        &variable.sort,
                        &mut work,
                        identity_multiplier,
                    )?;
                }
                ChcExpr::FuncApp(name, return_sort, _) => {
                    charge_source_identity_work(
                        &mut work,
                        name.len()
                            .checked_mul(identity_multiplier)
                            .ok_or_else(|| source_identity_error("function name work overflow"))?,
                    )?;
                    preflight_source_identity_sort_multiplied(
                        return_sort,
                        &mut work,
                        identity_multiplier,
                    )?;
                }
                ChcExpr::PredicateApp(name, _, _) | ChcExpr::IsTesterMarker(name) => {
                    charge_source_identity_work(
                        &mut work,
                        name.len()
                            .checked_mul(identity_multiplier)
                            .ok_or_else(|| source_identity_error("source name work overflow"))?,
                    )?;
                }
                ChcExpr::ConstArray(sort, _) | ChcExpr::ConstArrayMarker(sort) => {
                    preflight_source_identity_sort_multiplied(
                        sort,
                        &mut work,
                        identity_multiplier,
                    )?;
                }
                ChcExpr::Bool(_)
                | ChcExpr::Int(_)
                | ChcExpr::Real(_, _)
                | ChcExpr::BitVec(_, _)
                | ChcExpr::Op(_, _) => {}
            }
            let children: &[std::sync::Arc<ChcExpr>] = match expression {
                ChcExpr::ArrayLambda(_) => {
                    return Err(source_identity_error(
                        "historical oracle has no array-lambda grammar",
                    ))
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
            let child_depth = depth.checked_add(1).ok_or_else(|| {
                source_identity_error("whole-problem source expression depth overflow")
            })?;
            for child in children {
                push_source_identity_expr(&mut stack, child, child_depth, work)?;
            }
        }
    }
    // Recursive operator-sort derivation is safe only after the complete
    // iterative expression/sort preflight has accepted every live clause.
    for (expression, identity_multiplier) in bounded_expression_sorts {
        let expression_sort =
            catch_unwind(AssertUnwindSafe(|| expression.sort())).map_err(|_| {
                source_identity_error("whole-problem expression sort derivation panicked")
            })?;
        if let ChcSort::BitVec(width) = expression_sort {
            charge_source_identity_work(
                &mut work,
                source_bitvector_width_work(width)?
                    .checked_mul(identity_multiplier)
                    .ok_or_else(|| {
                        source_identity_error("source bitvector expression work overflow")
                    })?,
            )?;
        }
    }
    let sort_items = expression_nodes
        .max(problem.predicates().len())
        .max(problem.clauses().len())
        .max(problem.datatype_defs().len())
        .max(problem.action_names().len());
    let sort_rounds = sort_items.checked_sub(1).map_or(0, |maximum_index| {
        usize::BITS as usize - maximum_index.leading_zeros() as usize
    });
    let sort_work = work
        .checked_mul(sort_rounds)
        .ok_or_else(|| source_identity_error("whole-problem canonical sort work overflow"))?;
    charge_source_identity_work(&mut work, sort_work)
}

/// Bound and validate exactly the live source surface authenticated by ground
/// artifacts and native derivation replay.
///
/// The iterative identity pass runs first. Only then may the action, predicate,
/// background-expression, and typed-function validators inspect the bounded
/// source, or the global ordinary-UF collector clone/hash/sort source terms.
/// Pruned-query provenance is intentionally excluded because neither the
/// artifact hashes nor clause ordinals authenticate it.
pub(super) fn validate_ground_source_problem(
    problem: &ChcProblem,
) -> Result<(), ChcGroundDerivationArtifactError> {
    preflight_problem_source_identity(problem)?;
    catch_unwind(AssertUnwindSafe(|| {
        problem.validate_live_clause_actions()?;
        problem.validate_live_background_theory_expressions()?;
        problem.validate_live_predicate_applications()?;
        problem.validate_live_typed_function_applications()?;
        let expressions = problem.clauses().iter().flat_map(|clause| {
            let head_arguments = match &clause.head {
                crate::ClauseHead::Predicate(_, arguments) => arguments.as_slice(),
                crate::ClauseHead::False => &[],
            };
            clause
                .body
                .constraint
                .iter()
                .chain(
                    clause
                        .body
                        .predicates
                        .iter()
                        .flat_map(|(_, arguments)| arguments),
                )
                .chain(head_arguments)
        });
        crate::smt::executor_adapter::collect_uninterpreted_function_declarations_for_exprs(
            expressions,
        )
        .map(|_| ())
    }))
    .map_err(|_| {
        error(
            ChcGroundDerivationArtifactErrorReason::ValidationPanicked,
            "bounded live source validation panicked",
        )
    })?
    .map_err(|source_error| {
        error(
            ChcGroundDerivationArtifactErrorReason::InvalidSourceProblem,
            source_error.to_string(),
        )
    })
}
