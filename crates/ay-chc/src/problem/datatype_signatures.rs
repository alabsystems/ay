// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Nominal datatype signature comparison only after whole-surface authentication.
//!
//! The parser intentionally embeds finite snapshots of recursive definitions.
//! Reuse the executor's bounded, conflict-checking declaration collector before
//! the replay type checker's nominal compatibility can identify those snapshots.
//! This guard includes the explicit registry and unused predicate signatures,
//! not just the applications that happened to be selected by a ground witness.

use ay_core::kani_compat::DetHashMap;

use crate::{
    ChcDtConstructor, ChcDtSelector, ChcError, ChcExpr, ChcOp, ChcProblem, ChcResult, ChcSort,
    ChcVar,
};

// Local copying/comparison bounds precede allocations made to call the existing
// collector; its independent whole-surface limits remain authoritative as well.
const MAX_COPY_WORK: usize = 1024 * 1024;
const MAX_ARRAY_DEPTH: usize = 512;

pub(super) struct AuthenticatedDatatypes {
    signatures: DetHashMap<String, Vec<(ChcSort, Vec<ChcSort>)>>,
    comparison_remaining: usize,
}

impl AuthenticatedDatatypes {
    pub(super) fn new(problem: &ChcProblem, expressions: &[&ChcExpr]) -> ChcResult<Self> {
        let mut remaining = MAX_COPY_WORK;
        let mut declarations = Vec::new();
        for (name, constructors) in problem.datatype_defs() {
            charge(
                &mut remaining,
                name.len().saturating_add(constructors.len()),
            )?;
            let mut copied = Vec::with_capacity(constructors.len());
            for (constructor, selectors) in constructors {
                charge(
                    &mut remaining,
                    constructor.len().saturating_add(selectors.len()),
                )?;
                let mut fields = Vec::with_capacity(selectors.len());
                for (selector, sort) in selectors {
                    charge(&mut remaining, selector.len())?;
                    fields.push(ChcDtSelector {
                        name: selector.clone(),
                        sort: copy_sort(sort, 0, &mut remaining)?,
                    });
                }
                copied.push(ChcDtConstructor {
                    name: constructor.clone(),
                    selectors: fields,
                });
            }
            declarations.push(metadata_root(ChcSort::Datatype {
                name: name.clone(),
                constructors: crate::ChcDtConstructors::new(copied),
            }));
        }
        for predicate in problem.predicates() {
            for sort in &predicate.arg_sorts {
                push_metadata(sort, &mut declarations, &mut remaining)?;
            }
        }
        for expression in expressions {
            collect_expression_metadata(expression, &mut declarations, &mut remaining)?;
        }
        // These temporary roots carry only metadata. Their empty local names
        // never enter the problem or a solver namespace. A different sort for
        // that name is still visited by the collector, including hidden nested
        // definitions beneath same-name/same-signature recursive snapshots.
        let definitions =
            crate::smt::executor_adapter::collect_dt_declarations_for_exprs(declarations.iter())
                .map_err(|error| ChcError::Verification(error.to_string()))?;
        let mut signatures = DetHashMap::default();
        for (name, constructors) in definitions {
            charge(&mut remaining, name.len().saturating_add(1))?;
            let nominal = ChcSort::Uninterpreted(name.to_owned());
            for constructor in constructors {
                charge(&mut remaining, constructor.selectors.len())?;
                let mut arguments = Vec::with_capacity(constructor.selectors.len());
                for selector in &constructor.selectors {
                    arguments.push(copy_sort(&selector.sort, 0, &mut remaining)?);
                    insert_signature(
                        &mut signatures,
                        &selector.name,
                        &selector.sort,
                        std::slice::from_ref(&nominal),
                        &mut remaining,
                    )?;
                }
                insert_signature(
                    &mut signatures,
                    &constructor.name,
                    &nominal,
                    &arguments,
                    &mut remaining,
                )?;
                charge(&mut remaining, constructor.name.len().saturating_add(3))?;
                insert_signature(
                    &mut signatures,
                    &format!("is-{}", constructor.name),
                    &ChcSort::Bool,
                    std::slice::from_ref(&nominal),
                    &mut remaining,
                )?;
            }
        }
        Ok(Self {
            signatures,
            comparison_remaining: MAX_COPY_WORK,
        })
    }

    pub(super) fn contains(&self, name: &str) -> bool {
        self.signatures.contains_key(name)
    }

    pub(super) fn matches(
        &mut self,
        name: &str,
        actual_return: &ChcSort,
        actual_arguments: &[ChcSort],
    ) -> ChcResult<bool> {
        let Some(overloads) = self.signatures.get(name) else {
            return Ok(false);
        };
        for (expected_return, expected_arguments) in overloads {
            if Self::matches_signature(
                expected_return,
                expected_arguments,
                actual_return,
                actual_arguments,
                &mut self.comparison_remaining,
            )? {
                return Ok(true);
            }
        }
        Ok(false)
    }

    fn matches_signature(
        expected_return: &ChcSort,
        expected_arguments: &[ChcSort],
        actual_return: &ChcSort,
        actual_arguments: &[ChcSort],
        remaining: &mut usize,
    ) -> ChcResult<bool> {
        charge(remaining, 1)?;
        if expected_arguments.len() != actual_arguments.len() {
            return Ok(false);
        }
        for (expected, actual) in std::iter::once((expected_return, actual_return))
            .chain(expected_arguments.iter().zip(actual_arguments))
        {
            // copy_sort bounds array depth/name copying but deliberately keeps
            // already-authenticated datatype metadata in its interned list.
            let expected = copy_sort(expected, 0, remaining)?;
            let actual = copy_sort(actual, 0, remaining)?;
            // The established replay checker compares datatype references by
            // name and array structure; scalar sorts/widths remain exact. That
            // comparison is safe here only because new() authenticated ALL
            // definitions in the same source namespace first.
            if crate::pdr::validate_qf_operation(ChcOp::Eq, &[expected, actual]).is_err() {
                return Ok(false);
            }
        }
        Ok(true)
    }
}

fn collect_expression_metadata(
    root: &ChcExpr,
    declarations: &mut Vec<ChcExpr>,
    remaining: &mut usize,
) -> ChcResult<()> {
    // Preserve the existing ordinary function walk's scalar admission envelope.
    // Only datatype-bearing metadata enters the bounded declaration collector;
    // scalar expression nodes do not acquire its executor-query node ceiling.
    //
    // A shared inner node already popped is skipped (WP-F F0b): its subtree
    // contributed its metadata roots at the first visit, and a repeat could
    // only append copies of the same roots.
    let mut seen: ay_core::kani_compat::DetHashSet<*const ChcExpr> = Default::default();
    let mut stack = vec![root];
    while let Some(expression) = stack.pop() {
        if !crate::expr::dag::children(expression).is_empty()
            && !seen.insert(std::ptr::from_ref::<ChcExpr>(expression))
        {
            continue;
        }
        match expression {
            ChcExpr::ArrayLambda(lambda) => {
                for formal in std::iter::once(lambda.binder()).chain(lambda.formals()) {
                    push_metadata(&formal.sort, declarations, remaining)?;
                }
                stack.push(lambda.body());
                stack.extend(lambda.captures().iter().map(AsRef::as_ref));
            }
            ChcExpr::Var(variable) => push_metadata(&variable.sort, declarations, remaining)?,
            ChcExpr::FuncApp(_, result, args) => {
                push_metadata(result, declarations, remaining)?;
                stack.extend(args.iter().map(AsRef::as_ref));
            }
            ChcExpr::Op(_, args) | ChcExpr::PredicateApp(_, _, args) => {
                stack.extend(args.iter().map(AsRef::as_ref));
            }
            ChcExpr::ConstArray(index, value) => {
                push_metadata(index, declarations, remaining)?;
                stack.push(value);
            }
            ChcExpr::ConstArrayMarker(sort) => push_metadata(sort, declarations, remaining)?,
            ChcExpr::Bool(_)
            | ChcExpr::Int(_)
            | ChcExpr::Real(_, _)
            | ChcExpr::BitVec(_, _)
            | ChcExpr::IsTesterMarker(_) => {}
        }
    }
    Ok(())
}

fn push_metadata(sort: &ChcSort, roots: &mut Vec<ChcExpr>, remaining: &mut usize) -> ChcResult<()> {
    if contains_datatype(sort)? {
        charge(remaining, 1)?;
        roots.push(metadata_root(copy_sort(sort, 0, remaining)?));
    }
    Ok(())
}

fn contains_datatype(sort: &ChcSort) -> ChcResult<bool> {
    match sort {
        ChcSort::Datatype { .. } => return Ok(true),
        ChcSort::Array(_, _) => {}
        _ => return Ok(false),
    }
    let mut remaining = MAX_COPY_WORK;
    let mut pending = vec![(sort, 0usize)];
    while let Some((sort, depth)) = pending.pop() {
        charge(&mut remaining, 1)?;
        if depth >= MAX_ARRAY_DEPTH {
            return Err(ChcError::Verification(
                "datatype signature array nesting exceeds bound".into(),
            ));
        }
        match sort {
            ChcSort::Datatype { .. } => return Ok(true),
            ChcSort::Array(key, value) => {
                pending.push((key.as_ref(), depth + 1));
                pending.push((value.as_ref(), depth + 1));
            }
            _ => {}
        }
    }
    Ok(false)
}

fn insert_signature(
    signatures: &mut DetHashMap<String, Vec<(ChcSort, Vec<ChcSort>)>>,
    name: &str,
    result: &ChcSort,
    arguments: &[ChcSort],
    remaining: &mut usize,
) -> ChcResult<()> {
    charge(
        remaining,
        name.len().saturating_add(arguments.len()).saturating_add(1),
    )?;
    let result = copy_sort(result, 0, remaining)?;
    let mut copied = Vec::with_capacity(arguments.len());
    for argument in arguments {
        copied.push(copy_sort(argument, 0, remaining)?);
    }
    // A canonical declaration is visited once. Overloads are appended, not
    // deduplicated. (Datatype equality is a pointer comparison since datatype
    // lists are interned; it no longer expands a metadata DAG.)
    signatures
        .entry(name.to_owned())
        .or_default()
        .push((result, copied));
    Ok(())
}

fn metadata_root(sort: ChcSort) -> ChcExpr {
    ChcExpr::var(ChcVar::new("", sort))
}

fn charge(remaining: &mut usize, amount: usize) -> ChcResult<()> {
    let Some(rest) = remaining.checked_sub(amount) else {
        *remaining = 0;
        return Err(ChcError::Verification(
            "datatype signature surface exceeds copy/comparison work bound".into(),
        ));
    };
    *remaining = rest;
    Ok(())
}

fn copy_sort(sort: &ChcSort, depth: usize, remaining: &mut usize) -> ChcResult<ChcSort> {
    charge(remaining, 1)?;
    if depth >= MAX_ARRAY_DEPTH {
        return Err(ChcError::Verification(
            "datatype signature array nesting exceeds bound".into(),
        ));
    }
    match sort {
        ChcSort::Array(key, value) => Ok(ChcSort::Array(
            Box::new(copy_sort(key, depth + 1, remaining)?),
            Box::new(copy_sort(value, depth + 1, remaining)?),
        )),
        ChcSort::Datatype { name, .. } | ChcSort::Uninterpreted(name) => {
            charge(remaining, name.len())?;
            Ok(sort.clone())
        }
        _ => Ok(sort.clone()),
    }
}

#[cfg(test)]
#[path = "datatype_signatures/tests.rs"]
mod tests;
