// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Exact total-function data, never native model provenance or SAT authority.

use super::*;
use ay_core::Sort;

const MAX_OUTPUT: usize = 8 * 1024 * 1024;
const DECODER_BYTES: usize = 16 * 1024 * 1024;

pub(in crate::quantified::counterexample::trace) fn export(
    functions: &[ScalarFunctionModel],
    problem: &QuantifiedChcProblem,
    control: &SourceControl<'_>,
) -> Option<String> {
    authenticate_functions(problem, functions, control)?;
    let mut text = String::new();
    push(&mut text, "(model", control)?;
    for function in functions {
        push(&mut text, " ", control)?;
        // Construction-sealed data already contains a closed, typed canonical
        // definition. Source authentication above also includes unused entries.
        push(&mut text, function.definition_smtlib(), control)?;
    }
    push(&mut text, ")", control)?;
    control.poll()?;
    Some(text)
}

pub(in crate::quantified::counterexample::trace) fn import(
    text: &str,
    problem: &QuantifiedChcProblem,
    control: &SourceControl<'_>,
) -> Option<Vec<ScalarFunctionModel>> {
    control.poll()?;
    if text.len() > MAX_OUTPUT {
        return None;
    }
    if problem.function_declarations().is_empty() {
        control.charge(1)?;
        let identical = text == "(model)";
        control.poll()?;
        return identical.then(Vec::new);
    }
    // The decoder has its own fixed work/depth/text limits. Its complete
    // 16 MiB copy allowance includes literal scratch: it is prepaid here, not
    // added as an unaccounted second allowance. This bounded call is opaque to
    // SourceControl; the original deadline is polled before and after it.
    control.bytes(DECODER_BYTES)?;
    let signatures = signatures(problem, control)?;
    control.bytes(
        signatures
            .len()
            .checked_mul(std::mem::size_of::<(&str, &[Sort], &Sort)>())?,
    )?;
    let mut expected = Vec::new();
    expected.try_reserve_exact(signatures.len()).ok()?;
    for (declaration, (arguments, result)) in
        problem.function_declarations().iter().zip(&signatures)
    {
        control.charge(1)?;
        expected.push((declaration.name(), arguments.as_slice(), result));
    }
    control.poll()?;
    let functions = ScalarFunctionModel::decode_smtlib(text, &expected).ok()?;
    control.poll()?;
    let canonical = export(&functions, problem, control)?;
    // The decoder deliberately accepts definition reordering and alpha names.
    // This wire does not: exact pin identity includes the canonical spelling.
    control.bytes(text.len())?;
    let identical = canonical == text;
    drop(canonical);
    drop(expected);
    drop(signatures);
    control.poll()?;
    identical.then_some(functions)
}

fn signatures(
    problem: &QuantifiedChcProblem,
    control: &SourceControl<'_>,
) -> Option<Vec<(Vec<Sort>, Sort)>> {
    let declarations = problem.function_declarations();
    control.bytes(
        declarations
            .len()
            .checked_mul(std::mem::size_of::<(Vec<Sort>, Sort)>())?,
    )?;
    let mut signatures = Vec::new();
    signatures.try_reserve_exact(declarations.len()).ok()?;
    for declaration in declarations {
        control.charge(1)?;
        control.bytes(
            declaration
                .arg_sorts()
                .len()
                .checked_mul(std::mem::size_of::<Sort>())?,
        )?;
        let mut arguments = Vec::new();
        arguments
            .try_reserve_exact(declaration.arg_sorts().len())
            .ok()?;
        for argument in declaration.arg_sorts() {
            arguments.push(core_sort(argument, control)?);
        }
        let result = core_sort(declaration.result_sort(), control)?;
        if !matches!(result, Sort::BitVec(_)) {
            return None;
        }
        signatures.push((arguments, result));
    }
    control.poll()?;
    Some(signatures)
}

fn core_sort(sort: &crate::ChcSort, control: &SourceControl<'_>) -> Option<Sort> {
    control.charge(1)?;
    match sort {
        crate::ChcSort::Bool => Some(Sort::Bool),
        crate::ChcSort::BitVec(width) if (1..=crate::MAX_BITVECTOR_WIDTH).contains(width) => {
            Some(Sort::bitvec(*width))
        }
        _ => None,
    }
}

fn push(text: &mut String, piece: &str, control: &SourceControl<'_>) -> Option<()> {
    control.charge(1)?;
    if text.len().checked_add(piece.len())? > MAX_OUTPUT {
        return None;
    }
    control.bytes(piece.len().checked_mul(2)?)?;
    text.try_reserve(piece.len()).ok()?;
    text.push_str(piece);
    Some(())
}

#[cfg(test)]
mod tests;
