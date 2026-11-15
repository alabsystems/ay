// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Retained ordinary functions are global to the complete occurrence tree.
//! Never infer a subset from applications or freshen a function per occurrence.

use super::*;

#[cfg(test)]
mod tests;

pub(super) fn render(
    problem: &QuantifiedChcProblem,
    output: &mut Output<'_, '_>,
    control: &SourceControl<'_>,
) -> Result<()> {
    control
        .charge(problem.functions.work())
        .ok_or_else(refused)?;
    // Authenticate the whole retained allowance before formatting any name or
    // sort. Output additionally charges actual text and its capacity slack.
    control
        .bytes(problem.functions.copy_bytes())
        .ok_or_else(refused)?;
    for function in problem.function_declarations() {
        control.poll().ok_or_else(refused)?;
        output.push("(declare-fun ")?;
        output.symbol(function.name())?;
        output.push(" (")?;
        for (index, sort) in function.arg_sorts().iter().enumerate() {
            if index != 0 {
                output.push(" ")?;
            }
            output.sort(sort)?;
        }
        output.push(") ")?;
        output.sort(function.result_sort())?;
        output.push(")\n")?;
    }
    control.poll().ok_or_else(refused)
}
