// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Ordered ordinary scalar functions, distinct from Boolean Horn relations.

use super::records::Registry;
use crate::{ChcError, ChcProblem, ChcResult, ChcSort};
use std::collections::BTreeMap;

mod admission;
pub(crate) mod controlled;
#[cfg(test)]
mod tests;

/// An ordinary uninterpreted scalar function declaration.
///
/// Construction only records the declaration. `QuantifiedChcProblem` checks
/// its complete signature and namespace before retaining it as source.
/// Boolean results are deliberately excluded there: Boolean-returning
/// declarations are Horn relations, while ordinary Boolean summaries use BV1.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct QuantifiedChcFunction {
    name: String,
    args: Vec<ChcSort>,
    result: ChcSort,
}

impl QuantifiedChcFunction {
    /// Record an ordered signature without allocating additional metadata.
    pub fn new(name: String, args: Vec<ChcSort>, result: ChcSort) -> Self {
        Self { name, args, result }
    }

    /// Decoded source symbol, not an SMT-LIB expression.
    pub fn name(&self) -> &str {
        &self.name
    }

    /// Exact argument sorts in source declaration order.
    pub fn arg_sorts(&self) -> &[ChcSort] {
        &self.args
    }

    /// Exact result sort.
    pub fn result_sort(&self) -> &ChcSort {
        &self.result
    }
}

#[derive(Debug, Clone, Default)]
pub(super) struct Functions {
    declarations: Vec<QuantifiedChcFunction>,
    names: BTreeMap<String, usize>,
    bytes: usize,
    work: usize,
}

fn invalid(message: &str) -> ChcError {
    ChcError::Verification(format!("quantified function source: {message}"))
}

impl Functions {
    pub(super) fn new(
        declarations: Vec<QuantifiedChcFunction>,
        problem: &ChcProblem,
        records: &Registry,
    ) -> ChcResult<Self> {
        if declarations.is_empty() {
            return Ok(Self::default());
        }
        let cost = admission::check(&declarations, problem, records)?;
        // All signatures, names and duplicate/cross-family identities have
        // passed the borrowed preflight before the first owned metadata copy.
        let names = declarations
            .iter()
            .enumerate()
            .map(|(index, declaration)| (declaration.name.clone(), index))
            .collect();
        Ok(Self {
            declarations,
            names,
            bytes: cost.bytes,
            work: cost.work,
        })
    }

    pub(super) fn declarations(&self) -> &[QuantifiedChcFunction] {
        &self.declarations
    }

    pub(super) fn is_empty(&self) -> bool {
        self.declarations.is_empty()
    }

    pub(super) fn contains(&self, name: &str) -> bool {
        name.len() <= super::records::MAX_NAME_BYTES && self.names.contains_key(name)
    }

    pub(super) fn names(&self) -> impl Iterator<Item = &str> {
        self.declarations.iter().map(QuantifiedChcFunction::name)
    }

    /// Conservative declaration-vector, name/index, scalar metadata, validation
    /// scratch and SMT-rendering copy allowance. Empty registries cost zero.
    pub(super) fn copy_bytes(&self) -> usize {
        self.bytes
    }

    pub(super) fn work(&self) -> usize {
        self.work
    }

    pub(super) fn application(&self, name: &str, args: &[ChcSort]) -> ChcResult<ChcSort> {
        if name.len() > super::records::MAX_NAME_BYTES {
            return Err(invalid("application name limit"));
        }
        let declaration = self
            .names
            .get(name)
            .and_then(|index| self.declarations.get(*index))
            .ok_or_else(|| invalid("undeclared ordinary function"))?;
        if args.len() != declaration.args.len()
            || args
                .iter()
                .zip(&declaration.args)
                .any(|(actual, expected)| !admission::scalar(actual) || actual != expected)
        {
            return Err(invalid("ordinary function argument signature mismatch"));
        }
        Ok(declaration.result.clone())
    }

    pub(super) fn declarations_smtlib(&self) -> ChcResult<String> {
        use crate::smt::executor_adapter::sort_to_smtlib;
        use std::fmt::Write;
        let mut output = String::new();
        // No huge eager reservation: this allowance includes wide-value limb
        // costs, whereas the textual declaration only contains a width numeral.
        for declaration in &self.declarations {
            write!(
                output,
                "(declare-fun {} (",
                ay_core::quote_symbol(&declaration.name)
            )
            .map_err(|_| invalid("declaration output"))?;
            for (index, sort) in declaration.args.iter().enumerate() {
                if index != 0 {
                    output.push(' ');
                }
                output.push_str(&sort_to_smtlib(sort));
            }
            writeln!(output, ") {})", sort_to_smtlib(&declaration.result))
                .map_err(|_| invalid("declaration output"))?;
        }
        if output.len() > self.bytes {
            return Err(invalid("declaration output allowance"));
        }
        Ok(output)
    }
}
