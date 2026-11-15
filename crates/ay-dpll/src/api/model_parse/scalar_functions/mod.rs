// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Exact closed scalar models, separate from best-effort whole-model parsing.
//! No native model output, opaque function alias, or omitted definition is
//! turned into a default. Printing precedes admission and remains opaque.

use ay_core::Sort;
use ay_frontend::{sexp::parse_sexps, SExpr};

use super::typed::Decoder;
use crate::api::types::{ModelValue, ScalarFunctionModel};

// Reuse the existing allocation-free lexical envelope before any AST exists.
#[path = "../get_value/admission.rs"]
mod admission;
mod body;
mod budget;
mod operations;
mod quoted;
use budget::Budget;

const MAX_FUNCTIONS: usize = 1024;
const MAX_DEPTH: usize = 64;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Scalar {
    Bool,
    Bv(u32),
}

impl Scalar {
    fn from_sort(sort: &Sort) -> Option<Self> {
        match sort {
            Sort::Bool => Some(Self::Bool),
            Sort::BitVec(width)
                if (1..=crate::api::MAX_API_BITVECTOR_WIDTH).contains(&width.width) =>
            {
                Some(Self::Bv(width.width))
            }
            _ => None,
        }
    }

    fn parse(sort: &SExpr) -> Option<Self> {
        if sort.is_symbol("Bool") {
            return Some(Self::Bool);
        }
        let [marker, kind, width] = sort.as_list()? else {
            return None;
        };
        if !marker.is_symbol("_") || !kind.is_symbol("BitVec") {
            return None;
        }
        let width = natural(width)?;
        (1..=crate::api::MAX_API_BITVECTOR_WIDTH)
            .contains(&width)
            .then_some(Self::Bv(width))
    }

    fn core(self) -> Sort {
        match self {
            Self::Bool => Sort::Bool,
            Self::Bv(width) => Sort::bitvec(width),
        }
    }
}

fn natural(value: &SExpr) -> Option<u32> {
    let text = value.as_numeral()?;
    if text.is_empty()
        || text.len() > 10
        || !text.bytes().all(|b| b.is_ascii_digit())
        || (text.len() > 1 && text.starts_with('0'))
    {
        return None;
    }
    text.parse().ok()
}

fn valid_name(name: &str) -> bool {
    !name.is_empty()
        && name.len() <= 16_384
        && !name
            .bytes()
            .any(|b| b.is_ascii_control() || matches!(b, b'|' | b'\\'))
        && !crate::api::rec_def_name_conflates_with_builtin(name)
        && !matches!(
            name,
            "Bool"
                | "BitVec"
                | "Array"
                | "let"
                | "forall"
                | "exists"
                | "as"
                | "!"
                | "model"
                | "define-fun"
        )
}

pub(crate) fn parse_scalar_function_models(
    output: &str,
    expected: &[(&str, &[Sort], &Sort)],
) -> Option<Vec<ScalarFunctionModel>> {
    parse_with_budget(output, expected, &mut Budget::new())
}

/// Data-only ingress for a complete retained inventory, not model provenance.
pub(crate) fn decode_scalar_function_models(
    output: &str,
    expected: &[(&str, &[Sort], &Sort)],
) -> Option<Vec<ScalarFunctionModel>> {
    parse_inventory(output, expected, Inventory::Exact, &mut Budget::new())
}

#[derive(Clone, Copy)]
enum Inventory {
    RequestedSubset,
    Exact,
}

fn parse_with_budget(
    output: &str,
    expected: &[(&str, &[Sort], &Sort)],
    budget: &mut Budget,
) -> Option<Vec<ScalarFunctionModel>> {
    parse_inventory(output, expected, Inventory::RequestedSubset, budget)
}

fn parse_inventory(
    output: &str,
    expected: &[(&str, &[Sort], &Sort)],
    inventory: Inventory,
    budget: &mut Budget,
) -> Option<Vec<ScalarFunctionModel>> {
    let result = decode(output, expected, inventory, budget);
    if result.is_none() {
        budget.stopped = true;
    }
    result
}

fn admit_expected(expected: &[(&str, &[Sort], &Sort)], budget: &mut Budget) -> Option<()> {
    budget.charge(1, 0)?;
    if expected.len() > MAX_FUNCTIONS {
        return None;
    }
    // Complete caller metadata admission precedes any name/index/AST clone.
    budget.charge(expected.len(), expected.len().checked_mul(256)?)?;
    for (name, args, result) in expected {
        budget.name(name)?;
        if !matches!(Scalar::from_sort(result)?, Scalar::Bv(_)) {
            return None;
        }
        budget.scalar(Scalar::from_sort(result)?)?;
        budget.charge(
            args.len(),
            args.len().checked_mul(std::mem::size_of::<Sort>())?,
        )?;
        for sort in *args {
            budget.scalar(Scalar::from_sort(sort)?)?;
        }
    }
    // Inventory scans are explicitly metered; no uncharged ordered-map string
    // comparisons are hidden behind a nominal one-unit lookup debit.
    for (index, (name, _, _)) in expected.iter().enumerate() {
        for (previous, _, _) in &expected[..index] {
            budget.charge(name.len().min(previous.len()).checked_add(1)?, 0)?;
            if name == previous {
                return None;
            }
        }
    }
    Some(())
}

fn decode(
    output: &str,
    expected: &[(&str, &[Sort], &Sort)],
    inventory: Inventory,
    budget: &mut Budget,
) -> Option<Vec<ScalarFunctionModel>> {
    admit_expected(expected, budget)?;
    let mut admission = admission::Admission::new();
    admission.admit(output)?;
    // Conservative text/AST allowance before parsing, not an allocator or RSS
    // measurement. Each byte may begin a tiny list/atom in adversarial input.
    budget.charge(output.len(), output.len().checked_mul(32)?)?;
    quoted::admit(output, budget)?;
    let sexps = parse_sexps(output).ok()?;
    let [response] = sexps.as_slice() else {
        return None;
    };
    let [head, definitions @ ..] = response.as_list()? else {
        return None;
    };
    if !head.is_symbol("model") {
        return None;
    }
    // Native whole-model extraction may include unrelated declarations. The
    // public retained-data boundary instead requires the complete source
    // inventory: no omitted or extra definition may hide behind name selection.
    if matches!(inventory, Inventory::Exact) && definitions.len() != expected.len() {
        return None;
    }
    budget.charge(definitions.len(), definitions.len().checked_mul(256)?)?;
    let mut entries: Vec<(&str, (&SExpr, &SExpr, &SExpr))> = Vec::new();
    entries.try_reserve_exact(definitions.len()).ok()?;
    for definition in definitions {
        let [head, name, params, result, value] = definition.as_list()? else {
            return None;
        };
        if !head.is_symbol("define-fun") || params.as_list().is_none() {
            return None;
        }
        let name = name.as_symbol()?;
        budget.name(name)?;
        for (previous, _) in &entries {
            budget.charge(name.len().min(previous.len()).checked_add(1)?, 0)?;
            if name == *previous {
                return None;
            }
        }
        entries.push((name, (params, result, value)));
    }
    let mut models = Vec::new();
    models.try_reserve_exact(expected.len()).ok()?;
    for (name, args, result) in expected {
        budget.charge(name.len().checked_add(1)?, 0)?;
        let mut entry = None;
        for (printed, definition) in &entries {
            budget.charge(name.len().min(printed.len()).checked_add(1)?, 0)?;
            if name == printed {
                entry = Some(*definition);
                break;
            }
        }
        let (params, printed_sort, value) = entry?;
        if Scalar::parse(printed_sort)? != Scalar::from_sort(result)? {
            return None;
        }
        let definition = body::definition(
            name,
            params,
            args,
            value,
            Scalar::from_sort(result)?,
            budget,
        )?;
        budget.charge(
            1,
            name.len()
                .checked_add(std::mem::size_of::<ScalarFunctionModel>())?,
        )?;
        models.push(ScalarFunctionModel::from_decoded(
            (*name).to_owned(),
            args.to_vec(),
            (*result).clone(),
            definition,
        ));
    }
    // `entries` borrows the parsed tree; release it before the tree.
    drop(entries);
    drop(sexps);
    budget.charge(1, 0)?;
    Some(models)
}

#[cfg(test)]
mod tests;
