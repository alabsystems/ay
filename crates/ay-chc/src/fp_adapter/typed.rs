// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Exact whitelist; legacy FP's unconstrained unknown-op fallback is forbidden.

use ay_core::original_query::WorkBudget;
use ay_core::term::{Constant, Symbol, TermData, TermId, TermStore};
use ay_core::Sort;
use num_bigint::Sign;

use crate::ChcSort;

use super::source::{MAX_ARITY, MAX_NAME};
use super::{FpAdapterError, FpInputBinding};

mod guards;

#[derive(Clone, Copy)]
pub(super) enum CostClass {
    Other,
    Arithmetic,
    Division,
    Remainder,
    TruncatingRemainder,
    SquareRoot,
    Fused,
    NumericConversion,
}

pub(super) enum Children<'a> {
    Slice(std::slice::Iter<'a, TermId>),
    One(Option<TermId>),
    Three(std::array::IntoIter<TermId, 3>),
}

impl Iterator for Children<'_> {
    type Item = TermId;
    fn next(&mut self) -> Option<TermId> {
        match self {
            Self::Slice(iter) => iter.next().copied(),
            Self::One(id) => id.take(),
            Self::Three(ids) => ids.next(),
        }
    }
}

pub(super) fn binding_sort(source: &Sort, target: &ChcSort) -> bool {
    match (source, target) {
        (Sort::Bool, ChcSort::Bool) => true,
        (Sort::FloatingPoint(8, 24), ChcSort::BitVec(32))
        | (Sort::FloatingPoint(11, 53), ChcSort::BitVec(64)) => true,
        (Sort::BitVec(width), ChcSort::BitVec(target)) => {
            (1..=64).contains(&width.width) && width.width == *target
        }
        _ => false,
    }
}

pub(super) fn children<'a>(
    terms: &'a TermStore,
    id: TermId,
    bindings: &[FpInputBinding<'_>],
    budget: &mut WorkBudget<'_>,
) -> Result<(Children<'a>, CostClass), FpAdapterError> {
    budget.charge(512)?;
    let sort = terms.sort(id);
    match terms.get(id) {
        TermData::Const(Constant::Bool(_)) if sort == &Sort::Bool => {
            Ok((Children::One(None), CostClass::Other))
        }
        TermData::Const(Constant::BitVec { value, width }) => {
            if !(1..=64).contains(width)
                || sort != &Sort::bitvec(*width)
                || value.sign() == Sign::Minus
                || value.bits() > u64::from(*width)
            {
                return Err(FpAdapterError::Invalid("noncanonical BV constant"));
            }
            Ok((Children::One(None), CostClass::Other))
        }
        TermData::Var(name, _) => {
            budget.charge(bindings.len().saturating_mul(4))?;
            if name.len() > MAX_NAME || !bindings.iter().any(|b| b.source == id) {
                return Err(FpAdapterError::Invalid("unbound free input"));
            }
            Ok((Children::One(None), CostClass::Other))
        }
        TermData::Not(child) => {
            if terms.entry_stamp(*child).is_none()
                || sort != &Sort::Bool
                || terms.sort(*child) != &Sort::Bool
            {
                return Err(FpAdapterError::Invalid("not requires live Bool"));
            }
            Ok((Children::One(Some(*child)), CostClass::Other))
        }
        TermData::Ite(condition, left, right) => {
            let args = [*condition, *left, *right];
            for &arg in &args {
                budget.charge(256)?;
                if terms.entry_stamp(arg).is_none() {
                    return Err(FpAdapterError::Invalid("missing selection child"));
                }
            }
            selection(terms, sort, &args)?;
            Ok((Children::Three(args.into_iter()), CostClass::Other))
        }
        TermData::App(symbol, args) => {
            if args.len() > MAX_ARITY || symbol.name().len() > MAX_NAME {
                return Err(FpAdapterError::Unsupported("application population/name"));
            }
            for &arg in args {
                budget.charge(256)?;
                if terms.entry_stamp(arg).is_none() {
                    return Err(FpAdapterError::Invalid("missing application child"));
                }
            }
            let cost = application(terms, sort, symbol, args)?;
            Ok((Children::Slice(args.iter()), cost))
        }
        _ => Err(FpAdapterError::Unsupported("constant/binder/source kind")),
    }
}

fn application(
    terms: &TermStore,
    sort: &Sort,
    symbol: &Symbol,
    args: &[TermId],
) -> Result<CostClass, FpAdapterError> {
    if let Symbol::Indexed(name, indices) = symbol {
        if name.as_ref() == "extract" {
            raw_extract(terms, sort, indices, args)?;
            return Ok(CostClass::Other);
        }
        let Some((eb, sb)) = format(sort) else {
            return Err(FpAdapterError::Unsupported("indexed non-FP application"));
        };
        if indices.as_slice() != [eb, sb] {
            return Err(FpAdapterError::Invalid("indexed FP format mismatch"));
        }
        if matches!(name.as_ref(), "to_fp" | "to_fp_unsigned") && args.len() == 2 {
            numeric_conversion(terms, args)?;
            return Ok(CostClass::NumericConversion);
        }
        let valid = match name.as_ref() {
            "+zero" | "-zero" | "+oo" | "-oo" | "NaN" => args.is_empty(),
            "to_fp" => args.len() == 1 && terms.sort(args[0]) == &Sort::bitvec(eb + sb),
            _ => false,
        };
        return if valid {
            Ok(CostClass::Other)
        } else {
            Err(FpAdapterError::Unsupported("indexed FP operation"))
        };
    }
    if !matches!(symbol, Symbol::Named(_)) {
        return Err(FpAdapterError::Unsupported("source symbol kind"));
    }
    if symbol.name() == "ite" {
        selection(terms, sort, args)?;
        return Ok(CostClass::Other);
    }
    if sort == &Sort::Bool {
        return boolean(terms, symbol.name(), args).map(|_| CostClass::Other);
    }
    if rounding_sort(sort)
        && args.is_empty()
        && ay_fp::RoundingMode::from_name(symbol.name()).is_some()
    {
        return Ok(CostClass::Other);
    }
    let Some((eb, sb)) = format(sort) else {
        return Err(FpAdapterError::Unsupported("application result sort"));
    };
    let valid = match symbol.name() {
        "fp.neg" | "fp.abs" => args.len() == 1 && terms.sort(args[0]) == sort,
        "fp.add" | "fp.sub" | "fp.mul" | "fp.div" => {
            args.len() == 3
                && literal_mode(terms, args[0])
                && args[1..].iter().all(|&id| terms.sort(id) == sort)
        }
        "fp.sqrt" => args.len() == 2 && literal_mode(terms, args[0]) && terms.sort(args[1]) == sort,
        "fp.fma" => {
            args.len() == 4
                && literal_mode(terms, args[0])
                && args[1..].iter().all(|&id| terms.sort(id) == sort)
        }
        "fp.rem" | "__ay_fp_truncating_rem" => {
            args.len() == 2 && args.iter().all(|&id| terms.sort(id) == sort)
        }
        "fp" => {
            args.len() == 3
                && terms.sort(args[0]) == &Sort::bitvec(1)
                && terms.sort(args[1]) == &Sort::bitvec(eb)
                && terms.sort(args[2]) == &Sort::bitvec(sb - 1)
        }
        _ => false,
    };
    if !valid {
        return Err(FpAdapterError::Unsupported("FP operation/format/rounding"));
    }
    Ok(match symbol.name() {
        "fp.div" => CostClass::Division,
        "fp.rem" => CostClass::Remainder,
        "__ay_fp_truncating_rem" => CostClass::TruncatingRemainder,
        "fp.sqrt" => CostClass::SquareRoot,
        "fp.fma" => CostClass::Fused,
        "fp.add" | "fp.sub" | "fp.mul" => CostClass::Arithmetic,
        _ => CostClass::Other,
    })
}

// Numeric conversion is distinct from the one-argument raw IEEE word form.
// Complete descendant validation still runs before native construction.
fn numeric_conversion(terms: &TermStore, args: &[TermId]) -> Result<(), FpAdapterError> {
    let [rm, word] = args else {
        return Err(FpAdapterError::Invalid("numeric conversion arity"));
    };
    if !rounding_sort(terms.sort(*rm))
        || !matches!(terms.get(*rm),
            TermData::App(Symbol::Named(name), modes) if name.as_ref() == "RNE" && modes.is_empty())
    {
        return Err(FpAdapterError::Unsupported(
            "numeric conversion requires literal RNE",
        ));
    }
    if !matches!(terms.sort(*word), Sort::BitVec(bits) if (8..=64).contains(&bits.width))
        || !(matches!(
            terms.get(*word),
            TermData::Var(..) | TermData::Const(Constant::BitVec { .. })
        ) || matches!(terms.get(*word),
                TermData::App(Symbol::Indexed(name, _), _) if name.as_ref() == "extract"))
    {
        return Err(FpAdapterError::Unsupported("numeric conversion word"));
    }
    Ok(())
}

// Exact field slicing only: keep the complete original word as a visited
// child. Nested extracts/arithmetic aliases must not become unowned inputs.
fn raw_extract(
    terms: &TermStore,
    sort: &Sort,
    indices: &[u32],
    args: &[TermId],
) -> Result<(), FpAdapterError> {
    let ([high, low], [word]) = (indices, args) else {
        return Err(FpAdapterError::Invalid("raw extract arity/indices"));
    };
    let width = match terms.sort(*word) {
        Sort::BitVec(bits) if matches!(bits.width, 32 | 64) => bits.width,
        _ => return Err(FpAdapterError::Unsupported("raw extract word width")),
    };
    if !matches!(
        terms.get(*word),
        TermData::Var(..) | TermData::Const(Constant::BitVec { .. })
    ) {
        return Err(FpAdapterError::Unsupported("compound raw extract operand"));
    }
    if low > high || *high >= width || sort != &Sort::bitvec(*high - *low + 1) {
        return Err(FpAdapterError::Invalid("raw extract result/range"));
    }
    Ok(())
}

// Each Bool/FP mux is one OTHER occurrence. Its children are independently
// visited even if legacy simplification selects a constant arm.
fn selection(terms: &TermStore, sort: &Sort, args: &[TermId]) -> Result<(), FpAdapterError> {
    if sort != &Sort::Bool && format(sort).is_none() {
        return Err(FpAdapterError::Unsupported("selection result sort"));
    }
    if args.len() != 3
        || terms.sort(args[0]) != &Sort::Bool
        || terms.sort(args[1]) != sort
        || terms.sort(args[2]) != sort
    {
        return Err(FpAdapterError::Invalid(
            "selection condition/arm/result sort",
        ));
    }
    Ok(())
}

fn boolean(terms: &TermStore, name: &str, args: &[TermId]) -> Result<(), FpAdapterError> {
    if guards::supports(terms, name, args)? {
        return Ok(());
    }
    let valid = match name {
        "and" | "or" | "xor" => args.iter().all(|&id| terms.sort(id) == &Sort::Bool),
        "=>" => args.len() >= 2 && args.iter().all(|&id| terms.sort(id) == &Sort::Bool),
        "=" => {
            args.len() == 2
                && (terms.sort(args[0]) == &Sort::Bool || format(terms.sort(args[0])).is_some())
                && terms.sort(args[0]) == terms.sort(args[1])
        }
        "distinct" => args.len() == 2 && args.iter().all(|&id| terms.sort(id) == &Sort::Bool),
        "fp.eq" | "fp.lt" | "fp.leq" | "fp.gt" | "fp.geq" => {
            args.len() == 2
                && format(terms.sort(args[0])).is_some()
                && terms.sort(args[0]) == terms.sort(args[1])
        }
        "fp.isNaN" | "fp.isInfinite" | "fp.isZero" | "fp.isNormal" | "fp.isSubnormal"
        | "fp.isNegative" | "fp.isPositive" => {
            args.len() == 1 && format(terms.sort(args[0])).is_some()
        }
        _ => false,
    };
    if valid {
        Ok(())
    } else {
        Err(FpAdapterError::Unsupported("Bool FP predicate"))
    }
}

fn literal_mode(terms: &TermStore, id: TermId) -> bool {
    rounding_sort(terms.sort(id))
        && matches!(terms.get(id),
        TermData::App(Symbol::Named(name), args)
            if args.is_empty() && ay_fp::RoundingMode::from_name(name.as_ref()).is_some())
}

fn rounding_sort(sort: &Sort) -> bool {
    matches!(sort, Sort::Uninterpreted(name) if name == "RoundingMode")
}

pub(super) fn format(sort: &Sort) -> Option<(u32, u32)> {
    match sort {
        Sort::FloatingPoint(8, 24) => Some((8, 24)),
        Sort::FloatingPoint(11, 53) => Some((11, 53)),
        _ => None,
    }
}
