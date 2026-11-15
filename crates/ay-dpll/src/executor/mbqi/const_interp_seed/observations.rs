// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::{
    flat, Budget, CheckedProjectionBinding, EvalValue, Executor, FlatSort, Sort, Symbol, TermId,
};
use crate::executor::model::Model;
use num_bigint::{BigInt, Sign};

pub(super) fn valid_bv(value: &BigInt, width: u32) -> Option<()> {
    ((1..=64).contains(&width) && value.sign() != Sign::Minus && value.bits() <= u64::from(width))
        .then_some(())
}

pub(super) fn current_binding(
    exec: &Executor,
    head: &CheckedProjectionBinding,
    budget: &mut Budget<'_>,
) -> Option<()> {
    let Symbol::Named(name) = head.symbol() else {
        return None;
    };
    budget.charge(exec, name.len().checked_add(head.parameter_sorts().len())?)?;
    let result = flat(head.result_sort())?;
    if result == FlatSort::Bool
        || (matches!(result, FlatSort::Array(..)) && !head.parameter_sorts().is_empty())
    {
        return None;
    }
    if head
        .parameter_sorts()
        .iter()
        .any(|sort| !matches!(flat(sort), Some(FlatSort::Bool | FlatSort::Bv(_))))
    {
        return None;
    }
    // Preflight LIVE descriptors too, before the established checker compares
    // signatures. No recursive metadata equality is used for this new lane.
    let info = exec.ctx.symbol_info(name)?;
    budget.charge(exec, info.arg_sorts.len().checked_add(1)?)?;
    if flat(&info.sort)? != result || info.arg_sorts.len() != head.parameter_sorts().len() {
        return None;
    }
    for (actual, expected) in info.arg_sorts.iter().zip(head.parameter_sorts()) {
        if flat(actual)? != flat(expected)? {
            return None;
        }
    }
    exec.ctx
        .projection_binding_still_current(head)
        .then_some(())
}

pub(super) fn read(
    exec: &Executor,
    model: &Model,
    head: &CheckedProjectionBinding,
    term: TermId,
    budget: &mut Budget<'_>,
) -> Option<BigInt> {
    budget.charge(exec, 1)?;
    exec.ctx.terms.entry_stamp(term)?;
    let width = match flat(head.result_sort())? {
        FlatSort::Bv(width) | FlatSort::Array(_, width) => width,
        FlatSort::Bool => return None,
    };
    if flat(exec.ctx.terms.sort(term))? != FlatSort::Bv(width) {
        return None;
    }
    if let Some(bv) = &model.bv_model {
        // Capacity precharges worst-case probing, including unsuccessful probes.
        // Do not scan or clone maps; every chosen head pays its own lookup cost.
        budget.charge(exec, bv.term_to_bits.capacity().checked_add(1)?)?;
        if bv
            .term_to_bits
            .get(&term)
            .is_some_and(|bits| bits.len() != width as usize)
        {
            return None;
        }
        budget.charge(exec, bv.values.capacity().checked_add(1)?)?;
        if let Some(value) = bv.values.get(&term) {
            valid_bv(value, width)?;
            budget.charge(exec, 9)?; // at most eight payload bytes, before clone
            return Some(value.clone());
        }
    }
    // Only a primitive nullary declaration may use completed scalar data.
    // No UF/default rows, arrays, textual cells, congruence or evaluator reads.
    if !head.parameter_sorts().is_empty() || flat(head.result_sort())? != FlatSort::Bv(width) {
        return None;
    }
    budget.charge(exec, model.completed_values.capacity().checked_add(1)?)?;
    let EvalValue::BitVec {
        value,
        width: actual_width,
    } = model.completed_values.get(&term)?
    else {
        return None;
    };
    if *actual_width != width {
        return None;
    }
    valid_bv(value, width)?;
    budget.charge(exec, 9)?;
    Some(value.clone())
}

pub(super) fn materialize(
    exec: &mut Executor,
    head: &CheckedProjectionBinding,
    value: BigInt,
) -> Option<TermId> {
    match flat(head.result_sort())? {
        FlatSort::Bv(width) => Some(exec.ctx.terms.mk_bitvec(value, width)),
        FlatSort::Array(index, cell) => {
            let value = exec.ctx.terms.mk_bitvec(value, cell);
            Some(exec.ctx.terms.mk_const_array(Sort::bitvec(index), value))
        }
        FlatSort::Bool => None,
    }
}
