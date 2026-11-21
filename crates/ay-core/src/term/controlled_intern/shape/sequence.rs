// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Borrowed physical engine-sort admission for seq.empty and fresh Var factories.

use super::*;
use std::mem::size_of;

pub(in crate::term::controlled_intern) struct SortCost {
    pub(in crate::term::controlled_intern) work: usize,
    pub(in crate::term::controlled_intern) bytes: usize,
}

pub(super) fn admit(sort: &Sort, admission: &mut Admission<'_>) -> Result<SortCost> {
    visit(sort, admission, 0)
}

fn visit(sort: &Sort, admission: &mut Admission<'_>, depth: usize) -> Result<SortCost> {
    if depth > 128 {
        return Err(ControlledTermInternError::ResourceLimit);
    }
    admission.pay(1, 0)?;
    let mut cost = SortCost {
        work: 1,
        bytes: size_of::<Sort>(),
    };
    match sort {
        Sort::Bool | Sort::Int | Sort::Real | Sort::String | Sort::RegLan | Sort::Char => {}
        Sort::BitVec(width) if width.width > 0 => {}
        Sort::FloatingPoint(exponent, significand) if *exponent >= 2 && *significand >= 2 => {}
        Sort::Uninterpreted(name) => {
            // No clone or hashing precedes raw-name work admission.
            admission.pay(name.len(), 0)?;
            cost.work = cost
                .work
                .checked_add(name.len())
                .ok_or(ControlledTermInternError::ResourceLimit)?;
            cost.bytes = cost
                .bytes
                .checked_add(name.len())
                .ok_or(ControlledTermInternError::ResourceLimit)?;
        }
        Sort::Array(array) => {
            // Two physical children; repeated equal subtrees remain separate.
            merge(&mut cost, visit(&array.index_sort, admission, depth + 1)?)?;
            merge(&mut cost, visit(&array.element_sort, admission, depth + 1)?)?;
        }
        Sort::Seq(element) => merge(&mut cost, visit(element, admission, depth + 1)?)?,
        // Native nominal ownership is the caller's job. A full DT descriptor,
        // a type variable or a future kind is never silently reinterpreted.
        _ => return Err(ControlledTermInternError::UnsupportedFragment),
    }
    Ok(cost)
}

fn merge(cost: &mut SortCost, child: SortCost) -> Result<()> {
    cost.work = cost
        .work
        .checked_add(child.work)
        .ok_or(ControlledTermInternError::ResourceLimit)?;
    cost.bytes = cost
        .bytes
        .checked_add(child.bytes)
        .ok_or(ControlledTermInternError::ResourceLimit)?;
    Ok(())
}
