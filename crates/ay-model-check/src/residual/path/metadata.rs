// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Borrowed metadata admission before deep comparisons or owned snapshots.

use super::super::MAX_CLASSIFY_DEPTH;
use crate::dt_axiom::DtResolve;
use ay_core::{DatatypeSort, Sort};
use std::borrow::Cow;

pub(in crate::residual) fn datatype<'a>(
    sort: &'a Sort,
    resolve: &DtResolve<'_>,
    charge: &mut dyn FnMut(usize) -> bool,
) -> Option<Cow<'a, DatatypeSort>> {
    datatype_shape(sort, resolve, charge).flatten()
}

pub(in crate::residual) fn datatype_shape<'a>(
    sort: &'a Sort,
    resolve: &DtResolve<'_>,
    charge: &mut dyn FnMut(usize) -> bool,
) -> Option<Option<Cow<'a, DatatypeSort>>> {
    let datatype = match sort {
        Sort::Datatype(datatype) => Cow::Borrowed(datatype),
        Sort::Uninterpreted(name) => {
            if !charge(name.len().checked_add(1)?) {
                return None;
            }
            // The callback returns an owned definition. Its own allocation/latency
            // is outside this local ledger; further traversal and copies are not.
            let Some(datatype) = resolve(name) else {
                return Some(None);
            };
            Cow::Owned(datatype)
        }
        _ => return Some(None),
    };
    if !datatype_work(&datatype, 0, charge) {
        return None;
    }
    if matches!(sort, Sort::Uninterpreted(name) if datatype.name != *name) {
        return None;
    }
    Some(Some(datatype))
}

pub(in crate::residual) fn sort_work(
    sort: &Sort,
    depth: usize,
    charge: &mut dyn FnMut(usize) -> bool,
) -> bool {
    if depth > MAX_CLASSIFY_DEPTH || !charge(1) {
        return false;
    }
    match sort {
        Sort::Datatype(datatype) => datatype_work(datatype, depth, charge),
        Sort::Array(array) => {
            sort_work(&array.index_sort, depth + 1, charge)
                && sort_work(&array.element_sort, depth + 1, charge)
        }
        Sort::Seq(element) => sort_work(element, depth + 1, charge),
        Sort::Uninterpreted(name) | Sort::TypeVar(name) | Sort::FiniteDomain(name, _) => {
            charge(name.len())
        }
        // Sort metadata contains only a width, not a width-sized payload.
        // Model values and synthesized zeros have a separate payload ledger.
        Sort::BitVec(bitvec) => bitvec.width > 0,
        Sort::Bool
        | Sort::Int
        | Sort::Real
        | Sort::String
        | Sort::RegLan
        | Sort::Char
        | Sort::FloatingPoint(_, _) => true,
        _ => false,
    }
}

fn datatype_work(
    datatype: &DatatypeSort,
    depth: usize,
    charge: &mut dyn FnMut(usize) -> bool,
) -> bool {
    if depth > MAX_CLASSIFY_DEPTH || !charge(datatype.name.len()) {
        return false;
    }
    for (index, constructor) in datatype.constructors.iter().enumerate() {
        if !charge(1) || !charge(constructor.name.len()) {
            return false;
        }
        for previous in &datatype.constructors[..index] {
            if !charge(
                constructor
                    .name
                    .len()
                    .min(previous.name.len())
                    .saturating_add(1),
            ) || previous.name == constructor.name
            {
                return false;
            }
        }
        for (index, field) in constructor.fields.iter().enumerate() {
            if !charge(1) || !charge(field.name.len()) {
                return false;
            }
            for previous in &constructor.fields[..index] {
                if !charge(field.name.len().min(previous.name.len()).saturating_add(1))
                    || field.name == previous.name
                {
                    return false;
                }
            }
            if !sort_work(&field.sort, depth + 1, charge) {
                return false;
            }
        }
    }
    !datatype.constructors.is_empty()
}
