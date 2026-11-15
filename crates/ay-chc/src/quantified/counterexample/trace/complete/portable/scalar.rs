// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Exact bounded scalar DATA; numeric values never supply source sort authority.

use super::*;
use ay_core::Sort;
use ay_model_check::ModelValue;
use num_bigint::BigInt;
use num_traits::{Signed, ToPrimitive};

pub(super) fn element(sort: &Sort, control: &SourceControl<'_>) -> Option<wire::Element> {
    control.debit(1, 0)?;
    match sort {
        Sort::Bool => Some(wire::Element::Bool),
        Sort::BitVec(width) if (1..=128).contains(&width.width) => {
            Some(wire::Element::BitVec { width: width.width })
        }
        _ => None,
    }
}

pub(super) fn sort(element: wire::Element, control: &SourceControl<'_>) -> Option<Sort> {
    control.debit(1, 3 * std::mem::size_of::<Sort>())?;
    let cell = match element {
        wire::Element::Bool => Sort::Bool,
        wire::Element::BitVec { width } if (1..=128).contains(&width) => Sort::bitvec(width),
        _ => return None,
    };
    Some(Sort::array(Sort::bitvec(64), cell))
}

pub(super) fn unsigned(value: &BigInt, control: &SourceControl<'_>) -> Option<u64> {
    control.debit(32, 0)?;
    if value.is_negative() || value.bits() > 64 {
        return None;
    }
    value.to_u64()
}

pub(super) fn export(
    value: &ModelValue,
    expected: wire::Element,
    control: &SourceControl<'_>,
) -> Option<wire::Scalar> {
    control.debit(128, 256)?;
    match (value, expected) {
        (ModelValue::Bool(value), wire::Element::Bool) => {
            Some(wire::Scalar::Bool { value: *value })
        }
        (ModelValue::BitVec { value, width }, wire::Element::BitVec { width: expected })
            if *width == expected
                && (1..=128).contains(width)
                && !value.is_negative()
                && value.bits() <= u64::from(*width) =>
        {
            Some(wire::Scalar::BitVec {
                width: *width,
                value: value.to_u128()?.to_string(),
            })
        }
        _ => None,
    }
}

pub(super) fn import(
    value: &wire::Scalar,
    expected: wire::Element,
    control: &SourceControl<'_>,
) -> Option<ModelValue> {
    control.debit(128, 256)?;
    match (value, expected) {
        (wire::Scalar::Bool { value }, wire::Element::Bool) => Some(ModelValue::Bool(*value)),
        (wire::Scalar::BitVec { width, value }, wire::Element::BitVec { width: expected })
            if *width == expected && (1..=128).contains(width) =>
        {
            let number = decimal(value, control)?;
            if *width < 128 && number >= (1u128 << *width) {
                return None;
            }
            // Construct the exact admitted value, not a normalizing coercion.
            Some(ModelValue::BitVec {
                width: *width,
                value: BigInt::from(number),
            })
        }
        _ => None,
    }
}

fn decimal(text: &str, control: &SourceControl<'_>) -> Option<u128> {
    control.debit(text.len().checked_add(1)?, 0)?;
    if text.is_empty() || text.len() > 39 || (text.len() > 1 && text.starts_with('0')) {
        return None;
    }
    let mut value = 0u128;
    for byte in text.bytes() {
        if !byte.is_ascii_digit() {
            return None;
        }
        value = value
            .checked_mul(10)?
            .checked_add(u128::from(byte - b'0'))?;
    }
    control.poll()?;
    Some(value)
}
