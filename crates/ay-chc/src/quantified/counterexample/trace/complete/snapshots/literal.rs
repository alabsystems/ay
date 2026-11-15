// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Closed scalar snapshot captures only; no opaque token or value coercion.

use super::*;
use ay_model_check::ModelValue;
use num_traits::{Signed, ToPrimitive};

pub(super) fn scalar(
    value: &ModelValue,
    sort: &ay_core::Sort,
    control: &SourceControl<'_>,
) -> Option<String> {
    control.debit(64, 128)?;
    match (value, sort) {
        (ModelValue::Bool(value), ay_core::Sort::Bool) => {
            Some(if *value { "true" } else { "false" }.to_owned())
        }
        (ModelValue::BitVec { width, value }, ay_core::Sort::BitVec(expected))
            if *width == expected.width
                && (1..=128).contains(width)
                && !value.is_negative()
                && value.bits() <= u64::from(*width) =>
        {
            Some(format!("(_ bv{} {width})", value.to_u128()?))
        }
        _ => None,
    }
}

pub(super) fn unsigned(value: &num_bigint::BigInt, control: &SourceControl<'_>) -> Option<u64> {
    control.debit(32, 0)?;
    if value.is_negative() || value.bits() > 64 {
        return None;
    }
    value.to_u64()
}

pub(super) fn sort(sort: &ay_core::Sort, control: &SourceControl<'_>) -> Option<String> {
    control.debit(64, 128)?;
    let ay_core::Sort::Array(array) = sort else {
        return None;
    };
    if !matches!(&array.index_sort, ay_core::Sort::BitVec(width) if width.width == 64) {
        return None;
    }
    match &array.element_sort {
        ay_core::Sort::Bool => Some("(Array (_ BitVec 64) Bool)".to_owned()),
        ay_core::Sort::BitVec(width) if (1..=128).contains(&width.width) => {
            Some(format!("(Array (_ BitVec 64) (_ BitVec {}))", width.width))
        }
        _ => None,
    }
}

pub(super) fn finite(
    value: &ay_model_check::ArrayValue,
    sort: &ay_core::Sort,
    control: &SourceControl<'_>,
) -> Option<String> {
    let ay_core::Sort::Array(array) = sort else {
        return None;
    };
    let sort_text = self::sort(sort, control)?;
    let default = scalar(&value.default, &array.element_sort, control)?;
    let mut text = String::new();
    for _ in &value.store {
        append(&mut text, "(store ", control)?;
    }
    append(&mut text, "((as const ", control)?;
    append(&mut text, &sort_text, control)?;
    append(&mut text, ") ", control)?;
    append(&mut text, &default, control)?;
    append(&mut text, ")", control)?;
    // Every overwritten key/cell and the default was admitted by topology;
    // format them all in exact original order, never normalize sampled cells.
    for (index, datum) in &value.store {
        let index = scalar(index, &array.index_sort, control)?;
        let datum = scalar(datum, &array.element_sort, control)?;
        for piece in [" ", index.as_str(), " ", datum.as_str(), ")"] {
            append(&mut text, piece, control)?;
        }
    }
    Some(text)
}

pub(super) fn append(text: &mut String, piece: &str, control: &SourceControl<'_>) -> Option<()> {
    control.debit(piece.len().checked_add(1)?, piece.len().checked_mul(2)?)?;
    if text.len().checked_add(piece.len())? > 8 * 1024 * 1024 {
        control.stop();
        return None;
    }
    text.try_reserve(piece.len()).ok()?;
    text.push_str(piece);
    Some(())
}
