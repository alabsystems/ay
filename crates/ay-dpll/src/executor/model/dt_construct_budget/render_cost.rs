// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact allocation and rendering costs for bounded datatype construction.

use ay_model_check::ModelValue;

pub(super) fn model_value_work(value: &ModelValue, limit: usize) -> Option<usize> {
    let mut stack = vec![value];
    let mut work = 0usize;
    while let Some(value) = stack.pop() {
        let payload = match value {
            ModelValue::Bool(_) => 1,
            ModelValue::Int(value) => usize::try_from(value.bits()).ok()?.div_ceil(8) + 1,
            ModelValue::Real(value) => {
                usize::try_from(value.numer().bits()).ok()?.div_ceil(8)
                    + usize::try_from(value.denom().bits()).ok()?.div_ceil(8)
                    + 1
            }
            ModelValue::BitVec { width, value } => {
                usize::try_from(u64::from(*width).max(value.bits()))
                    .ok()?
                    .div_ceil(8)
                    + 1
            }
            ModelValue::Str(value) | ModelValue::Uninterpreted(value) => value.len() + 1,
            ModelValue::Datatype { ctor, args } => {
                if args.len() > limit.saturating_sub(work) {
                    return None;
                }
                stack.extend(args);
                ctor.len().checked_add(1)?
            }
            ModelValue::Seq(args) => {
                if args.len() > limit.saturating_sub(work) {
                    return None;
                }
                stack.extend(args);
                1
            }
            ModelValue::Array(array) => {
                let extra = 1usize.checked_add(array.store.len().checked_mul(2)?)?;
                if extra > limit.saturating_sub(work) {
                    return None;
                }
                stack.push(&array.default);
                for (key, cell) in &array.store {
                    stack.push(key);
                    stack.push(cell);
                }
                1
            }
            ModelValue::FloatingPoint { .. } | ModelValue::Algebraic(_) => return None,
        };
        work = work.checked_add(payload)?;
        if work > limit {
            return None;
        }
    }
    Some(work)
}

pub(super) fn canonical_render_bytes(value: &ModelValue, limit: usize) -> Option<usize> {
    let mut stack = vec![value];
    let mut bytes = 0usize;
    while let Some(value) = stack.pop() {
        let payload = match value {
            ModelValue::Bool(true) => 4,
            ModelValue::Bool(false) => 5,
            ModelValue::BitVec { width, value }
                if *width <= 256
                    && value.sign() != num_bigint::Sign::Minus
                    && value.bits() <= u64::from(*width) =>
            {
                let width = usize::try_from(*width).ok()?;
                2usize.checked_add(if width % 4 == 0 {
                    (width / 4).max(1)
                } else {
                    width.max(1)
                })?
            }
            // Numeric, element-token, and string payloads render as their
            // digit/byte length plus small fixed syntax (`(- n)`, `(/ a b)`,
            // quotes). These are the scalar fields ordinary total-DT
            // construction has always emitted (#dt-opaque-app-model); each is
            // charged by actual size so an oversized payload fails closed.
            ModelValue::Int(value) => usize::try_from(value.bits())
                .ok()?
                .div_ceil(3)
                .checked_add(5)?,
            ModelValue::Real(value) => usize::try_from(value.numer().bits())
                .ok()?
                .div_ceil(3)
                .checked_add(usize::try_from(value.denom().bits()).ok()?.div_ceil(3))?
                .checked_add(9)?,
            ModelValue::Str(text) => {
                canonical_string_literal_bytes(text, limit.saturating_sub(bytes))?
            }
            ModelValue::Uninterpreted(token) => token.len().checked_add(1)?,
            ModelValue::Datatype { ctor, args } => {
                if args.len() > limit.saturating_sub(bytes) {
                    return None;
                }
                stack.extend(args);
                ctor.len().checked_add(if args.is_empty() {
                    0
                } else {
                    2usize.checked_add(args.len())?
                })?
            }
            ModelValue::Array(array) => {
                // `dt_canonical_string` renders
                // `(#arr DEFAULT [KEY VALUE]...)`: seven fixed bytes for the
                // prefix/final `)`, plus four delimiters per store. Preflight
                // the child count before growing the traversal stack, then
                // charge every nested value through the same bounded walk.
                let children = 1usize.checked_add(array.store.len().checked_mul(2)?)?;
                if children > limit.saturating_sub(bytes) {
                    return None;
                }
                stack.push(&array.default);
                for (key, cell) in &array.store {
                    stack.push(key);
                    stack.push(cell);
                }
                7usize.checked_add(array.store.len().checked_mul(4)?)?
            }
            _ => return None,
        };
        bytes = bytes.checked_add(payload)?;
        if bytes > limit {
            return None;
        }
    }
    Some(bytes)
}

/// Allocation-free upper bound for `string_literal(text).len()`. Quotes and
/// non-printable code points use their exact SMT-LIB spelling. A backslash is
/// charged at the six-byte `\u{5c}` spelling even when its following text does
/// not form a Unicode escape and the formatter can emit it raw; that small
/// overcharge avoids allocating a lookahead character buffer before the work
/// budget has admitted the output.
fn canonical_string_literal_bytes(text: &str, limit: usize) -> Option<usize> {
    let mut bytes = 2usize;
    for character in text.chars() {
        let code = character as u32;
        let payload = match character {
            '"' => 2,
            '\\' => 6,
            '\u{20}'..='\u{7e}' => 1,
            _ if code > ay_core::SMTLIB_MAX_CODE_POINT => character.len_utf8(),
            _ => 4usize.checked_add(hex_digits(code))?,
        };
        bytes = bytes.checked_add(payload)?;
        if bytes > limit {
            return None;
        }
    }
    Some(bytes)
}

fn hex_digits(value: u32) -> usize {
    match value {
        0x0..=0xf => 1,
        0x10..=0xff => 2,
        0x100..=0xfff => 3,
        0x1000..=0xffff => 4,
        0x1_0000..=0xf_ffff => 5,
        _ => 6,
    }
}
