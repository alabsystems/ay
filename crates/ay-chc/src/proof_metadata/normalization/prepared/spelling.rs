// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Fixed-width decimal and serde-compatible JSON string spelling without serde.

use super::{bytes::Bytes, Control, QueryError};

pub(super) fn unsigned<C: Control>(
    out: &mut Bytes,
    mut value: u128,
    control: &mut C,
) -> Result<(), QueryError> {
    control.offer(40, 0)?;
    let mut digits = [0u8; 40];
    let mut at = digits.len();
    loop {
        control.offer(8, 0)?;
        at -= 1;
        digits[at] = b'0' + (value % 10) as u8;
        value /= 10;
        if value == 0 {
            break;
        }
    }
    out.append(&digits[at..], control)
}

pub(super) fn signed<C: Control>(
    out: &mut Bytes,
    value: i128,
    control: &mut C,
) -> Result<(), QueryError> {
    control.offer(2, 0)?;
    if value < 0 {
        out.text("-", control)?;
    }
    unsigned(out, value.unsigned_abs(), control)
}

pub(super) fn quoted<C: Control>(
    out: &mut Bytes,
    text: &str,
    control: &mut C,
) -> Result<(), QueryError> {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    out.text("\"", control)?;
    for index in 0..text.len() {
        control.offer(2, 0)?;
        let byte = text.as_bytes()[index];
        match byte {
            b'"' => out.text("\\\"", control)?,
            b'\\' => out.text("\\\\", control)?,
            b'\n' => out.text("\\n", control)?,
            b'\r' => out.text("\\r", control)?,
            b'\t' => out.text("\\t", control)?,
            8 => out.text("\\b", control)?,
            12 => out.text("\\f", control)?,
            0..=31 => {
                control.offer(12, 0)?;
                let escape = [
                    b'\\',
                    b'u',
                    b'0',
                    b'0',
                    HEX[(byte >> 4) as usize],
                    HEX[(byte & 15) as usize],
                ];
                out.append(&escape, control)?;
            }
            _ => {
                control.offer(1, 0)?;
                out.append(&[byte], control)?;
            }
        }
    }
    out.text("\"", control)
}
