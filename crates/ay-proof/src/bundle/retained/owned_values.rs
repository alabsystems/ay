// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Controlled leaves, not a generic owning serde decoder or bundle reader.
//!
//! The caller has already admitted and validated the borrowed RawValue. Array
//! children remain borrowed slices of that value. Scans and vector slots use
//! the SAME control; there is no new grant, deadline, parser scratch or JSON
//! error allocation here. An explicit element decoder must admit its own
//! nested owners. Vector slot accounting does not account arbitrary T owners.
//! The operation owner must drop partial values before Control::finish, and
//! separately record all returned owner capacities. No allocator RSS claim.

use super::{control::Control, lexical::WINDOW, RawValue, TransportError};

mod compound;
mod string;
pub(super) use compound::{structure, tagged, tuple, Form, Tag, UnknownFields};
pub(super) use string::owned_string;

/// Construction is restricted to already validated JSON, not arbitrary text.
#[derive(Clone, Copy, Debug)]
pub(super) struct RawSlice<'a>(&'a str);

impl<'a> RawSlice<'a> {
    /// RawValue validation and input/storage/depth admission belong to caller.
    pub(super) fn from_raw(raw: &'a RawValue) -> Self {
        Self(raw.get())
    }

    pub(super) fn as_str(self) -> &'a str {
        self.0
    }
}

pub(super) fn bool_value(
    raw: RawSlice<'_>,
    control: &mut Control<'_>,
) -> Result<bool, TransportError> {
    control.charge(1, 0)?;
    match raw.0 {
        "true" => Ok(true),
        "false" => Ok(false),
        _ => control.fail(TransportError::InvalidShape("expected bool")),
    }
}

pub(super) fn null(raw: RawSlice<'_>, control: &mut Control<'_>) -> Result<(), TransportError> {
    control.charge(1, 0)?;
    if raw.0 == "null" {
        Ok(())
    } else {
        control.fail(TransportError::InvalidShape("expected null"))
    }
}

fn integer(raw: RawSlice<'_>, control: &mut Control<'_>) -> Result<(bool, u64), TransportError> {
    control.charge(1, 0)?;
    let negative = raw.0.starts_with('-');
    let digits = if negative { &raw.0[1..] } else { raw.0 };
    if digits.is_empty() || digits.len() > 20 {
        return control.fail(TransportError::InvalidShape("expected integer"));
    }
    let mut magnitude = 0_u64;
    for byte in digits.bytes() {
        control.charge(1, 0)?;
        if !byte.is_ascii_digit() {
            return control.fail(TransportError::InvalidShape("expected integer"));
        }
        magnitude = magnitude
            .checked_mul(10)
            .and_then(|value| value.checked_add(u64::from(byte - b'0')))
            .ok_or(TransportError::InvalidShape("integer out of range"))
            .or_else(|error| control.fail(error))?;
    }
    // serde_json 1.0.150 de.rs::parse_number represents -0, decimal and
    // exponent tokens as f64; serde's integer visitors reject those tokens.
    if negative && magnitude == 0 {
        return control.fail(TransportError::InvalidShape("expected integer"));
    }
    Ok((negative, magnitude))
}

pub(super) fn u64_value(
    raw: RawSlice<'_>,
    control: &mut Control<'_>,
) -> Result<u64, TransportError> {
    let (negative, value) = integer(raw, control)?;
    if negative {
        control.fail(TransportError::InvalidShape("expected u64"))
    } else {
        Ok(value)
    }
}

pub(super) fn u32_value(
    raw: RawSlice<'_>,
    control: &mut Control<'_>,
) -> Result<u32, TransportError> {
    u32::try_from(u64_value(raw, control)?)
        .map_err(|_| TransportError::InvalidShape("expected u32"))
        .or_else(|error| control.fail(error))
}

pub(super) fn i64_value(
    raw: RawSlice<'_>,
    control: &mut Control<'_>,
) -> Result<i64, TransportError> {
    let (negative, value) = integer(raw, control)?;
    if negative && value == 1_u64 << 63 {
        return Ok(i64::MIN);
    }
    let value = i64::try_from(value)
        .map_err(|_| TransportError::InvalidShape("expected i64"))
        .or_else(|error| control.fail(error))?;
    Ok(if negative { -value } else { value })
}

pub(super) fn i8_value(raw: RawSlice<'_>, control: &mut Control<'_>) -> Result<i8, TransportError> {
    i8::try_from(i64_value(raw, control)?)
        .map_err(|_| TransportError::InvalidShape("expected i8"))
        .or_else(|error| control.fail(error))
}

/// Two charged scans: census before allocation, then decode into a fixed Vec.
/// `decode` is trusted typed code, NOT Deserialize<T>: it owns admission of any
/// nested buffers and must use this control. Only Vec<T> slots are priced here.
pub(super) fn vector<'a, T>(
    raw: RawSlice<'a>,
    maximum_count: usize,
    control: &mut Control<'_>,
    mut decode: impl FnMut(RawSlice<'a>, &mut Control<'_>) -> Result<T, TransportError>,
) -> Result<Vec<T>, TransportError> {
    let mut census = Array::new(raw, control)?;
    let mut count = 0;
    while census.next(control)?.is_some() {
        count = control.add(count, 1)?;
        control.cap("owned vector elements", count, maximum_count)?;
    }
    let mut output = control.vector::<T>(count)?;
    let mut input = Array::new(raw, control)?;
    while let Some(element) = input.next(control)? {
        if output.len() >= count {
            return control.fail(TransportError::InvalidShape("array census mismatch"));
        }
        control.charge(1, 0)?;
        let value = decode(element, control).or_else(|error| control.fail(error))?;
        // An element decoder cannot swallow a sticky refusal and publish T.
        control.charge(0, 0)?;
        output.push(value); // Exact census allocation; no growth is possible.
    }
    if output.len() != count {
        return control.fail(TransportError::InvalidShape("array census mismatch"));
    }
    control.charge(0, 0)?;
    Ok(output)
}

/// Allocation-free cursor over known-valid JSON. It recognizes only structural
/// boundaries, not legacy types. Escaped quotes and nested delimiters stay in
/// their original borrowed slice. Every byte pass is prepaid in bounded chunks.
struct Array<'a> {
    text: &'a str,
    position: usize,
    prepaid_end: usize,
    finished: bool,
}

impl<'a> Array<'a> {
    fn new(raw: RawSlice<'a>, control: &mut Control<'_>) -> Result<Self, TransportError> {
        control.charge(2, 0)?;
        if !raw.0.starts_with('[') || !raw.0.ends_with(']') {
            return control.fail(TransportError::InvalidShape("expected array"));
        }
        Ok(Self {
            text: raw.0,
            position: 1,
            prepaid_end: 1,
            finished: false,
        })
    }

    fn byte(&mut self, control: &mut Control<'_>) -> Result<u8, TransportError> {
        if self.position == self.prepaid_end {
            let amount = (self.text.len() - self.position).min(WINDOW);
            control.charge(amount, 0)?;
            self.prepaid_end = control.add(self.position, amount)?;
        }
        let byte = self.text.as_bytes().get(self.position).copied();
        if let Some(byte) = byte {
            self.position += 1; // position < the valid slice length.
            Ok(byte)
        } else {
            control.fail(TransportError::InvalidJson)
        }
    }

    fn next(&mut self, control: &mut Control<'_>) -> Result<Option<RawSlice<'a>>, TransportError> {
        control.charge(0, 0)?;
        if self.finished {
            return Ok(None);
        }
        let mut byte = self.byte(control)?;
        while whitespace(byte) {
            byte = self.byte(control)?;
        }
        if byte == b']' {
            self.finished = true;
            return Ok(None);
        }
        let start = self.position - 1;
        let (mut end, mut depth, mut quoted, mut escaped) = (start, 0_usize, false, false);
        loop {
            if !quoted && depth == 0 && matches!(byte, b',' | b']') {
                self.finished = byte == b']';
                let slice = self.text.get(start..end).filter(|value| !value.is_empty());
                return slice
                    .map(|text| Some(RawSlice(text)))
                    .ok_or(TransportError::InvalidJson)
                    .or_else(|error| control.fail(error));
            }
            if quoted {
                if byte == b'"' && !escaped {
                    quoted = false;
                }
                escaped = byte == b'\\' && !escaped;
            } else {
                match byte {
                    b'"' => quoted = true,
                    b'[' | b'{' => depth = control.add(depth, 1)?,
                    b']' | b'}' => {
                        depth = depth
                            .checked_sub(1)
                            .ok_or(TransportError::InvalidJson)
                            .or_else(|error| control.fail(error))?;
                    }
                    _ => {}
                }
            }
            if !whitespace(byte) {
                end = self.position;
            }
            byte = self.byte(control)?;
        }
    }
}

fn whitespace(byte: u8) -> bool {
    matches!(byte, b' ' | b'\n' | b'\r' | b'\t')
}

#[cfg(test)]
mod tests;
