// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Borrowed compound shape, not an owning ADT decoder. Input is validated JSON
//! already admitted by the caller. All new scans and temporary name owners use
//! the original control. Typed callers still validate values, variant bodies,
//! required fields and form-specific defaults. No proof authority is created.

use super::{owned_string, whitespace, Array, Control, RawSlice, TransportError};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(in crate::bundle::retained) enum UnknownFields {
    Reject,
    Ignore,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(in crate::bundle::retained) enum Form {
    Object,
    Sequence,
}

#[derive(Debug)]
pub(in crate::bundle::retained) struct Fields<'a, const N: usize> {
    pub(in crate::bundle::retained) form: Form,
    pub(in crate::bundle::retained) values: [Option<RawSlice<'a>>; N],
}

#[derive(Debug)]
pub(in crate::bundle::retained) struct Tag<'a> {
    pub(in crate::bundle::retained) index: usize,
    /// None is a string variant; Some(null) remains an actual object payload.
    pub(in crate::bundle::retained) payload: Option<RawSlice<'a>>,
}

pub(in crate::bundle::retained) fn tuple<'a, const N: usize>(
    raw: RawSlice<'a>,
    control: &mut Control<'_>,
) -> Result<[Option<RawSlice<'a>>; N], TransportError> {
    let values = sequence(raw, control)?;
    control.charge(N, 0)?;
    if values.iter().any(Option::is_none) {
        return control.fail(TransportError::InvalidShape("short tuple"));
    }
    Ok(values)
}

/// Names and N are trusted type metadata, not supplied by the JSON document.
/// Missing map fields and missing trailing sequence fields remain distinct:
/// serde's implicit Option default applies to maps, not to struct sequences.
pub(in crate::bundle::retained) fn structure<'a, const N: usize>(
    raw: RawSlice<'a>,
    names: &[&str; N],
    unknown: UnknownFields,
    control: &mut Control<'_>,
) -> Result<Fields<'a, N>, TransportError> {
    control.charge(N, 0)?;
    if raw.0.starts_with('[') {
        return Ok(Fields {
            form: Form::Sequence,
            values: sequence(raw, control)?,
        });
    }
    let mut input = Object::new(raw, control)?;
    let mut values = [None; N];
    while let Some((key, value)) = input.next(control)? {
        let Some(index) = name_index(key, names, unknown, control)? else {
            continue;
        };
        if values[index].is_some() {
            return control.fail(TransportError::InvalidShape("duplicate field"));
        }
        values[index] = Some(value);
    }
    control.charge(0, 0)?;
    Ok(Fields {
        form: Form::Object,
        values,
    })
}

/// serde_json's externally tagged enum grammar: string or single-entry map.
/// Whether a tag is unit/newtype/tuple/struct belongs to the typed caller.
pub(in crate::bundle::retained) fn tagged<'a>(
    raw: RawSlice<'a>,
    variants: &[&str],
    control: &mut Control<'_>,
) -> Result<Tag<'a>, TransportError> {
    control.charge(1, 0)?;
    let (name, payload) = if raw.0.starts_with('"') {
        (raw, None)
    } else {
        let mut object = Object::new(raw, control)?;
        let Some((name, payload)) = object.next(control)? else {
            return control.fail(TransportError::InvalidShape("empty enum object"));
        };
        if object.next(control)?.is_some() {
            return control.fail(TransportError::InvalidShape("multiple enum entries"));
        }
        (name, Some(payload))
    };
    let index = name_index(name, variants, UnknownFields::Reject, control)?
        .ok_or(TransportError::InvalidShape("unknown variant"))
        .or_else(|error| control.fail(error))?;
    control.charge(0, 0)?;
    Ok(Tag { index, payload })
}

fn sequence<'a, const N: usize>(
    raw: RawSlice<'a>,
    control: &mut Control<'_>,
) -> Result<[Option<RawSlice<'a>>; N], TransportError> {
    control.charge(N, 0)?;
    let mut values = [None; N];
    let mut input = Array::new(raw, control)?;
    let mut count = 0;
    while let Some(value) = input.next(control)? {
        control.charge(1, 0)?;
        let Some(slot) = values.get_mut(count) else {
            return control.fail(TransportError::InvalidShape("long sequence"));
        };
        *slot = Some(value);
        count += 1; // A slot exists, so count was strictly below N.
    }
    control.charge(0, 0)?;
    Ok(values)
}

fn name_index(
    raw: RawSlice<'_>,
    names: &[&str],
    unknown: UnknownFields,
    control: &mut Control<'_>,
) -> Result<Option<usize>, TransportError> {
    control.charge(names.len(), 0)?;
    if unknown == UnknownFields::Reject {
        let longest = names.iter().map(|name| name.len()).max().unwrap_or(0);
        let content = control.product(longest, 6)?;
        let maximum = control.add(content, 2)?;
        control.cap("encoded field name bytes", raw.0.len(), maximum)?;
    }
    // Ignore must not cap an unknown name by the known-name lengths: legacy
    // serde accepts longer ignored names. The original storage/work ceilings
    // still preadmit this temporary String, including lone-surrogate refusal.
    let name = owned_string(raw, control)?;
    let mut found = None;
    for (index, expected) in names.iter().enumerate() {
        let comparison = control.add(name.len().min(expected.len()), 1)?;
        control.charge(comparison, 0)?;
        if name == *expected {
            found = Some(index);
            break;
        }
    }
    drop(name);
    control.charge(0, 0)?;
    if found.is_none() && unknown == UnknownFields::Reject {
        return control.fail(TransportError::InvalidShape("unknown field or variant"));
    }
    Ok(found)
}

/// This reuses Array's chunk-prepaid byte reader, not its array grammar.
/// No serde parser, scratch, copied element or recursion is introduced.
struct Object<'a> {
    input: Array<'a>,
}

impl<'a> Object<'a> {
    fn new(raw: RawSlice<'a>, control: &mut Control<'_>) -> Result<Self, TransportError> {
        control.charge(2, 0)?;
        if !raw.0.starts_with('{') || !raw.0.ends_with('}') {
            return control.fail(TransportError::InvalidShape("expected object"));
        }
        Ok(Self {
            input: Array {
                text: raw.0,
                position: 1,
                prepaid_end: 1,
                finished: false,
            },
        })
    }

    fn non_space(&mut self, control: &mut Control<'_>) -> Result<u8, TransportError> {
        let mut byte = self.input.byte(control)?;
        while whitespace(byte) {
            byte = self.input.byte(control)?;
        }
        Ok(byte)
    }

    fn next(
        &mut self,
        control: &mut Control<'_>,
    ) -> Result<Option<(RawSlice<'a>, RawSlice<'a>)>, TransportError> {
        control.charge(0, 0)?;
        if self.input.finished {
            return Ok(None);
        }
        let first = self.non_space(control)?;
        if first == b'}' {
            self.input.finished = true;
            return Ok(None);
        }
        if first != b'"' {
            return control.fail(TransportError::InvalidJson);
        }
        let start = self.input.position - 1;
        let mut escaped = false;
        loop {
            let byte = self.input.byte(control)?;
            if byte == b'"' && !escaped {
                break;
            }
            escaped = byte == b'\\' && !escaped;
        }
        let key = self.slice(start, self.input.position, control)?;
        if self.non_space(control)? != b':' {
            return control.fail(TransportError::InvalidJson);
        }
        let value = self.value(control)?;
        Ok(Some((key, value)))
    }

    fn slice(
        &self,
        start: usize,
        end: usize,
        control: &mut Control<'_>,
    ) -> Result<RawSlice<'a>, TransportError> {
        self.input
            .text
            .get(start..end)
            .filter(|value| !value.is_empty())
            .map(RawSlice)
            .ok_or(TransportError::InvalidJson)
            .or_else(|error| control.fail(error))
    }

    fn value(&mut self, control: &mut Control<'_>) -> Result<RawSlice<'a>, TransportError> {
        let mut byte = self.non_space(control)?;
        let start = self.input.position - 1;
        let (mut end, mut depth, mut quoted, mut escaped) = (start, 0_usize, false, false);
        loop {
            if !quoted && depth == 0 && matches!(byte, b',' | b'}') {
                self.input.finished = byte == b'}';
                return self.slice(start, end, control);
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
                            .or_else(|error| control.fail(error))?
                    }
                    _ => {}
                }
            }
            if !whitespace(byte) {
                end = self.input.position;
            }
            byte = self.input.byte(control)?;
        }
    }
}

#[cfg(test)]
mod tests;
