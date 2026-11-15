// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Typed string ownership without serde's hidden unescaping scratch.
//! The RawSlice has already undergone outer JSON/input admission. This decoder
//! reserves the encoded content length (an upper bound on decoded UTF-8) once,
//! checks actual capacity, and never grows or shrinks that allocation. Every
//! input byte is visited under the existing control. Final UTF-8 validation is
//! a prepaid opaque span, not a hard cancellation-latency guarantee.

use super::{Control, RawSlice, TransportError};

pub(in crate::bundle::retained) fn owned_string(
    raw: RawSlice<'_>,
    control: &mut Control<'_>,
) -> Result<String, TransportError> {
    control.charge(1, 0)?;
    let bytes = raw.as_str().as_bytes();
    if bytes.len() < 2 || bytes.first() != Some(&b'"') || bytes.last() != Some(&b'"') {
        return control.fail(TransportError::InvalidShape("expected a string"));
    }
    let content = &bytes[1..bytes.len() - 1];
    let mut output = control.vector::<u8>(content.len())?;
    let mut cursor = Cursor {
        bytes: content,
        position: 0,
        control,
    };
    while cursor.position < content.len() {
        let byte = cursor.next()?;
        match byte {
            b'\\' => {
                let escaped = cursor.next()?;
                let decoded = match escaped {
                    b'"' | b'\\' | b'/' => escaped,
                    b'b' => 0x08,
                    b'f' => 0x0c,
                    b'n' => b'\n',
                    b'r' => b'\r',
                    b't' => b'\t',
                    b'u' => {
                        let scalar = cursor.unicode()?;
                        let mut buffer = [0_u8; 4];
                        append(
                            &mut output,
                            scalar.encode_utf8(&mut buffer).as_bytes(),
                            cursor.control,
                        )?;
                        continue;
                    }
                    _ => return cursor.control.fail(TransportError::InvalidJson),
                };
                append(&mut output, &[decoded], cursor.control)?;
            }
            0x00..=0x1f | b'"' => return cursor.control.fail(TransportError::InvalidJson),
            _ => append(&mut output, &[byte], cursor.control)?,
        }
    }
    // Consumes the Vec without copying or shrinking its allocation. Even
    // though the outer raw slice is UTF-8, unpaired surrogate escapes must
    // refuse before this point, exactly as the existing String decoder does.
    cursor.control.charge(output.len(), 0)?;
    let value = match String::from_utf8(output) {
        Ok(value) => value,
        Err(error) => {
            drop(error);
            return cursor.control.fail(TransportError::InvalidJson);
        }
    };
    cursor.control.charge(0, 0)?;
    Ok(value)
}

fn append(
    output: &mut Vec<u8>,
    bytes: &[u8],
    control: &mut Control<'_>,
) -> Result<(), TransportError> {
    let next = control.add(output.len(), bytes.len())?;
    control.cap("reserved string bytes", next, output.capacity())?;
    output.extend_from_slice(bytes);
    Ok(())
}

struct Cursor<'bytes, 'scope, 'progress> {
    bytes: &'bytes [u8],
    position: usize,
    control: &'scope mut Control<'progress>,
}

impl Cursor<'_, '_, '_> {
    fn next(&mut self) -> Result<u8, TransportError> {
        self.control.charge(1, 0)?;
        let Some(&byte) = self.bytes.get(self.position) else {
            return self.control.fail(TransportError::InvalidJson);
        };
        self.position += 1; // bounded by the admitted slice length
        Ok(byte)
    }

    fn hex(&mut self) -> Result<u16, TransportError> {
        let mut value = 0_u16;
        for _ in 0..4 {
            let digit = match self.next()? {
                byte @ b'0'..=b'9' => byte - b'0',
                byte @ b'a'..=b'f' => byte - b'a' + 10,
                byte @ b'A'..=b'F' => byte - b'A' + 10,
                _ => return self.control.fail(TransportError::InvalidJson),
            };
            value = (value << 4) | u16::from(digit);
        }
        Ok(value)
    }

    fn unicode(&mut self) -> Result<char, TransportError> {
        let first = self.hex()?;
        let scalar = match first {
            0xd800..=0xdbff => {
                if self.next()? != b'\\' || self.next()? != b'u' {
                    return self.control.fail(TransportError::InvalidJson);
                }
                let low = self.hex()?;
                if !(0xdc00..=0xdfff).contains(&low) {
                    return self.control.fail(TransportError::InvalidJson);
                }
                0x10000 + ((u32::from(first) - 0xd800) << 10) + (u32::from(low) - 0xdc00)
            }
            0xdc00..=0xdfff => return self.control.fail(TransportError::InvalidJson),
            _ => u32::from(first),
        };
        char::from_u32(scalar)
            .ok_or(TransportError::InvalidJson)
            .or_else(|error| self.control.fail(error))
    }
}

#[cfg(test)]
mod tests;
