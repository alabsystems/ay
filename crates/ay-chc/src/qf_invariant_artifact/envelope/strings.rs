// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Two-pass exact-requested-capacity JSON strings; no general JSON value tree.

use super::{Control, QfEnvelopePreparationError as Error, Reader};

impl<C: Control> Reader<'_, '_, C> {
    pub(super) fn string(&mut self) -> Result<String, Error> {
        self.whitespace()?;
        self.punctuation(b'"')?;
        let start = self.at;
        let mut count = 0usize;
        while let Some(unit) = self.unit()? {
            self.control.offer(1, 0)?;
            count = count
                .checked_add(unit.len)
                .ok_or_else(|| self.control.allocation_failed())?;
        }
        let end = self.at;
        // Exact byte writes, disposal and eight conservative fixed-header moves:
        // Vec -> String -> return -> Option -> array -> envelope -> return -> carrier.
        let work = count
            .checked_add(1 + 8 * std::mem::size_of::<String>())
            .ok_or_else(|| self.control.allocation_failed())?;
        self.control.offer(work, count)?;
        let mut copied = Vec::new();
        copied
            .try_reserve_exact(count)
            .map_err(|_| self.control.allocation_failed())?;
        self.at = start;
        while let Some(unit) = self.unit()? {
            copied.extend_from_slice(&unit.bytes[..unit.len]);
        }
        if self.at != end || copied.len() != count {
            return Err(Error::Malformed);
        }
        // UTF-8 validation scans the decoded payload and transfers the SAME allocation.
        self.control.offer(count, 0)?;
        String::from_utf8(copied).map_err(|_| Error::Malformed)
    }

    fn unit(&mut self) -> Result<Option<Unit>, Error> {
        self.control.offer(std::mem::size_of::<Unit>(), 0)?;
        let byte = self.take()?;
        match byte {
            b'"' => Ok(None),
            0..=31 => Err(Error::Malformed),
            b'\\' => {
                let escaped = self.take()?;
                let value = match escaped {
                    b'"' => b'"',
                    b'\\' => b'\\',
                    b'/' => b'/',
                    b'b' => 8,
                    b'f' => 12,
                    b'n' => b'\n',
                    b'r' => b'\r',
                    b't' => b'\t',
                    b'u' => return self.unicode().map(Some),
                    _ => return Err(Error::Malformed),
                };
                Ok(Some(Unit {
                    bytes: [value, 0, 0, 0],
                    len: 1,
                }))
            }
            _ => Ok(Some(Unit {
                bytes: [byte, 0, 0, 0],
                len: 1,
            })),
        }
    }

    fn hex4(&mut self) -> Result<u16, Error> {
        let mut value = 0u16;
        for _ in 0..4 {
            let byte = self.take()?;
            let digit = match byte {
                b'0'..=b'9' => byte - b'0',
                b'a'..=b'f' => byte - b'a' + 10,
                b'A'..=b'F' => byte - b'A' + 10,
                _ => return Err(Error::Malformed),
            };
            self.control.offer(2, 0)?;
            value = value * 16 + u16::from(digit);
        }
        Ok(value)
    }

    fn unicode(&mut self) -> Result<Unit, Error> {
        let first = self.hex4()?;
        let scalar = if (0xd800..=0xdbff).contains(&first) {
            if self.take()? != b'\\' || self.take()? != b'u' {
                return Err(Error::Malformed);
            }
            let second = self.hex4()?;
            if !(0xdc00..=0xdfff).contains(&second) {
                return Err(Error::Malformed);
            }
            self.control.offer(4, 0)?;
            0x10000 + ((u32::from(first) - 0xd800) << 10) + (u32::from(second) - 0xdc00)
        } else {
            u32::from(first)
        };
        self.control.offer(5, 0)?;
        let character = char::from_u32(scalar).ok_or(Error::Malformed)?;
        let mut bytes = [0u8; 4];
        let len = character.encode_utf8(&mut bytes).len();
        Ok(Unit { bytes, len })
    }
}

struct Unit {
    bytes: [u8; 4],
    len: usize,
}
