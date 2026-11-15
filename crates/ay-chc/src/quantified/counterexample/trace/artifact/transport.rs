// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Bounded JSON transport for the reviewed artifact wire types, not an
//! allocation sandbox for arbitrary user-written Serialize/Deserialize code.

use crate::transform::array_ghost_pairs::source_premises::SourceControl;
use serde::{de::DeserializeOwned, Serialize};
use sha2::{Digest, Sha256};
use std::io::{self, Read, Write};

pub(super) const MAX_BYTES: usize = 16 * 1024 * 1024;
const MAX_DEPTH: usize = 16;
const CHUNK: usize = 4096;

pub(in crate::quantified::counterexample::trace) fn decode<T: DeserializeOwned>(
    bytes: &[u8],
    control: &SourceControl<'_>,
) -> Option<T> {
    let mut surface = Surface::default();
    surface.feed(bytes, control)?;
    surface.finish(control)?;
    // IoRead's reusable string scratch may grow geometrically. Reserve all
    // retained payloads, twice the largest token's scratch, and conservative
    // String/Vec/entry capacity for every token before invoking serde. The
    // wire structs contain only scalar fields, Strings and their containers.
    let storage = surface
        .payload
        .checked_add(surface.largest.checked_mul(2)?)?
        .checked_add(surface.tokens.checked_mul(192)?)?
        .checked_add(256)?;
    control.bytes(storage)?;
    let reader = Reader {
        bytes,
        offset: 0,
        window: 0,
        failed: false,
        control,
    };
    let mut decoder = serde_json::Deserializer::from_reader(reader);
    let value = T::deserialize(&mut decoder).ok()?;
    decoder.end().ok()?;
    drop(decoder);
    control.poll()?;
    Some(value)
}

pub(in crate::quantified::counterexample::trace) fn encode<T: Serialize>(
    value: &T,
    control: &SourceControl<'_>,
) -> Option<Vec<u8>> {
    control.poll()?;
    let mut writer = Writer {
        bytes: Vec::new(),
        surface: Surface::default(),
        failed: false,
        control,
    };
    serde_json::to_writer(&mut writer, value).ok()?;
    if writer.failed {
        return None;
    }
    writer.surface.finish(control)?;
    let bytes = writer.bytes;
    control.poll()?;
    Some(bytes)
}

pub(in crate::quantified::counterexample::trace) fn digest(
    bytes: &[u8],
    control: &SourceControl<'_>,
) -> Option<String> {
    control.poll()?;
    if bytes.len() > MAX_BYTES {
        return None;
    }
    control.bytes(bytes.len())?;
    let mut hash = Sha256::new();
    for chunk in bytes.chunks(CHUNK) {
        control.charge(1)?;
        hash.update(chunk);
    }
    control.bytes(128)?;
    let result = format!("{:x}", hash.finalize());
    control.poll()?;
    Some(result)
}

#[derive(Default)]
struct Surface {
    bytes: usize,
    stack: [u8; MAX_DEPTH],
    depth: usize,
    string: bool,
    escaped: bool,
    atom: bool,
    current: usize,
    payload: usize,
    largest: usize,
    tokens: usize,
}

impl Surface {
    fn feed(&mut self, input: &[u8], control: &SourceControl<'_>) -> Option<()> {
        control.poll()?;
        self.bytes = self.bytes.checked_add(input.len())?;
        if self.bytes > MAX_BYTES {
            return None;
        }
        control.bytes(input.len())?;
        for chunk in input.chunks(CHUNK) {
            control.charge(1)?;
            for &byte in chunk {
                self.byte(byte, control)?;
            }
        }
        control.poll()
    }

    fn byte(&mut self, byte: u8, control: &SourceControl<'_>) -> Option<()> {
        if self.string {
            if byte < 0x20 {
                return None;
            }
            if !self.escaped && byte == b'"' {
                self.string = false;
                self.end_token();
            } else {
                self.payload_byte();
                self.escaped = !self.escaped && byte == b'\\';
            }
            return Some(());
        }
        match byte {
            b'"' => {
                self.end_token();
                self.token(control)?;
                self.string = true;
            }
            b'[' | b'{' => {
                self.end_token();
                self.token(control)?;
                if self.depth == MAX_DEPTH {
                    return None;
                }
                self.stack[self.depth] = byte;
                self.depth += 1;
            }
            b']' | b'}' => {
                self.end_token();
                let expected = if byte == b']' { b'[' } else { b'{' };
                self.depth = self.depth.checked_sub(1)?;
                if self.stack[self.depth] != expected {
                    return None;
                }
            }
            b':' | b',' | b' ' | b'\n' | b'\r' | b'\t' => self.end_token(),
            _ => {
                if !self.atom {
                    self.token(control)?;
                    self.atom = true;
                }
                self.payload_byte();
            }
        }
        Some(())
    }

    fn token(&mut self, control: &SourceControl<'_>) -> Option<()> {
        control.charge(1)?;
        self.tokens += 1; // Each token consumes at least one of MAX_BYTES bytes.
        Some(())
    }

    fn payload_byte(&mut self) {
        self.current += 1;
        self.payload += 1; // Both are bounded by the admitted surface length.
    }

    fn end_token(&mut self) {
        self.largest = self.largest.max(self.current);
        self.current = 0;
        self.atom = false;
    }

    fn finish(&mut self, control: &SourceControl<'_>) -> Option<()> {
        self.end_token();
        control.poll()?;
        (self.depth == 0 && !self.string && !self.escaped && self.tokens != 0).then_some(())
    }
}

struct Reader<'a, 'c> {
    bytes: &'a [u8],
    offset: usize,
    window: usize,
    failed: bool,
    control: &'a SourceControl<'c>,
}

impl Read for Reader<'_, '_> {
    fn read(&mut self, output: &mut [u8]) -> io::Result<usize> {
        if self.failed {
            return Err(refused());
        }
        if self.offset == self.bytes.len() || output.is_empty() {
            if self.control.poll().is_none() {
                self.failed = true;
                return Err(refused());
            }
            return Ok(0);
        }
        if self.window == 0 {
            if self.control.charge(1).is_none() {
                self.failed = true;
                return Err(refused());
            }
            self.window = CHUNK;
        }
        let count = output
            .len()
            .min(self.window)
            .min(self.bytes.len() - self.offset);
        output[..count].copy_from_slice(&self.bytes[self.offset..self.offset + count]);
        self.offset += count;
        self.window -= count;
        Ok(count)
    }
}

struct Writer<'a, 'c> {
    bytes: Vec<u8>,
    surface: Surface,
    failed: bool,
    control: &'a SourceControl<'c>,
}

impl Writer<'_, '_> {
    fn append(&mut self, input: &[u8]) -> Option<()> {
        self.surface.feed(input, self.control)?;
        let end = self.bytes.len().checked_add(input.len())?;
        if end > self.bytes.capacity() {
            let mut capacity = self.bytes.capacity().max(CHUNK);
            while capacity < end {
                capacity = capacity.checked_mul(2)?.min(MAX_BYTES);
            }
            // Debit each allocation and its complete old-buffer copy before
            // reserving. Geometric growth bounds their cumulative allowance.
            self.control
                .bytes(capacity.checked_add(self.bytes.len())?)?;
            self.bytes
                .try_reserve_exact(capacity.checked_sub(self.bytes.len())?)
                .ok()?;
        }
        for chunk in input.chunks(CHUNK) {
            self.control.poll()?;
            self.bytes.extend_from_slice(chunk);
        }
        self.control.poll()
    }
}

impl Write for Writer<'_, '_> {
    fn write(&mut self, input: &[u8]) -> io::Result<usize> {
        if self.failed || self.append(input).is_none() {
            self.failed = true;
            return Err(refused());
        }
        Ok(input.len())
    }

    fn flush(&mut self) -> io::Result<()> {
        if self.failed || self.control.poll().is_none() {
            self.failed = true;
            return Err(refused());
        }
        Ok(())
    }
}

fn refused() -> io::Error {
    // Interrupted errors may be retried by Read/Write helpers indefinitely.
    // The kind-only form needs no new owned diagnostic after budget refusal.
    io::Error::from(io::ErrorKind::Other)
}

#[cfg(test)]
mod tests;
