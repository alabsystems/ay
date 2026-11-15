// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Closed two/three-proof JSON transport. The caller binds the roles to live
//! source; framing is not proof authority. Each inner object still needs the
//! ordinary bounded wire decoder and source-bound replay.

use super::*;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum FrameSet {
    Outside,
    Disjoint,
    Combined,
}

impl FrameSet {
    fn roles(self) -> &'static [&'static [u8]] {
        match self {
            Self::Outside => &[b"outside_free_offset", b"final_clause"],
            Self::Disjoint => &[b"disjoint_free_offset", b"final_clause"],
            Self::Combined => &[
                b"disjoint_free_offset",
                b"outside_free_offset",
                b"final_clause",
            ],
        }
    }

    pub(crate) fn frame_count(self) -> usize {
        self.roles().len()
    }

    pub(crate) fn overhead(self) -> usize {
        // Two array delimiters, five object/key delimiters per frame and
        // count-1 commas. The closed static role list has at most three entries.
        1 + self
            .roles()
            .iter()
            .map(|role| role.len() + 6)
            .sum::<usize>()
    }
}

#[cfg(test)]
pub(crate) const OVERHEAD: usize = b"outside_free_offset".len() + b"final_clause".len() + 13;

/// The outside-frame pair as a fixed array (tests; production uses the plan).
#[cfg(test)]
pub(crate) fn encode(
    frames: [&[u8]; 2],
    wire: &WireLimits,
    proof: &BvExprProofLimits,
    gates: &BvBlastValidateLimits,
    poll: &mut dyn FnMut() -> bool,
) -> WireOutcome<Vec<u8>> {
    encode_frames(FrameSet::Outside, &frames, wire, proof, gates, poll)
}

pub(crate) fn encode_frames(
    plan: FrameSet,
    frames: &[&[u8]],
    wire: &WireLimits,
    proof: &BvExprProofLimits,
    gates: &BvBlastValidateLimits,
    poll: &mut dyn FnMut() -> bool,
) -> WireOutcome<Vec<u8>> {
    run(wire, proof, gates, poll, |control| {
        if frames.len() != plan.frame_count() {
            return control.fail(WireError::InvalidPayload("frame count"));
        }
        // Frame JSON was already debited by the same chain. Only the fixed
        // role framing is new JSON; copying is distinct additional work.
        control.cap(
            "frame delimiters",
            plan.overhead() as u128,
            control.limits.max_json_bytes as u128,
        )?;
        let mut length = plan.overhead();
        for frame in frames {
            length = control.add(length, frame.len())?;
        }
        control.retain(size_of::<Vec<u8>>())?;
        let mut output = Vec::new();
        control.reserve(&mut output, length)?;
        append(&mut output, b"[", control)?;
        for (index, (&role, &frame)) in plan.roles().iter().zip(frames).enumerate() {
            if index != 0 {
                append(&mut output, b",", control)?;
            }
            for bytes in [b"{\"".as_slice(), role, b"\":", frame, b"}"] {
                append(&mut output, bytes, control)?;
            }
        }
        append(&mut output, b"]", control)?;
        control.usage.returned_owned_bytes = control.storage;
        Ok(output)
    })
}

#[cfg(test)]
pub(crate) fn decode<'a>(
    bytes: &'a [u8],
    wire: &WireLimits,
    proof: &BvExprProofLimits,
    gates: &BvBlastValidateLimits,
    poll: &mut dyn FnMut() -> bool,
) -> WireOutcome<[&'a [u8]; 2]> {
    let outcome = decode_frames(FrameSet::Outside, bytes, wire, proof, gates, poll);
    WireOutcome {
        result: outcome.result.map(|frames| [frames[0], frames[1]]),
        usage: outcome.usage,
    }
}

pub(crate) fn decode_frames<'a>(
    plan: FrameSet,
    bytes: &'a [u8],
    wire: &WireLimits,
    proof: &BvExprProofLimits,
    gates: &BvBlastValidateLimits,
    poll: &mut dyn FnMut() -> bool,
) -> WireOutcome<[&'a [u8]; 3]> {
    run(wire, proof, gates, poll, |control| {
        control.cap(
            "pair JSON bytes",
            bytes.len() as u128,
            control.limits.max_json_bytes as u128,
        )?;
        control.retain(bytes.len())?;
        let mut input = Input {
            bytes,
            offset: 0,
            admitted: 0,
            control,
        };
        let mut frames = [b"".as_slice(); 3];
        input.delimiter(b'[')?;
        for (index, &role) in plan.roles().iter().enumerate() {
            if index != 0 {
                input.delimiter(b',')?;
            }
            input.delimiter(b'{')?;
            input.role(role)?;
            frames[index] = input.object()?;
            input.delimiter(b'}')?;
        }
        input.delimiter(b']')?;
        input.space()?;
        if input.offset != bytes.len() {
            return input.control.fail(WireError::InvalidJson);
        }
        Ok(frames)
    })
}

#[cfg(test)]
mod tests;

fn append(output: &mut Vec<u8>, bytes: &[u8], control: &mut Control<'_>) -> Result<(), WireError> {
    for chunk in bytes.chunks(lexical::WINDOW) {
        control.charge(chunk.len())?;
        output.extend_from_slice(chunk);
    }
    Ok(())
}

struct Input<'d, 'a, 'p> {
    bytes: &'d [u8],
    offset: usize,
    admitted: usize,
    control: &'a mut Control<'p>,
}

impl<'d> Input<'d, '_, '_> {
    fn peek(&mut self) -> Result<Option<u8>, WireError> {
        if self.offset == self.admitted && self.offset < self.bytes.len() {
            let grant = (self.bytes.len() - self.offset).min(lexical::WINDOW);
            self.control.charge(grant)?;
            self.admitted += grant;
        }
        Ok(self.bytes.get(self.offset).copied())
    }

    fn byte(&mut self) -> Result<u8, WireError> {
        let byte = self.peek()?.ok_or(WireError::InvalidJson)?;
        self.offset += 1;
        Ok(byte)
    }

    fn space(&mut self) -> Result<(), WireError> {
        while matches!(self.peek()?, Some(b' ' | b'\r' | b'\n' | b'\t')) {
            self.offset += 1;
        }
        Ok(())
    }

    fn delimiter(&mut self, expected: u8) -> Result<(), WireError> {
        self.space()?;
        if self.byte()? != expected {
            return self.control.fail(WireError::InvalidJson);
        }
        Ok(())
    }

    fn role(&mut self, role: &[u8]) -> Result<(), WireError> {
        self.delimiter(b'"')?;
        // Fixed protocol atoms, not arbitrary strings or escaped aliases.
        for &expected in role {
            if self.byte()? != expected {
                return self.control.fail(WireError::InvalidJson);
            }
        }
        // No whitespace may split a quoted protocol atom.
        if self.byte()? != b'"' {
            return self.control.fail(WireError::InvalidJson);
        }
        self.delimiter(b':')
    }

    fn object(&mut self) -> Result<&'d [u8], WireError> {
        self.space()?;
        let start = self.offset;
        self.delimiter(b'{')?;
        let mut stack = [0_u8; lexical::MAX_DEPTH];
        stack[0] = b'}';
        let mut depth = 1;
        let mut string = false;
        let mut escaped = false;
        while depth != 0 {
            let byte = self.byte()?;
            if string {
                if byte == b'"' && !escaped {
                    string = false;
                }
                escaped = byte == b'\\' && !escaped;
                continue;
            }
            match byte {
                b'"' => string = true,
                b'{' | b'[' => {
                    if depth == stack.len() {
                        return self.control.fail(WireError::InvalidJson);
                    }
                    stack[depth] = if byte == b'{' { b'}' } else { b']' };
                    depth += 1;
                }
                b'}' | b']' => {
                    if stack[depth - 1] != byte {
                        return self.control.fail(WireError::InvalidJson);
                    }
                    depth -= 1;
                }
                _ => {}
            }
        }
        Ok(&self.bytes[start..self.offset])
    }
}
