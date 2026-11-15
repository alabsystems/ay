// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! FIPS180-4 §5.1.1 padding; no byte-length truncation or wrapping.

use super::{block, constants::INITIAL, Control, QueryError};

pub(super) fn bit_length<C: Control>(length: usize, control: &mut C) -> Result<u64, QueryError> {
    control.offer(32, 0)?;
    let bytes = u64::try_from(length).map_err(|_| control.exhausted())?;
    bytes.checked_mul(8).ok_or_else(|| control.exhausted())
}

pub(super) fn run<C: Control>(input: &[u8], control: &mut C) -> Result<[u8; 32], QueryError> {
    control.offer(16, 0)?;
    let bits = bit_length(input.len(), control)?;
    control.offer(144, 32)?;
    let mut state = INITIAL;
    let mut offset = 0;
    loop {
        control.offer(16, 0)?;
        if input.len() - offset < 64 {
            break;
        }
        control.offer(144, 64)?;
        let mut chunk = [0u8; 64];
        for index in 0..64 {
            control.offer(24, 0)?;
            chunk[index] = input[offset + index];
        }
        block::compress(&mut state, &chunk, control)?;
        // The admitted loop header includes this bounded index update.
        offset += 64;
    }
    control.offer(144, 64)?;
    let mut tail = [0u8; 64];
    let remaining = input.len() - offset;
    for index in 0..remaining {
        control.offer(24, 0)?;
        tail[index] = input[offset + index];
    }
    control.offer(16, 0)?;
    tail[remaining] = 0x80;
    control.offer(16, 0)?;
    if remaining >= 56 {
        block::compress(&mut state, &tail, control)?;
        control.offer(144, 64)?;
        tail = [0u8; 64];
    }
    for index in 0..8 {
        control.offer(64, 0)?;
        tail[56 + index] = (bits >> (8 * (7 - index))) as u8;
    }
    block::compress(&mut state, &tail, control)?;
    control.offer(144, 32)?;
    let mut digest = [0u8; 32];
    for index in 0..32 {
        control.offer(64, 0)?;
        digest[index] = (state[index / 4] >> (8 * (3 - index % 4))) as u8;
    }
    control.offer(0, 0)?;
    Ok(digest)
}
