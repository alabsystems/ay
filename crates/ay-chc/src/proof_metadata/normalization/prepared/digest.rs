// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Portable FIPS180-4 §§5.1.1/6.2.2 SHA-256; no default hash is replaced.
//! https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.180-4.pdf
//! Costs are logical source operations/storage, not CPU, RSS or preemption.

use super::{Borrowed, ChcProblem, Control, QueryError, WorkBudget};
mod block;
mod constants;
mod hash;
#[cfg(test)]
mod tests;

pub(super) fn consume(
    source: &ChcProblem,
    bytes: &str,
    work: &mut WorkBudget<'_>,
    operation: impl FnOnce(&ChcProblem, &str, &str, &mut WorkBudget<'_>) -> Result<(), QueryError>,
) -> Result<(), QueryError> {
    work.charge(64)?;
    let digest = hash::run(bytes.as_bytes(), &mut Borrowed(work))?;
    let hex = hexadecimal(&digest, &mut Borrowed(work))?;
    // This exact generated alphabet is ASCII. The pinned core validator's ASCII
    // paths use <=32 logical operations/byte plus 32 fixed setup/return units.
    work.charge(32 + 32 * 64)?;
    let text = std::str::from_utf8(&hex)
        .map_err(|_| QueryError::Invalid("generated SHA-256 hex is not UTF-8"))?;
    operation(source, bytes, text, work)
    // digest/hex and consumed operation captures leave this frame before the
    // enclosing carrier drops bytes and observes its final original-owner fence.
}

fn hexadecimal<C: Control>(digest: &[u8; 32], control: &mut C) -> Result<[u8; 64], QueryError> {
    control.offer(272, 64)?;
    let mut out = [0u8; 64];
    const DIGITS: &[u8; 16] = b"0123456789abcdef";
    for index in 0..32 {
        // Reads/indexes, two nibble operations, two table reads, two writes,
        // local/index disposal and bounded loop bookkeeping all precede writes.
        control.offer(64, 0)?;
        let byte = digest[index];
        out[2 * index] = DIGITS[(byte >> 4) as usize];
        out[2 * index + 1] = DIGITS[(byte & 15) as usize];
    }
    control.offer(0, 0)?;
    Ok(out)
}
