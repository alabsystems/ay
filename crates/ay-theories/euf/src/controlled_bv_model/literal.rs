// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

pub(super) fn magnitude(
    value: &num_bigint::BigInt,
    width: u32,
    work: &mut WorkBudget<'_>,
) -> Result<u128, QueryError> {
    // Source sign/header/last-limb checks and <=two u64 digit reads. No heap
    // clone/radix conversion and no iteration over arbitrary spare capacity.
    work.admit(256, 256)?;
    if !(1..=128).contains(&width)
        || value.sign() == num_bigint::Sign::Minus
        || value.bits() > u64::from(width)
    {
        return Err(work.refuse_exhaustion());
    }
    let mut digits = value.iter_u64_digits();
    let low = u128::from(digits.next().unwrap_or(0));
    let high = u128::from(digits.next().unwrap_or(0));
    if digits.next().is_some() {
        return Err(work.refuse_exhaustion());
    }
    Ok(low | (high << 64))
}

pub(super) fn bitvector(
    value: u128,
    width: u32,
    work: &mut WorkBudget<'_>,
) -> Result<String, QueryError> {
    work.admit(160, 4 * 130)?;
    let mut buffer = [0u8; 130];
    buffer[0] = b'#';
    let (digits, shift) = if width.is_multiple_of(4) {
        buffer[1] = b'x';
        (width as usize / 4, 4usize)
    } else {
        buffer[1] = b'b';
        (width as usize, 1usize)
    };
    const HEX: &[u8; 16] = b"0123456789abcdef";
    for index in 0..digits {
        work.charge(16)?;
        let offset = (digits - index - 1) * shift;
        let digit = ((value >> offset) & ((1u128 << shift) - 1)) as usize;
        buffer[index + 2] = HEX[digit];
    }
    work.charge(32 * (digits + 2) + 64)?;
    let text = std::str::from_utf8(&buffer[..digits + 2]).map_err(|_| work.refuse_exhaustion())?;
    owned::text(text, work)
}

pub(super) fn placeholder(term: TermId, work: &mut WorkBudget<'_>) -> Result<String, QueryError> {
    work.admit(64, 4 * 12)?;
    let mut buffer = [0u8; 12];
    let mut value = term.0;
    let mut start = buffer.len();
    loop {
        work.charge(16)?;
        start -= 1;
        buffer[start] = b'0' + (value % 10) as u8;
        value /= 10;
        if value == 0 {
            break;
        }
    }
    work.charge(4)?;
    start -= 2;
    buffer[start] = b'@';
    buffer[start + 1] = b'?';
    work.charge(32 * (buffer.len() - start) + 64)?;
    let text = std::str::from_utf8(&buffer[start..]).map_err(|_| work.refuse_exhaustion())?;
    owned::text(text, work)
}
