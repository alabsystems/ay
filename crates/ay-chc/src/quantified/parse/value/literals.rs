// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Exact wide literals, without the modulo normalization of the general
//! literal constructor. The existing parser ledger admits source scans,
//! numeric conversion, chunks and output before their allocations. Decimal
//! conversion remains one bounded opaque BigUint call, not a latency promise.

use super::*;
use num_bigint::BigUint;

#[derive(Clone, Copy)]
enum Radix {
    Binary,
    Hexadecimal,
    Decimal,
}

impl Radix {
    fn base(self) -> u32 {
        match self {
            Self::Binary => 2,
            Self::Hexadecimal => 16,
            Self::Decimal => 10,
        }
    }

    fn valid(self, byte: u8) -> bool {
        match self {
            Self::Binary => matches!(byte, b'0' | b'1'),
            Self::Hexadecimal => byte.is_ascii_hexdigit(),
            Self::Decimal => byte.is_ascii_digit(),
        }
    }
}

pub(super) fn literal(expr: &SExpr, budget: &mut Budget) -> ChcResult<Option<Arc<ChcExpr>>> {
    budget.charge(0, 0)?;
    let (digits, width, radix) = match expr {
        SExpr::True => return Ok(Some(Arc::new(ChcExpr::Bool(true)))),
        SExpr::False => return Ok(Some(Arc::new(ChcExpr::Bool(false)))),
        SExpr::Binary(text) => radix_parts(text, "#b", Radix::Binary, 1)?,
        SExpr::Hexadecimal(text) => radix_parts(text, "#x", Radix::Hexadecimal, 4)?,
        SExpr::List(items) => {
            let Some((digits, width)) = decimal_parts(items)? else {
                return Ok(None);
            };
            (digits, width, Radix::Decimal)
        }
        _ => return Ok(None),
    };
    // Two borrowed scans: digit authentication and removal of leading zeroes.
    let scans = digits
        .len()
        .checked_mul(2)
        .ok_or_else(|| invalid("literal scan limit"))?;
    budget.charge(scans, 0)?;
    if digits.is_empty() || !digits.bytes().all(|byte| radix.valid(byte)) {
        return Err(invalid("invalid unsigned bitvector literal"));
    }
    let significant = digits.trim_start_matches('0');
    let chunks = admit(width, significant.len(), radix, budget)?;
    // Passing the significant suffix avoids repeated conversion of zeroes.
    // The all-zero case still emits the complete declared width below.
    let value = if significant.is_empty() {
        BigUint::default()
    } else {
        BigUint::parse_bytes(significant.as_bytes(), radix.base())
            .ok_or_else(|| invalid("invalid unsigned bitvector literal"))?
    };
    if value.bits() > u64::from(width) {
        return Err(invalid("bitvector literal does not fit its declared width"));
    }
    let expression = chunks_expression(&value, width, chunks)?;
    drop(value);
    // Retain ordinary <=128-bit literals as one unchanged compact leaf.
    Ok(Some(expression))
}

fn radix_parts<'a>(
    text: &'a str,
    prefix: &str,
    radix: Radix,
    bits: usize,
) -> ChcResult<(&'a str, u32, Radix)> {
    let digits = text
        .strip_prefix(prefix)
        .ok_or_else(|| invalid("malformed bitvector literal prefix"))?;
    let width = digits
        .len()
        .checked_mul(bits)
        .and_then(|width| u32::try_from(width).ok())
        .filter(|width| (1..=crate::MAX_BITVECTOR_WIDTH).contains(width))
        .ok_or_else(|| invalid("bitvector literal width exceeds the supported range"))?;
    Ok((digits, width, radix))
}

fn decimal_parts(items: &[SExpr]) -> ChcResult<Option<(&str, u32)>> {
    let Some(marker) = items.first() else {
        return Ok(None);
    };
    let digits = items
        .get(1)
        .and_then(SExpr::as_symbol)
        .and_then(|name| name.strip_prefix("bv"));
    let Some(digits) = digits.filter(|_| marker.is_symbol("_")) else {
        return Ok(None);
    };
    let [_, _, size] = items else {
        return Err(invalid("bitvector literal requires a value and width"));
    };
    Ok(Some((digits, super::width(size)?)))
}

fn admit(width: u32, digits: usize, radix: Radix, budget: &mut Budget) -> ChcResult<usize> {
    let width = usize::try_from(width).map_err(|_| invalid("literal width limit"))?;
    // Since 10^d > 2^(3d), more than floor(width/3)+1 significant
    // decimal digits cannot fit. Refuse before asking BigUint to parse them.
    if matches!(radix, Radix::Decimal) && digits > width / 3 + 1 {
        return Err(invalid("bitvector literal does not fit its declared width"));
    }
    let bits = digits
        .checked_mul(match radix {
            Radix::Binary => 1,
            Radix::Hexadecimal | Radix::Decimal => 4,
        })
        .ok_or_else(|| invalid("literal numeric limit"))?;
    let limbs = bits.div_ceil(32);
    // Conservative schoolbook upper envelope: one multiply/add over all
    // possible 32-bit limbs for every base-10^9 group (with spare passes).
    // Power-of-two conversion is linear. This is cumulative parse work.
    let conversion = match radix {
        Radix::Decimal => digits.div_ceil(9).checked_mul(limbs),
        _ => Some(limbs),
    }
    .and_then(|work| work.checked_mul(4))
    .ok_or_else(|| invalid("literal conversion limit"))?;
    let chunks = width.div_ceil(128);
    let nodes = chunks
        .checked_mul(2)
        .and_then(|nodes| nodes.checked_sub(1))
        .ok_or_else(|| invalid("literal tree size limit"))?;
    // Per-node allowance includes Arc/header/edge storage, the shrinking
    // level vectors, and canonical decimal leaves/concat output. Numeric
    // scratch is separate; no growing shifts or modulo masks are built.
    let bytes = nodes
        .checked_mul(256)
        .and_then(|bytes| bytes.checked_add(limbs.checked_mul(32)?))
        .and_then(|bytes| bytes.checked_add(digits.checked_mul(4)?))
        .ok_or_else(|| invalid("literal copy limit"))?;
    budget.charge(
        conversion
            .checked_add(nodes)
            .ok_or_else(|| invalid("literal work limit"))?,
        bytes,
    )?;
    Ok(chunks)
}

fn chunks_expression(value: &BigUint, width: u32, chunks: usize) -> ChcResult<Arc<ChcExpr>> {
    let mut words = value.iter_u32_digits();
    let mut level = Vec::new();
    level
        .try_reserve_exact(chunks)
        .map_err(|_| invalid("literal chunk allocation"))?;
    let mut remaining = width;
    while remaining > 0 {
        let size = remaining.min(128);
        let mut chunk = 0_u128;
        for shift in (0..size).step_by(32) {
            chunk |= u128::from(words.next().unwrap_or(0)) << shift;
        }
        level.push(Arc::new(ChcExpr::BitVec(chunk, size)));
        remaining -= size;
    }
    level.reverse();
    // Adjacent MSB-first pairs form balanced concat layers. Each layer has at
    // most ceil(previous/2) nodes, so even the maximum width adds only 13
    // concat levels; the existing source depth admission remains meaningful.
    while level.len() > 1 {
        let mut next = Vec::new();
        next.try_reserve_exact(level.len().div_ceil(2))
            .map_err(|_| invalid("literal tree allocation"))?;
        let mut children = level.into_iter();
        while let Some(high) = children.next() {
            next.push(match children.next() {
                Some(low) => Arc::new(ChcExpr::Op(ChcOp::BvConcat, vec![high, low])),
                None => high,
            });
        }
        level = next;
    }
    level
        .pop()
        .ok_or_else(|| invalid("empty bitvector literal"))
}

#[cfg(test)]
mod tests;
