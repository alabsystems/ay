// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Borrowed exact numeric kernels. Explicit base-2^32 buffers make original
//! admission cover the actual scratch rather than hidden host-bigint algorithms.
use super::*;
use num_bigint::{BigInt, Sign};

fn cells(bits: u64, owner: &dyn TermConstructionAdmission) -> Result<usize> {
    usize::try_from(bits.div_ceil(32).max(1)).map_err(|_| storage::work(owner))
}
fn result_buffer(
    size: usize,
    work: usize,
    owner: &dyn TermConstructionAdmission,
) -> Result<Vec<u32>> {
    owner.admit(
        work,
        size.checked_mul(8).ok_or_else(|| storage::storage(owner))?,
    )?;
    let mut digits = Vec::new();
    storage::reserve(&mut digits, size, owner)?;
    digits.resize(size, 0);
    Ok(digits)
}

/// Knuth, TAOCP 4.3.1 Algorithm M, unchanged from integer_product.
pub(super) fn multiply(
    a: &BigInt,
    b: &BigInt,
    owner: &dyn TermConstructionAdmission,
) -> Result<BigInt> {
    payload::bigint(a, owner, PayloadUse::Inspect)?;
    payload::bigint(b, owner, PayloadUse::Inspect)?;
    let bits = a
        .bits()
        .checked_add(b.bits())
        .ok_or_else(|| storage::work(owner))?;
    let work = cells(a.bits(), owner)?
        .checked_mul(cells(b.bits(), owner)?)
        .ok_or_else(|| storage::work(owner))?;
    let size = usize::try_from(bits.div_ceil(32))
        .ok()
        .and_then(|n| n.checked_add(2))
        .ok_or_else(|| storage::storage(owner))?;
    let mut digits = result_buffer(
        size,
        work.checked_add(size).ok_or_else(|| storage::work(owner))?,
        owner,
    )?;
    for (i, x) in a.iter_u32_digits().enumerate() {
        owner.check()?;
        let mut carry = 0u64;
        let mut end = i;
        for (j, y) in b.iter_u32_digits().enumerate() {
            let k = i + j;
            // (2^32-1)^2 + (2^32-1) + (2^32-1) fits u64.
            let sum = u64::from(x) * u64::from(y) + u64::from(digits[k]) + carry;
            digits[k] = sum as u32;
            carry = sum >> 32;
            end = k + 1;
        }
        digits[end] = carry as u32;
    }
    let sign = if a.sign() == b.sign() {
        Sign::Plus
    } else {
        Sign::Minus
    };
    let result = BigInt::from_slice(sign, &digits);
    owner.check()?;
    Ok(result)
}

/// Signed magnitude addition/subtraction with borrowed digits and one result
/// buffer. No host add/sub growth or hidden intermediate BigInt clone.
pub(super) fn add(a: &BigInt, b: &BigInt, owner: &dyn TermConstructionAdmission) -> Result<BigInt> {
    payload::bigint(a, owner, PayloadUse::Inspect)?;
    payload::bigint(b, owner, PayloadUse::Inspect)?;
    let count = cells(a.bits().max(b.bits()), owner)?;
    let size = count
        .checked_add(1)
        .ok_or_else(|| storage::storage(owner))?;
    let mut digits = result_buffer(
        size,
        size.checked_mul(2).ok_or_else(|| storage::work(owner))?,
        owner,
    )?;
    let same = a.sign() == b.sign();
    let (left, right, sign) = if same || a.magnitude() >= b.magnitude() {
        (a, b, a.sign())
    } else {
        (b, a, b.sign())
    };
    let mut x = left.iter_u32_digits();
    let mut y = right.iter_u32_digits();
    let mut carry = 0u64;
    for digit in digits.iter_mut().take(count) {
        owner.check()?;
        let a = u64::from(x.next().unwrap_or(0));
        let b = u64::from(y.next().unwrap_or(0));
        if same {
            let sum = a + b + carry;
            *digit = sum as u32;
            carry = sum >> 32;
        } else {
            let difference = a as i64 - b as i64 - carry as i64;
            *digit = difference as u32;
            carry = u64::from(difference < 0);
        }
    }
    if same {
        digits[count] = carry as u32;
    }
    let result = BigInt::from_slice(sign, &digits);
    owner.check()?;
    Ok(result)
}

pub(super) fn copy(value: &BigInt, owner: &dyn TermConstructionAdmission) -> Result<BigInt> {
    payload::bigint(value, owner, PayloadUse::Copy)?;
    let result = value.clone();
    owner.check()?;
    Ok(result)
}
pub(super) fn one(owner: &dyn TermConstructionAdmission) -> Result<BigInt> {
    owner.admit(1, 8)?;
    let result = BigInt::from(1);
    owner.check()?;
    Ok(result)
}
