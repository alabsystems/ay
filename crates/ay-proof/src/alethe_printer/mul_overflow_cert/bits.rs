// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Fixed-width bit-vector constants (least significant bit first).

pub(crate) fn zero(w: u32) -> Vec<bool> {
    vec![false; w as usize]
}

pub(crate) fn pow2(k: u32, w: u32) -> Vec<bool> {
    let mut v = zero(w);
    if let Some(b) = v.get_mut(k as usize) {
        *b = true;
    }
    v
}

pub(crate) fn from_u64(x: u64, w: u32) -> Vec<bool> {
    (0..w).map(|i| i < 64 && (x >> i) & 1 == 1).collect()
}

pub(crate) fn add(a: &[bool], b: &[bool]) -> Vec<bool> {
    let mut carry = false;
    a.iter()
        .zip(b)
        .map(|(&x, &y)| {
            let s = x ^ y ^ carry;
            carry = (x && y) || (carry && (x ^ y));
            s
        })
        .collect()
}

/// Two's complement negation modulo `2^w`.
pub(crate) fn neg(a: &[bool]) -> Vec<bool> {
    let inverted: Vec<bool> = a.iter().map(|&b| !b).collect();
    add(&inverted, &from_u64(1, a.len() as u32))
}

/// `2^k - 1` at width `w`.
pub(crate) fn mask(k: u32, w: u32) -> Vec<bool> {
    (0..w).map(|i| i < k).collect()
}

pub(crate) fn render(bits: &[bool]) -> String {
    let w = bits.len();
    if w > 0 && w % 4 == 0 {
        let mut s = String::from("#x");
        for nib in (0..w / 4).rev() {
            let v = (0..4).fold(0u32, |acc, j| acc | (u32::from(bits[nib * 4 + j]) << j));
            s.push(char::from_digit(v, 16).unwrap_or('0'));
        }
        return s;
    }
    let mut s = String::from("#b");
    for &b in bits.iter().rev() {
        s.push(if b { '1' } else { '0' });
    }
    s
}
