// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Rows, source sets and exact row arithmetic for [`super`].

use std::collections::BTreeMap;

use num_bigint::BigInt;
use num_integer::Integer;
use num_traits::{One, Signed, Zero};

/// A set of input-row indices, as a bitset.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct SourceSet {
    words: Vec<u64>,
}

impl SourceSet {
    /// The set `{index}`.
    pub(crate) fn single(index: usize) -> Self {
        let mut words = vec![0u64; index / 64 + 1];
        words[index / 64] |= 1u64 << (index % 64);
        Self { words }
    }

    /// `self ∪= other`.
    pub(crate) fn union_with(&mut self, other: &Self) {
        if self.words.len() < other.words.len() {
            self.words.resize(other.words.len(), 0);
        }
        for (dst, src) in self.words.iter_mut().zip(&other.words) {
            *dst |= *src;
        }
    }

    /// Number of members.
    pub(crate) fn len(&self) -> usize {
        self.words.iter().map(|w| w.count_ones() as usize).sum()
    }

    /// Members in increasing order.
    pub(crate) fn iter(&self) -> impl Iterator<Item = usize> + '_ {
        self.words.iter().enumerate().flat_map(|(wi, &w)| {
            (0..64)
                .filter(move |bit| w & (1u64 << bit) != 0)
                .map(move |bit| wi * 64 + bit)
        })
    }

    pub(super) fn joined(&self, other: &Self) -> Self {
        let mut out = self.clone();
        out.union_with(other);
        out
    }
}

/// `Σ coeffs·x  (= | <=)  constant` over integer variables `x`, with the input
/// rows it was derived from. `coeffs` is sorted by variable and has no zeros.
#[derive(Clone, Debug)]
pub(crate) struct IntRow {
    pub(crate) coeffs: Vec<(usize, BigInt)>,
    pub(crate) constant: BigInt,
    pub(crate) sources: SourceSet,
}

impl IntRow {
    /// Build a row, merging repeated variables and dropping zero coefficients.
    pub(crate) fn new(coeffs: Vec<(usize, BigInt)>, constant: BigInt, sources: SourceSet) -> Self {
        let mut merged: BTreeMap<usize, BigInt> = BTreeMap::new();
        for (var, c) in coeffs {
            *merged.entry(var).or_insert_with(BigInt::zero) += c;
        }
        let coeffs = merged.into_iter().filter(|(_, c)| !c.is_zero()).collect();
        Self {
            coeffs,
            constant,
            sources,
        }
    }

    pub(super) fn coeff_of(&self, var: usize) -> Option<&BigInt> {
        self.coeffs
            .binary_search_by_key(&var, |(v, _)| *v)
            .ok()
            .map(|i| &self.coeffs[i].1)
    }

    pub(super) fn gcd(&self) -> BigInt {
        self.coeffs
            .iter()
            .fold(BigInt::zero(), |g, (_, c)| g.gcd(c))
    }
}

/// `a·r1 + b·r2` over sparse sorted coefficient vectors.
pub(super) fn lin_comb(
    a: &BigInt,
    r1: &[(usize, BigInt)],
    b: &BigInt,
    r2: &[(usize, BigInt)],
) -> Vec<(usize, BigInt)> {
    let mut out = Vec::with_capacity(r1.len() + r2.len());
    let (mut i, mut j) = (0, 0);
    loop {
        let (var, c) = match (r1.get(i), r2.get(j)) {
            (None, None) => return out,
            (Some((v1, c1)), Some((v2, c2))) if v1 == v2 => {
                i += 1;
                j += 1;
                (*v1, a * c1 + b * c2)
            }
            (Some((v1, c1)), Some((v2, _))) if v1 < v2 => {
                i += 1;
                (*v1, a * c1)
            }
            (Some((v1, c1)), None) => {
                i += 1;
                (*v1, a * c1)
            }
            (_, Some((v2, c2))) => {
                j += 1;
                (*v2, b * c2)
            }
        };
        if !c.is_zero() {
            out.push((var, c));
        }
    }
}

/// Nearest-integer quotient `round(c / m)`, so `|c - q·m| <= |m| / 2`.
pub(super) fn round_div(c: &BigInt, m: &BigInt) -> BigInt {
    let am = m.abs();
    let n = if m.is_negative() { -c } else { c.clone() };
    let (q, r) = n.div_mod_floor(&am);
    if &r + &r > am {
        q + BigInt::one()
    } else {
        q
    }
}

/// Whether any number in `row` exceeds `max_bits` bits.
pub(super) fn too_big(row: &IntRow, max_bits: u64) -> bool {
    row.constant.bits() > max_bits || row.coeffs.iter().any(|(_, c)| c.bits() > max_bits)
}
