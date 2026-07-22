// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Candidate value generation and array minimization for counterexample shrinking.
//!
//! Extracted from `mod.rs` for code health (#5970). Contains the pure
//! functions that generate candidate replacement values for LIA, LRA, and BV
//! variables, plus the structural array interpretation minimizer.

use ay_arrays::ArrayInterpretation;
use ay_core::Sort;
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Signed, Zero};

/// Maximum number of candidate attempts per variable to bound minimization cost.
pub(super) const MAX_CANDIDATES_PER_VAR: usize = 12;

/// Parse the numeric SMT atoms emitted in array interpretations.
///
/// This intentionally accepts only exact, side-effect-free numeral syntax.  A
/// parse miss is not evidence of disequality: callers retain the store and
/// therefore fail closed.
fn parse_real_index_atom(raw: &str) -> Option<BigRational> {
    let raw = raw.trim();
    if let Ok(value) = raw.parse::<BigInt>() {
        return Some(BigRational::from(value));
    }
    if let Some(inner) = raw.strip_prefix("(- ").and_then(|s| s.strip_suffix(')')) {
        return parse_real_index_atom(inner).map(std::ops::Neg::neg);
    }
    if let Some(inner) = raw.strip_prefix("(/ ").and_then(|s| s.strip_suffix(')')) {
        let (numerator, denominator) = split_smt_pair(inner)?;
        let numerator = parse_real_index_atom(numerator)?;
        let denominator = parse_real_index_atom(denominator)?;
        if denominator.is_zero() {
            return None;
        }
        return Some(numerator / denominator);
    }

    let (negative, unsigned) = if let Some(rest) = raw.strip_prefix('-') {
        (true, rest)
    } else {
        (false, raw)
    };
    let (whole, fractional) = unsigned.split_once('.')?;
    if whole.is_empty()
        || fractional.is_empty()
        || !whole.bytes().all(|b| b.is_ascii_digit())
        || !fractional.bytes().all(|b| b.is_ascii_digit())
    {
        return None;
    }
    let scale = BigInt::from(10u8).pow(fractional.len() as u32);
    let mut numerator =
        whole.parse::<BigInt>().ok()? * &scale + fractional.parse::<BigInt>().ok()?;
    if negative {
        numerator = -numerator;
    }
    Some(BigRational::new(numerator, scale))
}

fn split_smt_pair(raw: &str) -> Option<(&str, &str)> {
    let mut depth = 0u32;
    for (offset, ch) in raw.char_indices() {
        match ch {
            '(' => depth = depth.checked_add(1)?,
            ')' => depth = depth.checked_sub(1)?,
            ' ' if depth == 0 => {
                let left = raw[..offset].trim();
                let right = raw[offset + 1..].trim();
                if !left.is_empty() && !right.is_empty() {
                    return Some((left, right));
                }
            }
            _ => {}
        }
    }
    None
}

fn parse_bv_index_atom(raw: &str, width: u32) -> Option<BigInt> {
    if width == 0 {
        return None;
    }
    let raw = raw.trim();
    let value = if let Some(hex) = raw.strip_prefix("#x") {
        if hex.len().checked_mul(4)? != width as usize {
            return None;
        }
        BigInt::parse_bytes(hex.as_bytes(), 16)?
    } else if let Some(bits) = raw.strip_prefix("#b") {
        if bits.len() != width as usize {
            return None;
        }
        BigInt::parse_bytes(bits.as_bytes(), 2)?
    } else if let Some(inner) = raw
        .strip_prefix("(_ bv")
        .and_then(|rest| rest.strip_suffix(')'))
    {
        let mut parts = inner.split_whitespace();
        let value = parts.next()?.parse::<BigInt>().ok()?;
        let literal_width = parts.next()?.parse::<u32>().ok()?;
        if parts.next().is_some() || literal_width != width {
            return None;
        }
        value
    } else {
        // Some theory extractors store the already-typed BV payload in decimal.
        raw.parse::<BigInt>().ok()?
    };
    let modulus = BigInt::one() << width;
    Some(((value % &modulus) + &modulus) % modulus)
}

/// Compare two serialized array indices using their declared sort.
///
/// `None` means the strings may still alias semantically.  The minimizer must
/// keep the relevant default-valued store in that case; only `Some(false)` is
/// sufficient evidence that a non-default store is at another point.
fn semantic_index_equal(left: &str, right: &str, sort: Option<&Sort>) -> Option<bool> {
    if left.trim() == right.trim() {
        return Some(true);
    }
    match sort {
        Some(Sort::Bool) => {
            let parse = |raw: &str| match raw.trim() {
                "true" => Some(true),
                "false" => Some(false),
                _ => None,
            };
            Some(parse(left)? == parse(right)?)
        }
        Some(Sort::Int | Sort::Char | Sort::FiniteDomain(_, _)) => {
            let left = parse_real_index_atom(left)?;
            let right = parse_real_index_atom(right)?;
            if !left.is_integer() || !right.is_integer() {
                return None;
            }
            Some(left == right)
        }
        Some(Sort::Real) => Some(parse_real_index_atom(left)? == parse_real_index_atom(right)?),
        Some(Sort::BitVec(bv)) => {
            Some(parse_bv_index_atom(left, bv.width)? == parse_bv_index_atom(right, bv.width)?)
        }
        // Without sort metadata, even numeral-looking strings might be names
        // in a symbolic carrier.  Differently formatted atoms therefore remain
        // conservatively possibly equal.
        None => None,
        Some(_) => None,
    }
}

/// Minimize an array interpretation without changing its denotation.
///
/// The default is part of the array's value at every index not named by a
/// store. It therefore cannot be invented or changed merely because one store
/// value is frequent: doing so changes every unlisted cell (an infinite set for
/// the usual Int/Real/uninterpreted index sorts). The only exact structural
/// reduction available here is removing a store whose value already equals the
/// existing default. Duplicate indices need care: stores are authoritative
/// first, so deleting one entry can expose a shadowed value. A default-valued
/// index is removed only when *all* of its entries equal the default.
///
/// FAIL-CLOSED (#select-read-conflict-fail-closed): a `read_conflicted`
/// interpretation — one whose extraction DROPPED a cell because two committed
/// reads of it disagreed — is left untouched. It is deliberately PARTIAL at
/// the dropped cell, and even otherwise exact reshaping is skipped so the
/// conflict marker's partial witness remains intact for validators and the
/// independent model-check gate.
pub(super) fn minimize_array_interpretation(
    interp: &mut ArrayInterpretation,
    read_conflicted: bool,
) {
    if interp.stores.is_empty() || read_conflicted {
        return;
    }

    let Some(default) = interp.default.clone() else {
        // A partial interpretation has no authoritative value for unlisted
        // indices. Promoting a store value would be model completion, not
        // minimization, and is intentionally left to validated model builders.
        return;
    };
    // A store chain may contain the same concrete index more than once. Keep
    // every entry for a key carrying any non-default value: removing a
    // default-valued authoritative entry could otherwise expose the shadowed
    // non-default entry (and removing a shadowed entry would rely on ordering
    // assumptions this local cleanup need not make). If every occurrence is
    // the default, the whole key is redundant under either orientation.
    let nondefault_indices: Vec<String> = interp
        .stores
        .iter()
        .filter(|(_, value)| value != &default)
        .map(|(index, _)| index.clone())
        .collect();
    let index_sort = interp.index_sort.as_ref();
    interp.stores.retain(|(index, value)| {
        value != &default
            || nondefault_indices.iter().any(|nondefault_index| {
                !matches!(
                    semantic_index_equal(index, nondefault_index, index_sort),
                    Some(false)
                )
            })
    });
}

/// Generate candidate integer values in preference order: 0, 1, -1, 2, -2, ...
/// For large values (|v| > 4), also includes sign-preserving powers of 10
/// to help find boundary conditions (e.g., x >= 100 with original=847293847
/// would try 0, 1, -1, 2, -2, 3, -3, 4, -4, 10, 100, 1000, ...).
pub(super) fn int_candidates(original: &BigInt) -> Vec<BigInt> {
    if original.is_zero() {
        return vec![BigInt::zero()];
    }

    let mut candidates = Vec::with_capacity(MAX_CANDIDATES_PER_VAR);
    candidates.push(BigInt::zero());
    candidates.push(BigInt::one());
    candidates.push(-BigInt::one());

    for i in 2i64..=4 {
        if candidates.len() >= MAX_CANDIDATES_PER_VAR {
            break;
        }
        candidates.push(BigInt::from(i));
        if candidates.len() < MAX_CANDIDATES_PER_VAR {
            candidates.push(BigInt::from(-i));
        }
    }

    // For large values, add sign-preserving powers of 10 as candidates.
    // This helps find boundary conditions like x >= 100.
    let orig_mag = original.magnitude().clone();
    if orig_mag > num_bigint::BigUint::from(4u32) {
        let sign = if original.is_positive() { 1i64 } else { -1i64 };
        let mut power = BigInt::from(10i64);
        while candidates.len() < MAX_CANDIDATES_PER_VAR {
            let candidate = &power * sign;
            if candidate.magnitude() >= &orig_mag {
                break;
            }
            if !candidates.contains(&candidate) {
                candidates.push(candidate);
            }
            power *= 10i64;
        }
    }

    candidates.retain(|c| c.magnitude() <= &orig_mag);

    candidates
}

/// Generate candidate rational values in preference order.
pub(super) fn rational_candidates(original: &BigRational) -> Vec<BigRational> {
    if original.is_zero() {
        return vec![BigRational::zero()];
    }

    let mut candidates = Vec::with_capacity(MAX_CANDIDATES_PER_VAR);
    candidates.push(BigRational::zero());
    candidates.push(BigRational::one());
    candidates.push(-BigRational::one());

    let half = BigRational::new(BigInt::one(), BigInt::from(2));
    candidates.push(half.clone());
    candidates.push(-half);

    for i in 2i64..=3 {
        if candidates.len() >= MAX_CANDIDATES_PER_VAR {
            break;
        }
        candidates.push(BigRational::from(BigInt::from(i)));
        if candidates.len() < MAX_CANDIDATES_PER_VAR {
            candidates.push(BigRational::from(BigInt::from(-i)));
        }
    }

    let orig_abs = original.abs();
    candidates.retain(|c| c.abs() <= orig_abs);

    candidates
}

/// Generate candidate bitvector values: 0, 1, MAX, MIN_SIGNED, powers of 2.
pub(super) fn bv_candidates(original: &BigInt, width: u32) -> Vec<BigInt> {
    if original.is_zero() {
        return vec![BigInt::zero()];
    }

    let max_unsigned: BigInt = (BigInt::one() << width) - 1;
    let min_signed: BigInt = BigInt::one() << (width - 1);

    let mut candidates = Vec::with_capacity(MAX_CANDIDATES_PER_VAR);
    candidates.push(BigInt::zero());
    candidates.push(BigInt::one());
    candidates.push(max_unsigned.clone());
    candidates.push(min_signed);

    for pow in 1..width.min(8) {
        if candidates.len() >= MAX_CANDIDATES_PER_VAR {
            break;
        }
        let val = BigInt::one() << pow;
        if val <= max_unsigned && !candidates.contains(&val) {
            candidates.push(val);
        }
    }

    candidates.retain(|c| *c >= BigInt::zero() && *c <= max_unsigned);

    candidates
}
