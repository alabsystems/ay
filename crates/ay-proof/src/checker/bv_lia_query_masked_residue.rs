// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact low-bit residue identity for masked `int2bv` terms.
//!
//! # The identity
//!
//! For every integer `x`, every width `w >= 1` and every `0 <= k <= w`:
//!
//! ```text
//! bv2nat(bvand(int2bv_w(x), M)) = x mod 2^k        where M = 2^k - 1
//! ```
//!
//! `int2bv_w(x)` is the width-`w` bit-vector whose unsigned value is
//! `x mod 2^w` (SMT-LIB; the residue is the non-negative one for negative
//! `x` too). `bvand` with `M`, whose set bits are exactly bits `0..k`, keeps
//! the low `k` bits, so the unsigned value is `(x mod 2^w) mod 2^k`. Because
//! `2^k` divides `2^w`, that is `x mod 2^k` (SMT-LIB `mod` with a positive
//! divisor is the non-negative Euclidean residue, the same one). QED.
//!
//! `bv2int` is accepted as the same UNSIGNED conversion: it is Z3's name for
//! `bv2nat`, AY's elaborator reads it that way (`mk_bv2int(_, false)`), and
//! so does this checker's `ground_evaluate`. The signed conversion is spelled
//! `sbv_to_int` and is never matched.
//!
//! This is the identity `TermStore::mk_bv2nat` applies when it elaborates the
//! authored `(bv2int (bvand ((_ int2bv 8) i) ((_ int2bv 8) 1)))` of Trust's
//! `(i & 1)` to `(mod i 2)`; without it a proof over the elaborated term had no
//! checked link back to the authored one.
//!
//! # What is checked
//!
//! Every quantity is read from the term store and verified, nothing is
//! assumed: the conversion head and arity, the `bvand` arity and its sort
//! `BitVec(w)`, the `int2bv` index `[w]` and its `BitVec(w)` sort, that both
//! sides name the SAME Int term `x` (identical `TermId`), the mask as either a
//! width-`w` bit-vector constant or `int2bv_w` of an Int constant in
//! `[0, 2^w)`, that the mask is exactly `2^k - 1` with `k <= w`, and that the
//! divisor is the Int constant `2^k`. A different mask, modulus, width, a
//! mismatched operand, or a signed reading does not match.

use ay_core::{Constant, Sort, Symbol, TermData, TermId, TermStore};
use num_bigint::BigInt;
use num_traits::{One, Signed, Zero};

/// Largest width read. The identity holds for every width; the cap only keeps
/// the constant arithmetic below proportional to ordinary machine widths.
const MAX_WIDTH: u32 = 1 << 16;

/// Whether `assertion` asserts an instance of the identity FALSE, as
/// `(not (= l r))` or `(= (= l r) false)`: such an assertion is unsatisfiable
/// on its own.
pub(super) fn refutes_identity(terms: &TermStore, assertion: TermId) -> bool {
    let equality = match terms.get(assertion) {
        TermData::Not(inner) => *inner,
        TermData::App(Symbol::Named(name), args)
            if name == "="
                && args.len() == 2
                && terms.sort(args[0]) == &Sort::Bool
                && matches!(terms.get(args[1]), TermData::Const(Constant::Bool(false))) =>
        {
            args[0]
        }
        _ => return false,
    };
    let TermData::App(Symbol::Named(name), args) = terms.get(equality) else {
        return false;
    };
    name == "="
        && args.len() == 2
        && (matches(terms, args[0], args[1]) || matches(terms, args[1], args[0]))
}

fn matches(terms: &TermStore, conversion: TermId, residue: TermId) -> bool {
    let Some((x, modulus)) = residue_parts(terms, residue) else {
        return false;
    };
    let Some((source, mask, width)) = masked_conversion_parts(terms, conversion) else {
        return false;
    };
    if source != x || !modulus.is_positive() {
        return false;
    }
    // `modulus = 2^k` with `k <= width`, and `mask = 2^k - 1`.
    let k = modulus.bits() - 1;
    (&modulus & (&modulus - BigInt::one())).is_zero()
        && k <= u64::from(width)
        && mask == modulus - BigInt::one()
}

/// `(mod x d)` over Int with an Int constant `d`.
fn residue_parts(terms: &TermStore, term: TermId) -> Option<(TermId, BigInt)> {
    let TermData::App(Symbol::Named(name), args) = terms.get(term) else {
        return None;
    };
    if name != "mod"
        || args.len() != 2
        || terms.sort(term) != &Sort::Int
        || terms.sort(args[0]) != &Sort::Int
    {
        return None;
    }
    let TermData::Const(Constant::Int(divisor)) = terms.get(args[1]) else {
        return None;
    };
    Some((args[0], divisor.clone()))
}

/// `(bv2nat|bv2int (bvand ((_ int2bv w) x) mask))`, either operand order:
/// `(x, mask value, w)`.
fn masked_conversion_parts(terms: &TermStore, term: TermId) -> Option<(TermId, BigInt, u32)> {
    let TermData::App(Symbol::Named(name), args) = terms.get(term) else {
        return None;
    };
    if !matches!(name.as_str(), "bv2nat" | "bv2int")
        || args.len() != 1
        || terms.sort(term) != &Sort::Int
    {
        return None;
    }
    let and = args[0];
    let TermData::App(Symbol::Named(and_name), operands) = terms.get(and) else {
        return None;
    };
    let Sort::BitVec(sort) = terms.sort(and) else {
        return None;
    };
    let width = sort.width;
    if and_name != "bvand" || operands.len() != 2 || width == 0 || width > MAX_WIDTH {
        return None;
    }
    for (value, mask) in [(operands[0], operands[1]), (operands[1], operands[0])] {
        let Some(x) = int2bv_source(terms, value, width) else {
            continue;
        };
        if let Some(mask) = mask_value(terms, mask, width) {
            return Some((x, mask, width));
        }
    }
    None
}

/// `((_ int2bv w) s)` with sort `BitVec(w)` and an Int source `s`.
fn int2bv_source(terms: &TermStore, term: TermId, width: u32) -> Option<TermId> {
    let TermData::App(Symbol::Indexed(name, indices), args) = terms.get(term) else {
        return None;
    };
    (name == "int2bv"
        && indices.as_slice() == [width]
        && args.len() == 1
        && bv_width(terms, term) == Some(width)
        && terms.sort(args[0]) == &Sort::Int)
        .then_some(args[0])
}

/// The unsigned value of a width-`w` mask: a bit-vector constant, or
/// `int2bv_w` of an Int constant already in `[0, 2^w)`.
fn mask_value(terms: &TermStore, term: TermId, width: u32) -> Option<BigInt> {
    if bv_width(terms, term) != Some(width) {
        return None;
    }
    let limit = BigInt::one() << width;
    let value = match terms.get(term) {
        TermData::Const(Constant::BitVec { value, width: w }) if *w == width => value.clone(),
        TermData::App(..) => {
            let source = int2bv_source(terms, term, width)?;
            let TermData::Const(Constant::Int(value)) = terms.get(source) else {
                return None;
            };
            value.clone()
        }
        _ => return None,
    };
    (!value.is_negative() && value < limit).then_some(value)
}

fn bv_width(terms: &TermStore, term: TermId) -> Option<u32> {
    match terms.sort(term) {
        Sort::BitVec(sort) => Some(sort.width),
        _ => None,
    }
}

#[cfg(test)]
#[path = "bv_lia_query_masked_residue_tests.rs"]
mod tests;
