// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Constants as the rewriter reads and writes them: FloatingPoint numerals,
//! rounding-mode literals, bit-vector constants and ground rationals.

use ay_core::term::{Constant, Symbol, TermData};
use ay_core::{Sort, TermId, TermStore};
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Zero};

use crate::{exact, FpModelValue, RoundingMode};

/// The value of `term` when it is a FloatingPoint numeral: the `fp`
/// constructor or a one-argument `to_fp` over bit-vector constants, or one of
/// the indexed special constants `(_ +zero eb sb)`, `(_ -zero ..)`,
/// `(_ +oo ..)`, `(_ -oo ..)`, `(_ NaN ..)`.
pub fn fp_numeral(terms: &TermStore, term: TermId) -> Option<FpModelValue> {
    let Sort::FloatingPoint(eb, sb) = *terms.sort(term) else {
        return None;
    };
    // Reject unsupported arithmetic formats before reconstructing potentially
    // much wider structural encodings. Both consumers share the strict decoder.
    exact::from_ieee_bits(&BigInt::zero(), eb, sb)?;
    let (bits, _) = ieee_bits(terms, term)?;
    exact::from_ieee_bits(&bits, eb, sb)
}

/// The private closed-arithmetic carrier can exceed the symbolic model's
/// checked field capacity.
pub(super) fn wide_numeral(terms: &TermStore, term: TermId) -> Option<exact::wide::Value> {
    let Sort::FloatingPoint(eb, sb) = *terms.sort(term) else {
        return None;
    };
    if !exact::wide::Value::checked_format(eb, sb) {
        return None;
    }
    let (bits, _) = ieee_bits(terms, term)?;
    exact::wide::from_ieee_bits(&bits, eb, sb)
}

pub(super) fn mk_wide_numeral(terms: &mut TermStore, value: &exact::wide::Value) -> TermId {
    let (bits, width) = value.to_ieee_bv();
    let pattern = terms.mk_bitvec(bits, width);
    terms.mk_app(
        Symbol::indexed("to_fp", vec![value.eb(), value.sb()]),
        vec![pattern],
        Sort::FloatingPoint(value.eb(), value.sb()),
    )
}

/// The canonical numeral the rewriter emits: `((_ to_fp eb sb) #b...)` over
/// the IEEE pattern, the same form the bit-blaster pins as constant bits.
pub fn mk_fp_numeral(terms: &mut TermStore, value: &FpModelValue) -> TermId {
    let (eb, sb) = (value.eb(), value.sb());
    let (bits, width) = value.to_ieee_bv();
    let pattern = terms.mk_bitvec(bits, width);
    terms.mk_app(
        Symbol::indexed("to_fp", vec![eb, sb]),
        vec![pattern],
        Sort::FloatingPoint(eb, sb),
    )
}

/// Whether `sort` is the `RoundingMode` sort.
pub fn is_rounding_mode_sort(sort: &Sort) -> bool {
    matches!(sort, Sort::Uninterpreted(name) if name == "RoundingMode")
}

/// The mode `term` denotes when it is one of the ten rounding-mode literals.
/// Sort-guarded: a constant that merely borrows a mode's spelling at another
/// sort is not a rounding mode.
pub fn rounding_mode_literal(terms: &TermStore, term: TermId) -> Option<RoundingMode> {
    if !is_rounding_mode_sort(terms.sort(term)) {
        return None;
    }
    match terms.get(term) {
        TermData::App(Symbol::Named(name), args) if args.is_empty() => {
            // Reject unknown spellings before hashing a potentially long user
            // declaration name. Only the ten native literals need the guard.
            let mode = RoundingMode::from_name(name)?;
            (!terms.is_declared_function(name)).then_some(mode)
        }
        _ => None,
    }
}

/// `(value, width)` of a bit-vector constant, the value unsigned.
pub(crate) fn bv_constant(terms: &TermStore, term: TermId) -> Option<(BigInt, u32)> {
    match terms.get(term) {
        TermData::Const(Constant::BitVec { value, width }) => Some((value.clone(), *width)),
        _ => None,
    }
}

/// IEEE field reconstruction needs no arithmetic model carrier. In particular,
/// significands wider than u128 remain exact. NaN has no specified encoding.
pub(crate) fn non_nan_ieee_bits(terms: &TermStore, term: TermId) -> Option<(BigInt, u32)> {
    let (bits, width) = ieee_bits(terms, term)?;
    let Sort::FloatingPoint(eb, sb) = *terms.sort(term) else {
        return None;
    };
    let exponent_mask = (BigInt::one() << eb) - 1;
    let exponent = (&bits >> (sb - 1)) & &exponent_mask;
    let fraction: BigInt = &bits & ((BigInt::one() << (sb - 1)) - BigInt::one());
    if exponent == exponent_mask && !fraction.is_zero() {
        return None;
    }
    Some((bits, width))
}

/// Decode only well-sorted, bounded IEEE fields. The canonical NaN below is
/// internal to numeral decoding; the public encoding fold excludes every NaN.
fn ieee_bits(terms: &TermStore, term: TermId) -> Option<(BigInt, u32)> {
    let Sort::FloatingPoint(eb, sb) = *terms.sort(term) else {
        return None;
    };
    if !(2..=crate::MAX_ENCODING_EXPONENT_BITS).contains(&eb)
        || !(2..=crate::MAX_ENCODING_SIGNIFICAND_BITS).contains(&sb)
    {
        return None;
    }
    let width = eb.checked_add(sb)?;
    let TermData::App(sym, args) = terms.get(term) else {
        return None;
    };
    if terms.is_declared_function(sym.name()) {
        return None;
    }
    let read = |id: TermId, expected: u32| {
        let (value, actual) = bv_constant(terms, id)?;
        (actual == expected
            && terms.sort(id) == &Sort::bitvec(expected)
            && value.sign() != num_bigint::Sign::Minus
            && value.bits() <= u64::from(expected))
        .then_some(value)
    };
    let exponent_mask = (BigInt::one() << eb) - 1;
    let bits = match (sym, args.as_slice()) {
        (Symbol::Indexed(name, indices), []) if indices.as_slice() == [eb, sb] => {
            let magnitude = match &**name {
                "+zero" | "-zero" => BigInt::zero(),
                "+oo" | "-oo" => &exponent_mask << (sb - 1),
                "NaN" => (&exponent_mask << (sb - 1)) | BigInt::one(),
                _ => return None,
            };
            let sign = BigInt::from(u8::from(name.starts_with('-'))) << (width - 1);
            sign | magnitude
        }
        (Symbol::Indexed(name, indices), [bits])
            if &**name == "to_fp" && indices.as_slice() == [eb, sb] =>
        {
            read(*bits, width)?
        }
        (Symbol::Named(name), [sign, exponent, fraction]) if &**name == "fp" => {
            (read(*sign, 1)? << (width - 1))
                | (read(*exponent, eb)? << (sb - 1))
                | read(*fraction, sb - 1)?
        }
        _ => return None,
    };
    Some((bits, width))
}

/// The exact value of a ground Real or Int expression: numerals combined with
/// `+`, `-`, `*` and `/` (a division by zero is not ground: `(/ x 0)` is an
/// uninterpreted value in SMT-LIB).
pub(crate) fn ground_rational(terms: &TermStore, term: TermId) -> Option<BigRational> {
    match terms.get(term) {
        TermData::Const(Constant::Rational(r)) => Some(r.0.clone()),
        TermData::Const(Constant::Int(n)) => Some(BigRational::from_integer(n.clone())),
        TermData::App(Symbol::Named(name), args)
            if !args.is_empty() && !terms.is_declared_function(name) =>
        {
            if !matches!(terms.sort(term), Sort::Real | Sort::Int) {
                return None;
            }
            let values = args
                .iter()
                .map(|&a| ground_rational(terms, a))
                .collect::<Option<Vec<_>>>()?;
            let (first, rest) = values.split_first()?;
            match (name.as_str(), rest.is_empty()) {
                ("-", true) => Some(-first.clone()),
                ("+", _) => Some(values.iter().sum()),
                ("*", _) => Some(values.iter().fold(BigRational::one(), |p, v| p * v)),
                ("-", false) => Some(rest.iter().fold(first.clone(), |d, v| d - v)),
                ("/", false) if rest.iter().all(|v| !v.is_zero()) => {
                    Some(rest.iter().fold(first.clone(), |q, v| q / v))
                }
                _ => None,
            }
        }
        _ => None,
    }
}

/// The signed value of a `width`-bit two's-complement pattern.
pub(crate) fn signed_value(value: &BigInt, width: u32) -> BigInt {
    if width > 0 && value.bit(u64::from(width - 1)) {
        value - (BigInt::one() << width)
    } else {
        value.clone()
    }
}
