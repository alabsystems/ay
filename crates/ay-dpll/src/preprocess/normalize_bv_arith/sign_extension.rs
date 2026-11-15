// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The spelled-out sign extension `concat(ite(msb(x) = 1, ones_k, 0_k), x)`.
//!
//! Lowerings that have no `sign_extend` in their own IR (external-codegen's `SMULL`,
//! for one) spell a sign extension as a `concat` whose high part replicates the
//! operand's sign bit through an `ite`. Its value is exactly
//! `((_ sign_extend k) x)`: the `ite` is `ones_k` precisely when the sign bit
//! is set and `0_k` precisely when it is clear. Rebuilding it as the operator
//! lets hash-consing identify it with an authored `sign_extend` of the same
//! operand, so a product of the two spellings, e.g.
//! `(bvmul (concat (ite ..) x) ..)` against `(bvmul ((_ sign_extend k) x) ..)`,
//! is decided by congruence instead of by bit-blasting two multipliers.
//!
//! The recognizer admits only the exact shape: both branches are the all-ones
//! and all-zero literals of the high part's own width, the condition compares
//! the operand's own sign bit (the canonical `extract`, so a nested extract
//! spelling is the same term) with a one-bit literal in either operand order,
//! and the branch order agrees with that literal. Anything else is left as it
//! is.

use ay_core::term::{Constant, Symbol, TermData};
use ay_core::{Sort, TermId, TermStore};
use num_bigint::BigInt;
use num_traits::{One, Zero};

/// The canonical rebuild of a `concat`: the spelled-out sign extension becomes
/// the operator, anything else goes through `mk_bvconcat`.
pub(super) fn rebuild_concat(terms: &mut TermStore, args: Vec<TermId>) -> TermId {
    if let [high, low] = args.as_slice() {
        if let Some(extension) = spelled_sign_extension(terms, *high, *low) {
            return terms.mk_bvsign_extend(extension, *low);
        }
    }
    terms.mk_bvconcat(args)
}

/// `Some(k)` when `concat(high, low)` is the spelled-out `sign_extend(k, low)`.
fn spelled_sign_extension(terms: &mut TermStore, high: TermId, low: TermId) -> Option<u32> {
    let (Sort::BitVec(high_sort), Sort::BitVec(low_sort)) = (terms.sort(high), terms.sort(low))
    else {
        return None;
    };
    let (extension, low_width) = (high_sort.width, low_sort.width);
    if extension == 0 || low_width == 0 {
        return None;
    }
    let TermData::Ite(condition, then_term, else_term) = terms.get(high).clone() else {
        return None;
    };
    let ones = (BigInt::one() << extension) - BigInt::one();
    let then_value = literal_of_width(terms, then_term, extension)?;
    let else_value = literal_of_width(terms, else_term, extension)?;
    // `(ite c ones 0)`: `c` must mean "the sign bit is 1"; `(ite c 0 ones)`:
    // it must mean "the sign bit is 0".
    let wanted_bit = if then_value == ones && else_value.is_zero() {
        true
    } else if then_value.is_zero() && else_value == ones {
        false
    } else {
        return None;
    };
    let (tested, bit) = sign_test(terms, condition)?;
    if bit != wanted_bit {
        return None;
    }
    let sign_bit = terms.mk_bvextract(low_width - 1, low_width - 1, low);
    (tested == sign_bit).then_some(extension)
}

/// `(t, b)` when `condition` is `(= t b)` or `(= b t)` for a one-bit term `t`
/// and a one-bit literal `b`.
fn sign_test(terms: &TermStore, condition: TermId) -> Option<(TermId, bool)> {
    let TermData::App(Symbol::Named(name), args) = terms.get(condition) else {
        return None;
    };
    let [left, right] = args.as_slice() else {
        return None;
    };
    if name != "=" {
        return None;
    }
    let (tested, literal) = match (
        literal_of_width(terms, *left, 1),
        literal_of_width(terms, *right, 1),
    ) {
        (None, Some(value)) => (*left, value),
        (Some(value), None) => (*right, value),
        _ => return None,
    };
    matches!(terms.sort(tested), Sort::BitVec(bv) if bv.width == 1)
        .then_some((tested, !literal.is_zero()))
}

fn literal_of_width(terms: &TermStore, term: TermId, width: u32) -> Option<BigInt> {
    match terms.get(term) {
        TermData::Const(Constant::BitVec {
            value,
            width: literal_width,
        }) if *literal_width == width => Some(value.clone()),
        _ => None,
    }
}

#[cfg(test)]
#[path = "sign_extension_tests.rs"]
mod tests;
