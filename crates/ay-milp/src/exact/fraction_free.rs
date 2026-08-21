// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Integer arithmetic for the exact rim's FRACTION-FREE tableau.
//!
//! WHY THIS EXISTS. The rim's tableau used to hold one reduced
//! [`Rational`] per entry, and a pivot rewrote every entry as
//! `dst += d * src`. MEASURED on `domset_mw19_19` (466x467, `sample(1)`
//! over the rim driven directly, 12s window): `ExactLp::pivot` is 12,510 of
//! `minimize`'s 12,606 samples — 99.2% — split 8,382 multiply / 4,094
//! add-assign, and the top-of-stack census is 93% `BigUint::gcd` and the
//! shift/subtract inside it. Reducing a fraction after every multiply and
//! every add IS the rim's cost, and the entries it reduces are wide:
//! 163-bit numerators by pivot 200, 297 bits by pivot 600, 98.9% off the
//! inline `i64` path.
//!
//! WHAT IS REMOVABLE. Nothing about the VALUES: a tableau entry is a fixed
//! rational function of the basis, and `Rational` always holds it fully
//! reduced, so re-deriving the rows from the original matrix (the "periodic
//! refactorization" analogue) reproduces the same numbers bit for bit, and
//! normalising a row cannot help either — MEASURED, the numerators of a row
//! rescaled to its own common denominator have gcd 1 on every sample
//! (`commonfactor_bits=0` at pivots 200/400/600). What is removable is the
//! REDUCTION ITSELF: hold the row as integers over one shared denominator and
//! the gcds have nothing left to do.
//!
//! THE REPRESENTATION. The tableau is `basic_i = Σ_v (t_iv / Δ)·x_v` with
//! `t` integral and `Δ > 0` shared by every row — the classical
//! integer-preserving (Bareiss) simplex tableau, in which `t = ±adj(B)·N` and
//! `Δ = |det B|` are minors of the ORIGINAL integer matrix. Pivoting on
//! `(r, e)` with `p = t_re` and `s = sign(p)` takes
//!
//! ```text
//!   t'_ik = s·(t_ik·p − t_ie·t_rk) / Δ     (i ≠ r)
//!   t'_i,leaving = s·t_ie                  (i ≠ r)
//!   t'_rk = −s·t_rk,   t'_r,leaving = s·Δ
//!   Δ'    = |p|
//! ```
//!
//! and EVERY division there is exact, because `t'` is again `±adj(B')·N` for
//! the new basis. No gcd occurs anywhere in a pivot.
//!
//! FAIL-CLOSED. Exactness is asserted, not assumed: [`fused`] divides with
//! `div_rem` and returns `None` on any nonzero remainder, and its caller
//! poisons the solve (every verdict becomes `Unknown`) rather than continuing
//! on a number it cannot justify. It earned its keep on the first run: it
//! caught a wrong rescale of the leaving column instantly, on every member of
//! the corpus, instead of letting one certificate out.
//!
//! WHAT IT IS WORTH, AND WHERE IT IS NOT. Every member of the oracle LP corpus
//! the rim can finish returns the SAME exact optimum in the SAME number of
//! pivots (the pivot rule is untouched — only the arithmetic under it moved),
//! at 60s, rim driven directly:
//!
//! ```text
//!   pk1     6.403s -> 0.342s   mas74  12.289s -> 1.510s   mas76 8.639s -> 1.190s
//!   blend2 30.379s -> 8.398s   misc07  5.116s -> 1.438s   mod008 0.508s -> 0.144s
//!   misc03  0.112s -> 0.047s   p0201   0.055s -> 0.032s   rout  13.614s -> 10.710s
//!   domset_mw19_19: 350 -> 950 pivots in 60s (neither finishes)
//!   dcmulti 0.606s -> 3.028s   qiu 2,757 -> 834 pivots    qnet1 53,747 -> 23,220
//! ```
//!
//! The split is not about size or sparsity; it is about whether the tableau's
//! entries NEED the determinant they are scaled by. On `domset_mw19_19` they
//! do — the reduced entries have no common factor to remove
//! (`commonfactor_bits = 0` at pivots 200/400/600), so the gcds the reduced
//! form runs buy nothing. On `dcmulti` they do not: its reduced entries are
//! 7.9 bits mean, 13-bit numerators, 100% inline `i64`, while the same tableau
//! held fraction-free is 259 bits mean and 100% `BigInt`, of which 98.2% is a
//! common factor the reduced form removes for free. There the gcds are buying
//! a 33x width cut and are the right trade.
//!
//! So this representation is the right one for the bit-growth class and the
//! wrong one for the word-sized class, and it is therefore NOT the rim's
//! representation — it is one of two, entered by the policy in
//! [`crate::exact`] when the reduced tableau is measured leaving the inline
//! path. Both forms are the same `TabRow` (`den = 1` with reduced entries IS
//! the reduced tableau), so what this module supplies is a second pivot's
//! arithmetic, not a second data structure. Row normalisation was measured as
//! a way to get the same effect inside this form and REFUSED: reducing each
//! rewritten row by its own gcd chain cost more than the width it removed
//! everywhere it was tried (`mas76` 1.190s -> 2.044s, `rout` 10.710s ->
//! 19.067s) and did not rescue the class it was aimed at (`dcmulti` 3.028s ->
//! 4.053s).
//!
//! WHAT THE CALLER OWES THIS MODULE. Every division below is exact only
//! because the tableau it is handed is `t = Δ·c` with `Δ = |det B|` for a
//! basis of an INTEGER matrix. `ExactLp` supplies both halves: it integralises
//! each row at construction (`λ_r`, and it declines the switch outright for a
//! row it cannot integralise on the inline path), and it carries `|det B|`
//! from the first pivot so the conversion has a real determinant to scale by.
//! Neither is assumed — the conversion checks integrality and every division
//! here checks its remainder.

use std::borrow::Cow;

use ay_lra::rational::Rational;
use num_bigint::BigInt;
use num_integer::Integer as _;
use num_rational::BigRational;
use num_traits::{Signed as _, Zero as _};

/// An integer in the rim's tableau: a [`Rational`] whose denominator is 1.
///
/// The type is the workspace's shared exact vocabulary rather than a new
/// integer type, for one measured reason: `Rational::Small` is an INLINE
/// `(i64, i64)`, so a tableau whose entries stay word-sized (the `hexgrid`
/// class: zero bit growth over the whole solve) allocates nothing, which a
/// `BigInt`-typed tableau could not manage.
pub(crate) type Int = Rational;

/// `n` as a tableau integer.
#[inline]
pub(crate) fn from_i64(n: i64) -> Int {
    Rational::new(n, 1)
}

/// A `BigInt` as a tableau integer (shrinking to the inline form when it fits).
#[inline]
pub(crate) fn from_bigint(n: BigInt) -> Int {
    Rational::from_big(BigRational::from_integer(n))
}

/// The integer as a `BigInt`, borrowed when it already is one.
#[inline]
fn as_bigint(x: &Int) -> Cow<'_, BigInt> {
    match x {
        Rational::Small(n, _) => Cow::Owned(BigInt::from(*n)),
        Rational::Big(br) => Cow::Borrowed(br.numer()),
    }
}

/// The inline value, if this integer has one.
#[inline]
fn as_i64(x: &Int) -> Option<i64> {
    match x {
        Rational::Small(n, _) => Some(*n),
        Rational::Big(_) => None,
    }
}

/// `a·b` as a `BigInt`, without widening an inline operand more than once.
#[inline]
fn mul_big(a: &Int, b: &Int) -> BigInt {
    match (as_i64(a), as_i64(b)) {
        (Some(x), Some(y)) => BigInt::from(i128::from(x) * i128::from(y)),
        (Some(x), None) => &*as_bigint(b) * x,
        (None, Some(y)) => &*as_bigint(a) * y,
        (None, None) => &*as_bigint(a) * &*as_bigint(b),
    }
}

/// `(a·p − b·q) / delta`, exact — the Bareiss step for one tableau entry.
///
/// `None` means the division left a remainder, which the identity above
/// forbids; the caller must treat it as a corrupted tableau and refuse to
/// produce a verdict. It is NOT a slow-path signal: there is no other way to
/// get this wrong quietly.
#[inline]
pub(crate) fn fused(a: &Int, p: &Int, b: &Int, q: &Int, delta: &Int) -> Option<Int> {
    // Inline path: four i64 multiplicands and an i64 divisor. Products are at
    // most 126 bits, so only their difference can leave i128, and that is
    // checked rather than assumed.
    if let (Some(a), Some(p), Some(d)) = (as_i64(a), as_i64(p), as_i64(delta)) {
        let bq = match (as_i64(b), as_i64(q)) {
            (Some(b), Some(q)) => i128::from(b) * i128::from(q),
            _ => return fused_big(&from_i64(a), &from_i64(p), b, q, delta),
        };
        let num = (i128::from(a) * i128::from(p)).checked_sub(bq)?;
        let d = i128::from(d);
        if num % d != 0 {
            return None;
        }
        let out = num / d;
        return Some(match i64::try_from(out) {
            Ok(small) => from_i64(small),
            Err(_) => from_bigint(BigInt::from(out)),
        });
    }
    fused_big(a, p, b, q, delta)
}

fn fused_big(a: &Int, p: &Int, b: &Int, q: &Int, delta: &Int) -> Option<Int> {
    let num = mul_big(a, p) - mul_big(b, q);
    let (quotient, remainder) = num.div_rem(&as_bigint(delta));
    if !remainder.is_zero() {
        return None;
    }
    Some(from_bigint(quotient))
}

/// The true tableau coefficient `x / delta`, as the reduced rational the
/// certificate layer and the ratio test speak.
#[inline]
pub(crate) fn over(x: &Int, delta: &Int) -> Rational {
    if let (Some(n), Some(d)) = (as_i64(x), as_i64(delta)) {
        return Rational::new(n, d);
    }
    Rational::new_big(as_bigint(x).into_owned(), as_bigint(delta).into_owned())
}

/// `|x|`.
#[inline]
pub(crate) fn abs(x: &Int) -> Int {
    match as_i64(x) {
        Some(n) => match n.checked_abs() {
            Some(v) => from_i64(v),
            None => from_bigint(-BigInt::from(n)), // i64::MIN
        },
        None => from_bigint(as_bigint(x).abs()),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn i(n: i64) -> Int {
        from_i64(n)
    }

    fn big(n: i64, shift: u32) -> Int {
        from_bigint(BigInt::from(n) << shift)
    }

    /// The step is the definition, on both arithmetic paths.
    #[test]
    fn fused_agrees_with_the_definition() {
        // (7·11 − 3·5) / 2 = 31
        assert_eq!(fused(&i(7), &i(11), &i(3), &i(5), &i(2)), Some(i(31)));
        // Same numbers, shifted past i64 on every operand.
        let got = fused(
            &big(7, 70),
            &big(11, 70),
            &big(3, 70),
            &big(5, 70),
            &big(2, 70),
        );
        assert_eq!(got, Some(big(31, 70)));
    }

    /// A remainder is a corrupted tableau, and says so.
    #[test]
    fn an_inexact_division_declines() {
        assert_eq!(fused(&i(7), &i(11), &i(3), &i(5), &i(4)), None);
        assert_eq!(fused(&big(7, 70), &big(11, 70), &i(3), &i(5), &i(7)), None);
    }

    /// The inline path and the big path are the same function.
    #[test]
    fn the_two_paths_agree() {
        for a in [-97i64, -3, 0, 5, 1_000_003] {
            for p in [-11i64, 1, 7, 65_537] {
                for b in [-13i64, 0, 29] {
                    for q in [-5i64, 3, 101] {
                        for d in [-7i64, 1, 2, 6] {
                            let inline = fused(&i(a), &i(p), &i(b), &i(q), &i(d));
                            let heavy = fused_big(&i(a), &i(p), &i(b), &i(q), &i(d));
                            assert_eq!(inline, heavy, "a={a} p={p} b={b} q={q} d={d}");
                        }
                    }
                }
            }
        }
    }

    /// i128 cannot hold every difference of two i64 products; the check that
    /// says so must route to the wide path rather than wrap.
    #[test]
    fn a_difference_past_i128_still_lands() {
        let big_i64 = i64::MAX;
        let got = fused(&i(big_i64), &i(big_i64), &i(-big_i64), &i(big_i64), &i(1));
        let expect = from_bigint(BigInt::from(big_i64) * BigInt::from(big_i64) * 2);
        assert_eq!(got, Some(expect));
    }

    #[test]
    fn over_and_abs_are_exact() {
        assert_eq!(over(&i(6), &i(4)), Rational::new(3, 2));
        assert_eq!(abs(&i(-5)), i(5));
        assert_eq!(abs(&big(-3, 90)), big(3, 90));
        assert_eq!(abs(&i(i64::MIN)), from_bigint(-BigInt::from(i64::MIN)));
    }
}
