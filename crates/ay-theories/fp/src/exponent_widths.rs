// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Exponent widths of the FP circuits, for every legal format.
//!
//! The circuits follow z3's `fpa2bv`, which keeps exponents in `eb + 2`
//! signed bits, a subnormal's leading-zero count in `eb` bits and `fp.sqrt`'s
//! exponent in `eb + 1`. That holds every intermediate of an ordinary format
//! (Float16 and up), but SMT-LIB admits any `eb, sb >= 2`, and a small `eb`
//! with a comparatively wide `sb` (or a wide integer) wrapped: the 2026-09-24
//! fp-strings fix-up found wrong `unsat`s in `(2,3)` `fp.fma`, `(3,8)`
//! `fp.sqrt` and `((_ to_fp_unsigned 2 3) RNE b)`, and its round-2 verifier
//! found legal formats such as `(2,6)`, `(3,9)` and `(4,17)` that the first
//! repair could only decline.
//!
//! Each width below is derived from the range of the values the operation
//! computes, the way SymFPU sizes its unpacked exponent: with `E = 2^(eb-1)`
//! and `S = sb`, a normalised unpacked exponent lies in `[3 - E - S, E - 1]`
//! (the smallest subnormal `2^(3 - E - S)`, the largest normal `2^(E - 1)`),
//! and a subnormal significand has at most `S - 1` leading zeros. Every
//! function returns z3's width exactly wherever that already holds the range,
//! which covers every ordinary format, so those encodings are unchanged (see
//! `ordinary_formats_keep_the_narrow_widths`).

use super::FpSolver;

/// `E = 2^(eb - 1)`, or `None` for an exponent field so wide that no
/// significand width reaches its range (`sb` comes from a `u32`); every width
/// is then the narrow one.
fn half_range(eb: usize) -> Option<i128> {
    (eb <= 64).then(|| 1i128 << (eb - 1))
}

/// The least signed width, at least `floor`, holding every value in
/// `[lo, hi]`.
fn signed_width(floor: usize, lo: i128, hi: i128) -> usize {
    let mut w = floor;
    while w < 127 && ((1i128 << (w - 1)) < -lo || (1i128 << (w - 1)) - 1 < hi) {
        w += 1;
    }
    w
}

impl FpSolver<'_> {
    /// Width of the leading-zero count a normalising `unpack` returns: `eb`
    /// (z3's), or wider when a subnormal significand's up to `sb - 1` leading
    /// zeros do not fit `eb` bits (`sb > 2^eb`, e.g. `(2,5)`).
    pub(crate) fn unpack_lz_width(eb: usize, sb: usize) -> usize {
        eb.max(Self::bits_to_hold(sb.saturating_sub(1) as u64))
    }

    /// Signed width `fp_round` needs for an exponent in `[lo, hi]` and a
    /// significand with at most `lz_max` leading zeros.
    ///
    /// `fp_round` compares the exponent with `e_max` (so it must be held),
    /// counts the significand's leading zeros (up to `sb + 4`, held as a
    /// non-negative value) against the cap `sb + 2`, and derives
    /// `t = exp + 1 - lz - e_min` (`e_min = 2 - E`), whose sign decides
    /// whether the result is subnormal: `t` reaches `lo + E - 1 - lz_max`
    /// below. Above, whatever it derives from an exponent past `e_max` is
    /// replaced by the overflow result, and from one at most `e_max` it stays
    /// below `2E`, which `eb + 2` bits hold.
    pub(crate) fn round_width(eb: usize, sb: usize, lo: i128, hi: i128, lz_max: i128) -> usize {
        let Some(e) = half_range(eb) else {
            return eb + 2;
        };
        let s = sb as i128;
        signed_width(eb + 2, lo.min(lo + e - 1 - lz_max), hi.max(s + 4))
    }

    /// `fp.add`/`fp.sub`: the sum keeps the larger operand's unnormalised
    /// exponent `[2 - E, E - 1]`, and its significand can lose up to `sb + 4`
    /// leading zeros to cancellation.
    pub(crate) fn add_exponent_width(eb: usize, sb: usize) -> usize {
        let Some(e) = half_range(eb) else {
            return eb + 2;
        };
        let s = sb as i128;
        Self::round_width(eb, sb, 2 - e, e - 1, s + 4)
    }

    /// `fp.mul`: the product of two normalised significands has at most one
    /// leading zero, and its exponent, the sum of two normalised exponents,
    /// lies in `[6 - 2E - 2S, 2E - 2]`: `(3,8)`'s product of two subnormals
    /// has exponent -18, below `eb + 2 = 5` bits (it wrapped to +14).
    pub(crate) fn mul_exponent_width(eb: usize, sb: usize) -> usize {
        let Some(e) = half_range(eb) else {
            return eb + 2;
        };
        let s = sb as i128;
        Self::round_width(eb, sb, 6 - 2 * e - 2 * s, 2 * e - 2, 1)
    }

    /// `fp.fma`: the product's exponent as in `fp.mul`, the addend's
    /// normalised; the alignment distance reaches `3E + 2S - 7`, the alignment
    /// cap is `2S + 3`, the sum has up to `2S + 5` leading zeros, and the
    /// renormalisation distance to `e_min` reaches `3E - 3`; `fp_round` then
    /// subtracts up to `S + 4` leading zeros and `e_min`. In `(2,3)` the cap 9
    /// did not fit 4 signed bits (it read as -7 and the addend was never
    /// aligned: the fix-up's fresh `g6_00041`, a wrong `unsat`).
    pub(crate) fn fma_exponent_width(eb: usize, sb: usize) -> usize {
        let Some(e) = half_range(eb) else {
            return eb + 2;
        };
        let s = sb as i128;
        let most_positive = (3 * e + 2 * s - 7).max(2 * s + 5).max(3 * e - 3);
        let most_negative = (2 * e + 2 * s - 6).max(e + 3 * s + 2);
        signed_width(eb + 2, -most_negative, most_positive)
    }

    /// `fp.div`: the quotient of two normalised operands has exponent
    /// `[4 - 2E - S, 2E + S - 4]`, one less after its at most one-place
    /// normalising shift, and at most one leading zero after it.
    pub(crate) fn div_exponent_width(eb: usize, sb: usize) -> usize {
        let Some(e) = half_range(eb) else {
            return eb + 2;
        };
        let s = sb as i128;
        Self::round_width(eb, sb, 3 - 2 * e - s, 2 * e + s - 4, 1)
    }

    /// `fp.sqrt`: `(unhalved, rounded)`. The operand's normalised exponent
    /// `[3 - E - S, E - 1]` is held (z3: `eb + 1` bits) before it is halved;
    /// the halved exponent goes to `fp_round`. In `(3,8)` the smallest
    /// subnormal's exponent -9 wrapped in 4 bits and its square root read as
    /// about 11.3 (the fix-up's `sqrt38b`, a wrong `unsat` on main).
    pub(crate) fn sqrt_exponent_widths(eb: usize, sb: usize) -> (usize, usize) {
        let Some(e) = half_range(eb) else {
            return (eb + 1, eb + 2);
        };
        let s = sb as i128;
        let lo = 3 - e - s;
        let unhalved = signed_width(eb + 1, lo, e - 1);
        let rounded = Self::round_width(eb, sb, lo.div_euclid(2), (e - 1).div_euclid(2), s + 4);
        (unhalved, rounded.max(unhalved - 1))
    }

    /// `fp.rem`: the exponent difference of two normalised operands,
    /// `[4 - 2E - S, 2E + S - 4]`, drives the modular reduction; the remainder
    /// is rounded at the divisor's normalised exponent `[3 - E - S, E - 1]`
    /// with up to `S + 4` leading zeros (the remainder candidate `8R`), which
    /// its adjustment step also counts.
    pub(crate) fn rem_exponent_width(eb: usize, sb: usize) -> usize {
        let Some(e) = half_range(eb) else {
            return eb + 2;
        };
        let s = sb as i128;
        let diff = signed_width(eb + 2, 4 - 2 * e - s, 2 * e + s - 4);
        diff.max(Self::round_width(eb, sb, 3 - e - s, e - 1, s + 4))
    }

    /// `fp.roundToIntegral`: the normalised exponent `[3 - E - S, E - 1]`
    /// against the constants `sb - 1` and `sb`.
    pub(crate) fn round_to_integral_exponent_width(eb: usize, sb: usize) -> usize {
        let Some(e) = half_range(eb) else {
            return eb + 2;
        };
        let s = sb as i128;
        signed_width(eb + 2, 3 - e - s, (e - 1).max(s))
    }

    /// `fp.to_ubv`/`fp.to_sbv`: the normalised exponent `[3 - E - S, E - 1]`
    /// and its negation, the right-shift distance of a value below one.
    pub(crate) fn to_bv_exponent_width(eb: usize, sb: usize) -> usize {
        let Some(e) = half_range(eb) else {
            return eb + 2;
        };
        let s = sb as i128;
        signed_width(eb + 2, 3 - e - s, e + s - 3)
    }

    /// A conversion from `(eb, sb)` to `(teb, tsb)`: `(work, rounded)`.
    ///
    /// The source's normalised exponent `[3 - E - S, E - 1]` is computed at
    /// `work` bits and clamped into the `rounded` bits `fp_round` receives. The
    /// clamp is exact when every clamped value rounds as the true one: below,
    /// the bound `-2^(rounded - 1)` must lie under half the target's smallest
    /// subnormal (`2^(1 - E_t - S_t)`); above, anything past the target's
    /// `e_max` overflows either way. z3 clamps at the target's `teb + 2` bits,
    /// which in `(2,10)` (`E_t + S_t = 12 > 8`) lifted `2^-24` to `2^-8`.
    pub(crate) fn fp_conversion_widths(
        eb: usize,
        sb: usize,
        teb: usize,
        tsb: usize,
    ) -> (usize, usize) {
        let narrow_work = eb.max(teb) + 2;
        let (Some(e), Some(te)) = (half_range(eb), half_range(teb)) else {
            return (narrow_work, teb + 2);
        };
        let (s, ts) = (sb as i128, tsb as i128);
        let rounded = signed_width(teb + 2, -(te + ts), ts + 4);
        let source = signed_width(eb + 2, 3 - e - s, e - 1);
        (narrow_work.max(rounded).max(source), rounded)
    }

    /// Signed width that holds every exponent the conversion of a `bv_sz`-bit
    /// integer to `(eb, sb)` computes (`bv_sz - 2` less the integer's leading
    /// zeros) and every exponent `fp_round` then derives from it: up to
    /// `bv_sz + E - 1` above (`E = 2^(eb-1)`, the bias added back) and
    /// `-(sb + 5)` below. z3's `eb + 2` holds these whenever the integer is
    /// narrow next to the format's range (Float16 from up to 48 bits, Float32
    /// from up to 384), and the width is then `eb + 2` exactly and the encoding
    /// unchanged. A small format from a wide integer needs more: in `(2,3)` a
    /// 24-bit integer's `bv_sz - 2 = 22` wrapped in 4 bits, and
    /// `((_ to_fp_unsigned 2 3) RNE b)` with `b = 1` read as `+0` (a wrong
    /// `unsat`, found by the 2026-09-24 fp-strings fix-up's conversion audit).
    pub(crate) fn int_conversion_exponent_width(eb: usize, sb: usize, bv_sz: usize) -> usize {
        let Some(e) = half_range(eb) else {
            // Both source widths come from u32. Above 64 exponent bits,
            // the ordinary width already dominates their entire range;
            // do not shift a host integer by a format-controlled amount
            // (`1u128 << (eb + 1)` overflowed from `eb = 127` on).
            return eb + 2;
        };
        let need = (bv_sz as i128 + e).max(sb as i128 + 6);
        signed_width(eb + 2, -need, need - 1)
    }
}

#[cfg(test)]
mod tests {
    use super::FpSolver;

    #[test]
    fn width_calculation_does_not_shift_by_an_unbounded_exponent_field() {
        // Width arithmetic is independently safe even where other existing
        // circuit code does not yet support such wide exponent fields.
        let largest_source_width = u32::MAX as usize;
        for eb in [64, 65, 127, 128, u32::MAX as usize] {
            assert_eq!(
                FpSolver::int_conversion_exponent_width(
                    eb,
                    largest_source_width,
                    largest_source_width,
                ),
                eb + 2,
            );
        }
    }
}
