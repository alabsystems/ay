// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The arithmetic and conversion circuits in small and unusual formats
//! (2026-09-24 fp-strings fix-up).
//!
//! z3's `fpa2bv`, which these circuits follow, keeps exponents in `eb + 2`
//! signed bits and a few counts in `eb` bits. That holds every intermediate of
//! an ordinary format (Float16 up) from an ordinary integer width, but not of a
//! small `eb` with a comparatively wide `sb` or a wide integer, where values
//! wrapped and the circuits answered wrong: the fresh hunt file `g6_00041`
//! (`fp.fma` in `(2,3)`) was a wrong `unsat`, and so was
//! `((_ to_fp_unsigned 2 3) RNE b)` with a 24-bit `b = 1`. Every circuit now
//! takes its widths from the ranges it computes (`exponent_widths.rs`), for
//! every legal format; none declines one. The round-2 audit ran each circuit
//! on every input of every format from `(2,3)` to `(4,6)` (and sampled wider
//! ones) against an exact rational IEEE-754 reference (the hunt's
//! `fpref.py`); each expected value below is that reference's.
//! `exhaustive_fp22` pins every arithmetic circuit on every input of the
//! minimum legal format `(2,2)` against a checked-in table from that same
//! reference.

use super::*;
use crate::tests_support::{extract_fp, solve_fp_clauses};
use ay_core::{Sort, Symbol};

mod exhaustive_fp22;

/// `(sign, biased exponent, stored significand)`.
type Bits = (u64, u64, u64);

fn pin(solver: &mut FpSolver<'_>, fp: &FpDecomposed, (s, e, m): Bits) {
    solver.add_clause(CnfClause::unit(if s == 1 { fp.sign } else { -fp.sign }));
    for (i, &bit) in fp.exponent.iter().enumerate() {
        solver.add_clause(CnfClause::unit(if (e >> i) & 1 == 1 { bit } else { -bit }));
    }
    for (i, &bit) in fp.significand.iter().enumerate() {
        solver.add_clause(CnfClause::unit(if (m >> i) & 1 == 1 { bit } else { -bit }));
    }
}

/// The circuit's result on pinned operands, or `None` when the encoder
/// declined the format (an encoding gap: the solver answers `unknown`).
fn run(
    (eb, sb): (u32, u32),
    op: &str,
    rm: RoundingMode,
    operands: &[Bits],
) -> Option<(bool, u64, u64)> {
    let mut terms = TermStore::new();
    let vars: Vec<TermId> = ["x", "y", "z"]
        .iter()
        .map(|name| terms.mk_var(*name, Sort::FloatingPoint(eb, sb)))
        .collect();
    let mut solver = FpSolver::new(&terms);
    let fps: Vec<FpDecomposed> = vars.iter().map(|&v| solver.get_fp(v)).collect();
    for (fp, &bits) in fps.iter().zip(operands) {
        pin(&mut solver, fp, bits);
    }
    let result = match op {
        "add" => solver.make_add(&fps[0], &fps[1], rm),
        "mul" => solver.make_mul(&fps[0], &fps[1], rm),
        "div" => solver.make_div(&fps[0], &fps[1], rm),
        "fma" => solver.make_fma(&fps[0], &fps[1], &fps[2], rm),
        "sqrt" => solver.make_sqrt(&fps[0], rm),
        "rem" => solver.make_rem(&fps[0], &fps[1]),
        "rti" => solver.make_round_to_integral(&fps[0], rm),
        other => panic!("no such op {other}"),
    };
    if solver.has_encoding_gap() {
        return None;
    }
    let model = solve_fp_clauses(&solver);
    Some(extract_fp(&model, &result))
}

/// `((_ to_fp eb sb) rm b)` (`signed`) or `((_ to_fp_unsigned eb sb) rm b)`
/// of the `width`-bit bitvector `b = value`, or `None` on an encoding gap.
fn run_from_int(
    (eb, sb): (u32, u32),
    signed: bool,
    rm: RoundingMode,
    width: u32,
    value: u64,
) -> Option<(bool, u64, u64)> {
    let mut terms = TermStore::new();
    let mode = terms.mk_app(
        Symbol::named(rm.name()),
        vec![],
        Sort::Uninterpreted("RoundingMode".to_string()),
    );
    let b = terms.mk_var("b", Sort::bitvec(width));
    let name = if signed { "to_fp" } else { "to_fp_unsigned" };
    let conversion = terms.mk_app(
        Symbol::indexed(name, vec![eb, sb]),
        vec![mode, b],
        Sort::FloatingPoint(eb, sb),
    );
    let mut solver = FpSolver::new(&terms);
    let bits = solver
        .bitblast_conv_bv_arg(b, width as usize)
        .expect("a bitvector variable bit-blasts");
    for (i, &bit) in bits.iter().enumerate() {
        solver.add_clause(CnfClause::unit(if (value >> i) & 1 == 1 {
            bit
        } else {
            -bit
        }));
    }
    let result = solver.get_fp(conversion);
    if solver.has_encoding_gap() {
        return None;
    }
    let model = solve_fp_clauses(&solver);
    Some(extract_fp(&model, &result))
}

/// `((_ to_fp teb tsb) rm x)` of `x` in `(eb, sb)`, or `None` on an encoding
/// gap.
fn run_convert(
    (eb, sb): (u32, u32),
    (teb, tsb): (u32, u32),
    rm: RoundingMode,
    x: Bits,
) -> Option<(bool, u64, u64)> {
    let mut terms = TermStore::new();
    let mode = terms.mk_app(
        Symbol::named(rm.name()),
        vec![],
        Sort::Uninterpreted("RoundingMode".to_string()),
    );
    let var = terms.mk_var("x", Sort::FloatingPoint(eb, sb));
    let conversion = terms.mk_app(
        Symbol::indexed("to_fp", vec![teb, tsb]),
        vec![mode, var],
        Sort::FloatingPoint(teb, tsb),
    );
    let mut solver = FpSolver::new(&terms);
    let fx = solver.get_fp(var);
    pin(&mut solver, &fx, x);
    let result = solver.get_fp(conversion);
    if solver.has_encoding_gap() {
        return None;
    }
    let model = solve_fp_clauses(&solver);
    Some(extract_fp(&model, &result))
}

/// `((_ fp.to_ubv width) rm x)` (`signed`: `fp.to_sbv`) of `x` in `(eb, sb)`,
/// or `None` on an encoding gap.
fn run_to_bv(
    (eb, sb): (u32, u32),
    rm: RoundingMode,
    width: usize,
    signed: bool,
    x: Bits,
) -> Option<u64> {
    let mut terms = TermStore::new();
    let var = terms.mk_var("x", Sort::FloatingPoint(eb, sb));
    let mut solver = FpSolver::new(&terms);
    let fx = solver.get_fp(var);
    pin(&mut solver, &fx, x);
    let bits = solver.bitblast_to_bv(var, rm, width, signed);
    if solver.has_encoding_gap() {
        return None;
    }
    let model = solve_fp_clauses(&solver);
    Some(tests_support::extract_bv(&model, &bits))
}

fn expect((s, e, m): Bits) -> Option<(bool, u64, u64)> {
    Some((s == 1, e, m))
}

/// `fp.fma` in `(2,3)`: the alignment cap `2*sb + 3 = 9` does not fit the
/// 4-bit signed exponent (it read as -7), so the addend was never aligned and
/// the result was the addend. Fresh `g6_00041` is the first case.
#[test]
fn fma_aligns_the_addend_in_a_two_bit_exponent_format() {
    use RoundingMode::{RNA, RTN};
    // -2 * 0.75 + 3 = 1.5 exactly (was 2.5).
    assert_eq!(
        run((2, 3), "fma", RTN, &[(1, 2, 0), (0, 0, 3), (0, 2, 2)]),
        expect((0, 1, 2))
    );
    // 2 * -0.75 + -1.75 = -3.25, a tie -> RNA -3.5 (was -1.75).
    assert_eq!(
        run((2, 3), "fma", RNA, &[(0, 2, 0), (1, 0, 3), (1, 1, 3)]),
        expect((1, 2, 3))
    );
}

/// `fp.fma` in `(3,8)`: the product of two subnormals has exponent -18,
/// below the 5-bit range, and wrapped to +14. The sticky product must still
/// lift `1 + tiny` to the next value under RTP.
#[test]
fn fma_keeps_a_subnormal_product_below_the_narrow_exponent_range() {
    assert_eq!(
        run(
            (3, 8),
            "fma",
            RoundingMode::RTP,
            &[(0, 0, 1), (0, 0, 1), (0, 3, 0)]
        ),
        expect((0, 3, 1))
    );
    // `fp.mul` of the same two subnormals: 2^-18 lies below the smallest
    // subnormal 2^-9, so RTP gives it (the wrapped exponent read as an
    // overflow, +oo).
    assert_eq!(
        run((3, 8), "mul", RoundingMode::RTP, &[(0, 0, 1), (0, 0, 1)]),
        expect((0, 0, 1))
    );
}

/// `fp.mul` with `sb < 4`: the product's low half is the TOP of the four
/// round bits, zero-padded below (z3: `concat(low, 0^(4-sb))`); it was padded
/// above, so -14 * 0.5 read as -6 under RTP in `(3,3)`.
#[test]
fn mul_places_a_short_low_half_at_the_top_of_the_round_bits() {
    assert_eq!(
        run((3, 3), "mul", RoundingMode::RTP, &[(1, 6, 3), (0, 2, 0)]),
        expect((1, 5, 3))
    );
}

/// `fp.add` in `(3,6)`: the alignment cap `sb + 2 = 8` does not fit the 3-bit
/// exponent difference (it read as 0), so the smaller addend was never
/// shifted. 15.5 + 15/128 rounds up to 15.75 under RTP (was +oo).
#[test]
fn add_aligns_with_a_cap_wider_than_the_exponent_field() {
    assert_eq!(
        run((3, 6), "add", RoundingMode::RTP, &[(0, 0, 15), (0, 6, 30)]),
        expect((0, 6, 31))
    );
}

/// Formats beyond the envelope z3's narrow encoding is exact in are legal
/// SMT-LIB, and the circuits size themselves for them instead of declining
/// (round 2: the first repair answered `unknown` on 27 generated files base
/// decided correctly). Each case wrapped a narrow width:
/// - a `(2,6)` subnormal has up to 5 leading zeros, which the unpack's 2-bit
///   count wrapped (`unpack_lz_width`);
/// - `fp.sqrt` held the normalised exponent in `eb + 1` bits: in `(3,8)` the
///   smallest subnormal's -9 wrapped and its square root read as about 11.3
///   (the fix-up's `sqrt38b`, a wrong `unsat` on main);
/// - a conversion clamped its exponent into the target's `teb + 2` bits, which
///   in `(2,10)` lifted Float16's `2^-24` to `2^-8`.
#[test]
fn formats_beyond_the_narrow_envelope_are_exact() {
    use RoundingMode::{RNE, RTN, RTP, RTZ};
    assert_eq!(
        run((2, 6), "mul", RTZ, &[(0, 0, 15), (1, 1, 23)]),
        expect((1, 0, 25))
    );
    assert_eq!(run((2, 6), "sqrt", RTZ, &[(0, 0, 15)]), expect((0, 0, 21)));
    assert_eq!(run((3, 8), "sqrt", RTZ, &[(0, 0, 1)]), expect((0, 0, 22)));
    assert_eq!(run((3, 8), "sqrt", RTZ, &[(0, 0, 15)]), expect((0, 0, 87)));
    assert_eq!(
        run((3, 8), "rem", RTZ, &[(0, 0, 1), (0, 1, 3)]),
        expect((0, 0, 1))
    );
    assert_eq!(run((3, 8), "rti", RTZ, &[(0, 0, 1)]), expect((0, 0, 0)));
    assert_eq!(run((3, 8), "rti", RTP, &[(0, 0, 1)]), expect((0, 3, 0)));
    // `(3,8)` multiplies exactly: its product exponent is widened.
    assert_eq!(
        run((3, 8), "mul", RTZ, &[(0, 0, 1), (0, 4, 0)]),
        expect((0, 0, 2))
    );
    // Conversions: `2^-9` into Float32 is exact; Float32's `2^-12` lies below
    // half of `(3,8)`'s smallest subnormal `2^-9`.
    assert_eq!(
        run_convert((3, 8), (8, 24), RNE, (0, 0, 1)),
        expect((0, 118, 0))
    );
    assert_eq!(
        run_convert((8, 24), (3, 8), RNE, (0, 115, 0)),
        expect((0, 0, 0))
    );
    assert_eq!(
        run_convert((8, 24), (3, 8), RTP, (0, 115, 0)),
        expect((0, 0, 1))
    );
    // Float16's smallest subnormal `2^-24` into `(2,10)`, whose smallest
    // subnormal is `2^-9`: zero, or `2^-9` toward +oo -- not `2^-8`.
    assert_eq!(
        run_convert((5, 11), (2, 10), RNE, (0, 0, 1)),
        expect((0, 0, 0))
    );
    assert_eq!(
        run_convert((5, 11), (2, 10), RTP, (0, 0, 1)),
        expect((0, 0, 1))
    );
    assert_eq!(
        run_convert((5, 11), (2, 10), RTN, (0, 0, 1)),
        expect((0, 0, 0))
    );
    assert_eq!(
        run_convert((5, 11), (2, 10), RNE, (0, 7, 0)),
        expect((0, 0, 2))
    );
    // `fp.to_ubv`/`fp.to_sbv` of `(3,8)`'s smallest subnormal.
    assert_eq!(run_to_bv((3, 8), RTP, 4, false, (0, 0, 1)), Some(1));
    assert_eq!(run_to_bv((3, 8), RTN, 4, true, (1, 0, 1)), Some(15));
}

/// One case per circuit width, in the smallest `eb = 2` format where z3's
/// narrow width wraps it (each fails with that one width put back to z3's):
/// - the unpack's count: `(2,6)`'s smallest subnormal has 5 leading zeros,
///   which 2 bits read as 1;
/// - `fp.add`: `(1 + 2^-11) - 1` in `(2,12)` cancels to a significand with 12
///   leading zeros, which 4 signed bits read as -4 (the result is `2^-11`, the
///   smallest subnormal);
/// - `fp.div`: in `(2,9)`, the smallest subnormal `2^-8` over the largest
///   finite value has exponent -10, below 4 signed bits;
/// - `fp.rem`: a remainder of `(2,7)` subnormals;
/// - `fp.roundToIntegral`: `(2,10)`'s smallest subnormal has exponent -9;
/// - `fp.to_ubv`/`fp.to_sbv`: `(2,10)`'s smallest subnormal has exponent -9,
///   which 4 signed bits read as 7 (the value as `2^7`);
/// - `fp.sqrt`'s rounded exponent: in `(2,17)` the square root of the
///   subnormal `2^-9` is a subnormal, and `fp_round`'s
///   `t = exp + 1 - lz - e_min` from its halved exponent reaches below what
///   `eb + 2 = 4` bits hold (`round_width` gives 6; round 2's verifier,
///   mutant `W6b`: a wrong `unsat` end to end);
/// - FP to FP, the work width: `(2,20)`'s `-2^-17` and `(2,10)`'s `2^-9` have
///   source exponents -17 and -9, which `max(eb, teb) + 2 = 4` bits wrap
///   before the clamp (mutant `W10a`: wrong `unsat`s end to end).
#[test]
fn each_circuit_width_holds_its_format() {
    use RoundingMode::{RNA, RNE, RTP, RTZ};
    // The unpack's leading-zero count (`unpack_lz_width`).
    assert_eq!(
        run((2, 6), "mul", RNE, &[(0, 0, 1), (0, 1, 0)]),
        expect((0, 0, 1))
    );
    // `add_exponent_width`.
    assert_eq!(
        run((2, 12), "add", RNE, &[(0, 1, 1), (1, 1, 0)]),
        expect((0, 0, 1))
    );
    // `div_exponent_width`: below half the smallest subnormal.
    assert_eq!(
        run((2, 9), "div", RTP, &[(0, 0, 1), (0, 2, 255)]),
        expect((0, 0, 1))
    );
    assert_eq!(
        run((2, 9), "div", RNE, &[(0, 0, 1), (0, 2, 255)]),
        expect((0, 0, 0))
    );
    // `round_width`'s upper bound `sb + 4` (the leading-zero count against
    // the cap; the 2026-09-28 verifier's `W13`, caught only by the exhaustive
    // audit): two `(2,6)` subnormals, 2^-5 / (3 * 2^-5) = 1/3, is the
    // subnormal 11 * 2^-5 under RNE and RTP; in 4 bits it read as +0 and the
    // smallest subnormal.
    assert_eq!(
        run((2, 6), "div", RNE, &[(0, 0, 1), (0, 0, 3)]),
        expect((0, 0, 11))
    );
    assert_eq!(
        run((2, 6), "div", RTP, &[(0, 0, 1), (0, 0, 3)]),
        expect((0, 0, 11))
    );
    // `rem_exponent_width`: the remainder of two `(2,7)` subnormals rounds at
    // the divisor's exponent, where a 6-leading-zero candidate wraps 4 bits.
    assert_eq!(
        run((2, 7), "rem", RNE, &[(0, 0, 2), (0, 0, 13)]),
        expect((0, 0, 2))
    );
    assert_eq!(
        run((2, 7), "rem", RNE, &[(1, 0, 52), (0, 0, 5)]),
        expect((1, 0, 2))
    );
    // `round_to_integral_exponent_width`.
    assert_eq!(run((2, 10), "rti", RTP, &[(0, 0, 1)]), expect((0, 1, 0)));
    // `to_bv_exponent_width`.
    assert_eq!(run_to_bv((2, 10), RTP, 16, false, (0, 0, 1)), Some(1));
    assert_eq!(
        run_to_bv((2, 10), RoundingMode::RTN, 16, true, (1, 0, 1)),
        Some(0xffff)
    );
    // `sqrt_exponent_widths`' rounded width: sqrt(2^-9) = 2^-4.5 in `(2,17)`,
    // a subnormal result (2896 or 2897 units of `2^-16`).
    assert_eq!(
        run((2, 17), "sqrt", RNE, &[(0, 0, 128)]),
        expect((0, 0, 2896))
    );
    assert_eq!(
        run((2, 17), "sqrt", RTP, &[(0, 0, 128)]),
        expect((0, 0, 2897))
    );
    assert_eq!(
        run((2, 17), "sqrt", RTZ, &[(0, 0, 128)]),
        expect((0, 0, 2896))
    );
    // `fp_conversion_widths`' work width: both lie below half the target's
    // smallest subnormal, so they round to a zero of their sign.
    assert_eq!(
        run_convert((2, 20), (2, 5), RTP, (1, 0, 4)),
        expect((1, 0, 0))
    );
    assert_eq!(
        run_convert((2, 10), (2, 3), RNA, (0, 0, 1)),
        expect((0, 0, 0))
    );
}

/// `(_ to_fp eb sb)` / `to_fp_unsigned` of a bitvector: the exponent starts
/// at `bv_sz - 2`, which z3's `eb + 2` bits did not hold for a small format
/// and a wide integer (4 bits against 22 in `(2,3)` from 24 bits). The
/// conversion audit of the 2026-09-24 fp-strings fix-up found 1,235 of 5,100
/// results wrong, among them a wrong `unsat` end to end (`fbvA`: z3 `sat`).
#[test]
fn integer_conversion_holds_the_integer_width() {
    use RoundingMode::{RNE, RTP, RTZ};
    // The 24-bit 1 is 1.0 (was +0).
    assert_eq!(run_from_int((2, 3), false, RNE, 24, 1), expect((0, 1, 0)));
    // The 16-bit -32768 overflows to -oo.
    assert_eq!(
        run_from_int((2, 3), true, RNE, 16, 0x8000),
        expect((1, 3, 0))
    );
    // 2^64 - 1 toward zero is the largest finite `(4,5)` value, 248.
    assert_eq!(
        run_from_int((4, 5), false, RTZ, 64, u64::MAX),
        expect((0, 14, 15))
    );
    // The 64-bit -1 is -1.0.
    assert_eq!(
        run_from_int((4, 5), true, RNE, 64, u64::MAX),
        expect((1, 7, 0))
    );
    // 100 toward +oo overflows `(3,5)` (largest finite 15.5).
    assert_eq!(run_from_int((3, 5), true, RTP, 32, 100), expect((0, 7, 0)));
    // Ordinary formats from ordinary widths keep z3's `eb + 2`.
    for (eb, sb, bv) in [(5, 11, 32), (8, 24, 64), (11, 53, 64), (15, 113, 128)] {
        assert_eq!(
            FpSolver::int_conversion_exponent_width(eb, sb, bv),
            eb + 2,
            "({eb},{sb}) from {bv} bits"
        );
    }
}

/// Every ordinary format keeps z3's widths, so its encoding is unchanged;
/// so does the corpus's small format `(3,5)`, except in `fp.fma`.
#[test]
fn ordinary_formats_keep_the_narrow_widths() {
    let narrow = |eb: usize, sb: usize| {
        [
            FpSolver::add_exponent_width(eb, sb),
            FpSolver::mul_exponent_width(eb, sb),
            FpSolver::div_exponent_width(eb, sb),
            FpSolver::rem_exponent_width(eb, sb),
            FpSolver::round_to_integral_exponent_width(eb, sb),
            FpSolver::to_bv_exponent_width(eb, sb),
            FpSolver::sqrt_exponent_widths(eb, sb).1,
        ]
        .iter()
        .all(|&w| w == eb + 2)
            && FpSolver::sqrt_exponent_widths(eb, sb).0 == eb + 1
            && FpSolver::unpack_lz_width(eb, sb) == eb
    };
    let ordinary = [(5, 11), (8, 24), (11, 53), (15, 64), (15, 113)];
    for (eb, sb) in ordinary {
        assert!(narrow(eb, sb), "({eb},{sb})");
        assert_eq!(FpSolver::fma_exponent_width(eb, sb), eb + 2, "({eb},{sb})");
        assert!(FpSolver::bits_to_hold((sb + 2) as u64) <= eb, "({eb},{sb})");
        for (teb, tsb) in ordinary {
            assert_eq!(
                FpSolver::fp_conversion_widths(eb, sb, teb, tsb),
                (eb.max(teb) + 2, teb + 2),
                "({eb},{sb}) to ({teb},{tsb})"
            );
        }
    }
    assert!(narrow(3, 5));
    assert_eq!(FpSolver::fma_exponent_width(3, 5), 6);
    // Where z3's widths wrap, the circuits widen.
    assert!(FpSolver::fma_exponent_width(2, 3) > 4);
    assert!(FpSolver::unpack_lz_width(2, 5) > 2);
    assert!(FpSolver::sqrt_exponent_widths(3, 8).0 > 4);
    assert!(FpSolver::fp_conversion_widths(5, 11, 2, 10).1 > 4);
}
