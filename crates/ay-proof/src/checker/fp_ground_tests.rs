// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for the exact IEEE-754 kernel behind `TheoryLemmaKind::FpGroundEval`.
//!
//! The NEGATIVE tests are the load-bearing ones. This validator's only job is
//! to refuse a clause that is not valid; a bug that makes it accept one is a
//! false-UNSAT, so every family below pins both a true instance (accepted) and
//! a near-miss (rejected).

use super::*;
use ay_core::BitVecSort;

// ---------------------------------------------------------------------------
// Kernel-level helpers
// ---------------------------------------------------------------------------

/// Float32.
const F32: (u32, u32) = (8, 24);
/// Float16.
const F16: (u32, u32) = (5, 11);

fn f32_bits(bits: u64) -> Fp {
    Fp::from_bits(&BigInt::from(bits), F32.0, F32.1).expect("valid Float32 pattern")
}

fn f16_bits(bits: u64) -> Fp {
    Fp::from_bits(&BigInt::from(bits), F16.0, F16.1).expect("valid Float16 pattern")
}

fn raw_bits(value: &Fp) -> u64 {
    (u64::from(value.sign) << (value.eb + value.sb - 1))
        | (value.exponent << (value.sb - 1))
        | value.significand
}

fn rational(numerator: i64, denominator: i64) -> BigRational {
    BigRational::new(BigInt::from(numerator), BigInt::from(denominator))
}

// ---------------------------------------------------------------------------
// Rounding kernel
// ---------------------------------------------------------------------------

#[test]
fn rounds_one_third_to_float32_rne() {
    // 1/3 in Float32 is 0x3EAAAAAB (the RNE result rounds the tail up).
    let value = round_rational(&rational(1, 3), false, F32.0, F32.1, Rm::Rne).expect("rounds");
    assert_eq!(raw_bits(&value), 0x3EAA_AAAB);
    // Toward zero the same value truncates to 0x3EAAAAAA.
    let toward_zero =
        round_rational(&rational(1, 3), false, F32.0, F32.1, Rm::Rtz).expect("rounds");
    assert_eq!(raw_bits(&toward_zero), 0x3EAA_AAAA);
}

#[test]
fn rounds_one_tenth_to_the_canonical_float32_encoding() {
    let value = round_rational(&rational(1, 10), false, F32.0, F32.1, Rm::Rne).expect("rounds");
    assert_eq!(raw_bits(&value), 0x3DCC_CCCD);
}

#[test]
fn round_to_nearest_even_breaks_exact_ties_to_even() {
    // 1 + 1/2 ulp is an exact tie in Float32: 1 + 2^-24. The even neighbour is
    // 1.0 itself (significand 0), so RNE keeps 1.0 while RNA rounds away.
    let tie = BigRational::one() + scale_by_pow2(&BigRational::one(), -24).expect("scale");
    let nearest_even = round_rational(&tie, false, F32.0, F32.1, Rm::Rne).expect("rounds");
    assert_eq!(raw_bits(&nearest_even), 0x3F80_0000);
    let nearest_away = round_rational(&tie, false, F32.0, F32.1, Rm::Rna).expect("rounds");
    assert_eq!(raw_bits(&nearest_away), 0x3F80_0001);
    // ...and one ulp higher the tie's even neighbour is the UPPER one.
    let upper_tie = BigRational::from_integer(BigInt::from(1))
        + scale_by_pow2(&BigRational::from_integer(BigInt::from(3)), -24).expect("scale");
    let upper = round_rational(&upper_tie, false, F32.0, F32.1, Rm::Rne).expect("rounds");
    assert_eq!(raw_bits(&upper), 0x3F80_0002);
}

#[test]
fn directed_modes_move_in_opposite_directions() {
    let third = rational(1, 3);
    let up = round_rational(&third, false, F32.0, F32.1, Rm::Rtp).expect("rounds");
    let down = round_rational(&third, false, F32.0, F32.1, Rm::Rtn).expect("rounds");
    assert_eq!(raw_bits(&up), 0x3EAA_AAAB);
    assert_eq!(raw_bits(&down), 0x3EAA_AAAA);
    // The negative value's directed rounding is mirrored.
    let negative = -third;
    let up_negative = round_rational(&negative, false, F32.0, F32.1, Rm::Rtp).expect("rounds");
    let down_negative = round_rational(&negative, false, F32.0, F32.1, Rm::Rtn).expect("rounds");
    assert_eq!(raw_bits(&up_negative), 0xBEAA_AAAA);
    assert_eq!(raw_bits(&down_negative), 0xBEAA_AAAB);
}

#[test]
fn overflow_follows_the_ieee_rule_per_mode() {
    // Twice the largest finite Float16 overflows.
    let huge = BigRational::from_integer(BigInt::from(1_000_000));
    let nearest = round_rational(&huge, false, F16.0, F16.1, Rm::Rne).expect("rounds");
    assert!(nearest.is_infinite() && !nearest.sign);
    let toward_zero = round_rational(&huge, false, F16.0, F16.1, Rm::Rtz).expect("rounds");
    assert_eq!(raw_bits(&toward_zero), 0x7BFF);
    let toward_negative = round_rational(&huge, false, F16.0, F16.1, Rm::Rtn).expect("rounds");
    assert_eq!(raw_bits(&toward_negative), 0x7BFF);
    let negative_huge = -huge;
    let negative_nearest =
        round_rational(&negative_huge, false, F16.0, F16.1, Rm::Rne).expect("rounds");
    assert!(negative_nearest.is_infinite() && negative_nearest.sign);
    let negative_up = round_rational(&negative_huge, false, F16.0, F16.1, Rm::Rtp).expect("rounds");
    assert_eq!(raw_bits(&negative_up), 0xFBFF);
}

#[test]
fn subnormals_and_underflow_round_exactly() {
    // The smallest Float16 subnormal is 2^-24; half of it ties to even = zero.
    let smallest = scale_by_pow2(&BigRational::one(), -24).expect("scale");
    let exact = round_rational(&smallest, false, F16.0, F16.1, Rm::Rne).expect("rounds");
    assert_eq!(raw_bits(&exact), 0x0001);
    let half = scale_by_pow2(&BigRational::one(), -25).expect("scale");
    let ties_to_even = round_rational(&half, false, F16.0, F16.1, Rm::Rne).expect("rounds");
    assert!(ties_to_even.is_zero() && !ties_to_even.sign);
    let ties_away = round_rational(&half, false, F16.0, F16.1, Rm::Rna).expect("rounds");
    assert_eq!(raw_bits(&ties_away), 0x0001);
    // Rounding a tiny NEGATIVE value toward zero keeps the sign on the zero.
    let tiny_negative = -scale_by_pow2(&BigRational::one(), -40).expect("scale");
    let signed_zero = round_rational(&tiny_negative, false, F16.0, F16.1, Rm::Rtz).expect("rounds");
    assert!(signed_zero.is_zero() && signed_zero.sign);
}

#[test]
fn rounding_up_across_the_subnormal_boundary_makes_the_smallest_normal() {
    // Just under the smallest Float16 normal (2^-14), rounding up must produce
    // exponent field 1 with a zero significand, not a malformed subnormal.
    let just_under = scale_by_pow2(&BigRational::one(), -14).expect("scale")
        - scale_by_pow2(&BigRational::one(), -30).expect("scale");
    let value = round_rational(&just_under, false, F16.0, F16.1, Rm::Rtp).expect("rounds");
    assert_eq!(raw_bits(&value), 0x0400);
}

// ---------------------------------------------------------------------------
// Arithmetic
// ---------------------------------------------------------------------------

#[test]
fn zero_and_infinity_arithmetic_follows_ieee() {
    let positive_zero = Fp::zero(false, F32.0, F32.1).expect("zero");
    let negative_zero = Fp::zero(true, F32.0, F32.1).expect("zero");
    let infinity = Fp::infinity(false, F32.0, F32.1).expect("inf");

    assert!(fp_add(Rm::Rne, &positive_zero, &positive_zero)
        .expect("add")
        .is_zero());
    // (+0) + (-0) is +0 in every mode but roundTowardNegative.
    let mixed = fp_add(Rm::Rne, &positive_zero, &negative_zero).expect("add");
    assert!(mixed.is_zero() && !mixed.sign);
    let mixed_down = fp_add(Rm::Rtn, &positive_zero, &negative_zero).expect("add");
    assert!(mixed_down.is_zero() && mixed_down.sign);

    assert!(fp_mul(Rm::Rne, &infinity, &infinity)
        .expect("mul")
        .is_infinite());
    assert!(fp_mul(Rm::Rne, &infinity, &positive_zero)
        .expect("mul")
        .is_nan());
    assert!(fp_add(Rm::Rne, &infinity, &infinity.negated())
        .expect("add")
        .is_nan());
}

#[test]
fn fma_rounds_once_and_signs_its_exact_zero_correctly() {
    let one = f16_bits(0x3C00);
    let minus_one = f16_bits(0xBC00);
    // 1*1 + (-1) cancels exactly: +0 under RNE, -0 under RTN.
    let nearest = fp_fma(Rm::Rne, &one, &one, &minus_one).expect("fma");
    assert!(nearest.is_zero() && !nearest.sign);
    let toward_negative = fp_fma(Rm::Rtn, &one, &one, &minus_one).expect("fma");
    assert!(toward_negative.is_zero() && toward_negative.sign);

    // A single rounding: 1 + 2^-24 + 2^-24 in Float32 rounds UP to 1+2^-23,
    // where two separate roundings would each vanish and leave 1.0.
    let one32 = f32_bits(0x3F80_0000);
    let tiny = f32_bits(0x3380_0000); // 2^-24
    let fused = fp_fma(Rm::Rne, &tiny, &f32_bits(0x4000_0000), &one32).expect("fma");
    assert_eq!(raw_bits(&fused), 0x3F80_0001);
}

#[test]
fn sqrt_is_correctly_rounded_and_keeps_the_sign_of_zero() {
    // sqrt(4) = 2 exactly.
    let four = f32_bits(0x4080_0000);
    assert_eq!(
        raw_bits(&fp_sqrt(Rm::Rne, &four).expect("sqrt")),
        0x4000_0000
    );
    // sqrt(2) = 1.41421356237... sits 0.20 ulp above 0x3FB504F3, so nearest
    // and toward-zero agree while toward-positive takes the neighbour above.
    let two = f32_bits(0x4000_0000);
    assert_eq!(
        raw_bits(&fp_sqrt(Rm::Rne, &two).expect("sqrt")),
        0x3FB5_04F3
    );
    assert_eq!(
        raw_bits(&fp_sqrt(Rm::Rtz, &two).expect("sqrt")),
        0x3FB5_04F3
    );
    assert_eq!(
        raw_bits(&fp_sqrt(Rm::Rtp, &two).expect("sqrt")),
        0x3FB5_04F4
    );
    let negative_zero = Fp::zero(true, 11, 53).expect("zero");
    let root = fp_sqrt(Rm::Rne, &negative_zero).expect("sqrt");
    assert!(root.is_zero() && root.sign);
    let negative_one = f32_bits(0xBF80_0000);
    assert!(fp_sqrt(Rm::Rne, &negative_one).expect("sqrt").is_nan());
}

#[test]
fn conversions_from_bitvector_integers_are_exact() {
    // Signed -1 over 32 bits is -1.0f.
    let signed = signed_value(&BigInt::from(0xFFFF_FFFFu64), 32).expect("signed");
    assert_eq!(signed, BigInt::from(-1));
    let converted = round_rational(
        &BigRational::from_integer(signed),
        false,
        F32.0,
        F32.1,
        Rm::Rne,
    )
    .expect("rounds");
    assert_eq!(raw_bits(&converted), 0xBF80_0000);
    // Unsigned the SAME pattern is 2^32 - 1, which rounds to 2^32.
    let unsigned = round_rational(
        &BigRational::from_integer(BigInt::from(0xFFFF_FFFFu64)),
        false,
        F32.0,
        F32.1,
        Rm::Rne,
    )
    .expect("rounds");
    assert_eq!(raw_bits(&unsigned), 0x4F80_0000);
}

// ---------------------------------------------------------------------------
// Differential validation against the hardware IEEE-754 unit
// ---------------------------------------------------------------------------
//
// The kernel's own tests can only pin the cases their author thought of. IEEE
// 754 arithmetic in `roundNearestTiesToEven` is EXACTLY what `f32`/`f64`
// hardware computes, so the CPU is an independent oracle for the RNE lane:
// millions of random operands, including subnormals, infinities, NaNs and the
// overflow boundary, compared bit for bit. A rounding bug that survives this
// would have to be one the silicon shares.

/// Deterministic xorshift64* stream — no `rand` dependency, reproducible runs.
struct Prng(u64);

impl Prng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 >> 12;
        self.0 ^= self.0 << 25;
        self.0 ^= self.0 >> 27;
        self.0.wrapping_mul(0x2545_F491_4F6C_DD1D)
    }

    /// A bit pattern biased toward the interesting corners of the format.
    fn next_f32_bits(&mut self) -> u32 {
        let raw = self.next();
        match raw % 8 {
            // Subnormals and values near zero.
            0 => (raw >> 32) as u32 & 0x807F_FFFF,
            // Values near the overflow boundary.
            1 => ((raw >> 32) as u32 & 0x807F_FFFF) | 0x7F00_0000,
            // Exact small integers.
            2 => f32::from(((raw >> 32) as i16) / 128).to_bits(),
            _ => (raw >> 32) as u32,
        }
    }
}

fn f32_from_fp(value: &Fp) -> f32 {
    assert_eq!((value.eb, value.sb), F32);
    f32::from_bits(u32::try_from(raw_bits(value)).expect("Float32 fits 32 bits"))
}

fn fp_from_f32(value: f32) -> Fp {
    f32_bits(u64::from(value.to_bits()))
}

/// Hardware and kernel agree, treating every NaN as the one abstract NaN.
fn assert_same_f32(kernel: &Fp, hardware: f32, what: &str) {
    let kernel_value = f32_from_fp(kernel);
    if hardware.is_nan() {
        assert!(
            kernel.is_nan(),
            "{what}: hardware NaN, kernel {kernel_value}"
        );
        return;
    }
    assert!(
        !kernel.is_nan(),
        "{what}: kernel NaN, hardware {hardware:?}"
    );
    assert_eq!(
        kernel_value.to_bits(),
        hardware.to_bits(),
        "{what}: kernel {kernel_value:?} vs hardware {hardware:?}"
    );
}

#[test]
fn rne_float32_arithmetic_matches_the_hardware_unit() {
    let mut prng = Prng(0x9E37_79B9_7F4A_7C15);
    for _ in 0..40_000 {
        let left = f32::from_bits(prng.next_f32_bits());
        let right = f32::from_bits(prng.next_f32_bits());
        let (a, b) = (fp_from_f32(left), fp_from_f32(right));
        assert_same_f32(
            &fp_add(Rm::Rne, &a, &b).expect("add"),
            left + right,
            "fp.add",
        );
        assert_same_f32(
            &fp_add(Rm::Rne, &a, &b.negated()).expect("sub"),
            left - right,
            "fp.sub",
        );
        assert_same_f32(
            &fp_mul(Rm::Rne, &a, &b).expect("mul"),
            left * right,
            "fp.mul",
        );
        assert_same_f32(
            &fp_div(Rm::Rne, &a, &b).expect("div"),
            left / right,
            "fp.div",
        );
        assert_same_f32(&fp_sqrt(Rm::Rne, &a).expect("sqrt"), left.sqrt(), "fp.sqrt");
    }
}

#[test]
fn rne_float32_fma_matches_the_hardware_fused_unit() {
    let mut prng = Prng(0xDEAD_BEEF_1234_5678);
    for _ in 0..30_000 {
        let x = f32::from_bits(prng.next_f32_bits());
        let y = f32::from_bits(prng.next_f32_bits());
        let z = f32::from_bits(prng.next_f32_bits());
        let kernel =
            fp_fma(Rm::Rne, &fp_from_f32(x), &fp_from_f32(y), &fp_from_f32(z)).expect("fma");
        assert_same_f32(&kernel, x.mul_add(y, z), "fp.fma");
    }
}

#[test]
fn rne_conversions_match_the_hardware_unit() {
    let mut prng = Prng(0x0BAD_C0DE_F00D_1111);
    for _ in 0..40_000 {
        let raw = prng.next();
        let signed = raw as i32;
        let unsigned = raw as u32;
        let signed_kernel = round_rational(
            &BigRational::from_integer(BigInt::from(signed)),
            false,
            F32.0,
            F32.1,
            Rm::Rne,
        )
        .expect("signed conversion");
        assert_same_f32(&signed_kernel, signed as f32, "to_fp (signed)");
        let unsigned_kernel = round_rational(
            &BigRational::from_integer(BigInt::from(unsigned)),
            false,
            F32.0,
            F32.1,
            Rm::Rne,
        )
        .expect("unsigned conversion");
        assert_same_f32(&unsigned_kernel, unsigned as f32, "to_fp_unsigned");

        // Float64 -> Float32 narrowing exercises the subnormal and overflow
        // paths of the rounding kernel through `fp_convert`.
        let wide = f64::from_bits(raw);
        if !wide.is_nan() && wide.is_finite() {
            let wide_fp = Fp::from_bits(&BigInt::from(raw), 11, 53).expect("Float64 pattern");
            let narrowed = fp_convert(Rm::Rne, &wide_fp, F32.0, F32.1).expect("narrowing");
            assert_same_f32(&narrowed, wide as f32, "to_fp (narrowing)");
        }
    }
}

#[test]
fn rne_float64_arithmetic_matches_the_hardware_unit() {
    let mut prng = Prng(0xC0FF_EE00_5EED_9999);
    let decode = |bits: u64| Fp::from_bits(&BigInt::from(bits), 11, 53).expect("Float64 pattern");
    let encode = |value: &Fp| f64::from_bits(raw_bits(value));
    for _ in 0..30_000 {
        let left_bits = prng.next();
        let right_bits = prng.next();
        let (left, right) = (f64::from_bits(left_bits), f64::from_bits(right_bits));
        let (a, b) = (decode(left_bits), decode(right_bits));
        for (kernel, hardware, what) in [
            (
                fp_add(Rm::Rne, &a, &b).expect("add"),
                left + right,
                "fp.add",
            ),
            (
                fp_mul(Rm::Rne, &a, &b).expect("mul"),
                left * right,
                "fp.mul",
            ),
            (
                fp_div(Rm::Rne, &a, &b).expect("div"),
                left / right,
                "fp.div",
            ),
            (fp_sqrt(Rm::Rne, &a).expect("sqrt"), left.sqrt(), "fp.sqrt"),
        ] {
            if hardware.is_nan() {
                assert!(kernel.is_nan(), "{what}: hardware NaN");
                continue;
            }
            assert!(
                !kernel.is_nan(),
                "{what}: kernel NaN, hardware {hardware:?}"
            );
            assert_eq!(
                encode(&kernel).to_bits(),
                hardware.to_bits(),
                "{what}: kernel {:?} vs hardware {hardware:?}",
                encode(&kernel)
            );
        }
    }
}

// ---------------------------------------------------------------------------
// Clause-level validation
// ---------------------------------------------------------------------------

fn fp_sort(format: (u32, u32)) -> Sort {
    Sort::FloatingPoint(format.0, format.1)
}

fn rounding_mode(terms: &mut TermStore, name: &str) -> TermId {
    terms.mk_app(
        Symbol::named(name),
        vec![],
        Sort::Uninterpreted("RoundingMode".to_string()),
    )
}

fn fp_literal(terms: &mut TermStore, name: &str, format: (u32, u32)) -> TermId {
    terms.mk_app(
        Symbol::indexed(name, vec![format.0, format.1]),
        vec![],
        fp_sort(format),
    )
}

fn fp_triple(
    terms: &mut TermStore,
    sign: u64,
    exponent: u64,
    significand: u64,
    format: (u32, u32),
) -> TermId {
    let sign = terms.mk_bitvec(BigInt::from(sign), 1);
    let exponent = terms.mk_bitvec(BigInt::from(exponent), format.0);
    let significand = terms.mk_bitvec(BigInt::from(significand), format.1 - 1);
    terms.mk_app(
        Symbol::named("fp"),
        vec![sign, exponent, significand],
        fp_sort(format),
    )
}

fn predicate(terms: &mut TermStore, name: &str, args: Vec<TermId>) -> TermId {
    terms.mk_app(Symbol::named(name), args, Sort::Bool)
}

fn binary_fp(terms: &mut TermStore, name: &str, args: Vec<TermId>, format: (u32, u32)) -> TermId {
    terms.mk_app(Symbol::named(name), args, fp_sort(format))
}

#[test]
fn accepts_the_ground_add_identity_and_rejects_its_negation() {
    let mut terms = TermStore::new();
    let rne = rounding_mode(&mut terms, "RNE");
    let zero = fp_literal(&mut terms, "+zero", F32);
    let sum = binary_fp(&mut terms, "fp.add", vec![rne, zero, zero], F32);
    let claim = predicate(&mut terms, "fp.eq", vec![sum, zero]);
    assert!(recognize_fp_ground_eval(&terms, &[claim]));
    assert!(validate_fp_ground_eval(&terms, ProofId(0), &[claim]).is_ok());

    // 0 + 0 is NOT nonzero: the negation must be refused.
    let negated = terms.mk_not(claim);
    assert!(!recognize_fp_ground_eval(&terms, &[negated]));
    assert!(validate_fp_ground_eval(&terms, ProofId(0), &[negated]).is_err());
}

#[test]
fn indexed_named_fp_builtins_fail_closed() {
    let mut terms = TermStore::new();
    let rne = rounding_mode(&mut terms, "RNE");
    let zero = fp_literal(&mut terms, "+zero", F32);
    let indexed_add = terms.mk_app(
        Symbol::indexed("fp.add", vec![0]),
        vec![rne, zero, zero],
        fp_sort(F32),
    );
    let forged_add = predicate(&mut terms, "fp.eq", vec![indexed_add, zero]);
    assert!(!recognize_fp_ground_eval(&terms, &[forged_add]));
    validate_fp_ground_eval(&terms, ProofId(0), &[forged_add])
        .expect_err("an indexed identifier named `fp.add` is not the named FP builtin");

    // Binding extraction is also identity-sensitive. Treating `(_ = 0)` as
    // core equality would substitute `x := +zero` and incorrectly make the
    // first literal below true without evaluating the forged second literal.
    let x = terms.mk_var("indexed_equality_x", fp_sort(F32));
    let is_zero = predicate(&mut terms, "fp.isZero", vec![x]);
    let indexed_equality = terms.mk_app(Symbol::indexed("=", vec![0]), vec![x, zero], Sort::Bool);
    let not_indexed_equality = terms.mk_not(indexed_equality);
    let forged_binding = [is_zero, not_indexed_equality];
    assert!(!recognize_fp_ground_eval(&terms, &forged_binding));
    validate_fp_ground_eval(&terms, ProofId(0), &forged_binding)
        .expect_err("an indexed identifier named `=` must not authorize an FP binding");
}

#[test]
fn accepts_infinity_times_zero_is_nan_and_rejects_the_near_miss() {
    let mut terms = TermStore::new();
    let rne = rounding_mode(&mut terms, "RNE");
    let infinity = fp_literal(&mut terms, "+oo", F32);
    let zero = fp_literal(&mut terms, "+zero", F32);
    let product = binary_fp(&mut terms, "fp.mul", vec![rne, infinity, zero], F32);
    let is_nan = predicate(&mut terms, "fp.isNaN", vec![product]);
    assert!(recognize_fp_ground_eval(&terms, &[is_nan]));

    // inf * inf is inf, NOT NaN.
    let square = binary_fp(&mut terms, "fp.mul", vec![rne, infinity, infinity], F32);
    let square_is_nan = predicate(&mut terms, "fp.isNaN", vec![square]);
    assert!(!recognize_fp_ground_eval(&terms, &[square_is_nan]));
}

#[test]
fn accepts_a_to_fp_reinterpretation_and_rejects_the_wrong_constant() {
    let mut terms = TermStore::new();
    let bits = terms.mk_bitvec(BigInt::from(0x3F80_0000u64), 32);
    let reinterpreted = terms.mk_app(
        Symbol::indexed("to_fp", vec![F32.0, F32.1]),
        vec![bits],
        fp_sort(F32),
    );
    let one = fp_triple(&mut terms, 0, 127, 0, F32);
    let claim = predicate(&mut terms, "fp.eq", vec![reinterpreted, one]);
    assert!(recognize_fp_ground_eval(&terms, &[claim]));

    let two = fp_triple(&mut terms, 0, 128, 0, F32);
    let wrong = predicate(&mut terms, "fp.eq", vec![reinterpreted, two]);
    assert!(!recognize_fp_ground_eval(&terms, &[wrong]));
}

#[test]
fn accepts_a_signed_bitvector_conversion_and_distinguishes_the_unsigned_reading() {
    let mut terms = TermStore::new();
    let rne = rounding_mode(&mut terms, "RNE");
    let pattern = terms.mk_bitvec(BigInt::from(0xFFFF_FFFFu64), 32);
    let signed = terms.mk_app(
        Symbol::indexed("to_fp", vec![F32.0, F32.1]),
        vec![rne, pattern],
        fp_sort(F32),
    );
    let unsigned = terms.mk_app(
        Symbol::indexed("to_fp_unsigned", vec![F32.0, F32.1]),
        vec![rne, pattern],
        fp_sort(F32),
    );
    // The two readings DISAGREE, so their equality is refutable...
    let agree = predicate(&mut terms, "fp.eq", vec![signed, unsigned]);
    let disagree = terms.mk_not(agree);
    assert!(recognize_fp_ground_eval(&terms, &[disagree]));
    // ...and claiming they agree is not.
    assert!(!recognize_fp_ground_eval(&terms, &[agree]));
}

#[test]
fn substitutes_clause_carried_ground_bindings() {
    // `(cl (not (= x 1.0)) (not (= y 2.0)) (not (fp.eq x y)))` is valid: under
    // both bindings `fp.eq 1.0 2.0` is false.
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", fp_sort(F32));
    let y = terms.mk_var("y", fp_sort(F32));
    let one = fp_triple(&mut terms, 0, 127, 0, F32);
    let two = fp_triple(&mut terms, 0, 128, 0, F32);
    let x_is_one = predicate(&mut terms, "=", vec![x, one]);
    let y_is_two = predicate(&mut terms, "=", vec![y, two]);
    let equal = predicate(&mut terms, "fp.eq", vec![x, y]);
    let clause = vec![
        terms.mk_not(x_is_one),
        terms.mk_not(y_is_two),
        terms.mk_not(equal),
    ];
    assert!(recognize_fp_ground_eval(&terms, &clause));

    // Bind `y` to 1.0 instead and the same clause is FALSIFIABLE (x = y = 1.0
    // satisfies every equality), so it must be refused.
    let y_is_one = predicate(&mut terms, "=", vec![y, one]);
    let falsifiable = vec![
        terms.mk_not(x_is_one),
        terms.mk_not(y_is_one),
        terms.mk_not(equal),
    ];
    assert!(!recognize_fp_ground_eval(&terms, &falsifiable));
}

#[test]
fn rejects_a_binding_whose_value_is_not_ground() {
    // `(cl (not (= x y)) (not (fp.eq x y)))` binds nothing (both sides are
    // variables) and is genuinely falsifiable, so it must be refused rather
    // than "substituted" into a tautology.
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", fp_sort(F32));
    let y = terms.mk_var("y", fp_sort(F32));
    let structural = predicate(&mut terms, "=", vec![x, y]);
    let ieee = predicate(&mut terms, "fp.eq", vec![x, y]);
    let clause = vec![terms.mk_not(structural), terms.mk_not(ieee)];
    assert!(!recognize_fp_ground_eval(&terms, &clause));
}

#[test]
fn enumerates_a_residual_boolean_variable() {
    // `(cl c (not (ite c (= one one) (= minus_one one))))` is valid: with
    // `c` false the `ite` selects a FALSE ground equality.
    let mut terms = TermStore::new();
    let condition = terms.mk_var("c", Sort::Bool);
    let one = fp_triple(&mut terms, 0, 15, 0, F16);
    let minus_one = fp_triple(&mut terms, 1, 15, 0, F16);
    let same = predicate(&mut terms, "=", vec![one, one]);
    let different = predicate(&mut terms, "=", vec![minus_one, one]);
    let selected = terms.mk_ite(condition, same, different);
    let clause = vec![condition, terms.mk_not(selected)];
    assert!(recognize_fp_ground_eval(&terms, &clause));

    // Dropping the `c` literal leaves a clause the `c = true` assignment
    // falsifies, so it must be refused.
    let without_guard = vec![terms.mk_not(selected)];
    assert!(!recognize_fp_ground_eval(&terms, &without_guard));
}

#[test]
fn enumerates_a_narrow_bitvector_variable() {
    // A subnormal Float16 with a SYMBOLIC sign bit is never zero.
    let mut terms = TermStore::new();
    let sign = terms.mk_var("s", Sort::BitVec(BitVecSort::new(1)));
    let exponent = terms.mk_bitvec(BigInt::from(0u64), 5);
    let significand = terms.mk_bitvec(BigInt::from(1u64), 10);
    let value = terms.mk_app(
        Symbol::named("fp"),
        vec![sign, exponent, significand],
        fp_sort(F16),
    );
    let is_zero = predicate(&mut terms, "fp.isZero", vec![value]);
    let clause = vec![terms.mk_not(is_zero)];
    assert!(recognize_fp_ground_eval(&terms, &clause));

    // The same construction IS subnormal for either sign, so claiming the
    // opposite must be refused.
    let is_subnormal = predicate(&mut terms, "fp.isSubnormal", vec![value]);
    let wrong = vec![terms.mk_not(is_subnormal)];
    assert!(!recognize_fp_ground_eval(&terms, &wrong));
}

#[test]
fn enumerates_one_float16_variable_but_refuses_two() {
    // A single Float16 fits the 16-bit enumeration budget: no value is both
    // strictly above and strictly below zero.
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", fp_sort(F16));
    let zero = fp_literal(&mut terms, "+zero", F16);
    let above = predicate(&mut terms, "fp.gt", vec![x, zero]);
    let below = predicate(&mut terms, "fp.lt", vec![x, zero]);
    let clause = vec![terms.mk_not(above), terms.mk_not(below)];
    assert!(recognize_fp_ground_eval(&terms, &clause));

    // Two Float16 variables exceed the budget and must fail CLOSED even though
    // the clause below happens to be valid.
    let y = terms.mk_var("y", fp_sort(F16));
    let x_above_y = predicate(&mut terms, "fp.gt", vec![x, y]);
    let y_above_x = predicate(&mut terms, "fp.gt", vec![y, x]);
    let wide = vec![terms.mk_not(x_above_y), terms.mk_not(y_above_x)];
    assert!(!recognize_fp_ground_eval(&terms, &wide));
}

#[test]
fn rejects_a_clause_with_no_floating_point_content() {
    let mut terms = TermStore::new();
    let p = terms.mk_var("p", Sort::Bool);
    let not_p = terms.mk_not(p);
    // A propositional tautology is valid, but it is not an FP lemma: the
    // hygiene gate keeps the exported rule name honest.
    assert!(!recognize_fp_ground_eval(&terms, &[p, not_p]));
}

#[test]
fn rejects_a_non_boolean_literal() {
    let mut terms = TermStore::new();
    let zero = fp_literal(&mut terms, "+zero", F32);
    assert!(!recognize_fp_ground_eval(&terms, &[zero]));
    assert!(validate_fp_ground_eval(&terms, ProofId(0), &[zero]).is_err());
    assert!(validate_fp_ground_eval(&terms, ProofId(0), &[]).is_err());
}

#[test]
fn rejects_an_unimplemented_operator() {
    // `fp.roundToIntegral` is deliberately absent from the kernel, so even a
    // genuinely valid clause over it fails closed.
    let mut terms = TermStore::new();
    let rne = rounding_mode(&mut terms, "RNE");
    let zero = fp_literal(&mut terms, "+zero", F32);
    let rounded = binary_fp(&mut terms, "fp.roundToIntegral", vec![rne, zero], F32);
    let claim = predicate(&mut terms, "fp.eq", vec![rounded, zero]);
    assert!(!recognize_fp_ground_eval(&terms, &[claim]));
}

#[test]
fn nan_is_not_fp_equal_to_itself_but_is_structurally_equal() {
    let mut terms = TermStore::new();
    let nan = fp_literal(&mut terms, "NaN", F32);
    let ieee = predicate(&mut terms, "fp.eq", vec![nan, nan]);
    let structural = predicate(&mut terms, "=", vec![nan, nan]);
    let not_ieee = terms.mk_not(ieee);
    assert!(recognize_fp_ground_eval(&terms, &[not_ieee]));
    assert!(recognize_fp_ground_eval(&terms, &[structural]));
    assert!(!recognize_fp_ground_eval(&terms, &[ieee]));
}

#[test]
fn signed_zeros_are_fp_equal_but_structurally_distinct() {
    let mut terms = TermStore::new();
    let positive = fp_literal(&mut terms, "+zero", F32);
    let negative = fp_literal(&mut terms, "-zero", F32);
    let ieee = predicate(&mut terms, "fp.eq", vec![positive, negative]);
    let structural = predicate(&mut terms, "=", vec![positive, negative]);
    let not_structural = terms.mk_not(structural);
    assert!(recognize_fp_ground_eval(&terms, &[ieee]));
    assert!(recognize_fp_ground_eval(&terms, &[not_structural]));
    assert!(!recognize_fp_ground_eval(&terms, &[structural]));
}

#[test]
fn real_to_fp_conversions_respect_the_rounding_mode() {
    // 1 + 1/4 ulp rounds UP under RTP and DOWN under RNE, so the two results
    // differ and a variable cannot equal both.
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", fp_sort(F32));
    let value = terms.mk_rational(rational(33_554_433, 33_554_432));
    let rtp = rounding_mode(&mut terms, "RTP");
    let rne = rounding_mode(&mut terms, "RNE");
    let up = terms.mk_app(
        Symbol::indexed("to_fp", vec![F32.0, F32.1]),
        vec![rtp, value],
        fp_sort(F32),
    );
    let nearest = terms.mk_app(
        Symbol::indexed("to_fp", vec![F32.0, F32.1]),
        vec![rne, value],
        fp_sort(F32),
    );
    let x_is_up = predicate(&mut terms, "=", vec![x, up]);
    let x_is_nearest = predicate(&mut terms, "=", vec![x, nearest]);
    let clause = vec![terms.mk_not(x_is_up), terms.mk_not(x_is_nearest)];
    assert!(recognize_fp_ground_eval(&terms, &clause));

    // Under RTZ the same value rounds the SAME way as RNE, so the analogous
    // clause is falsifiable and must be refused.
    let rtz = rounding_mode(&mut terms, "RTZ");
    let toward_zero = terms.mk_app(
        Symbol::indexed("to_fp", vec![F32.0, F32.1]),
        vec![rtz, value],
        fp_sort(F32),
    );
    let x_is_toward_zero = predicate(&mut terms, "=", vec![x, toward_zero]);
    let falsifiable = vec![terms.mk_not(x_is_toward_zero), terms.mk_not(x_is_nearest)];
    assert!(!recognize_fp_ground_eval(&terms, &falsifiable));
}

/// A BARE-named FP special literal must never be evaluated as the IEEE
/// constant, and an indexed one whose indices disagree with its sort must not
/// either.
///
/// `ay-frontend` classifies `+zero`/`-zero`/`+oo`/`-oo`/`NaN` `IndexedOnly`:
/// only `(_ NaN eb sb)` is theory syntax, while the BARE spelling stays an
/// ordinary user-declarable identity
/// (`declaration_requires_private_core_identity` leaves it alone, so a
/// declaration keeps that exact surface name in the core term DAG). Matching on
/// `sym.name()` alone would therefore hand IEEE semantics to a declared symbol.
/// This validator destructures `Symbol::Indexed` and pins the indices to the
/// recorded `Sort::FloatingPoint`, so the check is LOCAL rather than resting on
/// the frontend minting declared nullary symbols as `TermData::Var`.
#[test]
fn bare_named_fp_special_literals_are_not_ieee_constants() {
    // Control: the genuine indexed literal still certifies `(fp.isNaN NaN)`.
    let mut terms = TermStore::new();
    let nan = fp_literal(&mut terms, "NaN", F32);
    let claim = predicate(&mut terms, "fp.isNaN", vec![nan]);
    validate_fp_ground_eval(&terms, ProofId(0), &[claim])
        .expect("the indexed `(_ NaN 8 24)` literal must still evaluate");

    // A BARE `NaN` of the same sort is an ordinary symbol, so nothing about it
    // is ground and the lemma must fail closed.
    let mut terms = TermStore::new();
    let bare = terms.mk_app(Symbol::named("NaN"), vec![], fp_sort(F32));
    let claim = predicate(&mut terms, "fp.isNaN", vec![bare]);
    validate_fp_ground_eval(&terms, ProofId(0), &[claim]).expect_err(
        "a bare `NaN` application is a user-declarable symbol, not the IEEE \
         quiet NaN; certifying `(fp.isNaN NaN)` about it would be a wrong `unsat`",
    );

    // An indexed literal whose indices disagree with its recorded format is a
    // malformed lookalike and must also fail closed.
    let mut terms = TermStore::new();
    let mismatched = terms.mk_app(
        Symbol::indexed("+zero", vec![F16.0, F16.1]),
        vec![],
        fp_sort(F32),
    );
    let claim = predicate(&mut terms, "fp.isZero", vec![mismatched]);
    validate_fp_ground_eval(&terms, ProofId(0), &[claim])
        .expect_err("indexed FP-literal widths must agree with the term's sort");
}
