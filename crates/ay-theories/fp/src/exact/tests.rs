// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Two independent oracles for [`super`]: the bit-blasted circuits, compared
//! on every operand of a small format under every rounding mode, and the host's
//! IEEE 754 binary64/binary32 arithmetic (round-to-nearest-even, correctly
//! rounded for `+ - * /`, `sqrt` and `mul_add`) on pseudo-random operands.

use super::*;
use crate::tests_support::{extract_fp, solve_fp_clauses};
use crate::{FpDecomposed, FpSolver};
use ay_core::{CnfClause, Sort, TermStore};

const MODES: [RoundingMode; 5] = [
    RoundingMode::RNE,
    RoundingMode::RNA,
    RoundingMode::RTP,
    RoundingMode::RTN,
    RoundingMode::RTZ,
];

/// Every bit pattern of `(eb, sb)` as `(sign, exponent, significand)`.
fn patterns(eb: u32, sb: u32) -> Vec<(bool, u64, u128)> {
    let mut all = Vec::new();
    for sign in [false, true] {
        for e in 0..(1u64 << eb) {
            for m in 0..(1u128 << (sb - 1)) {
                all.push((sign, e, m));
            }
        }
    }
    all
}

fn value(eb: u32, sb: u32, (s, e, m): (bool, u64, u128)) -> FpModelValue {
    FpModelValue::from_fields(s, e, m, eb, sb).expect("a small format is in the carrier")
}

fn pin(solver: &mut FpSolver<'_>, fp: &FpDecomposed, (s, e, m): (bool, u64, u128)) {
    solver.add_clause(CnfClause::unit(if s { fp.sign } else { -fp.sign }));
    for (i, &bit) in fp.exponent.iter().enumerate() {
        solver.add_clause(CnfClause::unit(if (e >> i) & 1 == 1 { bit } else { -bit }));
    }
    for (i, &bit) in fp.significand.iter().enumerate() {
        solver.add_clause(CnfClause::unit(if (m >> i) & 1 == 1 { bit } else { -bit }));
    }
}

/// The circuit's value of `op` on pinned operands.
fn circuit(
    (eb, sb): (u32, u32),
    op: &str,
    rm: RoundingMode,
    operands: &[(bool, u64, u128)],
) -> FpModelValue {
    let mut terms = TermStore::new();
    let vars: Vec<_> = ["x", "y", "z"]
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
        "sub" => solver.make_sub(&fps[0], &fps[1], rm),
        "mul" => solver.make_mul(&fps[0], &fps[1], rm),
        "div" => solver.make_div(&fps[0], &fps[1], rm),
        "fma" => solver.make_fma(&fps[0], &fps[1], &fps[2], rm),
        "sqrt" => solver.make_sqrt(&fps[0], rm),
        "rem" => solver.make_rem(&fps[0], &fps[1]),
        "rti" => solver.make_round_to_integral(&fps[0], rm),
        other => panic!("no such op {other}"),
    };
    assert!(!solver.has_encoding_gap(), "{op} in ({eb},{sb}) declined");
    let model = solve_fp_clauses(&solver);
    let (s, e, m) = extract_fp(&model, &result);
    value(eb, sb, (s, e, u128::from(m)))
}

fn exact_op(op: &str, rm: RoundingMode, args: &[FpModelValue]) -> Option<FpModelValue> {
    match op {
        "add" => add(rm, &args[0], &args[1]),
        "sub" => sub(rm, &args[0], &args[1]),
        "mul" => mul(rm, &args[0], &args[1]),
        "div" => div(rm, &args[0], &args[1]),
        "fma" => fma(rm, &args[0], &args[1], &args[2]),
        "sqrt" => sqrt(rm, &args[0]),
        "rem" => rem(&args[0], &args[1]),
        "rti" => round_to_integral(rm, &args[0]),
        other => panic!("no such op {other}"),
    }
}

/// Compare the circuit and the exact value on `operands`; returns whether the
/// exact side defined the result.
fn agree(format: (u32, u32), op: &str, rm: RoundingMode, operands: &[(bool, u64, u128)]) -> bool {
    let values: Vec<_> = operands
        .iter()
        .map(|&p| value(format.0, format.1, p))
        .collect();
    let Some(expected) = exact_op(op, rm, &values) else {
        return false;
    };
    let got = circuit(format, op, rm, operands);
    assert!(
        same_element(&got, &expected) == Some(true),
        "{op} {rm:?} {values:?} in {format:?}: circuit {got:?}, exact {expected:?}"
    );
    true
}

#[test]
fn every_binary_operation_of_a_two_bit_exponent_format_matches_the_circuits() {
    let format = (2, 3);
    let all = patterns(format.0, format.1);
    let mut compared = 0;
    for op in ["add", "sub", "mul", "div", "rem"] {
        for rm in MODES {
            if op == "rem" && rm != RoundingMode::RNE {
                continue;
            }
            for &x in &all {
                for &y in &all {
                    compared += usize::from(agree(format, op, rm, &[x, y]));
                }
            }
        }
    }
    assert!(compared > 2_000, "only {compared} comparisons were defined");
}

#[test]
fn every_unary_operation_of_small_formats_matches_the_circuits() {
    for format in [(2, 3), (3, 4), (4, 3)] {
        for op in ["sqrt", "rti"] {
            for rm in MODES {
                for &x in &patterns(format.0, format.1) {
                    agree(format, op, rm, &[x]);
                }
            }
        }
    }
}

/// A deterministic xorshift stream, so a failure names its case.
struct Stream(u64);

impl Stream {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
}

#[test]
fn sampled_fma_and_wider_formats_match_the_circuits() {
    let mut stream = Stream(0x9E37_79B9_7F4A_7C15);
    for format in [(2, 3), (3, 4), (4, 5)] {
        let all = patterns(format.0, format.1);
        for _ in 0..400 {
            let pick = |s: &mut Stream| all[(s.next() % all.len() as u64) as usize];
            let (x, y, z) = (pick(&mut stream), pick(&mut stream), pick(&mut stream));
            let rm = MODES[(stream.next() % 5) as usize];
            agree(format, "fma", rm, &[x, y, z]);
            agree(format, "add", rm, &[x, y]);
            agree(format, "div", rm, &[x, y]);
        }
    }
}

fn f64_value(x: f64) -> FpModelValue {
    let bits = x.to_bits();
    let (s, e, m) = (
        bits >> 63 == 1,
        (bits >> 52) & 0x7ff,
        u128::from(bits & ((1 << 52) - 1)),
    );
    value(11, 53, (s, e, m))
}

fn f32_value(x: f32) -> FpModelValue {
    let bits = x.to_bits();
    let (s, e, m) = (
        bits >> 31 == 1,
        u64::from((bits >> 23) & 0xff),
        u128::from(bits & 0x7f_ffff),
    );
    value(8, 24, (s, e, m))
}

/// Operands that reach every class: random bit patterns (NaN, infinities,
/// subnormals and extreme exponents included) and ordinary magnitudes.
fn sample_f64(stream: &mut Stream) -> f64 {
    match stream.next() % 4 {
        0 => f64::from_bits(stream.next()),
        1 => (stream.next() % 2000) as f64 / 7.0 - 100.0,
        2 => f64::from_bits(stream.next() & 0x800f_ffff_ffff_ffff),
        _ => [0.0, -0.0, 1.0, 0.1, f64::MAX, f64::MIN_POSITIVE][(stream.next() % 6) as usize],
    }
}

#[test]
fn round_to_nearest_even_matches_hardware_binary64() {
    let mut stream = Stream(0x2545_F491_4F6C_DD1D);
    let rne = RoundingMode::RNE;
    for _ in 0..20_000 {
        let (x, y, z) = (
            sample_f64(&mut stream),
            sample_f64(&mut stream),
            sample_f64(&mut stream),
        );
        let (a, b, c) = (f64_value(x), f64_value(y), f64_value(z));
        let checks = [
            (add(rne, &a, &b), x + y),
            (sub(rne, &a, &b), x - y),
            (mul(rne, &a, &b), x * y),
            (div(rne, &a, &b), x / y),
            (sqrt(rne, &a), x.sqrt()),
            (fma(rne, &a, &b, &c), x.mul_add(y, z)),
        ];
        for (i, (exact, hardware)) in checks.into_iter().enumerate() {
            let exact = exact.expect("binary64 is computed");
            assert_eq!(
                same_element(&exact, &f64_value(hardware)),
                Some(true),
                "op {i} on {x:e}, {y:e}, {z:e}: exact {exact:?}, hardware {hardware:e}"
            );
        }
    }
}

#[test]
fn round_to_nearest_even_matches_hardware_binary32_and_narrowing() {
    let mut stream = Stream(0x5851_F42D_4C95_7F2D);
    let rne = RoundingMode::RNE;
    for _ in 0..20_000 {
        let x = f32::from_bits(stream.next() as u32);
        let y = f32::from_bits(stream.next() as u32);
        let wide = sample_f64(&mut stream);
        let (a, b) = (f32_value(x), f32_value(y));
        for (exact, hardware) in [
            (add(rne, &a, &b), x + y),
            (mul(rne, &a, &b), x * y),
            (div(rne, &a, &b), x / y),
            (sqrt(rne, &a), x.sqrt()),
            (to_fp_from_fp(rne, &f64_value(wide), 8, 24), wide as f32),
        ] {
            let exact = exact.expect("binary32 is computed");
            assert_eq!(
                same_element(&exact, &f32_value(hardware)),
                Some(true),
                "{x:e} {y:e} {wide:e}: exact {exact:?}, hardware {hardware:e}"
            );
        }
    }
}

#[test]
fn directed_modes_bracket_an_inexact_quotient() {
    let one = f64_value(1.0);
    let divisor = to_fp_from_rational(
        RoundingMode::RNE,
        &BigRational::new(8.into(), 5.into()),
        11,
        53,
    )
    .expect("8/5 rounds into binary64");
    let down = div(RoundingMode::RTN, &one, &divisor).expect("defined");
    let up = div(RoundingMode::RTP, &one, &divisor).expect("defined");
    let (down, up) = (
        to_real(&down).expect("finite"),
        to_real(&up).expect("finite"),
    );
    let exact = BigRational::from_integer(1.into()) / to_real(&divisor).expect("finite");
    assert!(down < exact && exact < up, "{down} < {exact} < {up}");
    assert_eq!(&up - &down, ops::two_to(-53), "one ulp apart in [0.5, 1)");
}

#[test]
fn unspecified_results_are_not_folded() {
    let (eb, sb) = (8, 24);
    let nan = FpModelValue::NaN { eb, sb };
    let pos_zero = FpModelValue::PosZero { eb, sb };
    let neg_zero = FpModelValue::NegZero { eb, sb };
    assert!(to_ubv(RoundingMode::RNE, &nan, 8).is_none());
    assert!(to_sbv(RoundingMode::RNE, &FpModelValue::PosInf { eb, sb }, 8).is_none());
    assert!(to_real(&nan).is_none());
    assert!(min(&pos_zero, &neg_zero).is_none());
    assert!(max(&neg_zero, &pos_zero).is_none());
    let three_halves = to_fp_from_rational(
        RoundingMode::RNE,
        &BigRational::new(3.into(), 2.into()),
        eb,
        sb,
    )
    .expect("1.5 is exact");
    assert_eq!(
        to_ubv(RoundingMode::RNE, &three_halves, 1),
        None,
        "2 needs two bits"
    );
    assert_eq!(
        to_ubv(RoundingMode::RTZ, &three_halves, 1),
        Some(BigInt::from(1))
    );
    let minus = neg(&three_halves).expect("defined");
    assert_eq!(
        to_sbv(RoundingMode::RTN, &minus, 2),
        Some(BigInt::from(2)),
        "-2 as two bits"
    );
    assert_eq!(to_sbv(RoundingMode::RTN, &minus, 1), None);
    assert_eq!(min(&nan, &pos_zero).map(|v| v.is_zero()), Some(true));
}

#[test]
fn formats_beyond_the_folding_envelope_decline() {
    assert!(Fmt::checked(21, 10).is_none());
    assert!(to_fp_from_rational(
        RoundingMode::RNE,
        &BigRational::from_integer(1.into()),
        21,
        10
    )
    .is_none());
    assert!(Fmt::checked(15, 113).is_some(), "binary128 is folded");
}
