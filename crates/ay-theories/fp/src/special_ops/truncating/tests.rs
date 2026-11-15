// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

mod ownership;

use ay_core::{CnfClause, TermStore};
use ay_sat::{Literal, SatResult, Solver};

use crate::{
    exact, FpBuiltEncoding, FpConstruction, FpDecomposed, FpModelValue, FpPrecision, FpSolver,
};

type Fields = (bool, u64, u128);

fn value(precision: FpPrecision, (sign, exponent, fraction): Fields) -> FpModelValue {
    FpModelValue::from_fields(
        sign,
        exponent,
        fraction,
        precision.exponent_bits(),
        precision.significand_bits(),
    )
    .expect("test fields fit the declared format")
}

fn operand(solver: &mut FpSolver<'_>, precision: FpPrecision, fields: Fields) -> FpDecomposed {
    let (sign, exponent, fraction) = fields;
    let yes = solver.const_true();
    let no = solver.const_false();
    let bit = |set| if set { yes } else { no };
    FpDecomposed {
        sign: bit(sign),
        exponent: (0..precision.exponent_bits())
            .map(|i| bit((exponent >> i) & 1 != 0))
            .collect(),
        significand: (0..precision.significand_bits() - 1)
            .map(|i| bit((fraction >> i) & 1 != 0))
            .collect(),
        precision,
    }
}

fn solve(built: &FpBuiltEncoding, extra: Option<CnfClause>) -> SatResult {
    let mut sat = Solver::new((built.cache.next_var - 1) as usize);
    for clause in built.clauses.iter().chain(extra.iter()) {
        sat.add_clause(
            clause
                .literals()
                .iter()
                .map(|&lit| Literal::from_dimacs(lit))
                .collect(),
        );
    }
    sat.solve().into_inner()
}

fn decoded(precision: FpPrecision, result: &FpDecomposed, model: &[bool]) -> FpModelValue {
    let bit = |lit: i32| {
        let index = usize::try_from(lit.unsigned_abs() - 1).expect("positive CNF index");
        let assigned = *model
            .get(index)
            .expect("every emitted literal has an assignment");
        if lit > 0 {
            assigned
        } else {
            !assigned
        }
    };
    let exponent = result
        .exponent
        .iter()
        .enumerate()
        .fold(0u64, |sum, (i, &lit)| sum | (u64::from(bit(lit)) << i));
    let fraction = result
        .significand
        .iter()
        .enumerate()
        .fold(0u128, |sum, (i, &lit)| sum | (u128::from(bit(lit)) << i));
    value(precision, (bit(result.sign), exponent, fraction))
}

fn encoding(
    terms: &TermStore,
    precision: FpPrecision,
    a: Fields,
    b: Fields,
) -> (FpBuiltEncoding, FpDecomposed) {
    let mut solver = FpSolver::new(terms);
    let x = operand(&mut solver, precision, a);
    let y = operand(&mut solver, precision, b);
    let mut healthy = |_| false;
    let mut attempt = FpConstruction::new(solver, &mut healthy).expect("healthy owner");
    let result = attempt
        .try_make_truncating_rem(&x, &y)
        .expect("healthy remainder");
    let built = attempt.finish().expect("complete encoding");
    assert!(!built.has_encoding_gap);
    assert!(built.pending_condition_links.is_empty());
    (built, result)
}

fn agrees(precision: FpPrecision, a: Fields, b: Fields) -> FpModelValue {
    let expected = exact::truncating_rem(&value(precision, a), &value(precision, b))
        .expect("matching admitted operands");
    let terms = TermStore::new();
    let (built, result) = encoding(&terms, precision, a, b);
    let SatResult::Sat(model) = solve(&built, None) else {
        panic!("complete deterministic remainder must admit the pinned operands");
    };
    let actual = decoded(precision, &result, &model);
    assert_eq!(
        exact::same_element(&actual, &expected),
        Some(true),
        "{precision:?}: {a:?} % {b:?}: actual {actual:?}, expected {expected:?}"
    );
    actual
}

#[test]
fn five_mod_three_is_two_not_ieee_minus_one() {
    let p = FpPrecision::Float16;
    let a = (false, 17, 256); // 5
    let b = (false, 16, 512); // 3
    assert_eq!(
        exact::same_element(&agrees(p, a, b), &value(p, (false, 16, 0))),
        Some(true)
    );
    let ieee = exact::rem(&value(p, a), &value(p, b)).expect("IEEE remainder");
    assert_eq!(
        exact::same_element(&ieee, &value(p, (true, 15, 0))),
        Some(true)
    );
}

#[test]
fn every_operand_sign_preserves_the_dividend_sign() {
    let p = FpPrecision::Float16;
    for a_negative in [false, true] {
        for b_negative in [false, true] {
            let result = agrees(p, (a_negative, 17, 256), (b_negative, 16, 512));
            assert_eq!(
                exact::same_element(&result, &value(p, (a_negative, 16, 0))),
                Some(true)
            );
        }
    }
}

#[test]
fn smaller_same_binade_retains_exact_dividend() {
    // |1.75| < |1.875| but both unbiased exponents are identical. This
    // requires the full magnitude guard, not only the old IEEE c6 shortcut.
    for negative in [false, true] {
        let p = FpPrecision::Float16;
        let a = (negative, 15, 768);
        assert_eq!(
            exact::same_element(&agrees(p, a, (false, 15, 896)), &value(p, a)),
            Some(true)
        );
    }
}

#[test]
fn exact_multiples_keep_both_zero_signs() {
    let p = FpPrecision::Float16;
    for negative in [false, true] {
        let result = agrees(p, (negative, 17, 512), (true, 16, 512)); // +/-6 mod -3
        assert_eq!(
            exact::same_element(&result, &value(p, (negative, 0, 0))),
            Some(true)
        );
    }
}

#[test]
fn zero_dividends_keep_both_zero_signs() {
    let p = FpPrecision::Float16;
    for negative in [false, true] {
        let zero = (negative, 0, 0);
        assert_eq!(
            exact::same_element(&agrees(p, zero, (true, 15, 0)), &value(p, zero)),
            Some(true)
        );
    }
}

#[test]
fn subnormal_residues_and_subnormal_divisors_are_exact() {
    let p = FpPrecision::Float16;
    for negative in [false, true] {
        let residue = agrees(p, (negative, 0, 5), (false, 0, 3));
        assert_eq!(
            exact::same_element(&residue, &value(p, (negative, 0, 2))),
            Some(true)
        );
        let residue = agrees(p, (negative, 1, 0), (true, 0, 3));
        assert_eq!(
            exact::same_element(&residue, &value(p, (negative, 0, 1))),
            Some(true)
        );
    }
}

#[test]
fn extreme_exponent_differences_do_not_round_an_intermediate_quotient() {
    for p in [
        FpPrecision::Float16,
        FpPrecision::Float32,
        FpPrecision::Float64,
        FpPrecision::Float128,
    ] {
        let largest_exponent = (1u64 << p.exponent_bits()) - 2;
        let largest_fraction = (1u128 << (p.significand_bits() - 1)) - 1;
        let result = agrees(p, (true, largest_exponent, largest_fraction), (false, 0, 1));
        assert_eq!(
            exact::same_element(&result, &value(p, (true, 0, 0))),
            Some(true)
        );
    }
}

#[test]
fn finite_modulo_either_infinity_is_the_original_value() {
    let p = FpPrecision::Float16;
    let a = (true, 0, 7);
    for negative in [false, true] {
        assert_eq!(
            exact::same_element(&agrees(p, a, (negative, 31, 0)), &value(p, a)),
            Some(true)
        );
    }
}

#[test]
fn invalid_division_classes_are_logical_nan_not_claimed_source_payloads() {
    let p = FpPrecision::Float16;
    for (a, b) in [
        ((false, 31, 0), (false, 15, 0)),
        ((true, 31, 0), (false, 31, 0)),
        ((false, 15, 0), (false, 0, 0)),
        ((false, 0, 0), (true, 0, 0)),
        ((true, 31, 1), (false, 15, 0)),
        ((false, 15, 0), (false, 31, 511)),
    ] {
        assert!(agrees(p, a, b).is_nan());
    }
    // Payload/sign collapse is intentional for the logical FP value model:
    // this control makes NO assertion that these are allowed Rust result bits.
}

#[test]
fn quotient_ties_and_neighboring_inputs_do_not_apply_ieee_nearest_rounding() {
    let p = FpPrecision::Float16;
    for fraction in [511, 512, 513] {
        // the three values around 3; divisor 2
        let a = (false, 16, fraction);
        let result = agrees(p, a, (false, 16, 0));
        assert!(!result.is_negative());
    }
    // Exact halfway 3/2: Rust remainder 1, IEEE ties-to-even remainder -1.
    let result = agrees(p, (false, 16, 512), (false, 16, 0));
    assert_eq!(
        exact::same_element(&result, &value(p, (false, 15, 0))),
        Some(true)
    );
}

#[test]
fn exhaustive_small_format_matches_independent_rational_reference() {
    let p = FpPrecision::Custom { eb: 2, sb: 3 };
    let mut compared = 0;
    for a_bits in 0u32..32 {
        for b_bits in 0u32..32 {
            let fields = |bits: u32| {
                (
                    bits & 16 != 0,
                    u64::from((bits >> 2) & 3),
                    u128::from(bits & 3),
                )
            };
            agrees(p, fields(a_bits), fields(b_bits));
            compared += 1;
        }
    }
    assert_eq!(compared, 1024);
}

#[test]
fn circuit_cannot_choose_the_ieee_result_for_rust_five_mod_three() {
    let terms = TermStore::new();
    let (built, result) = encoding(
        &terms,
        FpPrecision::Float16,
        (false, 17, 256),
        (false, 16, 512),
    );
    assert!(matches!(
        solve(&built, Some(CnfClause::unit(result.sign))),
        SatResult::Unsat(_)
    ));
}

#[test]
fn reference_refuses_mismatched_formats_instead_of_truncating_fields() {
    let a = value(FpPrecision::Float16, (false, 15, 0));
    let b = value(FpPrecision::Float32, (false, 127, 0));
    assert!(exact::truncating_rem(&a, &b).is_none());
}

#[test]
fn reference_matches_f32_and_f64_percent_without_rounded_division() {
    let p32 = FpPrecision::Float32;
    let p64 = FpPrecision::Float64;
    let v32 = |x: f32| {
        value(
            p32,
            (
                x.is_sign_negative(),
                u64::from((x.to_bits() >> 23) & 255),
                u128::from(x.to_bits() & 0x7f_ffff),
            ),
        )
    };
    let v64 = |x: f64| {
        value(
            p64,
            (
                x.is_sign_negative(),
                (x.to_bits() >> 52) & 2047,
                u128::from(x.to_bits() & 0x000f_ffff_ffff_ffff),
            ),
        )
    };
    for (x, y) in [
        (5.0f32, 3.0),
        (-3.0, -2.0),
        (f32::MAX, 3.0),
        (f32::MIN_POSITIVE, f32::from_bits(3)),
        (f32::from_bits(5), f32::from_bits(3)),
        (-0.0, 1.0),
        (1.0, f32::INFINITY),
        (f32::INFINITY, 1.0),
        (1.0, 0.0),
    ] {
        assert_eq!(
            exact::same_element(
                &exact::truncating_rem(&v32(x), &v32(y)).expect("f32"),
                &v32(x % y)
            ),
            Some(true),
            "f32: {x:?} % {y:?}"
        );
    }
    for (x, y) in [
        (5.0f64, 3.0),
        (-3.0, -2.0),
        (f64::MAX, 3.0),
        (f64::MIN_POSITIVE, f64::from_bits(3)),
        (f64::from_bits(5), f64::from_bits(3)),
        (-0.0, 1.0),
        (1.0, f64::INFINITY),
        (f64::INFINITY, 1.0),
        (1.0, 0.0),
    ] {
        assert_eq!(
            exact::same_element(
                &exact::truncating_rem(&v64(x), &v64(y)).expect("f64"),
                &v64(x % y)
            ),
            Some(true),
            "f64: {x:?} % {y:?}"
        );
    }
}
