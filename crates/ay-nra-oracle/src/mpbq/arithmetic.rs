// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact dyadic arithmetic checks.

use super::*;

// ===========================================================================
// Check 1 — `bq-arith`: the dyadic type itself
// ===========================================================================

/// Dyadic arithmetic against **two** independent references.
///
/// 1. **z3**, through `Z3_algebraic_add` / `Z3_algebraic_mul` on the two values
///    as rational numerals: a real differential leg on the arithmetic.
/// 2. **`BigRational`**, a gcd-reduced representation that shares no code and
///    no representation with `a / 2^k`: `add`, `sub`, `mul`, the ordering,
///    `floor`, `ceil` and both shift directions.
///
/// Plus the invariants that are the type's whole contract: canonical form
/// (`k == 0` or numerator odd), structural equality being numeric equality, and
/// the representability predicate with **both** a positive and a negative
/// control. Without the negative control an `is_representable` that returned
/// `true` unconditionally would satisfy every other assertion here — the exact
/// hole this campaign found in `is_irreducible`.
pub(crate) fn check_arith(z3: &Z3, g: &GenBq, sab: Sabotage) -> Outcome {
    let x = bq(&g.x);
    let y = bq(&g.y);
    let rx = x.to_rational();
    let ry = y.to_rational();
    let case = ArithmeticCase {
        g,
        x: &x,
        y: &y,
        rx: &rx,
        ry: &ry,
    };
    let mut comparisons = 0;
    if let Err(outcome) = add_matches(&mut comparisons, check_canonical_form(&case)) {
        return outcome;
    }
    let mut sum = x.add(&y);
    if sab.on() {
        sum = OBq::new(sum.numerator() + BigInt::one(), sum.k());
    }
    if let Err(outcome) = add_matches(&mut comparisons, check_rational_arithmetic(&case, &sum)) {
        return outcome;
    }
    if let Err(outcome) = add_matches(&mut comparisons, check_ordering_and_rounding(&case)) {
        return outcome;
    }
    if let Err(outcome) = add_matches(&mut comparisons, check_unary_and_scaled_rounding(&case)) {
        return outcome;
    }
    if let Err(outcome) = add_matches(&mut comparisons, check_power_of_two_shifts(&case)) {
        return outcome;
    }
    if let Err(outcome) = add_matches(&mut comparisons, check_representability(&case)) {
        return outcome;
    }
    if let Err(outcome) = add_matches(&mut comparisons, check_z3_arithmetic(z3, &case, &sum)) {
        return outcome;
    }
    Outcome::Match(comparisons)
}

struct ArithmeticCase<'a> {
    g: &'a GenBq,
    x: &'a OBq,
    y: &'a OBq,
    rx: &'a BigRational,
    ry: &'a BigRational,
}

fn check_canonical_form(case: &ArithmeticCase<'_>) -> Outcome {
    let mut comparisons = 0;
    for value in [case.x, case.y] {
        if value.k() > 0 && !value.numerator().is_odd() {
            return Divergence::outcome(
                "bq-arith",
                "identity",
                format!("non-canonical value {}", render_bq(value)),
                vec![("value".into(), render_bq(value))],
            );
        }
        if value.numerator().is_zero() && value.k() != 0 {
            return Divergence::outcome(
                "bq-arith",
                "identity",
                format!("non-canonical zero: k = {}", value.k()),
                vec![("value".into(), render_bq(value))],
            );
        }
        comparisons += 2;
    }
    if (case.x == case.y) != (case.rx == case.ry) {
        return Divergence::outcome(
            "bq-arith",
            "identity",
            format!(
                "structural equality {} disagrees with numeric equality {}",
                case.x == case.y,
                case.rx == case.ry
            ),
            pair_inputs(case),
        );
    }
    Outcome::Match(comparisons + 1)
}

fn check_rational_arithmetic(case: &ArithmeticCase<'_>, sum: &OBq) -> Outcome {
    let product = match case.x.mul(case.y) {
        Some(value) => value.to_rational(),
        None => return Outcome::Declined("bq mul exponent overflow"),
    };
    let checks = [
        ("add", sum.to_rational(), case.rx + case.ry),
        ("sub", case.x.sub(case.y).to_rational(), case.rx - case.ry),
        ("mul", product, case.rx * case.ry),
    ];
    for (name, actual, expected) in checks {
        if actual != expected {
            return Divergence::outcome(
                "bq-arith",
                "identity",
                format!("{name}: AY {actual} vs BigRational {expected}"),
                pair_inputs(case),
            );
        }
    }
    Outcome::Match(3)
}

fn check_ordering_and_rounding(case: &ArithmeticCase<'_>) -> Outcome {
    if case.x.cmp_bq(case.y) != case.rx.cmp(case.ry) {
        return Divergence::outcome(
            "bq-arith",
            "identity",
            format!(
                "ordering: AY {:?} vs BigRational {:?}",
                case.x.cmp_bq(case.y),
                case.rx.cmp(case.ry)
            ),
            pair_inputs(case),
        );
    }
    let mut comparisons = 1;
    for (value, rational) in [(case.x, case.rx), (case.y, case.ry)] {
        if value.floor() != rational.floor().to_integer()
            || value.ceil() != rational.ceil().to_integer()
        {
            return Divergence::outcome(
                "bq-arith",
                "identity",
                format!(
                    "floor/ceil: AY ({}, {}) vs BigRational ({}, {})",
                    value.floor(),
                    value.ceil(),
                    rational.floor().to_integer(),
                    rational.ceil().to_integer()
                ),
                vec![("value".into(), render_bq(value))],
            );
        }
        comparisons += 2;
    }
    Outcome::Match(comparisons)
}

fn check_unary_and_scaled_rounding(case: &ArithmeticCase<'_>) -> Outcome {
    let mut comparisons = 0;
    for (value, rational) in [(case.x, case.rx), (case.y, case.ry)] {
        if value.abs().to_rational() != rational.abs() {
            return unary_divergence("abs", value);
        }
        if value.neg().to_rational() != -rational.clone() {
            return unary_divergence("neg", value);
        }
        if value.is_int() != rational.is_integer() {
            return unary_divergence("is_int", value);
        }
        for target in [0u32, 1, 5, 20] {
            let scaled = rational * BigRational::from(BigInt::one() << target);
            if value.floor_at(target) != scaled.floor().to_integer()
                || value.ceil_at(target) != scaled.ceil().to_integer()
            {
                return Divergence::outcome(
                    "bq-arith",
                    "identity",
                    format!("floor_at/ceil_at disagree at 2^{target}"),
                    vec![("value".into(), render_bq(value))],
                );
            }
            comparisons += 2;
        }
        comparisons += 3;
    }
    Outcome::Match(comparisons)
}

fn unary_divergence(name: &str, value: &OBq) -> Outcome {
    Divergence::outcome(
        "bq-arith",
        "identity",
        format!("{name} disagrees with BigRational"),
        vec![("value".into(), render_bq(value))],
    )
}

fn check_power_of_two_shifts(case: &ArithmeticCase<'_>) -> Outcome {
    let mut comparisons = 0;
    for exponent in [0u32, 1, 3, 17] {
        let up = case.x.mul_two_pow(exponent);
        let Some(down) = case.x.div_two_pow(exponent) else {
            return Outcome::Declined("bq div_two_pow exponent overflow");
        };
        let scale = BigRational::from(BigInt::one() << exponent);
        if up.to_rational() != case.rx * &scale || down.to_rational() != case.rx / &scale {
            return Divergence::outcome(
                "bq-arith",
                "identity",
                format!("shift by 2^{exponent} is not exact"),
                vec![("x".into(), render_bq(case.x))],
            );
        }
        if up.k() > case.x.k() || down.k() > case.x.k() + exponent {
            return Divergence::outcome(
                "bq-arith",
                "identity",
                format!(
                    "shift 2^{exponent} moved k out of bounds: {} -> {} / {}",
                    case.x.k(),
                    up.k(),
                    down.k()
                ),
                vec![("x".into(), render_bq(case.x))],
            );
        }
        if down.mul_two_pow(exponent) != *case.x {
            return Divergence::outcome(
                "bq-arith",
                "identity",
                format!("div then mul by 2^{exponent} is not the identity"),
                vec![("x".into(), render_bq(case.x))],
            );
        }
        comparisons += 4;
    }
    Outcome::Match(comparisons)
}

fn check_representability(case: &ArithmeticCase<'_>) -> Outcome {
    if !OBq::is_representable(&case.g.dyadic) {
        return Divergence::outcome(
            "bq-arith",
            "identity",
            format!("dyadic {} was rejected", case.g.dyadic),
            vec![("r".into(), case.g.dyadic.to_string())],
        );
    }
    match OBq::from_rational(&case.g.dyadic) {
        Some(value) if value.to_rational() == case.g.dyadic => {}
        other => {
            return Divergence::outcome(
                "bq-arith",
                "identity",
                format!("from_rational({}) failed: {other:?}", case.g.dyadic),
                vec![("r".into(), case.g.dyadic.to_string())],
            );
        }
    }
    if OBq::is_representable(&case.g.non_dyadic) || OBq::from_rational(&case.g.non_dyadic).is_some()
    {
        return Divergence::outcome(
            "bq-arith",
            "identity",
            format!("non-dyadic {} was accepted", case.g.non_dyadic),
            vec![("r".into(), case.g.non_dyadic.to_string())],
        );
    }
    Outcome::Match(3)
}

fn check_z3_arithmetic(z3: &Z3, case: &ArithmeticCase<'_>, sum: &OBq) -> Outcome {
    let (Some(x), Some(y)) = (z3.rational(case.rx), z3.rational(case.ry)) else {
        return Outcome::Skipped("z3 could not build the numerals");
    };
    let (Some(z3_sum), Some(z3_product)) = (z3.add(x, y), z3.mul(x, y)) else {
        return Outcome::Skipped("z3 errored on algebraic add/mul");
    };
    let (Some(expected_sum), Some(expected_product)) =
        (z3.numeral_value(z3_sum), z3.numeral_value(z3_product))
    else {
        return Outcome::Skipped("z3 did not return numerals");
    };
    if sum.to_rational() != expected_sum {
        return Divergence::outcome(
            "bq-arith",
            "z3",
            format!("add: AY {} vs z3 {expected_sum}", sum.to_rational()),
            pair_inputs(case),
        );
    }
    let Some(product) = case.x.mul(case.y) else {
        return Outcome::Declined("bq mul exponent overflow");
    };
    if product.to_rational() != expected_product {
        return Divergence::outcome(
            "bq-arith",
            "z3",
            format!("mul: AY {} vs z3 {expected_product}", product.to_rational()),
            pair_inputs(case),
        );
    }
    Outcome::Match(2)
}

fn pair_inputs(case: &ArithmeticCase<'_>) -> Vec<(String, String)> {
    vec![
        ("x".into(), render_bq(case.x)),
        ("y".into(), render_bq(case.y)),
    ]
}
