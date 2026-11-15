// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use num_bigint::BigUint;

fn value(sign: bool, exponent: u64, fraction: BigUint, eb: u32) -> ModelValue {
    ModelValue::floating_point_exact(sign, exponent.into(), fraction, eb, 200).unwrap()
}
fn fp(sign: bool, exponent: u64, fraction: BigUint) -> ModelValue {
    value(sign, exponent, fraction, 8)
}
fn check(name: &str, mode: &str, values: &[ModelValue], expected: &ModelValue) {
    let mut terms = TermStore::new();
    let crate::fp_exact::View { eb, sb, .. } = crate::fp_exact::view(expected).unwrap();
    let sort = Sort::FloatingPoint(eb, sb);
    let mut args = Vec::new();
    if name != "fp.rem" {
        args.push(terms.mk_app(
            Symbol::named(mode),
            [],
            Sort::Uninterpreted("RoundingMode".into()),
        ));
    }
    let mut model = StubModel::new();
    for (i, value) in values.iter().enumerate() {
        let arg = terms.mk_var(format!("x{i}"), sort.clone());
        args.push(arg);
        model = model.with(arg, value.clone());
    }
    let operation = app(&mut terms, name, &args, sort.clone());
    let result = evaluate_term(&terms, &model, operation);
    let EvalOutcome::Value(actual) = result else {
        panic!("{name} {mode}: {result:?}");
    };
    assert!(
        crate::fp::same_element(&actual, expected),
        "{name} {mode}: {actual:?} != {expected:?}"
    );
    let output = terms.mk_var("expected", sort);
    let claim = app(&mut terms, "=", &[operation, output], Sort::Bool);
    assert_confirmed(&verdict(
        &terms,
        &model.with(output, expected.clone()),
        &[claim],
    ));
}

#[test]
fn fp_remainder_exact_sb200_ties_and_low_bits() {
    let two = fp(false, 128, 0u8.into());
    for (a, expected) in [
        // 3/2 ties to integer 2, whereas 5/2 ties to integer 2 as well.
        (
            fp(false, 128, BigUint::from(1u8) << 198usize),
            fp(true, 127, 0u8.into()),
        ),
        (
            fp(false, 129, BigUint::from(1u8) << 197usize),
            fp(false, 127, 0u8.into()),
        ),
        (
            fp(true, 128, BigUint::from(1u8) << 198usize),
            fp(false, 127, 0u8.into()),
        ),
    ] {
        check(
            "fp.rem",
            "no-rounding-operand",
            &[a, two.clone()],
            &expected,
        );
    }
    let one = fp(false, 127, 0u8.into());
    check(
        "fp.rem",
        "no-rounding-operand",
        &[fp(false, 127, 1u8.into()), one.clone()],
        &fp(false, 0, BigUint::from(1u8) << 126usize),
    );
    check(
        "fp.rem",
        "no-rounding-operand",
        &[
            fp(
                false,
                126,
                (BigUint::from(1u8) << 199usize) - BigUint::from(1u8),
            ),
            one,
        ],
        &fp(true, 0, BigUint::from(1u8) << 125usize),
    );
    check(
        "fp.rem",
        "no-rounding-operand",
        &[fp(false, 0, 3u8.into()), fp(false, 0, 2u8.into())],
        &fp(true, 0, 1u8.into()),
    );
    // Changing the divisor's sign changes the nearest quotient's sign, not
    // the remainder. In particular this must not become truncating fmod.
    check(
        "fp.rem",
        "no-rounding-operand",
        &[
            fp(false, 128, BigUint::from(1u8) << 198usize),
            fp(true, 128, 0u8.into()),
        ],
        &fp(true, 127, 0u8.into()),
    );
}

#[test]
fn fp_remainder_exact_sb200_preserves_signed_zero_and_special_cases() {
    let one = fp(false, 127, 0u8.into());
    let nan = fp(false, 255, 1u8.into());
    for sign in [false, true] {
        let zero = fp(sign, 0, 0u8.into());
        let signed_one = fp(sign, 127, 0u8.into());
        let infinity = fp(sign, 255, 0u8.into());
        for operands in [
            [zero.clone(), one.clone()],
            [signed_one.clone(), one.clone()],
        ] {
            check("fp.rem", "no-rounding-operand", &operands, &zero);
        }
        check(
            "fp.rem",
            "no-rounding-operand",
            &[signed_one.clone(), infinity.clone()],
            &signed_one,
        );
        for operands in [
            [infinity, one.clone()],
            [one.clone(), zero],
            [nan.clone(), signed_one.clone()],
            [signed_one, nan.clone()],
        ] {
            check("fp.rem", "no-rounding-operand", &operands, &nan);
        }
    }
}

#[test]
fn fp_sqrt_exact_sb200_rounding_low_bits_and_subnormals() {
    for mode in ["RNE", "RNA", "RTP", "RTN", "RTZ"] {
        // sqrt(1+u) is strictly between 1 and 1+u/2 for u=2^-199.
        check(
            "fp.sqrt",
            mode,
            &[fp(false, 127, 1u8.into())],
            &fp(false, 127, u8::from(mode == "RTP").into()),
        );
        // sqrt(1+2u) is below 1+u but above its midpoint with 1.
        check(
            "fp.sqrt",
            mode,
            &[fp(false, 127, 2u8.into())],
            &fp(
                false,
                127,
                u8::from(matches!(mode, "RNE" | "RNA" | "RTP")).into(),
            ),
        );
        // (1+2^-90)^2 = 1+2^-89+2^-180, exactly representable at SB200.
        check(
            "fp.sqrt",
            mode,
            &[fp(
                false,
                127,
                (BigUint::from(1u8) << 110usize) + (BigUint::from(1u8) << 19usize),
            )],
            &fp(false, 127, BigUint::from(1u8) << 109usize),
        );
        // 2*minimum-subnormal = 2^-324, whose root is 2^-162.
        check(
            "fp.sqrt",
            mode,
            &[fp(false, 0, 2u8.into())],
            &fp(false, 0, BigUint::from(1u8) << 163usize),
        );
        check(
            "fp.sqrt",
            mode,
            &[fp(false, 1, 0u8.into())],
            &fp(false, 64, 0u8.into()),
        );
        // The predecessor of 4 has a root strictly BELOW the midpoint
        // between predecessor(2) and 2: that midpoint's square exceeds
        // the operand by 2^-400. Only RTP carries into exponent 128.
        let max = (BigUint::from(1u8) << 199usize) - BigUint::from(1u8);
        let down = mode != "RTP";
        check(
            "fp.sqrt",
            mode,
            &[fp(false, 128, max.clone())],
            &fp(
                false,
                if down { 127 } else { 128 },
                if down { max } else { 0u8.into() },
            ),
        );
    }
}

#[test]
fn fp_sqrt_exact_sb200_special_values() {
    for mode in ["RNE", "RNA", "RTP", "RTN", "RTZ"] {
        for negative in [false, true] {
            let zero = fp(negative, 0, 0u8.into());
            check("fp.sqrt", mode, &[zero.clone()], &zero);
        }
        let nan = fp(false, 255, 1u8.into());
        for operand in [
            fp(true, 127, 0u8.into()),
            fp(true, 255, 0u8.into()),
            nan.clone(),
        ] {
            check("fp.sqrt", mode, &[operand], &nan);
        }
        let infinity = fp(false, 255, 0u8.into());
        check("fp.sqrt", mode, &[infinity.clone()], &infinity);
    }
}

#[test]
fn fp_arithmetic_exact_sb200_preserves_low_bits_and_refutes_wrong_sum() {
    let one = fp(false, 127, 0u8.into());
    let next = fp(false, 127, 1u8.into());
    let two = fp(false, 128, 0u8.into());
    check("fp.add", "RNE", &[one.clone(), one.clone()], &two);
    check(
        "fp.mul",
        "RNE",
        &[next.clone(), two.clone()],
        &fp(false, 128, 1u8.into()),
    );
    check(
        "fp.div",
        "RNE",
        &[next.clone(), two],
        &fp(false, 126, 1u8.into()),
    );
    check(
        "fp.sub",
        "RNE",
        &[next, one],
        &fp(false, 0, BigUint::from(1u8) << 126usize),
    );
    let mut terms = TermStore::new();
    let sort = Sort::FloatingPoint(8, 200);
    let x = terms.mk_var("x", sort.clone());
    let rm = terms.mk_app(
        Symbol::named("RNE"),
        [],
        Sort::Uninterpreted("RoundingMode".into()),
    );
    let sum = app(&mut terms, "fp.add", &[rm, x, x], sort);
    let wrong = app(&mut terms, "=", &[sum, x], Sort::Bool);
    assert_violates(&verdict(
        &terms,
        &StubModel::new().with(x, fp(false, 127, 1u8.into())),
        &[wrong],
    ));
}

#[test]
fn fp_arithmetic_exact_sb200_ties_and_division_use_all_five_modes() {
    let modes = ["RNE", "RNA", "RTP", "RTN", "RTZ"];
    for negative in [false, true] {
        for mode in modes {
            let half_ulp = fp(negative, 0, BigUint::from(1u8) << 125usize);
            for odd in [false, true] {
                let first = fp(negative, 127, u8::from(odd).into());
                let increment = match mode {
                    "RNA" => true,
                    "RNE" => odd,
                    "RTP" => !negative,
                    "RTN" => negative,
                    _ => false,
                };
                check(
                    "fp.add",
                    mode,
                    &[first, half_ulp.clone()],
                    &fp(negative, 127, (u8::from(odd) + u8::from(increment)).into()),
                );
            }
            // 1/3 has significand 4/3 at exponent -2. 2^199 mod 3 = 2,
            // strictly above halfway; the expected quotient is independent of
            // the implementation's rational-rounding kernel.
            let fraction = (BigUint::from(1u8) << 199usize) / BigUint::from(3u8);
            let up = matches!(mode, "RNE" | "RNA")
                || (mode == "RTP" && !negative)
                || (mode == "RTN" && negative);
            check(
                "fp.div",
                mode,
                &[
                    fp(negative, 127, 0u8.into()),
                    fp(false, 128, BigUint::from(1u8) << 198usize),
                ],
                &fp(negative, 125, fraction + BigUint::from(u8::from(up))),
            );
        }
    }
}

#[test]
fn fp_arithmetic_exact_sb200_underflow_carry_overflow_and_zero_signs() {
    for negative in [false, true] {
        for mode in ["RNE", "RNA", "RTP", "RTN", "RTZ"] {
            let up = mode == "RNA" || (mode == "RTP" && !negative) || (mode == "RTN" && negative);
            check(
                "fp.div",
                mode,
                &[fp(negative, 0, 1u8.into()), fp(false, 128, 0u8.into())],
                &fp(negative, 0, u8::from(up).into()),
            );
            let infinity = matches!(mode, "RNE" | "RNA")
                || (mode == "RTP" && !negative)
                || (mode == "RTN" && negative);
            let max = (BigUint::from(1u8) << 199usize) - BigUint::from(1u8);
            check(
                "fp.mul",
                mode,
                &[fp(negative, 254, max.clone()), fp(false, 128, 0u8.into())],
                &fp(
                    negative,
                    if infinity { 255 } else { 254 },
                    if infinity { 0u8.into() } else { max },
                ),
            );
            check(
                "fp.add",
                mode,
                &[fp(negative, 0, 0u8.into()), fp(!negative, 0, 0u8.into())],
                &fp(mode == "RTN", 0, 0u8.into()),
            );
        }
    }
    let largest = (BigUint::from(1u8) << 199usize) - BigUint::from(1u8);
    check(
        "fp.add",
        "RNE",
        &[fp(false, 0, largest), fp(false, 0, 1u8.into())],
        &fp(false, 1, 0u8.into()),
    );
}

#[test]
fn fp_arithmetic_exact_sb200_fma_rounds_once_and_preserves_special_rules() {
    let high = BigUint::from(1u8) << 199usize;
    let a = value(false, 1023, 1u8.into(), 11); // 1 + 2^-199
    let b = value(false, 1022, &high - BigUint::from(2u8), 11); // 1 - 2^-199
    let c = value(true, 1023, 0u8.into(), 11);
    for mode in ["RNE", "RNA", "RTP", "RTN", "RTZ"] {
        // Exact product minus one is -2^-398. Rounding the product first
        // would erase this nonzero result (or return a different one).
        check(
            "fp.fma",
            mode,
            &[a.clone(), b.clone(), c.clone()],
            &value(true, 625, 0u8.into(), 11),
        );
    }
    let zero = fp(false, 0, 0u8.into());
    let inf = fp(false, 255, 0u8.into());
    let nan = fp(false, 255, 1u8.into());
    let neg_inf = fp(true, 255, 0u8.into());
    check("fp.mul", "RNE", &[zero.clone(), inf.clone()], &nan);
    check("fp.div", "RNE", &[inf.clone(), inf.clone()], &nan);
    check("fp.div", "RNE", &[zero.clone(), zero.clone()], &nan);
    check("fp.add", "RNE", &[inf.clone(), neg_inf.clone()], &nan);
    check(
        "fp.fma",
        "RNE",
        &[inf.clone(), fp(false, 127, 0u8.into()), neg_inf],
        &nan,
    );
    check("fp.fma", "RNE", &[zero.clone(), inf, zero], &nan);
}
