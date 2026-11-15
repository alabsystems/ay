// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn all_rounding_literals_accept_only_nullary_native_rounding_sort() {
    for name in [
        "RNE",
        "RNA",
        "RTP",
        "RTN",
        "RTZ",
        "roundNearestTiesToEven",
        "roundNearestTiesToAway",
        "roundTowardPositive",
        "roundTowardNegative",
        "roundTowardZero",
    ] {
        positive(Symbol::named(name), &[], rounding());
        negative(Symbol::named(name), &[0], rounding());
        for result in [
            Sort::Bool,
            Sort::Int,
            bv(3),
            Sort::Uninterpreted("roundingmode".into()),
        ] {
            negative(Symbol::named(name), &[], result);
        }
        negative(Symbol::indexed(name, vec![]), &[], rounding());
        negative(Symbol::indexed(name, vec![0]), &[], rounding());
    }
}

#[test]
fn rounded_binary_arithmetic_requires_one_rm_and_two_same_format_operands() {
    for name in ["fp.add", "fp.sub", "fp.mul", "fp.div"] {
        positive(Symbol::named(name), &[0, 1, 1], Sort::FloatingPoint(8, 24));
        positive(Symbol::named(name), &[0, 2, 2], Sort::FloatingPoint(11, 53));
        for args in [
            &[][..],
            &[1, 1],
            &[0, 1, 1, 1],
            &[3, 1, 1],
            &[8, 1, 1],
            &[0, 1, 2],
            &[0, 1, 3],
        ] {
            negative(Symbol::named(name), args, Sort::FloatingPoint(8, 24));
        }
        negative(Symbol::named(name), &[0, 1, 1], Sort::FloatingPoint(11, 53));
        negative(Symbol::named(name), &[0, 1, 1], Sort::Bool);
        negative(
            Symbol::indexed(name, vec![]),
            &[0, 1, 1],
            Sort::FloatingPoint(8, 24),
        );
    }
}

#[test]
fn rounded_unary_arithmetic_checks_rm_format_and_result() {
    for name in ["fp.sqrt", "fp.roundToIntegral"] {
        positive(Symbol::named(name), &[0, 1], Sort::FloatingPoint(8, 24));
        for args in [&[][..], &[1], &[0, 1, 1], &[3, 1], &[8, 1], &[0, 3]] {
            negative(Symbol::named(name), args, Sort::FloatingPoint(8, 24));
        }
        negative(Symbol::named(name), &[0, 1], Sort::FloatingPoint(11, 53));
        negative(
            Symbol::indexed(name, vec![1]),
            &[0, 1],
            Sort::FloatingPoint(8, 24),
        );
    }
}

#[test]
fn fma_checks_every_operand_and_is_not_a_binary_signature() {
    positive(
        Symbol::named("fp.fma"),
        &[0, 1, 1, 1],
        Sort::FloatingPoint(8, 24),
    );
    for args in [
        &[][..],
        &[0, 1, 1],
        &[0, 1, 1, 1, 1],
        &[8, 1, 1, 1],
        &[0, 2, 1, 1],
        &[0, 1, 2, 1],
        &[0, 1, 1, 2],
    ] {
        negative(Symbol::named("fp.fma"), args, Sort::FloatingPoint(8, 24));
    }
    negative(Symbol::named("fp.fma"), &[0, 1, 1, 1], Sort::Real);
}

#[test]
fn remainder_and_min_max_are_unrounded_same_format_binary_operations() {
    for name in ["fp.rem", "fp.min", "fp.max"] {
        positive(Symbol::named(name), &[1, 1], Sort::FloatingPoint(8, 24));
        for args in [&[][..], &[1], &[0, 1, 1], &[1, 2], &[1, 3]] {
            negative(Symbol::named(name), args, Sort::FloatingPoint(8, 24));
        }
        negative(Symbol::named(name), &[1, 1], Sort::FloatingPoint(11, 53));
        negative(
            Symbol::indexed(name, vec![]),
            &[1, 1],
            Sort::FloatingPoint(8, 24),
        );
    }
}

#[test]
fn to_real_and_ieee_interchange_require_their_actual_result_sorts() {
    positive(Symbol::named("fp.to_real"), &[1], Sort::Real);
    positive(Symbol::named("fp.to_ieee_bv"), &[1], bv(32));
    positive(Symbol::named("fp.to_ieee_bv"), &[2], bv(64));
    for name in ["fp.to_real", "fp.to_ieee_bv"] {
        negative(Symbol::named(name), &[], Sort::Real);
        negative(Symbol::named(name), &[1, 1], Sort::Real);
        negative(Symbol::named(name), &[4], Sort::Real);
        negative(Symbol::named(name), &[1], Sort::Int);
        negative(Symbol::indexed(name, vec![]), &[1], Sort::Real);
    }
    negative(Symbol::named("fp.to_ieee_bv"), &[1], bv(31));
    negative(Symbol::named("fp.to_real"), &[1], bv(32));
}
