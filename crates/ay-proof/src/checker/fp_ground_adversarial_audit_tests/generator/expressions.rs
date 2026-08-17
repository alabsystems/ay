// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::{bv_text, fp_sort, Prng, T};
use ay_core::{Sort, Symbol, TermStore};
use num_bigint::BigInt;
use num_rational::BigRational;

const RMS: [&str; 5] = ["RNE", "RNA", "RTP", "RTN", "RTZ"];

fn rm_sort() -> Sort {
    Sort::Uninterpreted("RoundingMode".to_string())
}

fn mk_rm(terms: &mut TermStore, name: &str) -> T {
    T {
        id: terms.mk_app(Symbol::named(name), vec![], rm_sort()),
        text: name.to_string(),
    }
}

fn fp_const(
    terms: &mut TermStore,
    format: (u32, u32),
    sign: u64,
    exponent: u64,
    significand: u64,
) -> T {
    let sign_term = terms.mk_bitvec(BigInt::from(sign), 1);
    let exponent_term = terms.mk_bitvec(BigInt::from(exponent), format.0);
    let significand_term = terms.mk_bitvec(BigInt::from(significand), format.1 - 1);
    T {
        id: terms.mk_app(
            Symbol::named("fp"),
            vec![sign_term, exponent_term, significand_term],
            fp_sort(format),
        ),
        text: format!(
            "(fp {} {} {})",
            bv_text(sign, 1),
            bv_text(exponent, format.0),
            bv_text(significand, format.1 - 1)
        ),
    }
}

fn fp_special(terms: &mut TermStore, format: (u32, u32), name: &str) -> T {
    T {
        id: terms.mk_app(
            Symbol::indexed(name, vec![format.0, format.1]),
            vec![],
            fp_sort(format),
        ),
        text: format!("(_ {} {} {})", name, format.0, format.1),
    }
}

fn random_fp_leaf(terms: &mut TermStore, rng: &mut Prng, format: (u32, u32)) -> T {
    if rng.chance(15) {
        let name = ["+zero", "-zero", "+oo", "-oo", "NaN"][rng.below(5) as usize];
        return fp_special(terms, format, name);
    }
    let sign = rng.below(2);
    let significand_bits = format.1 - 1;
    let significand_mask = if significand_bits >= 64 {
        u64::MAX
    } else {
        (1u64 << significand_bits) - 1
    };
    let (exponent, significand) = match rng.below(5) {
        0 => (0, rng.next() & significand_mask),
        1 => ((1u64 << format.0) - 2, rng.next() & significand_mask),
        2 => (
            ((1u64 << (format.0 - 1)) - 1)
                .wrapping_add(rng.below(7))
                .wrapping_sub(3)
                & ((1 << format.0) - 1),
            0,
        ),
        3 => (
            (1u64 << (format.0 - 1)) - 1 + rng.below(3),
            if rng.chance(50) { significand_mask } else { 1 },
        ),
        _ => (
            rng.next() % (1u64 << format.0),
            rng.next() & significand_mask,
        ),
    };
    fp_const(terms, format, sign, exponent, significand)
}

pub(super) fn random_fp_expr(
    terms: &mut TermStore,
    rng: &mut Prng,
    format: (u32, u32),
    depth: u32,
    vars: &[T],
) -> T {
    if depth == 0 || rng.chance(30) {
        if !vars.is_empty() && rng.chance(45) {
            return vars[rng.below(vars.len() as u64) as usize].clone();
        }
        return random_fp_leaf(terms, rng, format);
    }
    let rounding_mode = mk_rm(terms, RMS[rng.below(5) as usize]);
    let operation = rng.below(11);
    match operation {
        0..=5 => random_binary_expr(terms, rng, format, depth, vars, rounding_mode, operation),
        6..=8 => random_other_expr(terms, rng, format, depth, vars, rounding_mode, operation),
        9 => random_raw_conversion(terms, rng, format),
        _ => random_conversion(terms, rng, format, rounding_mode),
    }
}

fn random_binary_expr(
    terms: &mut TermStore,
    rng: &mut Prng,
    format: (u32, u32),
    depth: u32,
    vars: &[T],
    rounding_mode: T,
    operation: u64,
) -> T {
    let left = random_fp_expr(terms, rng, format, depth - 1, vars);
    let right = random_fp_expr(terms, rng, format, depth - 1, vars);
    let name = match operation {
        0 | 1 => "fp.add",
        2 => "fp.sub",
        3 | 4 => "fp.mul",
        5 => "fp.div",
        _ => unreachable!(),
    };
    T {
        id: terms.mk_app(
            Symbol::named(name),
            vec![rounding_mode.id, left.id, right.id],
            fp_sort(format),
        ),
        text: format!(
            "({name} {} {} {})",
            rounding_mode.text, left.text, right.text
        ),
    }
}

fn random_other_expr(
    terms: &mut TermStore,
    rng: &mut Prng,
    format: (u32, u32),
    depth: u32,
    vars: &[T],
    rounding_mode: T,
    operation: u64,
) -> T {
    let first = random_fp_expr(terms, rng, format, depth - 1, vars);
    match operation {
        6 => {
            let second = random_fp_expr(terms, rng, format, depth - 1, vars);
            let third = random_fp_expr(terms, rng, format, depth - 1, vars);
            T {
                id: terms.mk_app(
                    Symbol::named("fp.fma"),
                    vec![rounding_mode.id, first.id, second.id, third.id],
                    fp_sort(format),
                ),
                text: format!(
                    "(fp.fma {} {} {} {})",
                    rounding_mode.text, first.text, second.text, third.text
                ),
            }
        }
        7 => T {
            id: terms.mk_app(
                Symbol::named("fp.sqrt"),
                vec![rounding_mode.id, first.id],
                fp_sort(format),
            ),
            text: format!("(fp.sqrt {} {})", rounding_mode.text, first.text),
        },
        8 => {
            let name = if rng.chance(50) { "fp.abs" } else { "fp.neg" };
            T {
                id: terms.mk_app(Symbol::named(name), vec![first.id], fp_sort(format)),
                text: format!("({name} {})", first.text),
            }
        }
        _ => unreachable!(),
    }
}

fn random_raw_conversion(terms: &mut TermStore, rng: &mut Prng, format: (u32, u32)) -> T {
    let width = format.0 + format.1;
    let bits = if width >= 64 {
        rng.next()
    } else {
        rng.next() & ((1u64 << width) - 1)
    };
    let pattern = terms.mk_bitvec(BigInt::from(bits), width);
    T {
        id: terms.mk_app(
            Symbol::indexed("to_fp", vec![format.0, format.1]),
            vec![pattern],
            fp_sort(format),
        ),
        text: format!(
            "((_ to_fp {} {}) {})",
            format.0,
            format.1,
            bv_text(bits, width)
        ),
    }
}

fn random_conversion(
    terms: &mut TermStore,
    rng: &mut Prng,
    format: (u32, u32),
    rounding_mode: T,
) -> T {
    match rng.below(4) {
        0 => random_fp_conversion(terms, rng, format, rounding_mode),
        1 => random_bv_conversion(terms, rng, format, rounding_mode, false),
        2 => random_bv_conversion(terms, rng, format, rounding_mode, true),
        _ => random_real_conversion(terms, rng, format, rounding_mode),
    }
}

fn random_fp_conversion(
    terms: &mut TermStore,
    rng: &mut Prng,
    format: (u32, u32),
    rounding_mode: T,
) -> T {
    let source_format = match rng.below(3) {
        0 => (5, 11),
        1 => (8, 24),
        _ => (11, 53),
    };
    let inner = random_fp_expr(terms, rng, source_format, 0, &[]);
    T {
        id: terms.mk_app(
            Symbol::indexed("to_fp", vec![format.0, format.1]),
            vec![rounding_mode.id, inner.id],
            fp_sort(format),
        ),
        text: format!(
            "((_ to_fp {} {}) {} {})",
            format.0, format.1, rounding_mode.text, inner.text
        ),
    }
}

fn random_bv_conversion(
    terms: &mut TermStore,
    rng: &mut Prng,
    format: (u32, u32),
    rounding_mode: T,
    unsigned: bool,
) -> T {
    let width = [8u32, 16, 32][rng.below(3) as usize];
    let bits = rng.next() & ((1u64 << width) - 1);
    let pattern = terms.mk_bitvec(BigInt::from(bits), width);
    let name = if unsigned { "to_fp_unsigned" } else { "to_fp" };
    T {
        id: terms.mk_app(
            Symbol::indexed(name, vec![format.0, format.1]),
            vec![rounding_mode.id, pattern],
            fp_sort(format),
        ),
        text: format!(
            "((_ {name} {} {}) {} {})",
            format.0,
            format.1,
            rounding_mode.text,
            bv_text(bits, width)
        ),
    }
}

fn random_real_conversion(
    terms: &mut TermStore,
    rng: &mut Prng,
    format: (u32, u32),
    rounding_mode: T,
) -> T {
    let numerator = (rng.next() % 2_000_001) as i64 - 1_000_000;
    let denominator = (rng.next() % 1_000_000) as i64 + 1;
    let value = BigRational::new(BigInt::from(numerator), BigInt::from(denominator));
    let real = terms.mk_rational(value);
    let magnitude = format!("(/ {}.0 {}.0)", numerator.abs(), denominator);
    let rendered = if numerator < 0 {
        format!("(- {magnitude})")
    } else {
        magnitude
    };
    T {
        id: terms.mk_app(
            Symbol::indexed("to_fp", vec![format.0, format.1]),
            vec![rounding_mode.id, real],
            fp_sort(format),
        ),
        text: format!(
            "((_ to_fp {} {}) {} {})",
            format.0, format.1, rounding_mode.text, rendered
        ),
    }
}

pub(super) fn random_literal(
    terms: &mut TermStore,
    rng: &mut Prng,
    format: (u32, u32),
    depth: u32,
    vars: &[T],
) -> T {
    let atom = match rng.below(10) {
        0..=4 => random_comparison(terms, rng, format, depth, vars),
        5 | 6 => random_equality(terms, rng, format, depth, vars),
        _ => random_classification(terms, rng, format, depth, vars),
    };
    if rng.chance(50) {
        T {
            id: terms.mk_not(atom.id),
            text: format!("(not {})", atom.text),
        }
    } else {
        atom
    }
}

fn random_comparison(
    terms: &mut TermStore,
    rng: &mut Prng,
    format: (u32, u32),
    depth: u32,
    vars: &[T],
) -> T {
    let name = ["fp.eq", "fp.lt", "fp.leq", "fp.gt", "fp.geq"][rng.below(5) as usize];
    let left = random_fp_expr(terms, rng, format, depth, vars);
    let right = random_fp_expr(terms, rng, format, depth, vars);
    T {
        id: terms.mk_app(Symbol::named(name), vec![left.id, right.id], Sort::Bool),
        text: format!("({name} {} {})", left.text, right.text),
    }
}

fn random_equality(
    terms: &mut TermStore,
    rng: &mut Prng,
    format: (u32, u32),
    depth: u32,
    vars: &[T],
) -> T {
    let left = random_fp_expr(terms, rng, format, depth, vars);
    let right = random_fp_expr(terms, rng, format, depth, vars);
    T {
        id: terms.mk_app(Symbol::named("="), vec![left.id, right.id], Sort::Bool),
        text: format!("(= {} {})", left.text, right.text),
    }
}

fn random_classification(
    terms: &mut TermStore,
    rng: &mut Prng,
    format: (u32, u32),
    depth: u32,
    vars: &[T],
) -> T {
    let name = [
        "fp.isNaN",
        "fp.isInfinite",
        "fp.isZero",
        "fp.isNormal",
        "fp.isSubnormal",
        "fp.isPositive",
        "fp.isNegative",
    ][rng.below(7) as usize];
    let argument = random_fp_expr(terms, rng, format, depth, vars);
    T {
        id: terms.mk_app(Symbol::named(name), vec![argument.id], Sort::Bool),
        text: format!("({name} {})", argument.text),
    }
}
