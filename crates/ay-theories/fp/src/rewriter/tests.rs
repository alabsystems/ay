// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::tests_support::{extract_fp, solve_fp_clauses};
use crate::FpSolver;
use crate::{exact, FpModelValue};
use ay_core::Sort;

pub(super) fn mode(terms: &mut TermStore, rm: RoundingMode) -> TermId {
    terms.mk_app(
        Symbol::named(rm.name()),
        vec![],
        Sort::Uninterpreted("RoundingMode".to_string()),
    )
}

pub(super) fn real(terms: &mut TermStore, num: i64, den: i64) -> TermId {
    terms.mk_rational(BigRational::new(num.into(), den.into()))
}

pub(super) fn to_fp(terms: &mut TermStore, (eb, sb): (u32, u32), rm: TermId, x: TermId) -> TermId {
    terms.mk_app(
        Symbol::indexed("to_fp", vec![eb, sb]),
        vec![rm, x],
        Sort::FloatingPoint(eb, sb),
    )
}

pub(super) fn app(terms: &mut TermStore, name: &str, args: Vec<TermId>, sort: Sort) -> TermId {
    terms.mk_app(Symbol::named(name), args, sort)
}

pub(super) fn value_of(terms: &TermStore, term: TermId) -> FpModelValue {
    fp_numeral(terms, term).unwrap_or_else(|| panic!("{:?} is not a numeral", terms.get(term)))
}

#[test]
fn a_constant_quotient_folds_to_the_correctly_rounded_value() {
    let mut terms = TermStore::new();
    let f64s = Sort::FloatingPoint(11, 53);
    let rne = mode(&mut terms, RoundingMode::RNE);
    let one = real(&mut terms, 1, 1);
    let eight_fifths = real(&mut terms, 8, 5);
    let x = to_fp(&mut terms, (11, 53), rne, one);
    let y = to_fp(&mut terms, (11, 53), rne, eight_fifths);
    let q = app(&mut terms, "fp.div", vec![rne, x, y], f64s);
    let mut rewriter = FpRewriter::new();
    let folded = rewriter.rewrite(&mut terms, q);
    // The host divides the RNE-rounded 1.6 under RNE: exactly the folded value.
    let expected = 1.0f64 / 1.6f64;
    let got = exact::to_real(&value_of(&terms, folded)).expect("finite");
    assert_eq!(got, BigRational::from_float(expected).expect("finite"));
    assert_eq!(rewriter.folds(), 3, "two literals and the quotient");
}

#[test]
fn a_mode_independent_conversion_folds_under_a_symbolic_mode() {
    let mut terms = TermStore::new();
    let rm = terms.mk_var("rm", Sort::Uninterpreted("RoundingMode".to_string()));
    let one = real(&mut terms, 1, 1);
    let exact_one = to_fp(&mut terms, (11, 53), rm, one);
    let eight_fifths = real(&mut terms, 8, 5);
    let inexact = to_fp(&mut terms, (11, 53), rm, eight_fifths);
    let mut rewriter = FpRewriter::new();
    let folded = rewriter.rewrite(&mut terms, exact_one);
    assert_eq!(
        exact::to_real(&value_of(&terms, folded)),
        Some(BigRational::from_integer(1.into()))
    );
    // 8/5 depends on the mode: it splits into an `ite` over `(= rm MODE)` of
    // its two roundings.
    let split = rewriter.rewrite(&mut terms, inexact);
    let TermData::Ite(_, up, down) = terms.get(split).clone() else {
        panic!("{:?}", terms.get(split));
    };
    assert!(fp_numeral(&terms, up).is_some() || matches!(terms.get(up), TermData::Ite(..)));
    assert!(fp_numeral(&terms, down).is_some() || matches!(terms.get(down), TermData::Ite(..)));
}

#[test]
fn unspecified_results_stay_symbolic() {
    let mut terms = TermStore::new();
    let f32s = Sort::FloatingPoint(8, 24);
    let rne = mode(&mut terms, RoundingMode::RNE);
    let nan = terms.mk_app(Symbol::indexed("NaN", vec![8, 24]), vec![], f32s.clone());
    let pz = terms.mk_app(Symbol::indexed("+zero", vec![8, 24]), vec![], f32s.clone());
    let nz = terms.mk_app(Symbol::indexed("-zero", vec![8, 24]), vec![], f32s.clone());
    let inf = terms.mk_app(Symbol::indexed("+oo", vec![8, 24]), vec![], f32s.clone());
    let to_ubv = terms.mk_app(
        Symbol::indexed("fp.to_ubv", vec![8]),
        vec![rne, nan],
        Sort::bitvec(8),
    );
    let min = app(&mut terms, "fp.min", vec![pz, nz], f32s);
    let to_real = app(&mut terms, "fp.to_real", vec![inf], Sort::Real);
    let ieee = app(&mut terms, "fp.to_ieee_bv", vec![nan], Sort::bitvec(32));
    let mut rewriter = FpRewriter::new();
    for term in [to_ubv, min, to_real, ieee] {
        assert_eq!(rewriter.rewrite(&mut terms, term), term);
    }
    assert_eq!(rewriter.folds(), 0);
}

#[test]
fn wide_ieee_fields_fold_without_the_arithmetic_carrier() {
    let mut terms = TermStore::new();
    let sort = Sort::FloatingPoint(11, 200);
    let expected = BigInt::from(1023u32) << 199usize;
    let pattern = terms.mk_bitvec(expected.clone(), 211);
    let reinterpret = terms.mk_app(
        Symbol::indexed("to_fp", vec![11, 200]),
        vec![pattern],
        sort.clone(),
    );
    let sign = terms.mk_bitvec(0.into(), 1);
    let exponent = terms.mk_bitvec(1023.into(), 11);
    let fraction = terms.mk_bitvec(0.into(), 199);
    let components = terms.mk_app(
        Symbol::named("fp"),
        vec![sign, exponent, fraction],
        sort.clone(),
    );
    let mut rewriter = FpRewriter::new();
    for value in [reinterpret, components] {
        let conversion = app(&mut terms, "fp.to_ieee_bv", vec![value], Sort::bitvec(211));
        let result = rewriter.rewrite(&mut terms, conversion);
        assert_eq!(bv_constant(&terms, result), Some((expected.clone(), 211)));
    }

    let nan_bits = terms.mk_bitvec((BigInt::from(2047u32) << 199usize) | BigInt::from(1), 211);
    let nan = terms.mk_app(
        Symbol::indexed("to_fp", vec![11, 200]),
        vec![nan_bits],
        sort.clone(),
    );
    let malformed = terms.mk_app(Symbol::indexed("to_fp", vec![8, 24]), vec![pattern], sort);
    for value in [nan, malformed] {
        let conversion = app(&mut terms, "fp.to_ieee_bv", vec![value], Sort::bitvec(211));
        assert_eq!(rewriter.rewrite(&mut terms, conversion), conversion);
    }
}

#[test]
fn predicates_comparisons_and_mode_literals_fold_to_booleans() {
    let mut terms = TermStore::new();
    let f16 = Sort::FloatingPoint(5, 11);
    let rtz = mode(&mut terms, RoundingMode::RTZ);
    let rne = mode(&mut terms, RoundingMode::RNE);
    let pz = terms.mk_app(Symbol::indexed("+zero", vec![5, 11]), vec![], f16.clone());
    let nz = terms.mk_app(Symbol::indexed("-zero", vec![5, 11]), vec![], f16);
    let cases = [
        (app(&mut terms, "fp.eq", vec![pz, nz], Sort::Bool), true),
        (app(&mut terms, "=", vec![pz, nz], Sort::Bool), false),
        (app(&mut terms, "fp.lt", vec![nz, pz], Sort::Bool), false),
        (app(&mut terms, "fp.isNegative", vec![nz], Sort::Bool), true),
        (app(&mut terms, "=", vec![rtz, rne], Sort::Bool), false),
        (
            app(&mut terms, "distinct", vec![rtz, rne], Sort::Bool),
            true,
        ),
    ];
    let mut rewriter = FpRewriter::new();
    for (term, expected) in cases {
        let folded = rewriter.rewrite(&mut terms, term);
        assert_eq!(folded, terms.mk_bool(expected), "{:?}", terms.get(term));
    }
}

#[test]
fn a_mode_name_at_another_sort_and_a_user_function_are_not_theory_terms() {
    let mut terms = TermStore::new();
    let int_rne = terms.mk_app(Symbol::named("RNE"), vec![], Sort::Int);
    let int_rtz = terms.mk_app(Symbol::named("RTZ"), vec![], Sort::Int);
    let eq = app(&mut terms, "=", vec![int_rne, int_rtz], Sort::Bool);
    let rne = mode(&mut terms, RoundingMode::RNE);
    let one = real(&mut terms, 1, 1);
    // A Named `to_fp` is not the indexed theory conversion.
    let user = app(
        &mut terms,
        "to_fp",
        vec![rne, one],
        Sort::FloatingPoint(8, 24),
    );
    let mut rewriter = FpRewriter::new();
    assert_eq!(rewriter.rewrite(&mut terms, eq), eq);
    assert_eq!(rewriter.rewrite(&mut terms, user), user);
}

#[test]
fn a_deep_chain_is_rewritten_without_recursion() {
    let mut terms = TermStore::new();
    let f32s = Sort::FloatingPoint(8, 24);
    let x = terms.mk_var("x", f32s.clone());
    let mut chain = x;
    for _ in 0..200_000 {
        chain = app(&mut terms, "fp.neg", vec![chain], f32s.clone());
    }
    let mut rewriter = FpRewriter::new();
    assert_eq!(
        rewriter.rewrite(&mut terms, chain),
        chain,
        "nothing constant to fold"
    );
    let pz = terms.mk_app(Symbol::indexed("+zero", vec![8, 24]), vec![], f32s.clone());
    let mut chain = pz;
    for _ in 0..200_001 {
        chain = app(&mut terms, "fp.neg", vec![chain], f32s.clone());
    }
    let folded = rewriter.rewrite(&mut terms, chain);
    assert!(
        value_of(&terms, folded).is_negative(),
        "an odd number of negations"
    );
}

/// A deterministic xorshift stream.
pub(super) struct Stream(pub(super) u64);

impl Stream {
    pub(super) fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
}

pub(super) fn random_leaf(
    terms: &mut TermStore,
    stream: &mut Stream,
    (eb, sb): (u32, u32),
) -> TermId {
    let width = eb + sb;
    let bits = BigInt::from(stream.next() % (1u64 << width));
    let pattern = terms.mk_bitvec(bits, width);
    terms.mk_app(
        Symbol::indexed("to_fp", vec![eb, sb]),
        vec![pattern],
        Sort::FloatingPoint(eb, sb),
    )
}

fn random_tree(
    terms: &mut TermStore,
    stream: &mut Stream,
    format: (u32, u32),
    depth: u32,
) -> TermId {
    if depth == 0 || stream.next() % 4 == 0 {
        return random_leaf(terms, stream, format);
    }
    let sort = Sort::FloatingPoint(format.0, format.1);
    let modes = [
        RoundingMode::RNE,
        RoundingMode::RNA,
        RoundingMode::RTP,
        RoundingMode::RTN,
        RoundingMode::RTZ,
    ];
    let rm = mode(terms, modes[(stream.next() % 5) as usize]);
    let mut sub = |terms: &mut TermStore| random_tree(terms, stream, format, depth - 1);
    let (a, b, c) = (sub(terms), sub(terms), sub(terms));
    match stream.next() % 9 {
        0 => app(terms, "fp.add", vec![rm, a, b], sort),
        1 => app(terms, "fp.sub", vec![rm, a, b], sort),
        2 => app(terms, "fp.mul", vec![rm, a, b], sort),
        3 => app(terms, "fp.div", vec![rm, a, b], sort),
        4 => app(terms, "fp.fma", vec![rm, a, b, c], sort),
        5 => app(terms, "fp.sqrt", vec![rm, a], sort),
        6 => app(terms, "fp.roundToIntegral", vec![rm, a], sort),
        7 => app(terms, "fp.rem", vec![a, b], sort),
        _ => app(terms, "fp.abs", vec![a], sort),
    }
}

/// Folding a random constant expression gives the value the bit-blaster
/// computes for the unfolded expression.
#[test]
fn folded_expressions_match_the_bit_blasted_expressions() {
    let mut stream = Stream(0x1234_5678_9ABC_DEF1);
    let mut compared = 0;
    for format in [(3, 4), (4, 5), (5, 11)] {
        for _ in 0..150 {
            let mut terms = TermStore::new();
            let tree = random_tree(&mut terms, &mut stream, format, 3);
            let folded = FpRewriter::new().rewrite(&mut terms, tree);
            let Some(value) = fp_numeral(&terms, folded) else {
                // Only an undefined rounding (roundToIntegral past the largest
                // finite value of a tiny format) stops a fold.
                continue;
            };
            let mut solver = FpSolver::new(&terms);
            let bits = solver.get_fp(tree);
            assert!(!solver.has_encoding_gap());
            let model = solve_fp_clauses(&solver);
            let (s, e, m) = extract_fp(&model, &bits);
            let circuit = FpModelValue::from_fields(s, e, u128::from(m), format.0, format.1)
                .expect("a small format");
            assert_eq!(
                exact::same_element(&circuit, &value),
                Some(true),
                "{format:?}: circuit {circuit:?}, folded {value:?}"
            );
            compared += 1;
        }
    }
    assert!(compared > 300, "{compared}");
}

#[test]
fn every_conversion_folds_and_round_trips() {
    let mut terms = TermStore::new();
    let rtn = mode(&mut terms, RoundingMode::RTN);
    let minus_seven = terms.mk_bitvec(BigInt::from(-7), 8);
    let signed = to_fp(&mut terms, (8, 24), rtn, minus_seven);
    let unsigned = terms.mk_app(
        Symbol::indexed("to_fp_unsigned", vec![8, 24]),
        vec![rtn, minus_seven],
        Sort::FloatingPoint(8, 24),
    );
    let back = terms.mk_app(
        Symbol::indexed("fp.to_sbv", vec![8]),
        vec![rtn, signed],
        Sort::bitvec(8),
    );
    let to_real = app(&mut terms, "fp.to_real", vec![unsigned], Sort::Real);
    let narrowed = to_fp(&mut terms, (5, 11), rtn, signed);
    let mut rewriter = FpRewriter::new();
    let back = rewriter.rewrite(&mut terms, back);
    assert_eq!(back, terms.mk_bitvec(BigInt::from(-7), 8));
    let to_real = rewriter.rewrite(&mut terms, to_real);
    assert_eq!(
        to_real,
        terms.mk_rational(BigRational::from_integer(249.into()))
    );
    let narrowed = rewriter.rewrite(&mut terms, narrowed);
    let narrowed = value_of(&terms, narrowed);
    assert_eq!(
        exact::to_real(&narrowed),
        Some(BigRational::from_integer((-7).into()))
    );
    assert!(rewriter.folds() >= 5, "{}", rewriter.folds());
}

#[path = "tests/wide.rs"]
mod wide;
