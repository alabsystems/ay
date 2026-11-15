// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Malformed raw ASTs must not acquire numeral authority through rewriting.
use super::*;
use crate::{exact, FpModelValue};

#[test]
fn rewriter_rounding_names_do_not_assign_values_to_free_or_declared_symbols() {
    let mut terms = TermStore::new();
    let sort = Sort::Uninterpreted("RoundingMode".into());
    let free = terms.mk_var("RNE", sort.clone());
    assert!(rounding_mode_literal(&terms, free).is_none());
    let indexed = terms.mk_app(Symbol::indexed("RNE", vec![0]), [], sort.clone());
    assert!(rounding_mode_literal(&terms, indexed).is_none());
    let declared = terms.mk_app(Symbol::named("RTP"), [], sort);
    terms.register_declared_function("RTP");
    assert!(rounding_mode_literal(&terms, declared).is_none());
}

#[test]
fn rewriter_declared_constructor_and_arithmetic_heads_remain_opaque() {
    for name in ["fp", "to_fp", "fp.neg"] {
        let mut terms = TermStore::new();
        let value = exact::from_ieee_bits(&BigInt::from(0x3f80_0000u32), 8, 24).unwrap();
        let one = if name == "fp" {
            let sign = terms.mk_bitvec(0.into(), 1);
            let exponent = terms.mk_bitvec(127.into(), 8);
            let fraction = terms.mk_bitvec(0.into(), 23);
            terms.mk_app(
                Symbol::named("fp"),
                [sign, exponent, fraction],
                Sort::FloatingPoint(8, 24),
            )
        } else {
            mk_fp_numeral(&mut terms, &value)
        };
        let negated = terms.mk_app(Symbol::named("fp.neg"), [one], Sort::FloatingPoint(8, 24));
        terms.register_declared_function(name);
        assert_eq!(
            FpRewriter::new().rewrite(&mut terms, negated),
            negated,
            "{name}"
        );
    }
}

#[test]
fn rewriter_cache_is_bound_to_the_physical_term_universe() {
    let mut rewriter = FpRewriter::new();
    for raw in [0x3f80_0000u32, 0x4000_0000u32] {
        let mut terms = TermStore::new();
        let value = exact::from_ieee_bits(&BigInt::from(raw), 8, 24).unwrap();
        let input = mk_fp_numeral(&mut terms, &value);
        let term = terms.mk_app(Symbol::named("fp.neg"), [input], Sort::FloatingPoint(8, 24));
        let result = rewriter.rewrite(&mut terms, term);
        assert_eq!(
            fp_numeral(&terms, result).and_then(|v| exact::to_real(&v)),
            exact::to_real(&value).map(|v| -v)
        );
    }
}

#[test]
fn rewriter_cache_retires_when_the_same_store_registers_a_user_head() {
    let mut terms = TermStore::new();
    let value = exact::from_ieee_bits(&BigInt::from(0x3f80_0000u32), 8, 24).unwrap();
    let one = mk_fp_numeral(&mut terms, &value);
    let term = terms.mk_app(Symbol::named("fp.neg"), [one], Sort::FloatingPoint(8, 24));
    let mut rewriter = FpRewriter::new();
    assert_ne!(rewriter.rewrite(&mut terms, term), term);
    terms.register_declared_function("fp.neg");
    assert_eq!(rewriter.rewrite(&mut terms, term), term);
}

#[test]
fn rewriter_does_not_interpret_declared_rational_or_ite_heads() {
    let mut terms = TermStore::new();
    let rm = tests::mode(&mut terms, RoundingMode::RNE);
    let one_real = terms.mk_rational(BigRational::from_integer(1.into()));
    let sum = terms.mk_app(Symbol::named("+"), [one_real, one_real], Sort::Real);
    let converted = tests::to_fp(&mut terms, (8, 24), rm, sum);
    terms.register_declared_function("+");
    assert_eq!(FpRewriter::new().rewrite(&mut terms, converted), converted);

    let value = exact::from_ieee_bits(&BigInt::from(0x3f80_0000u32), 8, 24).unwrap();
    let one = mk_fp_numeral(&mut terms, &value);
    let two = mk_fp_numeral(&mut terms, &exact::neg(&value).unwrap());
    let condition = terms.mk_var("condition", Sort::Bool);
    let opaque = terms.mk_app(
        Symbol::named("ite"),
        [condition, one, two],
        Sort::FloatingPoint(8, 24),
    );
    let term = terms.mk_app(
        Symbol::named("fp.neg"),
        [opaque],
        Sort::FloatingPoint(8, 24),
    );
    terms.register_declared_function("ite");
    assert_eq!(FpRewriter::new().rewrite(&mut terms, term), term);
}

#[test]
fn mismatched_literal_indices_stay_opaque_under_arithmetic() {
    let mut terms = TermStore::new();
    let sort = Sort::FloatingPoint(8, 24);
    let pattern = terms.mk_bitvec(0x3f80_0000.into(), 32);
    let malformed = terms.mk_app(
        Symbol::indexed("to_fp", vec![11, 53]),
        vec![pattern],
        sort.clone(),
    );
    let negated = terms.mk_app(Symbol::named("fp.neg"), vec![malformed], sort.clone());
    let mut rewriter = FpRewriter::new();
    assert!(fp_numeral(&terms, malformed).is_none());
    assert_eq!(rewriter.rewrite(&mut terms, negated), negated);
    for name in ["+zero", "-zero", "+oo", "-oo", "NaN"] {
        let value = terms.mk_app(Symbol::indexed(name, vec![11, 53]), vec![], sort.clone());
        assert!(fp_numeral(&terms, value).is_none(), "{name}");
    }
}

#[test]
fn invalid_formats_and_component_widths_refuse_without_panicking() {
    let mut terms = TermStore::new();
    let sign = terms.mk_bitvec(0.into(), 1);
    let exponent = terms.mk_bitvec(127.into(), 16);
    let fraction = terms.mk_bitvec(0.into(), 23);
    for (eb, sb) in [(8, 24), (0, 0), (u32::MAX, 1), (8, 0)] {
        let value = terms.mk_app(
            Symbol::named("fp"),
            vec![sign, exponent, fraction],
            Sort::FloatingPoint(eb, sb),
        );
        assert!(fp_numeral(&terms, value).is_none());
    }
}

#[test]
fn folded_values_must_keep_the_declared_result_sort() {
    let mut terms = TermStore::new();
    let value = exact::from_ieee_bits(&BigInt::from(0x3f80_0000u32), 8, 24).unwrap();
    let one = mk_fp_numeral(&mut terms, &value);
    let rm = tests::mode(&mut terms, RoundingMode::RNE);
    let mut rewriter = FpRewriter::new();
    for (name, args, sort) in [
        ("fp.neg", vec![one], Sort::FloatingPoint(11, 53)),
        ("fp.add", vec![rm, one, one], Sort::FloatingPoint(11, 53)),
        ("fp.isNaN", vec![one], Sort::Real),
        ("=", vec![one, one], Sort::Real),
    ] {
        let term = terms.mk_app(Symbol::named(name), args, sort);
        assert_eq!(rewriter.rewrite(&mut terms, term), term, "{name}");
    }
    let real = terms.mk_int(1.into());
    for (symbol, args, sort) in [
        (
            Symbol::indexed("to_fp", vec![11, 53]),
            vec![rm, real],
            Sort::FloatingPoint(8, 24),
        ),
        (
            Symbol::indexed("fp.to_ubv", vec![16]),
            vec![rm, one],
            Sort::bitvec(8),
        ),
    ] {
        let term = terms.mk_app(symbol, args, sort);
        assert_eq!(rewriter.rewrite(&mut terms, term), term);
    }
}

#[test]
fn valid_nan_remains_a_numeral_without_specifying_its_ieee_encoding() {
    let mut terms = TermStore::new();
    let nan = terms.mk_app(
        Symbol::indexed("NaN", vec![8, 24]),
        vec![],
        Sort::FloatingPoint(8, 24),
    );
    assert!(matches!(
        fp_numeral(&terms, nan),
        Some(FpModelValue::NaN { eb: 8, sb: 24 })
    ));
    let encoded = terms.mk_app(Symbol::named("fp.to_ieee_bv"), vec![nan], Sort::bitvec(32));
    assert_eq!(FpRewriter::new().rewrite(&mut terms, encoded), encoded);
}
