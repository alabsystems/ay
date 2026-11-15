// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Raw indexed extracts used by the BV-to-FP bridge, without constructor folding.

use super::*;

fn extract(terms: &mut TermStore, arg: TermId, high: u32, low: u32) -> TermId {
    terms.mk_app(
        Symbol::indexed("extract", vec![high, low]),
        [arg],
        Sort::bitvec(high - low + 1),
    )
}

fn from_bits(terms: &mut TermStore, bits: TermId, eb: u32, sb: u32) -> TermId {
    let sign = extract(terms, bits, eb + sb - 1, eb + sb - 1);
    let exponent = extract(terms, bits, eb + sb - 2, sb - 1);
    let significand = extract(terms, bits, sb - 2, 0);
    for part in [sign, exponent, significand] {
        assert!(
            matches!(terms.get(part), TermData::App(Symbol::Indexed(name, _), _) if name == "extract")
        );
    }
    terms.mk_app(
        Symbol::named("fp"),
        [sign, exponent, significand],
        Sort::FloatingPoint(eb, sb),
    )
}

fn assert_predicate(terms: &mut TermStore, fp: TermId, name: &str, expected: bool) {
    let predicate = terms.mk_app(Symbol::named(name), [fp], Sort::Bool);
    let not_predicate = terms.mk_not_raw(predicate);
    let (valid, invalid) = if expected {
        (predicate, not_predicate)
    } else {
        (not_predicate, predicate)
    };
    assert!(recognize_fp_ground_eval(terms, &[valid]), "{name}");
    assert!(validate_fp_ground_eval(terms, ProofId(0), &[valid]).is_ok());
    assert!(!recognize_fp_ground_eval(terms, &[invalid]), "{name}");
    assert!(validate_fp_ground_eval(terms, ProofId(0), &[invalid]).is_err());
}

fn check_bridge_format(eb: u32, sb: u32) {
    let width = eb + sb;
    let sign = 1_u64 << (width - 1);
    let infinity = ((1_u64 << eb) - 1) << (sb - 1);
    let one = ((1_u64 << (eb - 1)) - 1) << (sb - 1);
    let mut terms = TermStore::new();
    for (bits, predicate, expected) in [
        (0, "fp.isNaN", false),
        (sign, "fp.isZero", true),
        (sign, "fp.isNegative", true),
        (infinity, "fp.isInfinite", true),
        (infinity | 1, "fp.isNaN", true),
        (one, "fp.isNormal", true),
        (1, "fp.isSubnormal", true),
    ] {
        let bits = terms.mk_bitvec(BigInt::from(bits), width);
        let fp = from_bits(&mut terms, bits, eb, sb);
        assert_predicate(&mut terms, fp, predicate, expected);
    }
}

#[test]
fn raw_extract_bridge_float16_true_and_false_clauses() {
    check_bridge_format(5, 11);
}

#[test]
fn raw_extract_bridge_float32_true_and_false_clauses() {
    check_bridge_format(8, 24);
}

#[test]
fn raw_extract_bridge_float64_true_and_false_clauses() {
    check_bridge_format(11, 53);
}

fn eval(terms: &TermStore, term: TermId) -> Option<Val> {
    let mut no_caller = |_, _| true;
    let mut meter = Meter::new(&mut no_caller);
    Evaluator::new(terms, HashMap::default(), &mut meter).eval(
        term,
        &HashMap::default(),
        &mut HashMap::default(),
        0,
    )
}

#[test]
fn extract_rejects_malformed_identity_arity_bounds_and_sorts() {
    let mut terms = TermStore::new();
    let byte = terms.mk_bitvec(BigInt::from(0xb6), 8);
    let integer = terms.mk_int(BigInt::zero());
    let too_wide = terms.mk_bitvec(BigInt::zero(), MAX_BV_WIDTH + 1);
    let zero_width = terms.mk_bitvec(BigInt::zero(), 0);
    let good = extract(&mut terms, byte, 5, 2);
    assert_eq!(eval(&terms, good), Some(Val::Bv(BigInt::from(13), 4)));
    let full = extract(&mut terms, byte, 7, 0);
    assert_eq!(eval(&terms, full), Some(Val::Bv(BigInt::from(0xb6), 8)));
    for (symbol, args, sort) in [
        (Symbol::named("extract"), vec![byte], Sort::bitvec(4)),
        (
            Symbol::indexed("extract", vec![]),
            vec![byte],
            Sort::bitvec(4),
        ),
        (
            Symbol::indexed("extract", vec![5]),
            vec![byte],
            Sort::bitvec(4),
        ),
        (
            Symbol::indexed("extract", vec![5, 2, 0]),
            vec![byte],
            Sort::bitvec(4),
        ),
        (
            Symbol::indexed("extract", vec![5, 2]),
            vec![],
            Sort::bitvec(4),
        ),
        (
            Symbol::indexed("extract", vec![5, 2]),
            vec![byte, byte],
            Sort::bitvec(4),
        ),
        (
            Symbol::indexed("extract", vec![2, 5]),
            vec![byte],
            Sort::bitvec(4),
        ),
        (
            Symbol::indexed("extract", vec![8, 5]),
            vec![byte],
            Sort::bitvec(4),
        ),
        (
            Symbol::indexed("extract", vec![u32::MAX, 0]),
            vec![byte],
            Sort::bitvec(4),
        ),
        (
            Symbol::indexed("extract", vec![5, 2]),
            vec![byte],
            Sort::bitvec(5),
        ),
        (
            Symbol::indexed("extract", vec![5, 2]),
            vec![byte],
            Sort::Bool,
        ),
        (
            Symbol::indexed("extract", vec![5, 2]),
            vec![integer],
            Sort::bitvec(4),
        ),
        (
            Symbol::indexed("extract", vec![5, 2]),
            vec![too_wide],
            Sort::bitvec(4),
        ),
        (
            Symbol::indexed("extract", vec![0, 0]),
            vec![zero_width],
            Sort::bitvec(1),
        ),
    ] {
        let malformed = terms.mk_app(symbol, args, sort);
        assert_eq!(eval(&terms, malformed), None, "{:?}", terms.get(malformed));
    }
    let bits = terms.mk_bitvec(BigInt::zero(), 64);
    let fp = from_bits(&mut terms, bits, 11, 53);
    for name in ["fp.isNaN", "fp.isZero"] {
        let malformed = terms.mk_app(Symbol::indexed(name, vec![0]), [fp], Sort::Bool);
        let negated = terms.mk_not_raw(malformed);
        assert!(!recognize_fp_ground_eval(&terms, &[malformed]));
        assert!(!recognize_fp_ground_eval(&terms, &[negated]));
    }
}

#[test]
fn extract_rejects_noncanonical_snapshot_payloads_before_evaluation() {
    // The normal constructor canonicalizes constants, so use the actual
    // checker-only snapshot boundary to retain hostile constant payloads.
    let mut terms = TermStore::new();
    let bits = terms.mk_bitvec(BigInt::zero(), 64);
    let fp = from_bits(&mut terms, bits, 11, 53);
    let is_nan = terms.mk_app(Symbol::named("fp.isNaN"), [fp], Sort::Bool);
    let not_nan = terms.mk_not_raw(is_nan);
    let entries = terms.entries_snapshot();
    for (value, width, sort) in [
        (BigInt::from(-1), 64, Sort::bitvec(64)),
        (BigInt::one() << 64, 64, Sort::bitvec(64)),
        (BigInt::one() << 4096, 64, Sort::bitvec(64)),
        (BigInt::zero(), 63, Sort::bitvec(64)),
        (BigInt::zero(), 64, Sort::bitvec(63)),
        (BigInt::zero(), 64, Sort::Bool),
    ] {
        let mut forged = entries.clone();
        forged[bits.0 as usize] = (TermData::Const(Constant::BitVec { value, width }), sort);
        let forged = TermStore::from_entries(forged, None, None, 0);
        assert!(!recognize_fp_ground_eval(&forged, &[not_nan]));
        assert!(validate_fp_ground_eval(&forged, ProofId(0), &[not_nan]).is_err());
    }
}

#[test]
fn extract_keeps_shared_work_depth_and_residual_domain_limits() {
    let mut terms = TermStore::new();
    let byte = terms.mk_bitvec(BigInt::from(0xff), 8);
    let extracted = extract(&mut terms, byte, 7, 0);
    let mut no_caller = |_, _| true;
    let mut meter = Meter::with_local_limit(&mut no_caller, 1);
    let mut evaluator = Evaluator::new(&terms, HashMap::default(), &mut meter);
    assert_eq!(
        evaluator.eval(extracted, &HashMap::default(), &mut HashMap::default(), 0),
        None
    );
    assert!(evaluator.meter.refused());
    let mut meter = Meter::new(&mut no_caller);
    let mut evaluator = Evaluator::new(&terms, HashMap::default(), &mut meter);
    assert_eq!(
        evaluator.eval(extracted, &HashMap::default(), &mut HashMap::default(), 0),
        Some(Val::Bv(BigInt::from(0xff), 8)),
    );
    assert!(!evaluator.meter.refused());
    let mut nested = byte;
    for _ in 0..=MAX_DEPTH {
        nested = extract(&mut terms, nested, 7, 0);
    }
    assert_eq!(eval(&terms, nested), None);
    let free = terms.mk_var("free_bits", Sort::bitvec(64));
    let fp = from_bits(&mut terms, free, 11, 53);
    let is_nan = terms.mk_app(Symbol::named("fp.isNaN"), [fp], Sort::Bool);
    let not_nan = terms.mk_not_raw(is_nan);
    assert!(!recognize_fp_ground_eval(&terms, &[not_nan]));
    assert!(validate_fp_ground_eval(&terms, ProofId(0), &[not_nan]).is_err());
}
