// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The unsigned bit-vector order admitted by `unsigned_order`, and what stays
//! outside it.

use super::*;

fn bv(width: u32) -> Sort {
    Sort::BitVec(ay_core::BitVecSort::new(width))
}

fn compare(terms: &mut TermStore, name: &str, left: TermId, right: TermId) -> TermId {
    terms.mk_app(Symbol::named(name), [left, right], Sort::Bool)
}

fn equals(terms: &mut TermStore, left: TermId, right: TermId) -> TermId {
    terms.mk_app(Symbol::named("="), [left, right], Sort::Bool)
}

#[test]
fn unsigned_comparisons_evaluate_over_the_unsigned_value() {
    let mut terms = TermStore::new();
    let sixty_four = terms.mk_bitvec(BigInt::from(64), 64);
    let sixty_five = terms.mk_bitvec(BigInt::from(65), 64);
    // 2^63: negative as a signed value, the LARGEST of the three unsigned.
    let high_bit = terms.mk_bitvec(BigInt::one() << 63, 64);
    let truth = terms.true_term();
    let falsity = terms.false_term();

    for (name, left, right, holds) in [
        ("bvult", sixty_four, sixty_five, true),
        ("bvult", sixty_five, sixty_four, false),
        ("bvult", sixty_five, sixty_five, false),
        ("bvule", sixty_five, sixty_five, true),
        ("bvugt", high_bit, sixty_five, true),
        ("bvuge", sixty_four, high_bit, false),
        ("bvult", high_bit, sixty_four, false),
    ] {
        let atom = compare(&mut terms, name, left, right);
        assert_eq!(recognize_ground_evaluate(&terms, atom), holds, "{name}");
        let (right_value, wrong_value) = if holds {
            (truth, falsity)
        } else {
            (falsity, truth)
        };
        let step = equals(&mut terms, atom, right_value);
        validate_ground_evaluate(&terms, ProofId(0), &[step], 0, &[])
            .unwrap_or_else(|error| panic!("{name}: the exact value is admitted: {error}"));
        let mutant = equals(&mut terms, atom, wrong_value);
        validate_ground_evaluate(&terms, ProofId(0), &[mutant], 0, &[])
            .expect_err("the opposite value must be refused");
    }
}

#[test]
fn signed_comparisons_and_mixed_widths_stay_outside_the_fragment() {
    let mut terms = TermStore::new();
    let one = terms.mk_bitvec(BigInt::one(), 8);
    let minus_one = terms.mk_bitvec(BigInt::from(255), 8);
    let wide_one = terms.mk_bitvec(BigInt::one(), 16);
    let truth = terms.true_term();
    for name in ["bvslt", "bvsle", "bvsgt", "bvsge"] {
        let atom = compare(&mut terms, name, minus_one, one);
        assert!(
            !recognize_ground_evaluate(&terms, atom),
            "{name} must not be evaluated (carcara misreads negative operands)"
        );
        let step = equals(&mut terms, atom, truth);
        assert!(validate_ground_evaluate(&terms, ProofId(0), &[step], 0, &[]).is_err());
    }
    let mixed = terms.mk_app(Symbol::named("bvult"), [one, wide_one], Sort::Bool);
    assert!(!recognize_ground_evaluate(&terms, mixed));
    // A non-constant operand is never closed.
    let x = terms.mk_var("x", bv(8));
    let open = compare(&mut terms, "bvult", x, one);
    assert!(!recognize_ground_evaluate(&terms, open));
}

#[test]
fn unsigned_comparisons_admit_only_literal_operands() {
    // `(bvugt (bvsub #xff #x01) #x10)` is true, but pinned carcara reads
    // `#xff` as the magnitude 1 inside `bvsub`, computes 0, and refutes the
    // step `(= (bvugt (bvsub #xff #x01) #x10) true)` (measured: "expected
    // terms to be equal: 'false' and 'true'"). The comparison is therefore
    // admitted over literals only, never over a nested closed operand.
    let mut terms = TermStore::new();
    let all_ones = terms.mk_bitvec(BigInt::from(0xff), 8);
    let one = terms.mk_bitvec(BigInt::one(), 8);
    let sixteen = terms.mk_bitvec(BigInt::from(16), 8);
    let difference = terms.mk_app(Symbol::named("bvsub"), [all_ones, one], bv(8));
    let nested = compare(&mut terms, "bvugt", difference, sixteen);
    assert!(!recognize_ground_evaluate(&terms, nested));
    let truth = terms.true_term();
    let step = equals(&mut terms, nested, truth);
    assert!(validate_ground_evaluate(&terms, ProofId(0), &[step], 0, &[]).is_err());
    let literal = compare(&mut terms, "bvugt", all_ones, sixteen);
    assert!(recognize_ground_evaluate(&terms, literal));
}

#[test]
fn wide_unsigned_literal_evaluation_checks_actual_width_and_boolean_value() {
    for width in [65, 128, 4_096] {
        let mut terms = TermStore::new();
        let zero = terms.mk_bitvec(BigInt::from(0), width);
        let high = terms.mk_bitvec(BigInt::one() << (width - 1), width);
        let maximum = terms.mk_bitvec((BigInt::one() << width) - BigInt::one(), width);
        for (name, left, right, holds) in [
            ("bvult", zero, high, true),
            ("bvule", high, high, true),
            ("bvugt", maximum, high, true),
            ("bvuge", zero, maximum, false),
            ("bvult", high, zero, false),
        ] {
            let atom = compare(&mut terms, name, left, right);
            let right_value = if holds {
                terms.true_term()
            } else {
                terms.false_term()
            };
            let wrong_value = if holds {
                terms.false_term()
            } else {
                terms.true_term()
            };
            let equality = equals(&mut terms, atom, right_value);
            validate_ground_evaluate(&terms, ProofId(0), &[equality], 0, &[]).unwrap();
            let forged = equals(&mut terms, atom, wrong_value);
            assert!(validate_ground_evaluate(&terms, ProofId(0), &[forged], 0, &[]).is_err());
            assert!(validate_ground_evaluate(&terms, ProofId(0), &[equality], 1, &[]).is_err());
            assert!(validate_ground_evaluate(&terms, ProofId(0), &[equality], 0, &[atom]).is_err());
        }
        let symbolic = terms.mk_var("open", bv(width));
        let wider = terms.mk_bitvec(BigInt::one(), width + 1);
        let nested = terms.mk_app(Symbol::named("bvmul"), [high, zero], bv(width));
        let truth = terms.true_term();
        for (name, left, right) in [
            ("bvult", symbolic, high),
            ("bvult", zero, wider),
            ("bvult", nested, high),
            ("bvslt", high, maximum),
        ] {
            let atom = compare(&mut terms, name, left, right);
            let equality = equals(&mut terms, atom, truth);
            assert!(validate_ground_evaluate(&terms, ProofId(0), &[equality], 0, &[]).is_err());
        }
        let ill_sorted = terms.mk_app(Symbol::named("bvult"), [zero, high], bv(width));
        let equality = equals(&mut terms, ill_sorted, truth);
        assert!(validate_ground_evaluate(&terms, ProofId(0), &[equality], 0, &[]).is_err());
        let spoof = terms.mk_app(Symbol::indexed("bvult", vec![]), [zero, high], Sort::Bool);
        let equality = equals(&mut terms, spoof, truth);
        assert!(validate_ground_evaluate(&terms, ProofId(0), &[equality], 0, &[]).is_err());
    }
}

#[test]
fn unsigned_literal_evaluation_retains_the_existing_value_bit_limit() {
    let width = u32::try_from(MAX_VALUE_BITS).unwrap();
    for (width, accepted) in [(width, true), (width + 1, false)] {
        let mut terms = TermStore::new();
        let zero = terms.mk_bitvec(BigInt::from(0), width);
        let one = terms.mk_bitvec(BigInt::one(), width);
        let atom = compare(&mut terms, "bvult", zero, one);
        let truth = terms.true_term();
        let equality = equals(&mut terms, atom, truth);
        assert_eq!(
            validate_ground_evaluate(&terms, ProofId(0), &[equality], 0, &[]).is_ok(),
            accepted
        );
    }
}
