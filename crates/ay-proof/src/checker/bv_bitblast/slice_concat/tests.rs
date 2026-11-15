// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

fn raw_concat(terms: &mut TermStore, high: TermId, low: TermId, width: u32) -> TermId {
    terms.mk_app(Symbol::named("concat"), [high, low], Sort::bitvec(width))
}

#[test]
fn every_six_bit_slice_matches_the_integer_value_and_rejects_a_changed_bit() {
    for value in 0_u32..64 {
        let mut terms = TermStore::new();
        let upper = terms.mk_bitvec((value >> 3).into(), 3);
        let middle = terms.mk_bitvec(((value >> 1) & 3).into(), 2);
        let lower = terms.mk_bitvec((value & 1).into(), 1);
        let tail = raw_concat(&mut terms, middle, lower, 3);
        let source = raw_concat(&mut terms, upper, tail, 6);
        for high in 0..6 {
            for low in 0..=high {
                let width = high - low + 1;
                let extracted = terms.mk_app(
                    Symbol::indexed("extract", vec![high, low]),
                    [source],
                    Sort::bitvec(width),
                );
                let expected = (value >> low) & ((1 << width) - 1);
                for (literal, valid) in [(expected, true), (expected ^ 1, false)] {
                    let literal = terms.mk_bitvec(literal.into(), width);
                    let equality =
                        terms.mk_app(Symbol::named("="), [extracted, literal], Sort::Bool);
                    let negated = terms.mk_not_raw(equality);
                    let result = authenticate_bool_bv_unsat_query(&terms, &[negated], None);
                    assert_eq!(
                        result.is_ok(),
                        valid,
                        "value={value} range={high}:{low}: {result:?}"
                    );
                    if !valid {
                        assert!(matches!(
                            result,
                            Err(BoolBvUnsatAuthenticationError::Satisfiable)
                        ));
                    }
                }
            }
        }
    }
}

#[test]
fn extracting_one_child_still_refuses_malformed_discarded_children() {
    let mut terms = TermStore::new();
    let good = terms.mk_var("good", Sort::bitvec(4));
    let bool_value = terms.mk_var("wrong_sort", Sort::Bool);
    let unknown = terms.mk_app(Symbol::named("unsupported"), [good], Sort::bitvec(4));
    for bad in [bool_value, unknown] {
        for source in [
            raw_concat(&mut terms, bad, good, 8),
            raw_concat(&mut terms, good, bad, 8),
        ] {
            for (high, low) in [(3, 0), (7, 4)] {
                let mut lowerer =
                    ProofProducingLowerer::new(&terms, Instant::now() + Duration::from_secs(3));
                assert!(lowerer.lower_bv_extract(source, high, low).is_err());
            }
        }
    }
    let bad_width = raw_concat(&mut terms, good, good, 9);
    let mut lowerer = ProofProducingLowerer::new(&terms, Instant::now() + Duration::from_secs(3));
    assert!(lowerer.lower_bv_extract(bad_width, 3, 0).is_err());
}

#[test]
fn slice_lowering_preserves_every_cancellation_boundary() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::bitvec(4));
    let b = terms.mk_var("b", Sort::bitvec(4));
    let source = raw_concat(&mut terms, a, b, 8);
    let mut polls = 0;
    let mut counter = || {
        polls += 1;
        true
    };
    let mut lowerer = ProofProducingLowerer::new(&terms, Instant::now() + Duration::from_secs(3));
    lowerer.keep_going = Some(&mut counter);
    lowerer.lower_bv_extract(source, 5, 2).unwrap();
    drop(lowerer);
    for stop in 1..=polls {
        let mut calls = 0;
        let mut cancel = || {
            calls += 1;
            calls != stop
        };
        let mut lowerer =
            ProofProducingLowerer::new(&terms, Instant::now() + Duration::from_secs(3));
        lowerer.keep_going = Some(&mut cancel);
        assert!(lowerer.lower_bv_extract(source, 5, 2).is_err());
        assert!(lowerer.cancelled);
        drop(lowerer);
        assert_eq!(calls, stop);
    }
}

/// Every slice of a six-bit `zero_extend` of a four-bit literal matches its
/// integer value, whether it lies inside the operand (projected out of the
/// lowered extension) or reaches the zero bits, and a changed bit is refused.
#[test]
fn every_slice_of_a_zero_extension_matches_the_integer_value() {
    for value in 0_u32..16 {
        let mut terms = TermStore::new();
        let operand = terms.mk_bitvec(value.into(), 4);
        let source = terms.mk_app(
            Symbol::indexed("zero_extend", vec![2]),
            [operand],
            Sort::bitvec(6),
        );
        for high in 0..6 {
            for low in 0..=high {
                let width = high - low + 1;
                let extracted = terms.mk_app(
                    Symbol::indexed("extract", vec![high, low]),
                    [source],
                    Sort::bitvec(width),
                );
                let expected = (value >> low) & ((1 << width) - 1);
                for (literal, valid) in [(expected, true), (expected ^ 1, false)] {
                    let literal = terms.mk_bitvec(literal.into(), width);
                    let equality =
                        terms.mk_app(Symbol::named("="), [extracted, literal], Sort::Bool);
                    let negated = terms.mk_not_raw(equality);
                    let result = authenticate_bool_bv_unsat_query(&terms, &[negated], None);
                    assert_eq!(
                        result.is_ok(),
                        valid,
                        "value={value} range={high}:{low}: {result:?}"
                    );
                }
            }
        }
    }
}
