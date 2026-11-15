// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![cfg(test)]

use super::*;

#[test]
fn named_arity_and_operand_type_failures_match_without_expanding_the_grammar() {
    let mut terms = TermStore::new();
    let a = bv(&mut terms, 1, 2);
    let b = bv(&mut terms, 1, 1);
    let truth = terms.true_term();
    for name in operators::BINARY.iter().chain(operators::COMPARISONS) {
        for args in [vec![], vec![a], vec![a, a, a]] {
            let term = app(&mut terms, name, &args, Sort::Bool);
            assert_eq!(compare(&terms, term, &[]), None);
        }
        if *name == "=" {
            continue; // Equality compares EvalValue variants, not BV operand types.
        }
        for args in [[a, b], [truth, a], [a, truth]] {
            let term = app(&mut terms, name, &args, Sort::Bool);
            assert_eq!(compare(&terms, term, &[]), None);
        }
    }
    for name in ["bvnot", "bvneg"] {
        for args in [vec![], vec![a, a], vec![truth]] {
            let term = app(&mut terms, name, &args, Sort::bitvec(2));
            assert_eq!(compare(&terms, term, &[]), None);
        }
    }
    for name in ["and", "or"] {
        let term = app(&mut terms, name, &[truth, a], Sort::Bool);
        assert_eq!(compare(&terms, term, &[]), None);
    }
    for name in ["xor", "=>", "distinct", "bvcomp", "int2bv", "unknown"] {
        let term = app(&mut terms, name, &[a, a], Sort::Bool);
        assert_eq!(compare(&terms, term, &[]), None);
    }
    let integer = terms.mk_int(BigInt::from(2));
    assert_eq!(compare(&terms, integer, &[]), None);
    let local = terms.mk_let(vec![("local".to_owned(), a)], a);
    assert_eq!(compare(&terms, local, &[]), None);
}

#[test]
fn raw_integer_payload_conversion_keeps_masking_and_out_of_machine_range_refusal() {
    // No term minting in reconstructed checker-only stores. Keep every handle
    // live; malformed-ID authentication belongs to the structural preflight.
    for (value, width, expected) in [
        (BigInt::from(7), 2, Some(3)),
        (BigInt::from(-1), 2, None),
        (BigInt::from(u64::MAX), 64, Some(u64::MAX)),
        (BigInt::from(1u8) << 64usize, 64, None),
    ] {
        let terms = TermStore::from_entries(
            vec![(
                TermData::Const(Constant::BitVec { value, width }),
                Sort::bitvec(width),
            )],
            None,
            None,
            0,
        );
        assert_eq!(
            compare(&terms, TermId(0), &[]),
            expected.map(|value| EvalValue::BitVec { value, width })
        );
    }
}

#[test]
fn raw_not_and_ite_reject_non_boolean_values_in_the_same_accessed_positions() {
    let value = TermData::Const(Constant::BitVec {
        value: BigInt::from(1),
        width: 1,
    });
    let entries = vec![
        (value, Sort::bitvec(1)),
        (TermData::Const(Constant::Bool(true)), Sort::Bool),
        (TermData::Not(TermId(0)), Sort::Bool),
        (TermData::Ite(TermId(0), TermId(1), TermId(1)), Sort::Bool),
    ];
    let terms = TermStore::from_entries(entries, Some(TermId(1)), None, 0);
    assert_eq!(compare(&terms, TermId(2), &[]), None);
    assert_eq!(compare(&terms, TermId(3), &[]), None);
}
