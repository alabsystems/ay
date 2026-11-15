// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Independent, exact-source Int div/mod checks; no solver verdict is an input.

use ay_core::{Sort, Symbol, TermId, TermStore};
use ay_proof::{authenticate_bv_lia_unsat_query, BvLiaUnsatAuthenticationError};
use num_bigint::BigInt;

fn operation(terms: &mut TermStore, head: &str, divisor: i128) -> (TermId, TermId) {
    let x = terms.mk_var("x".to_string(), Sort::Int);
    let divisor = terms.mk_int(BigInt::from(divisor));
    let operation = terms.mk_app(Symbol::named(head), [x, divisor], Sort::Int);
    (x, operation)
}

fn check(head: &str, dividend: i128, divisor: i128, expected: i128) {
    for (claimed, negate, unsat) in [
        (expected, false, false),
        (expected, true, true),
        (expected + 1, false, true),
    ] {
        let mut terms = TermStore::new();
        let (x, operation) = operation(&mut terms, head, divisor);
        let dividend = terms.mk_int(BigInt::from(dividend));
        let pin = terms.mk_eq(x, dividend);
        let claimed = terms.mk_int(BigInt::from(claimed));
        let equality = terms.mk_eq(operation, claimed);
        let claim = if negate {
            terms.mk_not(equality)
        } else {
            equality
        };
        let result = authenticate_bv_lia_unsat_query(&terms, &[pin, claim], None);
        if unsat {
            let evidence = result.expect("the exact arithmetic contradiction must authenticate");
            assert!(evidence.is_current_for(&terms, &[pin, claim]));
        } else {
            assert!(matches!(
                result,
                Err(BvLiaUnsatAuthenticationError::Satisfiable)
            ));
        }
    }
}

#[test]
fn signed_integer_division_and_modulus_match_euclidean_equations() {
    for dividend in -16_i128..=16 {
        for divisor in (-5_i128..=5).filter(|value| *value != 0) {
            check("div", dividend, divisor, dividend.div_euclid(divisor));
            check("mod", dividend, divisor, dividend.rem_euclid(divisor));
        }
    }
    let min = i128::from(i64::MIN);
    check("div", min, -1, -min);
    check("mod", min, -1, 0);
}

#[test]
fn bare_zero_division_and_modulus_never_authenticate_a_chosen_value() {
    for head in ["div", "mod"] {
        for claimed in [-1, 0, 1] {
            let mut terms = TermStore::new();
            let (x, operation) = operation(&mut terms, head, 0);
            let seven = terms.mk_int(BigInt::from(7));
            let pin = terms.mk_eq(x, seven);
            let claimed = terms.mk_int(BigInt::from(claimed));
            let equality = terms.mk_eq(operation, claimed);
            let unequal = terms.mk_not(equality);
            for claim in [equality, unequal] {
                assert!(authenticate_bv_lia_unsat_query(&terms, &[pin, claim], None).is_err());
            }
        }
    }
}

#[test]
fn an_unreachable_zero_division_branch_does_not_block_an_honest_totalization() {
    for head in ["div", "mod"] {
        let mut terms = TermStore::new();
        let (x, operation) = operation(&mut terms, head, 0);
        let seven = terms.mk_int(BigInt::from(7));
        let pin = terms.mk_eq(x, seven);
        let zero = terms.mk_int(BigInt::from(0));
        let selected = terms.true_term();
        let total = terms.mk_ite_raw(selected, zero, operation);
        let equal = terms.mk_eq(total, zero);
        let wrong = terms.mk_not(equal);
        authenticate_bv_lia_unsat_query(&terms, &[pin, wrong], None)
            .expect("only the selected branch is evaluated");
        assert!(matches!(
            authenticate_bv_lia_unsat_query(&terms, &[pin, equal], None),
            Err(BvLiaUnsatAuthenticationError::Satisfiable)
        ));
    }
}

#[test]
fn integer_division_rejects_malformed_arity_and_result_sort() {
    for (sort, arity) in [
        (Sort::Int, 1),
        (Sort::Int, 3),
        (Sort::Bool, 1),
        (Sort::Bool, 2),
        (Sort::Bool, 3),
    ] {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x".to_string(), Sort::Int);
        let malformed = terms.mk_app(Symbol::named("div"), vec![x; arity], sort);
        let claim = terms.mk_app(Symbol::named("="), [malformed, malformed], Sort::Bool);
        let false_claim = terms.mk_not_raw(claim);
        assert!(authenticate_bv_lia_unsat_query(&terms, &[false_claim], None).is_err());
    }
}
