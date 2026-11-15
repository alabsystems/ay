// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! End to end through [`validate`]: each reading the producer may take of a
//! clause (`hypotheses.rs`, `case_split.rs`, `wide_equality.rs`) admits a
//! valid lemma and rejects the false lemma one literal away from it. A
//! reading that substituted too much, or split into cases that do not cover
//! every assignment, would admit the false one.

#![cfg(test)]

use super::*;

const WIDTH: u32 = 32;

fn word(terms: &mut TermStore, name: &str, width: u32) -> TermId {
    terms.mk_var(name.to_string(), Sort::bitvec(width))
}

fn literal(terms: &mut TermStore, value: u64, width: u32) -> TermId {
    terms.mk_bitvec(value.into(), width)
}

fn apply(terms: &mut TermStore, name: &str, args: &[TermId], width: u32) -> TermId {
    terms.mk_app(Symbol::named(name), args, Sort::bitvec(width))
}

fn equal(terms: &mut TermStore, left: TermId, right: TermId) -> TermId {
    terms.mk_app(Symbol::named("="), [left, right], Sort::Bool)
}

fn verdict(terms: &TermStore, clause: &[TermId]) -> Result<(), Failure> {
    validate(terms, clause, &mut || Ok(()))
}

/// `(cl (not (= v w)) (= (bvmul v 5) (bvmul w K)))`: valid for `K = 5`
/// only. Read with its hypothesis, the valid clause is one product on both
/// sides; the false one is rejected.
#[test]
fn a_hypothesis_is_read_as_a_substitution_and_a_false_lemma_is_still_rejected() {
    let mut terms = TermStore::new();
    let (v, w) = (word(&mut terms, "v", WIDTH), word(&mut terms, "w", WIDTH));
    let hypothesis = equal(&mut terms, v, w);
    let not_hypothesis = terms.mk_not_raw(hypothesis);
    let five = literal(&mut terms, 5, WIDTH);
    let six = literal(&mut terms, 6, WIDTH);
    let left = apply(&mut terms, "bvmul", &[v, five], WIDTH);
    for (factor, valid) in [(five, true), (six, false)] {
        let right = apply(&mut terms, "bvmul", &[w, factor], WIDTH);
        let goal = equal(&mut terms, left, right);
        let result = verdict(&terms, &[not_hypothesis, goal]);
        if valid {
            assert_eq!(result, Ok(()));
        } else {
            assert!(matches!(result, Err(Failure::Rejected(_))), "{result:?}");
        }
    }
}

/// `(= (ite (= b 1) X (bvudiv a b)) (bvudiv a b))`: valid for `X = a`, since
/// dividing by one is the identity, and false for `X = a + 1`. Both cases of
/// the split must hold for the lemma to be admitted.
#[test]
fn a_lemma_guarded_by_a_variable_literal_condition_is_admitted_only_when_both_cases_hold() {
    let mut terms = TermStore::new();
    let (a, b) = (word(&mut terms, "a", WIDTH), word(&mut terms, "b", WIDTH));
    let one = literal(&mut terms, 1, WIDTH);
    let condition = equal(&mut terms, b, one);
    let quotient = apply(&mut terms, "bvudiv", &[a, b], WIDTH);
    let successor = apply(&mut terms, "bvadd", &[a, one], WIDTH);
    for (guarded, valid) in [(a, true), (successor, false)] {
        let ite = terms.mk_ite_raw(condition, guarded, quotient);
        let goal = equal(&mut terms, ite, quotient);
        let result = verdict(&terms, &[goal]);
        if valid {
            assert_eq!(result, Ok(()));
        } else {
            assert!(matches!(result, Err(Failure::Rejected(_))), "{result:?}");
        }
    }
}

/// A 192-bit `concat` equality is checked slice by slice: associativity
/// holds, and swapping two 64-bit words is refused.
#[test]
fn an_equality_wider_than_the_producer_is_checked_slice_by_slice() {
    let mut terms = TermStore::new();
    let (a, b, c) = (
        word(&mut terms, "a", 64),
        word(&mut terms, "b", 64),
        word(&mut terms, "c", 64),
    );
    let bc = apply(&mut terms, "concat", &[b, c], 128);
    let a_bc = apply(&mut terms, "concat", &[a, bc], 192);
    let ab = apply(&mut terms, "concat", &[a, b], 128);
    let ab_c = apply(&mut terms, "concat", &[ab, c], 192);
    let associative = equal(&mut terms, a_bc, ab_c);
    assert_eq!(verdict(&terms, &[associative]), Ok(()));
    let ac = apply(&mut terms, "concat", &[a, c], 128);
    let ac_b = apply(&mut terms, "concat", &[ac, b], 192);
    let swapped = equal(&mut terms, a_bc, ac_b);
    let result = verdict(&terms, &[swapped]);
    assert!(matches!(result, Err(Failure::Rejected(_))), "{result:?}");
}
