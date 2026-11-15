// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

struct Words {
    terms: TermStore,
    x: TermId,
    y: TermId,
}

fn words() -> Words {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::bitvec(8));
    let y = terms.mk_var("y", Sort::bitvec(8));
    Words { terms, x, y }
}

/// `(= (bvadd c x) y)`, spelled as authored.
fn offset_atom(words: &mut Words, c: u64) -> (TermId, TermId, TermId) {
    let constant = words.terms.mk_bitvec(BigInt::from(c), 8);
    let lhs = words.terms.mk_app(
        Symbol::named("bvadd"),
        vec![constant, words.x],
        Sort::bitvec(8),
    );
    let rhs = words.y;
    let atom = words
        .terms
        .mk_app(Symbol::named("="), vec![lhs, rhs], Sort::Bool);
    (atom, lhs, rhs)
}

fn never_stop() -> impl FnMut() -> bool {
    || true
}

#[test]
fn a_pair_is_read_from_its_second_equality_on() {
    let mut w = words();
    let (_, first_lhs, first_rhs) = offset_atom(&mut w, 1);
    let (_, second_lhs, second_rhs) = offset_atom(&mut w, 2);
    let mut shares = BvOffsetShares::default();
    assert!(w.terms.bv_offset_equality(first_lhs, first_rhs).is_some());
    assert_eq!(
        shares.reading(&w.terms, first_lhs, first_rhs),
        None,
        "a pair one equality reads stays authored"
    );
    assert_eq!(
        shares.reading(&w.terms, first_lhs, first_rhs),
        None,
        "counting the same operands again adds nothing"
    );
    let second = shares
        .reading(&w.terms, second_lhs, second_rhs)
        .expect("a second equality over the pair shares its difference");
    assert!(shares.uses(&second));
    assert_eq!(
        shares.reading(&w.terms, first_lhs, first_rhs),
        None,
        "the first equality keeps the encoding it was given"
    );
}

#[test]
fn the_reachable_count_walks_each_term_once() {
    let mut w = words();
    let (first, ..) = offset_atom(&mut w, 1);
    let (second, second_lhs, second_rhs) = offset_atom(&mut w, 2);
    // The first equality twice in one conjunction is one equality.
    let twice = w
        .terms
        .mk_app(Symbol::named("and"), vec![first, first], Sort::Bool);
    let mut shares = BvOffsetShares::default();
    shares.count_reachable(&w.terms, [twice], false, &mut never_stop());
    let reading = w
        .terms
        .bv_offset_equality(second_lhs, second_rhs)
        .expect("offset equality");
    assert!(!shares.uses(&reading));
    // Under a negation and an `ite`, the second one is found.
    let negated = w
        .terms
        .mk_app(Symbol::named("not"), vec![second], Sort::Bool);
    let guarded = w
        .terms
        .mk_app(Symbol::named("or"), vec![negated, twice], Sort::Bool);
    shares.count_reachable(&w.terms, [guarded], false, &mut never_stop());
    assert!(shares.uses(&reading));
}

#[test]
fn distinct_counts_only_when_asked_and_a_stop_counts_nothing() {
    let mut w = words();
    let (_, lhs, rhs) = offset_atom(&mut w, 1);
    let (other, ..) = offset_atom(&mut w, 2);
    let distinct = w
        .terms
        .mk_app(Symbol::named("distinct"), vec![lhs, rhs], Sort::Bool);
    let root = w
        .terms
        .mk_app(Symbol::named("and"), vec![distinct, other], Sort::Bool);
    let reading = w
        .terms
        .bv_offset_equality(lhs, rhs)
        .expect("offset equality");

    let mut equalities_only = BvOffsetShares::default();
    equalities_only.count_reachable(&w.terms, [root], false, &mut never_stop());
    assert!(!equalities_only.uses(&reading));

    let mut with_distinct = BvOffsetShares::default();
    with_distinct.count_reachable(&w.terms, [root], true, &mut never_stop());
    assert!(with_distinct.uses(&reading));

    let mut stopped = BvOffsetShares::default();
    stopped.count_reachable(&w.terms, [root], true, &mut || false);
    assert!(!stopped.uses(&reading));

    // A handle outside the store is not walked.
    let mut outside = BvOffsetShares::default();
    outside.count_reachable(&w.terms, [TermId::new(u32::MAX)], true, &mut never_stop());
    assert_eq!(outside.walked(), 0);
}

/// A reading that cancels is used alone; one that only renames the authored
/// comparison is not.
#[test]
fn a_reading_that_cancels_is_used_alone() {
    let mut w = words();
    let base = w.terms.mk_var("base", Sort::bitvec(8));
    let left = w
        .terms
        .mk_app(Symbol::named("bvsub"), vec![base, w.x], Sort::bitvec(8));
    let right = w
        .terms
        .mk_app(Symbol::named("bvsub"), vec![base, w.y], Sort::bitvec(8));
    let mut shares = BvOffsetShares::default();
    let reading = shares
        .reading(&w.terms, left, right)
        .expect("base cancels: (= x y) is read");
    assert!(reading.cancels);
    let negated_x = w
        .terms
        .mk_app(Symbol::named("bvneg"), vec![w.x], Sort::bitvec(8));
    let negated_y = w
        .terms
        .mk_app(Symbol::named("bvneg"), vec![w.y], Sort::bitvec(8));
    assert!(w.terms.bv_offset_equality(negated_x, negated_y).is_some());
    assert_eq!(
        BvOffsetShares::default().reading(&w.terms, negated_x, negated_y),
        None,
        "(= (bvneg x) (bvneg y)) cancels nothing and is read once"
    );
}
