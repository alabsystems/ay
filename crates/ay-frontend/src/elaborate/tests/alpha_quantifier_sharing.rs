// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Alpha-equivalence sharing of authored quantifiers (#alpha-quantifier-sharing).
//!
//! One positive pair, then a negative control for every way two quantifiers can
//! differ that alpha-equivalence does NOT permit. A share in any negative case
//! would be a wrong answer, not a missed optimisation, so each is pinned
//! separately rather than folded into one fixture.

use super::*;

/// Elaborate a script and return its concrete authored assertion terms in order.
fn authored_assertions(script: &str) -> (Context, Vec<TermId>) {
    let commands = parse(script).expect("fixture parses");
    let mut context = Context::new();
    for command in &commands {
        context
            .process_command(command)
            .unwrap_or_else(|error| panic!("command must elaborate: {error}"));
    }
    let assertions = context.concrete_authored_assertion_terms();
    (context, assertions)
}

#[test]
fn the_same_existential_on_both_sides_of_a_refutation_is_one_term() {
    // The LIA `recHanoi03` shape: the goal negates exactly the existential the
    // state asserts. The one-resolution-step refutation exists only if the two
    // occurrences are the SAME term.
    let (context, assertions) = authored_assertions(
        "(declare-fun n () Int)\
         (declare-fun m () Int)\
         (assert (and (<= m n) (exists ((v Int)) (<= v n))))\
         (assert (not (exists ((v Int)) (<= v n))))",
    );
    assert_eq!(assertions.len(), 2);
    let TermData::App(Symbol::Named(name), args) = context.terms.get(assertions[0]) else {
        panic!("the first assertion must elaborate to an `and`");
    };
    assert_eq!(name, "and");
    let positive = *args.last().expect("the conjunction has a last conjunct");
    let TermData::Not(negated) = context.terms.get(assertions[1]) else {
        panic!("the second assertion must elaborate to a negation");
    };
    assert_eq!(
        positive, *negated,
        "alpha-equivalent authored existentials must share one term"
    );
}

#[test]
fn binder_spelling_does_not_affect_sharing() {
    let (_, assertions) = authored_assertions(
        "(declare-fun n () Int)\
         (assert (exists ((v Int)) (<= v n)))\
         (assert (exists ((w Int)) (<= w n)))",
    );
    assert_eq!(
        assertions[0], assertions[1],
        "alpha-equivalence must not depend on the authored binder spelling"
    );
}

#[test]
fn a_body_that_drops_its_binder_is_not_shared() {
    let (_, assertions) = authored_assertions(
        "(declare-fun n () Int)\
         (assert (exists ((v Int)) (<= v n)))\
         (assert (exists ((v Int)) (<= n n)))",
    );
    assert_ne!(
        assertions[0], assertions[1],
        "a body that does not mention its binder is a different formula"
    );
}

#[test]
fn a_different_quantifier_kind_is_not_shared() {
    let (_, assertions) = authored_assertions(
        "(declare-fun n () Int)\
         (assert (exists ((v Int)) (<= v n)))\
         (assert (forall ((v Int)) (<= v n)))",
    );
    assert_ne!(
        assertions[0], assertions[1],
        "an existential and a universal are different formulas"
    );
}

#[test]
fn a_different_free_symbol_is_not_shared() {
    let (_, assertions) = authored_assertions(
        "(declare-fun n () Int)\
         (declare-fun m () Int)\
         (assert (exists ((v Int)) (<= v n)))\
         (assert (exists ((v Int)) (<= v m)))",
    );
    assert_ne!(
        assertions[0], assertions[1],
        "alpha-equivalence must compare free symbols exactly"
    );
}

#[test]
fn a_different_binder_sort_is_not_shared() {
    let (_, assertions) = authored_assertions(
        "(declare-fun r () Real)\
         (declare-fun n () Int)\
         (assert (exists ((v Int)) (<= v n)))\
         (assert (exists ((v Real)) (<= v r)))",
    );
    assert_ne!(assertions[0], assertions[1], "binder sorts must match");
}

#[test]
fn binder_position_is_part_of_the_formula() {
    let (_, assertions) = authored_assertions(
        "(declare-fun p (Int Int) Bool)\
         (assert (exists ((a Int) (b Int)) (p a b)))\
         (assert (exists ((a Int) (b Int)) (p b a)))",
    );
    assert_ne!(
        assertions[0], assertions[1],
        "swapping the binder roles changes the formula"
    );
}

#[test]
fn a_nested_binder_correspondence_is_respected() {
    // Inner binders must correspond POSITIONALLY too: `∃a.∃b.(p a b)` and
    // `∃a.∃b.(p b a)` differ, while a pure renaming of both does not.
    let (_, assertions) = authored_assertions(
        "(declare-fun p (Int Int) Bool)\
         (assert (exists ((a Int)) (exists ((b Int)) (p a b))))\
         (assert (exists ((c Int)) (exists ((d Int)) (p c d))))\
         (assert (exists ((a Int)) (exists ((b Int)) (p b a))))",
    );
    assert_eq!(
        assertions[0], assertions[1],
        "a nested renaming is still alpha-equivalent"
    );
    assert_ne!(
        assertions[0], assertions[2],
        "a nested binder swap is a different formula"
    );
}

#[test]
fn quantifiers_carrying_distinct_annotations_are_not_merged() {
    // `:qid` and friends are attached to the TermId rather than interned into
    // it, so sharing two annotated occurrences would transplant one
    // occurrence's annotation onto the other. Both sides are refused.
    let (_, assertions) = authored_assertions(
        "(declare-fun p (Int) Bool)\
         (assert (forall ((v Int)) (! (p v) :qid qid-1)))\
         (assert (forall ((v Int)) (! (p v) :qid qid-2)))",
    );
    assert_ne!(
        assertions[0], assertions[1],
        "an annotated quantifier must keep its own term"
    );
}
