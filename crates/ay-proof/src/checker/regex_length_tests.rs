// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for the independent regex minimum-length checker.
//!
//! Two load-bearing properties:
//!
//! 1. A bound the checker's own compositional computation supports is
//!    ACCEPTED, for each modelled node.
//! 2. An OVER-STRONG bound, a mismatched membership subject, a wrong clause
//!    shape, and an unmodelled operator are all REJECTED — a forged
//!    `regex_length_lower_bound` cannot pin a string's length out of nothing.

use super::*;
use ay_core::{ProofId, Sort, Symbol, TermId, TermStore};

fn v(terms: &mut TermStore, name: &str) -> TermId {
    terms.mk_var(name, Sort::String)
}
fn to_re(terms: &mut TermStore, s: &str) -> TermId {
    let c = terms.mk_string(s.to_string());
    terms.mk_app(Symbol::named("str.to_re"), [c], Sort::RegLan)
}
fn re(terms: &mut TermStore, name: &str, args: &[TermId]) -> TermId {
    terms.mk_app(Symbol::named(name), args, Sort::RegLan)
}
fn re_indexed(terms: &mut TermStore, name: &str, indices: Vec<u32>, args: &[TermId]) -> TermId {
    terms.mk_app(Symbol::indexed(name, indices), args, Sort::RegLan)
}
fn in_re(terms: &mut TermStore, x: TermId, r: TermId) -> TermId {
    terms.mk_app(Symbol::named("str.in_re"), [x, r], Sort::Bool)
}
fn bound_literal(terms: &mut TermStore, k: i64, x: TermId) -> TermId {
    let k = terms.mk_int(BigInt::from(k));
    let len = terms.mk_app(Symbol::named("str.len"), [x], Sort::Int);
    terms.mk_app(Symbol::named("<="), [k, len], Sort::Bool)
}

fn clause_for(terms: &mut TermStore, x: TermId, r: TermId, k: i64) -> [TermId; 2] {
    let membership = in_re(terms, x, r);
    let negated = terms.mk_not_raw(membership);
    let bound = bound_literal(terms, k, x);
    [negated, bound]
}

fn accept(terms: &TermStore, clause: &[TermId], why: &str) {
    assert!(
        recognize_regex_length_lower_bound(terms, clause),
        "recognizer should ACCEPT: {why}"
    );
    validate_regex_length_lower_bound(terms, ProofId(0), clause)
        .unwrap_or_else(|e| panic!("strict validation must accept {why}: {e}"));
}

fn reject(terms: &TermStore, clause: &[TermId], why: &str) {
    assert!(
        !recognize_regex_length_lower_bound(terms, clause),
        "recognizer should REJECT: {why}"
    );
    assert!(
        validate_regex_length_lower_bound(terms, ProofId(0), clause).is_err(),
        "strict validation must reject {why}"
    );
}

#[test]
fn minimum_lengths_are_computed_compositionally() {
    let mut terms = TermStore::new();
    let a = to_re(&mut terms, "a");
    let abc = to_re(&mut terms, "abc");
    let empty = to_re(&mut terms, "");

    let cases: Vec<(TermId, i64, &str)> = vec![
        (a, 1, "(str.to_re \"a\")"),
        (abc, 3, "(str.to_re \"abc\")"),
        (empty, 0, "(str.to_re \"\")"),
    ];
    for (r, expected, why) in cases {
        assert_eq!(
            regex_min_length(&terms, r),
            Some(BigInt::from(expected)),
            "min length of {why}"
        );
    }

    let concat = re(&mut terms, "re.++", &[abc, a]);
    assert_eq!(regex_min_length(&terms, concat), Some(BigInt::from(4)));
    let union = re(&mut terms, "re.union", &[abc, a]);
    assert_eq!(regex_min_length(&terms, union), Some(BigInt::from(1)));
    let inter = re(&mut terms, "re.inter", &[abc, a]);
    assert_eq!(regex_min_length(&terms, inter), Some(BigInt::from(3)));
    let star = re(&mut terms, "re.*", &[abc]);
    assert_eq!(regex_min_length(&terms, star), Some(BigInt::from(0)));
    let opt = re(&mut terms, "re.opt", &[abc]);
    assert_eq!(regex_min_length(&terms, opt), Some(BigInt::from(0)));
    let plus = re(&mut terms, "re.+", &[abc]);
    assert_eq!(regex_min_length(&terms, plus), Some(BigInt::from(3)));
    let diff = re(&mut terms, "re.diff", &[abc, a]);
    assert_eq!(regex_min_length(&terms, diff), Some(BigInt::from(3)));
    let allchar = re(&mut terms, "re.allchar", &[]);
    assert_eq!(regex_min_length(&terms, allchar), Some(BigInt::from(1)));
    let all = re(&mut terms, "re.all", &[]);
    assert_eq!(regex_min_length(&terms, all), Some(BigInt::from(0)));
    let none = re(&mut terms, "re.none", &[]);
    assert_eq!(regex_min_length(&terms, none), Some(BigInt::from(0)));
    let looped = re_indexed(&mut terms, "re.loop", vec![3, 5], &[a]);
    assert_eq!(regex_min_length(&terms, looped), Some(BigInt::from(3)));
    let powered = re_indexed(&mut terms, "re.^", vec![4], &[abc]);
    assert_eq!(regex_min_length(&terms, powered), Some(BigInt::from(12)));
}

#[test]
fn unmodelled_and_non_ground_nodes_are_rejected() {
    let mut terms = TermStore::new();
    let a = to_re(&mut terms, "a");
    // A complemented language routinely contains `""`, so no bound is derived.
    let complement = re(&mut terms, "re.comp", &[a]);
    assert_eq!(regex_min_length(&terms, complement), None);
    // A non-constant `str.to_re` argument is not ground.
    let x = v(&mut terms, "x");
    let symbolic = terms.mk_app(Symbol::named("str.to_re"), [x], Sort::RegLan);
    assert_eq!(regex_min_length(&terms, symbolic), None);
    // A regex variable is not ground.
    let opaque = terms.mk_var("R", Sort::RegLan);
    assert_eq!(regex_min_length(&terms, opaque), None);
    // An unknown operator is not modelled.
    let unknown = re(&mut terms, "re.mystery", &[a]);
    assert_eq!(regex_min_length(&terms, unknown), None);
    // A complement nested inside an otherwise-modelled node poisons the whole
    // computation rather than being skipped.
    let nested = re(&mut terms, "re.++", &[a, complement]);
    assert_eq!(regex_min_length(&terms, nested), None);
}

#[test]
fn supported_bounds_are_accepted() {
    let mut terms = TermStore::new();
    let x = v(&mut terms, "x");
    let a = to_re(&mut terms, "a");
    let looped = re_indexed(&mut terms, "re.loop", vec![3, 5], &[a]);
    let clause = clause_for(&mut terms, x, looped, 3);
    accept(
        &terms,
        &clause,
        "((_ re.loop 3 5) (str.to_re \"a\")) bounds len(x) >= 3",
    );
    // A WEAKER bound than the computed minimum is still valid.
    let weaker = clause_for(&mut terms, x, looped, 2);
    accept(&terms, &weaker, "a weaker bound");
    let zero = clause_for(&mut terms, x, looped, 0);
    accept(&terms, &zero, "the trivial bound");
    // Clause order is immaterial.
    let reversed = [clause[1], clause[0]];
    accept(&terms, &reversed, "reversed clause order");
}

#[test]
fn over_strong_bounds_are_rejected() {
    let mut terms = TermStore::new();
    let x = v(&mut terms, "x");
    let a = to_re(&mut terms, "a");
    let looped = re_indexed(&mut terms, "re.loop", vec![3, 5], &[a]);
    let clause = clause_for(&mut terms, x, looped, 4);
    reject(&terms, &clause, "a bound one above the computed minimum");
    // `re.*` admits the empty word, so nothing above 0 is derivable.
    let star = re(&mut terms, "re.*", &[a]);
    let clause = clause_for(&mut terms, x, star, 1);
    reject(&terms, &clause, "a positive bound on a starred language");
    // A negative bound is not a length bound.
    let negative = clause_for(&mut terms, x, looped, -1);
    reject(&terms, &negative, "a negative bound");
}

#[test]
fn mismatched_subject_is_rejected() {
    let mut terms = TermStore::new();
    let x = v(&mut terms, "x");
    let y = v(&mut terms, "y");
    let a = to_re(&mut terms, "a");
    let looped = re_indexed(&mut terms, "re.loop", vec![3, 5], &[a]);
    // The bound must be on the SAME term the membership constrains; otherwise
    // an unrelated string's length would be pinned out of nothing.
    let membership = in_re(&mut terms, x, looped);
    let negated = terms.mk_not_raw(membership);
    let bound = bound_literal(&mut terms, 3, y);
    reject(&terms, &[negated, bound], "a bound on a DIFFERENT subject");
}

#[test]
fn wrong_clause_shapes_are_rejected() {
    let mut terms = TermStore::new();
    let x = v(&mut terms, "x");
    let a = to_re(&mut terms, "a");
    let looped = re_indexed(&mut terms, "re.loop", vec![3, 5], &[a]);
    let membership = in_re(&mut terms, x, looped);
    let negated = terms.mk_not_raw(membership);
    let bound = bound_literal(&mut terms, 3, x);

    // The membership must be NEGATED: the positive pair asserts membership.
    reject(&terms, &[membership, bound], "an unnegated membership");
    // The bound must be positive.
    let negated_bound = terms.mk_not_raw(bound);
    reject(&terms, &[negated, negated_bound], "a negated bound");
    // Units and over-long clauses are not the theorem.
    reject(&terms, &[negated], "a unit clause");
    reject(
        &terms,
        &[negated, bound, membership],
        "a three-literal clause",
    );
    // A `>=` spelling is not the exact `(<= k (str.len x))` schema.
    let k = terms.mk_int(BigInt::from(3));
    let len = terms.mk_app(Symbol::named("str.len"), [x], Sort::Int);
    let flipped = terms.mk_app(Symbol::named("<="), [len, k], Sort::Bool);
    reject(&terms, &[negated, flipped], "an UPPER bound spelled as <=");
    // Empty and non-Bool clauses.
    assert!(!recognize_regex_length_lower_bound(&terms, &[]));
    assert!(validate_regex_length_lower_bound(&terms, ProofId(0), &[]).is_err());
    assert!(validate_regex_length_lower_bound(&terms, ProofId(0), &[x]).is_err());
}
