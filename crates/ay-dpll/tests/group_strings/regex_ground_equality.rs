// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Ground RegLan equalities are decided by LANGUAGE, not syntax.
//!
//! Nothing in the string pipeline used to inspect an equality between two
//! regex terms — it is neither a word equation nor a membership — so
//! `(= re.none (re.inter (str.to_re "a") (str.to_re "b")))` produced a
//! candidate the independent model gate could not confirm (there is no
//! RegLan model value) and AY answered `unknown` where z3 answers `sat`;
//! the overlapping form likewise stayed `unknown` instead of `unsat`.
//! The string theory now conflicts on a false ground equality and the
//! model gate decides RegLan equality by exact language equality.
//! Every verdict below matches z3 5.1.0.

fn solve(smt: &str) -> String {
    crate::common::solve(smt)
}

#[test]
fn none_equals_disjoint_intersection_is_sat() {
    assert_eq!(
        solve(
            "(set-logic QF_S)\
             (assert (= re.none (re.inter (str.to_re \"a\") (str.to_re \"b\"))))\
             (check-sat)"
        ),
        "sat"
    );
}

#[test]
fn none_equals_overlapping_intersection_is_unsat() {
    assert_eq!(
        solve(
            "(set-logic QF_S)\
             (assert (= re.none (re.inter (str.to_re \"a\") (re.* re.allchar))))\
             (check-sat)"
        ),
        "unsat"
    );
}

#[test]
fn distinct_ground_regexes_follow_language() {
    assert_eq!(
        solve(
            "(set-logic QF_S)\
             (assert (distinct re.none (re.inter (str.to_re \"a\") (re.* re.allchar))))\
             (check-sat)"
        ),
        "sat"
    );
    assert_eq!(
        solve(
            "(set-logic QF_S)\
             (assert (distinct re.none (re.inter (str.to_re \"a\") (str.to_re \"b\"))))\
             (check-sat)"
        ),
        "unsat"
    );
}

#[test]
fn union_with_none_and_none_vs_all_follow_language() {
    assert_eq!(
        solve(
            "(set-logic QF_S)\
             (assert (= (re.union re.none (str.to_re \"a\")) (str.to_re \"a\")))\
             (check-sat)"
        ),
        "sat"
    );
    assert_eq!(
        solve("(set-logic QF_S)(assert (= re.none re.all))(check-sat)"),
        "unsat"
    );
}

#[test]
fn negated_true_ground_equality_is_unsat() {
    assert_eq!(
        solve(
            "(set-logic QF_S)\
             (assert (not (= re.none (re.inter (str.to_re \"a\") (str.to_re \"b\")))))\
             (check-sat)"
        ),
        "unsat"
    );
}

#[test]
fn wildcard_patterns_with_disjoint_first_literals_intersect_empty() {
    // Miniature of the QF_S census shape (20250410-matching): two long
    // wildcard patterns whose first literals already disagree.
    assert_eq!(
        solve(
            "(set-logic QF_S)\
             (assert (= re.none (re.inter \
               (re.++ (str.to_re \"cfuucbho\") (re.* re.allchar) (str.to_re \"bbdalfoqjem\")) \
               (re.++ (str.to_re \"rqytapqswnevz\") (re.* re.allchar) (str.to_re \"c\")))))\
             (check-sat)"
        ),
        "sat"
    );
}
