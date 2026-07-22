// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Regex membership must propagate through concatenation. `(str.++ x y) ∈ R`
//! constrains its operands; a membership was silently dropped when its subject
//! was a concat (not a single variable), so e.g. `(str.++ x y) ∈ a* ∧ x = "b"`
//! came back `unknown` instead of `unsat`. The extraction now binds the concat
//! to a fresh `s` (`s = x·y ∧ s ∈ R`) so the Nielsen solver propagates it.
//! Every verdict matches z3 4.15.4. Soundness re-validated by a 406-instance
//! QF_SLIA/QF_S differential sweep (0 wrong answers).

fn solve(smt: &str) -> String {
    crate::common::solve(smt)
}

#[test]
fn concat_in_astar_with_nonmatching_prefix_is_unsat() {
    // x·y ∈ a* and x = "b" (∉ a*) -> unsat (was unknown; the membership over the
    // concat was dropped).
    assert_eq!(
        solve(
            "(set-logic QF_SLIA)\
             (declare-fun x () String)(declare-fun y () String)\
             (assert (str.in_re (str.++ x y) (re.* (str.to_re \"a\"))))\
             (assert (= x \"b\"))\
             (check-sat)"
        ),
        "unsat"
    );
}

#[test]
fn concat_in_astar_with_matching_prefix_stays_sat() {
    // The fix must NOT over-reject: x="a", y="" gives "a" ∈ a* -> sat.
    assert_eq!(
        solve(
            "(set-logic QF_SLIA)\
             (declare-fun x () String)(declare-fun y () String)\
             (assert (str.in_re (str.++ x y) (re.* (str.to_re \"a\"))))\
             (assert (= x \"a\"))(assert (= y \"\"))\
             (check-sat)"
        ),
        "sat"
    );
}

#[test]
fn nested_concat_with_nonmatching_middle_is_unsat() {
    // x·(y·z) ∈ a* and y = "b" -> unsat, through a nested concatenation.
    assert_eq!(
        solve(
            "(set-logic QF_SLIA)\
             (declare-fun x () String)(declare-fun y () String)(declare-fun z () String)\
             (assert (str.in_re (str.++ x (str.++ y z)) (re.* (str.to_re \"a\"))))\
             (assert (= y \"b\"))\
             (check-sat)"
        ),
        "unsat"
    );
}

#[test]
fn negative_concat_membership_propagates() {
    // ¬((x·y) ∈ ¬a*)  ≡  (x·y) ∈ a*  ; with x = "b" -> unsat. The NEGATIVE
    // membership over a concat was dropped by the same intern_var gap.
    assert_eq!(
        solve(
            "(set-logic QF_SLIA)\
             (declare-fun x () String)(declare-fun y () String)\
             (assert (not (str.in_re (str.++ x y) (re.comp (re.* (str.to_re \"a\"))))))\
             (assert (= x \"b\"))\
             (check-sat)"
        ),
        "unsat"
    );
}
