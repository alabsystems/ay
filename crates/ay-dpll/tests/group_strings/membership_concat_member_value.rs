// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Ground regex membership through an equivalence-class concat member.
//!
//! Minimised from QF_S `2019-Jiang/slog/slog_stranger_2391_sink` (z3: unsat):
//! once the SAT layer picks a branch for `v`, `x`'s class has no constant and
//! its value exists only through the member `"ab"·v·"cd"`. The ground
//! membership check resolves that member with every link explained
//! (`known_string_with_reasons`). That resolver once walked each class's
//! member list again from every member, exponentially in the class size;
//! these shapes pin what it must still decide now that each class is
//! scanned at most once per depth.

use ntest::timeout;

fn solve(smt: &str) -> String {
    crate::common::solve(smt)
}

fn slog_sink(branch: &str) -> String {
    format!(
        "(set-logic QF_S)\
         (declare-fun v () String)(declare-fun x () String)\
         (assert (or (= v \"\") (= v \"{branch}\")))\
         (assert (= x (str.++ \"ab\" v \"cd\")))\
         (assert (str.in_re x (re.++ re.all (str.to_re \"Z\") re.all)))\
         (check-sat)"
    )
}

/// Neither `"abcd"` nor `"abqcd"` contains `Z`: z3 answers unsat.
#[test]
#[timeout(30_000)]
fn slog_sink_shape_is_unsat() {
    assert_eq!(solve(&slog_sink("q")), "unsat");
}

/// Negative twin: `v = "Z"` gives `x = "abZcd"`, which contains `Z`.
#[test]
#[timeout(30_000)]
fn slog_sink_shape_with_a_matching_branch_is_sat() {
    assert_eq!(solve(&slog_sink("Z")), "sat");
}

/// The same shape behind a chain of variable aliases `x = y1 = … = y4`:
/// the value still comes from the one concat member.
#[test]
#[timeout(30_000)]
fn slog_sink_shape_through_aliases_is_unsat() {
    assert_eq!(
        solve(
            "(set-logic QF_S)\
             (declare-fun v () String)(declare-fun x () String)\
             (declare-fun y1 () String)(declare-fun y2 () String)\
             (declare-fun y3 () String)(declare-fun y4 () String)\
             (assert (or (= v \"\") (= v \"q\")))\
             (assert (= x y1))(assert (= y1 y2))(assert (= y2 y3))(assert (= y3 y4))\
             (assert (= y4 (str.++ \"ab\" v \"cd\")))\
             (assert (str.in_re x (re.++ re.all (str.to_re \"Z\") re.all)))\
             (check-sat)"
        ),
        "unsat"
    );
}
