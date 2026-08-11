// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Higher-order sequence combinator goals must be REFUTABLE, not merely
//! satisfiable (#ho-seq-array-free).
//!
//! Every `seq.foldl` / `seq.foldli` takes a CURRIED function-as-array
//! (`(Array A (Array E A))`), which is a NESTED array. The declared-sort test
//! that opens `quarantine_unverified_nested_array_unsat` looks at the whole
//! root DAG, so it fired on every fold goal ever written and withheld the
//! verdict — `unfold_ho_seq_ops` would correctly rewrite
//! `(seq.foldl f a (as seq.empty …))` to `a`, the arithmetic solver would
//! refute what remained, and the answer still came back `unknown` with
//! `:unknown.cost_center "nested-array-unsat-quarantine"`.
//!
//! The unfolding is an equivalence, not an entailment (a function-as-array
//! application IS `select`), and when it leaves no nested array in the live
//! assertions the solver is never handed the structure that quarantine guards.
//! These tests pin both directions: the refutations that were unreachable, and
//! the SAT cases that must not have moved.

use ntest::timeout;

/// `(seq.foldl f a (as seq.empty …))` IS `a`, so pinning it to a different
/// constant is UNSAT. Returned `unknown` before the exemption.
#[test]
#[timeout(60_000)]
fn fold_over_empty_pinned_to_another_constant_is_unsat() {
    let result = crate::common::solve(
        "(set-logic ALL)
         (declare-const hff (Array Int (Array Int Int)))
         (assert (= (seq.foldl hff 0 (as seq.empty (Seq Int))) 1))
         (check-sat)",
    );
    assert_eq!(
        result, "unsat",
        "foldl over the empty sequence is the accumulator, so 0 = 1 is refutable"
    );
}

/// The same identity with a SYMBOLIC accumulator: `(seq.foldl f a empty) = r`
/// together with `a != r` is UNSAT.
#[test]
#[timeout(60_000)]
fn fold_over_empty_with_symbolic_accumulator_is_unsat() {
    let result = crate::common::solve(
        "(set-logic ALL)
         (declare-const hff (Array Int (Array Int Int)))
         (declare-const a Int)
         (declare-const r Int)
         (assert (= (seq.foldl hff a (as seq.empty (Seq Int))) r))
         (assert (not (= a r)))
         (check-sat)",
    );
    assert_eq!(
        result, "unsat",
        "the fold result and the accumulator are the same term"
    );
}

/// The consistent orientation stays SAT. The exemption must not turn a
/// satisfiable fold goal into a refutation.
#[test]
#[timeout(60_000)]
fn fold_over_empty_pinned_to_the_accumulator_stays_sat() {
    let result = crate::common::solve(
        "(set-logic ALL)
         (declare-const hff (Array Int (Array Int Int)))
         (assert (= (seq.foldl hff 0 (as seq.empty (Seq Int))) 0))
         (check-sat)",
    );
    assert_eq!(result, "sat", "the identity itself is satisfiable");
}

/// A NON-empty fold still leaves real `select` chains over the very nested
/// array the quarantine guards, so the exemption must NOT apply and the honest
/// `unknown` must survive. This is the boundary that keeps the exemption
/// narrow: it is not "folds are exempt", it is "no nested array remains".
#[test]
#[timeout(60_000)]
fn fold_over_a_non_empty_sequence_is_not_exempted() {
    let result = crate::common::solve(
        "(set-logic ALL)
         (declare-const hff (Array Int (Array Int Int)))
         (assert (not (= (seq.foldl hff 0 (seq.unit 5)) (select (select hff 0) 5))))
         (check-sat)",
    );
    assert_ne!(
        result, "unsat",
        "a non-empty fold keeps nested-array structure; its UNSAT stays quarantined"
    );
}

/// `seq.map` over the empty sequence was already refutable (its function
/// operand is a FLAT array, so the quarantine never fired). Pinned so the
/// exemption cannot regress the case that already worked.
#[test]
#[timeout(60_000)]
fn map_over_empty_is_empty_and_stays_unsat() {
    let result = crate::common::solve(
        "(set-logic ALL)
         (declare-const g (Array Int Int))
         (assert (not (= (seq.map g (as seq.empty (Seq Int))) (as seq.empty (Seq Int)))))
         (check-sat)",
    );
    assert_eq!(result, "unsat", "mapping over the empty sequence is empty");
}
