// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Regression tests for cross-predicate seq compatibility (#seq-pairwise-compat).
//!
//! Multiple symbolic `seq.prefixof`/`seq.suffixof`/`seq.contains` over the SAME
//! seq variable (NO direct `s = seq.++ …`) used to be left un-cross-related, so
//! contradictory constraints were wrongly SAT. The fix adds sound compatibility
//! axioms (pairwise monotonicity/incompatibility, ground-needle nth pins with the
//! prefixof/suffixof element definition, endpoint→contains, contains→contains
//! substring transitivity, contains-from-nth-pins, and bounded contains packing).
//!
//! The hard requirement is SOUNDNESS: these contradictory conjunctions must NEVER
//! be reported `sat` (unsat preferred, unknown acceptable). Genuinely satisfiable
//! conjunctions must NOT be degraded to unsat.

use ntest::timeout;

/// Two prefixes of the same s pin s[0] to different values: UNSAT.
/// Exact reproduction from the bug report (`[1]` vs `[2,2,2]`).
#[test]
#[timeout(30_000)]
fn prefixof_prefixof_head_conflict_int_unsat() {
    let result = crate::common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const s (Seq Int))
         (assert (seq.prefixof (seq.unit 1) s))
         (assert (seq.prefixof (seq.++ (seq.++ (seq.unit 2) (seq.unit 2)) (seq.unit 2)) s))
         (check-sat)",
    );
    assert_eq!(
        result, "unsat",
        "prefixof([1],s) ∧ prefixof([2,2,2],s) pins s[0]=1∧s[0]=2"
    );
}

/// Same conflict over Bool elements: s[0]=true ∧ s[0]=false: UNSAT.
#[test]
#[timeout(30_000)]
fn prefixof_prefixof_head_conflict_bool_unsat() {
    let result = crate::common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const s (Seq Bool))
         (assert (seq.prefixof (seq.unit true) s))
         (assert (seq.prefixof (seq.++ (seq.unit false) (seq.unit false)) s))
         (check-sat)",
    );
    assert_eq!(
        result, "unsat",
        "prefixof([true],s) ∧ prefixof([false,false],s) is UNSAT"
    );
}

/// Three predicates: prefixof([2]) ∧ prefixof([1]) ∧ suffixof([2]) — the two
/// prefixes already pin s[0]=2 ∧ s[0]=1: UNSAT.
#[test]
#[timeout(30_000)]
fn prefixof_prefixof_with_suffixof_unsat() {
    let result = crate::common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const s (Seq Int))
         (assert (seq.prefixof (seq.unit 2) s))
         (assert (seq.prefixof (seq.unit 1) s))
         (assert (seq.suffixof (seq.unit 2) s))
         (check-sat)",
    );
    assert_eq!(
        result, "unsat",
        "two prefixes pinning s[0] to 2 and 1 is UNSAT"
    );
}

/// Two suffixes of the same s pin the tail to different values: UNSAT.
#[test]
#[timeout(30_000)]
fn suffixof_suffixof_tail_conflict_unsat() {
    let result = crate::common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const s (Seq Int))
         (assert (seq.suffixof (seq.unit 1) s))
         (assert (seq.suffixof (seq.++ (seq.unit 2) (seq.unit 2)) s))
         (check-sat)",
    );
    assert_eq!(
        result, "unsat",
        "suffixof([1],s) ∧ suffixof([2,2],s) pins the last element to 1∧2"
    );
}

/// BitVec elements: a longer prefix and a shorter prefix that disagree: UNSAT.
#[test]
#[timeout(30_000)]
fn prefixof_prefixof_bitvec_conflict_unsat() {
    let result = crate::common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const s (Seq (_ BitVec 4)))
         (assert (seq.prefixof (seq.++ (seq.unit #x5) (seq.unit #x3)) s))
         (assert (seq.prefixof (seq.unit #x6) s))
         (check-sat)",
    );
    assert_eq!(
        result, "unsat",
        "prefixof([5,3],s) ∧ prefixof([6],s) pins s[0]=5∧s[0]=6"
    );
}

/// Monotonicity with MIXED polarity: a longer suffix is asserted, the shorter
/// suffix it implies is negated: UNSAT.
#[test]
#[timeout(30_000)]
fn suffixof_monotonicity_mixed_polarity_unsat() {
    let result = crate::common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const s (Seq Bool))
         (assert (seq.suffixof (seq.++ (seq.unit false) (seq.unit false)) s))
         (assert (not (seq.suffixof (seq.unit false) s)))
         (check-sat)",
    );
    assert_eq!(
        result, "unsat",
        "suffixof([false,false],s) ⟹ suffixof([false],s)"
    );
}

/// A ground prefix needle conflicts with an external nth pin (no definite length): UNSAT.
#[test]
#[timeout(30_000)]
fn prefixof_vs_nth_pin_unsat() {
    let result = crate::common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const s (Seq Int))
         (assert (seq.prefixof (seq.unit 1) s))
         (assert (= (seq.nth s 0) 2))
         (check-sat)",
    );
    assert_eq!(
        result, "unsat",
        "prefixof([1],s) pins s[0]=1, contradicting nth(s,0)=2"
    );
}

/// A positive suffix needle contains an element whose containment is negated: UNSAT.
/// suffixof([3,2],s) ⟹ contains(s,[2]); ¬contains(s,[2]) contradicts it.
#[test]
#[timeout(30_000)]
fn suffixof_implies_contains_unsat() {
    let result = crate::common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const s (Seq Int))
         (assert (seq.suffixof (seq.++ (seq.unit 3) (seq.unit 2)) s))
         (assert (not (seq.contains s (seq.unit 2))))
         (check-sat)",
    );
    assert_eq!(result, "unsat", "suffixof([3,2],s) ⟹ contains(s,[2])");
}

/// contains→contains substring transitivity: contains(s,[1,2,3]) ⟹ contains(s,[2]);
/// ¬contains(s,[2]) contradicts it: UNSAT.
#[test]
#[timeout(30_000)]
fn contains_substring_transitivity_unsat() {
    let result = crate::common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const s (Seq Int))
         (assert (seq.contains s (seq.++ (seq.++ (seq.unit 1) (seq.unit 2)) (seq.unit 3))))
         (assert (not (seq.contains s (seq.unit 2))))
         (check-sat)",
    );
    assert_eq!(result, "unsat", "contains(s,[1,2,3]) ⟹ contains(s,[2])");
}

/// contains-from-nth-pin: nth(s,2)=-1 (in range, since len(s)>=3 via suffixof)
/// implies contains(s,[-1]); ¬contains(s,[-1]) contradicts it: UNSAT.
#[test]
#[timeout(30_000)]
fn contains_from_nth_pin_unsat() {
    let result = crate::common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const s (Seq Int))
         (assert (seq.suffixof (seq.++ (seq.++ (seq.unit 3) (seq.unit 0)) (seq.unit 2)) s))
         (assert (not (seq.contains s (seq.unit -1))))
         (assert (= (seq.nth s 2) -1))
         (check-sat)",
    );
    assert_eq!(result, "unsat", "nth(s,2)=-1 in range ⟹ contains(s,[-1])");
}

/// Contains packing: two length-3 needles cannot co-occupy a length-4 s whose
/// last element is pinned by a suffix: UNSAT.
#[test]
#[timeout(30_000)]
fn contains_packing_unsat() {
    let result = crate::common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const s (Seq Int))
         (assert (seq.contains s (seq.++ (seq.++ (seq.unit -2) (seq.unit 2)) (seq.unit 3))))
         (assert (seq.suffixof (seq.unit 2) s))
         (assert (seq.contains s (seq.++ (seq.++ (seq.unit 2) (seq.unit 1)) (seq.unit 3))))
         (assert (= (seq.len s) 4))
         (check-sat)",
    );
    assert_eq!(
        result, "unsat",
        "two length-3 needles cannot pack into length-4 s"
    );
}

/// SOUNDNESS GUARD (no over-refutation): a short prefix and a short suffix of the
/// same s do NOT conflict — `s = [1, …, 2]` is a model, so the verdict must never
/// be `unsat`.
///
/// #nonstring-seq-failclose: AY's symbolic non-string sequence theory could not
/// produce a VALID model here — the baseline emitted `s = [1]`, which falsifies
/// `(seq.suffixof (seq.unit 2) s)` (`[1]` does not end with `[2]`), the exact
/// self-falsifying wrong-`sat` signature the audits flagged. The non-string-seq
/// fail-closed gate therefore soundly returns `unknown` instead of a `sat` it
/// cannot back with a witness. Accept `sat` (with a real model) or `unknown`;
/// reject only `unsat` (over-refutation).
#[test]
#[timeout(30_000)]
fn prefixof_suffixof_distinct_ends_not_unsat() {
    let result = crate::common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const s (Seq Int))
         (assert (seq.prefixof (seq.unit 1) s))
         (assert (seq.suffixof (seq.unit 2) s))
         (check-sat)",
    );
    assert_ne!(
        result, "unsat",
        "prefixof([1],s) ∧ suffixof([2],s) IS satisfiable; must not be unsat"
    );
}

/// SOUNDNESS GUARD: a prefix that is a prefix of the other (nested) is consistent;
/// both prefixof([1]) and prefixof([1,2]) hold for s=[1,2,…]. Must stay SAT.
#[test]
#[timeout(30_000)]
fn prefixof_nested_consistent_sat() {
    let result = crate::common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const s (Seq Int))
         (assert (seq.prefixof (seq.unit 1) s))
         (assert (seq.prefixof (seq.++ (seq.unit 1) (seq.unit 2)) s))
         (check-sat)",
    );
    assert_eq!(
        result, "sat",
        "prefixof([1],s) ∧ prefixof([1,2],s) is satisfiable (s=[1,2,…])"
    );
}
