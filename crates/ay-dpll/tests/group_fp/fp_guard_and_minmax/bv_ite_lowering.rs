// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by `fp_guard_and_minmax` to preserve test FQNs.

// =========================================================================
// Bitvector-sorted ITE inside a BV op (CSET-style FP lowering)
// =========================================================================
//
// A bitvector-sorted `(ite <fp-predicate> #b1 #b0)` nested inside a BV
// operator (bvor/bvand/...) must be bit-blasted (mux over the encoded
// condition), not fail-closed as `unsupported`. This is the shape emitted
// by AArch64 `FCMP + CSET` lowerings — in particular UnorderedEqual, which
// is `(CSET EQ) OR (CSET VS)` = `(bvor (ite (fp.eq..) 1 0) (ite (isNaN..) 1 0))`.
// Previously the FP solver returned `unknown (:reason-unknown unsupported)`.

/// The `bvor` of two theory-conditioned CSET selects must solve, not gap.
/// Here a==b==0.0: fp.eq true -> 1, isNaN false -> 0, bvor = 1 == 1 -> sat.
#[test]
#[timeout(30_000)]
fn test_bv_ite_bvor_of_cset_selects_solvable() {
    let smt = r#"
        (set-logic QF_BVFP)
        (declare-const a (_ FloatingPoint 8 24))
        (assert (= a (fp #b0 #b00000000 #b00000000000000000000000)))
        (assert (= (_ bv1 1)
                   (bvor (ite (fp.eq a a) (_ bv1 1) (_ bv0 1))
                         (ite (fp.isNaN a) (_ bv1 1) (_ bv0 1)))))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["sat"],
        "bvor of CSET-style ites over FP predicates must bit-blast, not gap"
    );
}

/// SOUNDNESS: the CSET-based UnorderedEqual lowering
/// `(bvor (ite (fp.eq a b) 1 0) (ite (isNaN a | isNaN b) 1 0))` is provably
/// equivalent to the UEQ spec `(a == b) | isNaN(a) | isNaN(b)` for ALL
/// symbolic a,b — the negated equivalence must be UNSAT.
#[test]
#[timeout(60_000)]
fn test_bv_ite_ueq_cset_lowering_is_valid() {
    let smt = r#"
        (set-logic QF_BVFP)
        (declare-const a (_ FloatingPoint 8 24))
        (declare-const b (_ FloatingPoint 8 24))
        (define-fun spec () (_ BitVec 1)
            (ite (or (or (fp.eq a b) (fp.isNaN a)) (fp.isNaN b)) (_ bv1 1) (_ bv0 1)))
        (define-fun machine () (_ BitVec 1)
            (bvor (ite (fp.eq a b) (_ bv1 1) (_ bv0 1))
                  (ite (or (fp.isNaN a) (fp.isNaN b)) (_ bv1 1) (_ bv0 1))))
        (assert (not (= spec machine)))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["unsat"],
        "correct CSET UEQ lowering must be equivalent to the UEQ spec"
    );
}

/// SOUNDNESS (refutation): a WRONG UEQ lowering that drops the NaN branch
/// must NOT verify — the negated equivalence must be SAT (counterexample
/// where an operand is NaN). Guards against the mux trivially returning
/// verified.
#[test]
#[timeout(60_000)]
fn test_bv_ite_ueq_wrong_lowering_is_refuted() {
    let smt = r#"
        (set-logic QF_BVFP)
        (declare-const a (_ FloatingPoint 8 24))
        (declare-const b (_ FloatingPoint 8 24))
        (define-fun spec () (_ BitVec 1)
            (ite (or (or (fp.eq a b) (fp.isNaN a)) (fp.isNaN b)) (_ bv1 1) (_ bv0 1)))
        (define-fun wrong () (_ BitVec 1)
            (ite (fp.eq a b) (_ bv1 1) (_ bv0 1)))
        (assert (not (= spec wrong)))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["sat"],
        "NaN-dropping UEQ lowering must be refuted, not falsely verified"
    );
}
