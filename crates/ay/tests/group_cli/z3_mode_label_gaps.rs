// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Repros from the label-conformance review of the z3-reach walk (class A),
//! each with a twin that differs in a line or two and answers sat. z3 binds
//! a `:named` label when it reads it and drops a command at its first error,
//! so a construct ay accepted and z3 rejects before or around a label left
//! ay with an assertion and a label z3 never has. The expected answers are
//! z3 4.12.5's or `unknown` in `--z3-mode` (stdin and file); plain mode (a
//! file, quiet and in the default posture) gives z3's answer, `unknown`, or
//! its documented own reading. A label in a subterm elaboration passes over
//! (the untaken branch of a constant `ite`, an unused `let` value) is not
//! trusted in plain mode, so a twin with one answers `unknown` there.

use ntest::timeout;

use super::label_answer_lanes::{assert_pairs, Case};

const A_QUANTIFIER_WITH_A_NON_BOOLEAN_BODY: &[(Case, Case)] = &[
    (
        (
            "skiplabel_unvouched_qbody",
            r#"(declare-const p Bool)
(declare-const q Bool)
(assert (and p (forall ((z Int)) 5) (ite true true (! q :named a))))
(assert (not p))
(check-sat)
"#,
            "unknown",
            "unknown",
        ),
        (
            "skiplabel_unvouched_qbody_twin",
            r#"(declare-const p Bool)
(declare-const q Bool)
(assert (or p (forall ((z Int)) true) (ite true true (! q :named a))))
(assert (not p))
(check-sat)
"#,
            "sat",
            "unknown",
        ),
    ),
    (
        (
            "skiplabel_unvouched_inbranch",
            r#"(declare-const p Bool)
(declare-const q Bool)
(assert (and p (ite true true (and (forall ((z Int)) 5) (! q :named a)))))
(assert (not p))
(check-sat)
"#,
            "unknown",
            "unknown",
        ),
        (
            "skiplabel_unvouched_inbranch_twin",
            r#"(declare-const p Bool)
(declare-const q Bool)
(assert (or p (ite true true (and (forall ((z Int)) true) (! q :named a)))))
(assert (not p))
(check-sat)
"#,
            "sat",
            "unknown",
        ),
    ),
    (
        (
            "skiplabel_after_gap_label_first",
            r#"(declare-const p Bool)
(declare-const q Bool)
(assert (and p (ite true true (! q :named a)) (forall ((z Int)) 5)))
(assert (not p))
(check-sat)
"#,
            "unknown",
            "unknown",
        ),
        (
            "skiplabel_after_gap_label_first_twin",
            r#"(declare-const p Bool)
(declare-const q Bool)
(assert (or p (ite true true (! q :named a)) (forall ((z Int)) true)))
(assert (not p))
(check-sat)
"#,
            "sat",
            "unknown",
        ),
    ),
    (
        (
            "skiplabel_unvouched_let",
            r#"(declare-const p Bool)
(declare-const q Bool)
(assert (and p (forall ((z Int)) 5) (let ((l (! q :named a))) true)))
(assert (not p))
(check-sat)
"#,
            "unknown",
            "unknown",
        ),
        (
            "skiplabel_unvouched_let_twin",
            r#"(declare-const p Bool)
(declare-const q Bool)
(assert (or p (forall ((z Int)) true) (let ((l q)) true)))
(assert (not p))
(check-sat)
"#,
            "sat",
            "sat",
        ),
    ),
    (
        (
            "nolabel_qbody",
            r#"(declare-const p Bool)
(assert (and p (forall ((z Int)) 5)))
(assert (not p))
(check-sat)
"#,
            "unknown",
            "unknown",
        ),
        (
            "nolabel_qbody_twin",
            r#"(declare-const p Bool)
(assert (or p (forall ((z Int)) true)))
(assert (not p))
(check-sat)
"#,
            "sat",
            "sat",
        ),
    ),
    (
        (
            "label_unskipped_qbody",
            r#"(declare-const p Bool)
(declare-const q Bool)
(assert (and p (forall ((z Int)) 5) (! q :named a)))
(assert (not p))
(check-sat)
"#,
            "unknown",
            "unknown",
        ),
        (
            "label_unskipped_qbody_twin",
            r#"(declare-const p Bool)
(declare-const q Bool)
(assert (or p (forall ((z Int)) true) (! q :named a)))
(assert (not p))
(check-sat)
"#,
            "sat",
            "sat",
        ),
    ),
    (
        (
            "quoted_label_name",
            r#"(declare-const p Bool)
(declare-const q Bool)
(assert (or (forall ((z Int)) 5) (ite true true (! q :named |a|))))
(assert (not a))
(assert q)
(check-sat)
"#,
            "unknown",
            "unknown",
        ),
        (
            "quoted_label_name_twin",
            r#"(declare-const p Bool)
(declare-const q Bool)
(assert (or (forall ((z Int)) true) (ite true true (! q :named |a|))))
(assert (not a))
(assert p)
(check-sat)
"#,
            "sat",
            "unknown",
        ),
    ),
];

/// A quantifier whose body is not Boolean, before, after or around label
/// `a` (in the untaken branch of a constant `ite`, a `let` value or a taken
/// position). z3 rejects the assertion and never binds `a`, so it answers
/// sat. ay accepted the quantifier in every mode and answered unsat once the
/// skipped-branch label was bound (the review's class A). Every mode now
/// rejects it, which withholds the later answers. Each twin has a Boolean
/// body and answers sat, in plain mode only without a skipped-branch label.
#[test]
#[timeout(180_000)]
fn a_quantifier_with_a_non_boolean_body() {
    assert_pairs(A_QUANTIFIER_WITH_A_NON_BOOLEAN_BODY);
}

const A_BIT_VECTOR_OPERAND_OF_ARITHMETIC_BEFORE_A_LABEL: &[(Case, Case)] = &[
    (
        (
            "skiplabel_unvouched_bvcmp",
            r#"(declare-const p Bool)
(declare-const q Bool)
(declare-const b (_ BitVec 8))
(declare-const c (_ BitVec 4))
(assert (and p (> b c) (ite true true (! q :named a))))
(assert (not p))
(check-sat)
"#,
            "unknown",
            "unknown",
        ),
        (
            "skiplabel_unvouched_bvcmp_twin",
            r#"(declare-const p Bool)
(declare-const q Bool)
(declare-const b (_ BitVec 8))
(declare-const c (_ BitVec 4))
(assert (or p (bvugt b b) (ite true true (! q :named a))))
(assert (not p))
(check-sat)
"#,
            "sat",
            "unknown",
        ),
    ),
    (
        (
            "fuzz_zlab1_s564_core",
            r#"(declare-const b0 (_ BitVec 8))
(declare-const c0 (_ BitVec 4))
(assert (not (ite false (! (> b0 c0) :named a) (= (! false :named c) false))))
(check-sat)
"#,
            "unknown",
            "unknown",
        ),
        (
            "fuzz_zlab1_s564_core_twin",
            r#"(declare-const b0 (_ BitVec 8))
(declare-const c0 (_ BitVec 4))
(assert (ite false (! (bvugt b0 b0) :named a) (= (! false :named c) false)))
(check-sat)
"#,
            "sat",
            "unknown",
        ),
    ),
];

/// A bit-vector operand of Int arithmetic before label `a`: z3 rejects the
/// assertion. z3 mode now rejects it too; plain mode keeps reading it (the
/// CHC engine relies on that) but no longer trusts the labels after it, so
/// both withhold the later answers. The second pair is the core of the
/// review's fuzz script zlab1/s564. The twins compare bit-vectors with
/// `bvugt` and answer sat in z3 mode; plain mode does not trust their
/// skipped-branch labels.
#[test]
#[timeout(180_000)]
fn a_bit_vector_operand_of_arithmetic_before_a_label() {
    assert_pairs(A_BIT_VECTOR_OPERAND_OF_ARITHMETIC_BEFORE_A_LABEL);
}

const A_BOOL_BESIDE_AN_INT_AFTER_A_SKIPPED_BRANCH_LABEL: &[(Case, Case)] = &[(
    (
        "fuzz_skiplab_s275_core",
        r#"(declare-const p1 Bool)
(assert (ite (not false) true (! (! p1 :named c) :named a)))
(assert (= a (- 2)))
(check-sat)
"#,
        "unknown",
        "unknown",
    ),
    (
        "fuzz_skiplab_s275_core_twin",
        r#"(declare-const p1 Bool)
(assert (ite (not false) true (! (! p1 :named c) :named a)))
(assert (= a false))
(check-sat)
"#,
        "sat",
        "unknown",
    ),
)];

/// The core of the review's fuzz script skiplab/s275: label `a` is bound in
/// the untaken branch of a constant `ite`, as z3 binds it, and then set
/// beside an Int. z3 4.12.5 rejects that assertion (sat), z3 5.1.0 coerces
/// the Bool (unsat). z3 mode rejects it. Plain mode would keep z3 5.1.0's
/// reading, but it does not trust a skipped-branch label and withholds the
/// answer. The twin compares `a` with a Bool and answers sat in z3 mode,
/// which shows the skipped-branch label is bound there.
#[test]
#[timeout(180_000)]
fn a_bool_beside_an_int_after_a_skipped_branch_label() {
    assert_pairs(A_BOOL_BESIDE_AN_INT_AFTER_A_SKIPPED_BRANCH_LABEL);
}
