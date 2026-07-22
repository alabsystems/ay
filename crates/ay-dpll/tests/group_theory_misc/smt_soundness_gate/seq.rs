// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! QF_S / QF_SEQ sequence-theory soundness gate tests.
//!
//! Focus: the `seq_falsesat_iteofseq_eq_operand` wrong-SAT family. An
//! `(= L (ite c t e))` over sequences distributes (at elaboration) into branch
//! atoms of the shape `(= (seq.unit a) (seq.unit b))` (CONTENT) and
//! `(= (seq.unit a) seq.empty)` (LENGTH). The EUF+Seq core treats `seq.unit` as
//! an uninterpreted function and has no length axioms, so without `seq.unit`
//! injectivity + unit/empty length separation it reports a spurious SAT.
//!
//! Every UNSAT case below is confirmed by z3 AND cvc5. The SAT cases guard that
//! the new axioms are content/length facts only and never over-constrain a
//! genuinely satisfiable formula into a wrong-UNSAT.

use ntest::timeout;

use super::helpers::{assert_not_sat, assert_not_unsat, assert_not_unsat_file};

// --- 1. The reported wrong-SAT: ite-of-seq operand (z3=cvc5=unsat) ---

#[test]
#[timeout(10_000)]
fn test_gate_qf_s_iteofseq_eq_operand_unsat() {
    // (seq.at v1 0) = [false]; both ite branches mismatch ([true] content, empty
    // length) -> UNSAT. The original soundness-conflict benchmark.
    assert_not_sat(
        r#"
        (set-logic QF_S)
        (declare-fun v1 () (Seq Bool))
        (declare-fun v3 () (Seq Bool))
        (declare-fun v5 () Bool)
        (assert (= v1 (seq.++ (seq.unit false) (seq.unit false))))
        (assert (= v3 (as seq.empty (Seq Bool))))
        (assert (= (seq.at v1 0)
                   (ite (seq.nth (seq.unit v5) (- 3))
                        (seq.unit true)
                        (seq.++ v3 (as seq.empty (Seq Bool)) (as seq.empty (Seq Bool))))))
        (check-sat)
    "#,
    );
}

// --- 2. Minimal ite-of-seq equality (no extract) ---

#[test]
#[timeout(10_000)]
fn test_gate_qf_s_minimal_iteofseq_unsat() {
    // [false] = (ite b [true] empty): both branches mismatch -> UNSAT.
    assert_not_sat(
        r#"
        (set-logic QF_S)
        (declare-fun b () Bool)
        (assert (= (seq.unit false) (ite b (seq.unit true) (as seq.empty (Seq Bool)))))
        (check-sat)
    "#,
    );
}

// --- 3. seq.unit content injectivity ---

#[test]
#[timeout(10_000)]
fn test_gate_qf_s_unit_content_mismatch_unsat() {
    // (seq.unit false) = (seq.unit true) is UNSAT (content mismatch).
    assert_not_sat(
        r#"
        (set-logic QF_S)
        (assert (= (seq.unit false) (seq.unit true)))
        (check-sat)
    "#,
    );
}

#[test]
#[timeout(10_000)]
fn test_gate_qf_s_unit_content_mismatch_via_var_unsat() {
    // x = [false], x = [true] -> [false] = [true] -> UNSAT (transitive content).
    assert_not_sat(
        r#"
        (set-logic QF_S)
        (declare-fun x () (Seq Bool))
        (assert (= x (seq.unit false)))
        (assert (= x (seq.unit true)))
        (check-sat)
    "#,
    );
}

// --- 4. seq.unit vs seq.empty length separation ---

#[test]
#[timeout(10_000)]
fn test_gate_qf_s_unit_vs_empty_length_unsat() {
    // (seq.unit false) = empty: length 1 != 0 -> UNSAT.
    assert_not_sat(
        r#"
        (set-logic QF_S)
        (assert (= (seq.unit false) (as seq.empty (Seq Bool))))
        (check-sat)
    "#,
    );
}

#[test]
#[timeout(10_000)]
fn test_gate_qf_s_unit_vs_empty_concat_length_unsat() {
    // (seq.unit false) = (seq.++ empty empty empty): the RHS is semantically
    // empty (all-empty leaves) -> length 1 != 0 -> UNSAT.
    assert_not_sat(
        r#"
        (set-logic QF_S)
        (declare-fun v3 () (Seq Bool))
        (assert (= v3 (as seq.empty (Seq Bool))))
        (assert (= (seq.unit false)
                   (seq.++ v3 (as seq.empty (Seq Bool)) (as seq.empty (Seq Bool)))))
        (check-sat)
    "#,
    );
}

// --- 5. SAT guards: the new axioms must NOT over-constrain (no wrong-UNSAT) ---

#[test]
#[timeout(10_000)]
fn test_gate_qf_s_iteofseq_satisfiable_branch_not_unsat() {
    // [true] = (ite b [true] [false]): the then-branch matches, so SAT (set b).
    // Guards against the ite/injectivity passes flipping a real SAT to UNSAT.
    assert_not_unsat(
        r#"
        (set-logic QF_S)
        (declare-fun b () Bool)
        (assert (= (seq.unit true) (ite b (seq.unit true) (seq.unit false))))
        (check-sat)
    "#,
    );
}

#[test]
#[timeout(10_000)]
fn test_gate_qf_s_unit_content_match_sat() {
    // (seq.unit a) = (seq.unit b) with a, b free Bools is SAT (a = b).
    assert_not_unsat(
        r#"
        (set-logic QF_S)
        (declare-fun a () Bool)
        (declare-fun b () Bool)
        (assert (= (seq.unit a) (seq.unit b)))
        (check-sat)
    "#,
    );
}

// --- 6. Cross-sort seq.empty interning (#6734): sort-aware hash-consing ---
//
// `(as seq.empty (Seq Bool))` and `(as seq.empty (Seq Int))` share identical
// `TermData` (`App("seq.empty", [])`) but differ in sort. Before the fix the
// sort-blind hash-cons merged them into ONE `TermId`, aliasing a `Seq(Bool)`
// and a `Seq(Int)` value. A downstream seq axiom then built `mk_eq` across the
// two: debug PANIC at `term/boolean_eq.rs` ("mk_eq expects same sort"), release
// a degenerate equality → wrong UNSAT. z3 AND cvc5 agree these are SAT.

#[test]
#[timeout(10_000)]
fn test_gate_qf_slia_cross_sort_seq_empty_interning_not_unsat() {
    // The reported benchmark: a (Seq Bool) empty and a (Seq Int) empty coexist.
    // Must NOT crash and must NOT report wrong-UNSAT (z3=cvc5=sat).
    assert_not_unsat_file(
        "benchmarks/smt/regression/soundness_fuzz_round2/rank1_qf_slia_CRASH_seq_sort_interning.smt2",
    );
}

#[test]
#[timeout(10_000)]
fn test_gate_qf_s_cross_sort_seq_empty_minimal_not_unsat() {
    // Minimal cross-sort repro: a (Seq Bool) empty and a (Seq Int) empty in the
    // same problem. Each constraint is trivially satisfiable; merging the two
    // empties to one ill-typed TermId is what fabricated the spurious UNSAT.
    assert_not_unsat(
        r#"
        (set-logic QF_SLIA)
        (declare-fun vb () (Seq Bool))
        (declare-fun vi () (Seq Int))
        (assert (= vb (as seq.empty (Seq Bool))))
        (assert (= vi (as seq.empty (Seq Int))))
        (check-sat)
    "#,
    );
}

#[test]
#[timeout(10_000)]
fn test_gate_qf_s_cross_sort_seq_empty_len_zero_not_unsat() {
    // Both empties have length 0 (sound, agreed by z3/cvc5). Exercises the seq
    // length axioms over BOTH the Bool-sorted and Int-sorted empty so the two
    // distinct TermIds are each reasoned about correctly without a cross-sort
    // mk_eq.
    assert_not_unsat(
        r#"
        (set-logic QF_SLIA)
        (assert (= (seq.len (as seq.empty (Seq Bool))) 0))
        (assert (= (seq.len (as seq.empty (Seq Int))) 0))
        (check-sat)
    "#,
    );
}

#[test]
#[timeout(10_000)]
fn test_gate_qf_s_unit_vs_empty_disjunction_sat() {
    // (or (= [a] empty) (= a true)): the first disjunct is the (false)
    // length-separated unit/empty equality, so the disjunction holds only via the
    // second, forcing a = true — SAT with a concrete model. Guards that the
    // length-separation disequality does not falsely close the disjunction.
    assert_not_unsat(
        r#"
        (set-logic QF_S)
        (declare-fun a () Bool)
        (assert (or (= (seq.unit a) (as seq.empty (Seq Bool))) (= a true)))
        (check-sat)
    "#,
    );
}
