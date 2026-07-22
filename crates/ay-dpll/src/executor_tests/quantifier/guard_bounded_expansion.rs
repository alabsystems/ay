// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Guard-bounded finite-binder expansion in the quantified model gate
//! (#quantified-model-gate, `quantified_gate_guard_bounded_bv_domain`).
//!
//! The guarded pointwise-axiom shape verifier encoders emit for fixed-length
//! collections — `∀i. i <u len ⇒ a[i] = f(i)` with a LITERAL `len` — used to
//! fail closed at the gate: the wide (BV64) binder is not enumerable by
//! width, and the nested certification solve cannot decide the folded
//! bv2nat-mixing residue, so a genuinely satisfiable out-of-range read
//! degraded Sat → Unknown (deductive-checks `seq_from_fn` red, R1 2026-07-18). The
//! guard makes the matrix vacuous outside `[0, len)`, so expanding the binder
//! over exactly that range is a pure logical equivalence; the instances then
//! ground-fold and evaluate exactly against the emitted witness.

use super::*;

/// Int-element collection axiom + out-of-range read: the read at index 7 is
/// unconstrained (len 5), so the query is SAT and the gate must certify the
/// witness through the guard-bounded expansion (the nested-solve route cannot
/// decide the `bv2nat`-mixing residue).
#[test]
fn guarded_pointwise_axiom_out_of_range_int_read_is_sat() {
    let input = r#"
        (set-logic ALL)
        (declare-const s (Array (_ BitVec 64) Int))
        (assert (forall ((i (_ BitVec 64)))
          (! (=> (bvult i #x0000000000000005) (= (select s i) (* 10 (bv2int i))))
             :pattern ((select s i)))))
        (assert (=> (bvult #x0000000000000000 #x0000000000000005) (= (select s #x0000000000000000) 0)))
        (assert (=> (bvult #x0000000000000001 #x0000000000000005) (= (select s #x0000000000000001) 10)))
        (assert (=> (bvult #x0000000000000002 #x0000000000000005) (= (select s #x0000000000000002) 20)))
        (assert (=> (bvult #x0000000000000003 #x0000000000000005) (= (select s #x0000000000000003) 30)))
        (assert (=> (bvult #x0000000000000004 #x0000000000000005) (= (select s #x0000000000000004) 40)))
        (assert (= (select s #x0000000000000007) 0))
        (check-sat)
    "#;

    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execution succeeds");

    assert_eq!(
        outputs,
        vec!["sat"],
        "out-of-range read of a guarded pointwise Seq axiom must stay SAT (R1)"
    );
}

/// Pure-BV element variant of the same shape (deductive-checks
/// `seq_from_fn_out_of_bounds_region_is_unconstrained` encoding).
#[test]
fn guarded_pointwise_axiom_out_of_range_bv_read_is_sat() {
    let input = r#"
        (set-logic ALL)
        (declare-const s (Array (_ BitVec 64) (_ BitVec 32)))
        (assert (forall ((i (_ BitVec 64)))
          (! (=> (bvult i #x0000000000000002) (= (select s i) ((_ extract 31 0) i)))
             :pattern ((select s i)))))
        (assert (= (select s #x0000000000000005) #x00000000))
        (check-sat)
    "#;

    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execution succeeds");

    assert_eq!(outputs, vec!["sat"]);
}

/// Soundness twin: an IN-range read conflicting with the axiom must stay
/// refuted — the expansion is an equivalence, so it can never weaken the
/// UNSAT direction.
#[test]
fn guarded_pointwise_axiom_in_range_conflict_stays_unsat() {
    let input = r#"
        (set-logic ALL)
        (declare-const s (Array (_ BitVec 64) Int))
        (assert (forall ((i (_ BitVec 64)))
          (! (=> (bvult i #x0000000000000005) (= (select s i) (* 10 (bv2int i))))
             :pattern ((select s i)))))
        (assert (= (select s #x0000000000000002) 25))
        (check-sat)
    "#;

    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execution succeeds");

    assert_eq!(
        outputs,
        vec!["unsat"],
        "in-range conflicting read must stay refuted under the expansion"
    );
}
