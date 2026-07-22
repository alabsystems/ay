// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Regression tests for EUF congruence over Bool-sorted UF argument positions
//! in the eager-bitblast route (#boolarg-congruence wrong-SAT class).
//!
//! Bool-sorted UF arguments have no BV bits, so BOTH combined-theory
//! congruence generators (`generate_euf_bv_axioms_debug` for BV-return UFs,
//! `generate_non_bv_euf_congruence` via `build_arg_diff_vars`) silently
//! dropped every application pair containing one. With `BoolUnbox : Bool ->
//! (_ BitVec 8)` applied to 256 finite-domain quantifier instances, the
//! missing 2-into-256 pigeonhole (Bool has only two values) let an UNSAT
//! instance answer `sat` — and because the quantified path defers model
//! validation, the wrong SAT escaped the independent-model-check gate that
//! degrades the quantifier-free variants to `unknown`.
//!
//! Fix: materialize a single CNF literal for every Bool-sorted UF argument
//! (`BvSolver::ensure_bool_literal`) BEFORE Tseitin<->BV linking, then encode
//! the argument difference as a 1-bit XOR in both generators.

use ntest::timeout;

/// The live wrong-SAT repro: `BoolUnbox (BoolBox x) = x` over all 256 BV8
/// values forces BoolBox to be injective into Bool's 2 values — UNSAT.
/// Preprocessing expands the forall to 256 ground instances; the ground
/// QF_UFBV solve must refute the pigeonhole via congruence over the
/// Bool-sorted `BoolUnbox` argument. Previously answered `sat`.
#[test]
#[timeout(60_000)]
fn test_boolbox_unbox_bv8_forall_pigeonhole_unsat() {
    let smt = r#"
        (set-logic ALL)
        (declare-fun BoolBox ((_ BitVec 8)) Bool)
        (declare-fun BoolUnbox (Bool) (_ BitVec 8))
        (declare-const w (_ BitVec 8))
        (assert (forall ((x (_ BitVec 8))) (! (= (BoolUnbox (BoolBox x)) x) :pattern ((BoolBox x)))))
        (assert (= (BoolBox w) true))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["unsat"],
        "BoolUnbox . BoolBox = id over 256 values is a 2-into-256 pigeonhole (Bool has 2 values)"
    );
}

/// Same class, smaller domain: BV4 (16 values) into Bool's 2 values.
#[test]
#[timeout(60_000)]
fn test_boolbox_unbox_bv4_forall_pigeonhole_unsat() {
    let smt = r#"
        (set-logic ALL)
        (declare-fun BoolBox ((_ BitVec 4)) Bool)
        (declare-fun BoolUnbox (Bool) (_ BitVec 4))
        (declare-const w (_ BitVec 4))
        (assert (forall ((x (_ BitVec 4))) (! (= (BoolUnbox (BoolBox x)) x) :pattern ((BoolBox x)))))
        (assert (= (BoolBox w) true))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["unsat"]);
}

/// Quantifier-free ground core of the same bug: three ground instances with
/// COMPOUND Bool arguments `(BoolBox c)`. Previously degraded to `unknown`
/// (bogus model caught by the independent model-check gate); the congruence
/// clauses now refute it outright.
#[test]
#[timeout(60_000)]
fn test_boolbox_unbox_ground_compound_bool_arg_pigeonhole_unsat() {
    let smt = r#"
        (set-logic ALL)
        (declare-fun BoolBox ((_ BitVec 8)) Bool)
        (declare-fun BoolUnbox (Bool) (_ BitVec 8))
        (assert (= (BoolUnbox (BoolBox #x00)) #x00))
        (assert (= (BoolUnbox (BoolBox #x01)) #x01))
        (assert (= (BoolUnbox (BoolBox #x02)) #x02))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["unsat"],
        "three distinct BoolUnbox results need three distinct Bool arguments — impossible"
    );
}

/// Plain Bool VARIABLE arguments (the shape `purify_bool_args` deliberately
/// leaves alone): the bitblast route itself must congruence-close over them.
#[test]
#[timeout(60_000)]
fn test_bool_var_arg_pigeonhole_unsat() {
    let smt = r#"
        (set-logic ALL)
        (declare-const p0 Bool)
        (declare-const p1 Bool)
        (declare-const p2 Bool)
        (declare-fun BoolUnbox (Bool) (_ BitVec 8))
        (assert (= (BoolUnbox p0) #x00))
        (assert (= (BoolUnbox p1) #x01))
        (assert (= (BoolUnbox p2) #x02))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["unsat"]);
}

/// Congruence trigger direction: an asserted Bool equality between the
/// arguments must force equal results (args-equal => results-equal).
#[test]
#[timeout(60_000)]
fn test_bool_var_arg_asserted_eq_forces_result_eq_unsat() {
    let smt = r#"
        (set-logic ALL)
        (declare-const p Bool)
        (declare-const q Bool)
        (declare-fun f (Bool) (_ BitVec 8))
        (assert (= (f p) #x00))
        (assert (= (f q) #x01))
        (assert (= p q))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["unsat"]);
}

/// SAT guard (no false-UNSAT): two applications with DIFFERENT Bool argument
/// values may produce different results.
#[test]
#[timeout(60_000)]
fn test_bool_var_arg_two_apps_distinct_results_sat() {
    let smt = r#"
        (set-logic ALL)
        (declare-const p Bool)
        (declare-const q Bool)
        (declare-fun f (Bool) (_ BitVec 8))
        (assert (= (f p) #x00))
        (assert (= (f q) #x01))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["sat"],
        "p != q satisfies both equations — congruence must not force f(p) = f(q)"
    );
}

/// SAT guard (no false-UNSAT): equal Bool arguments with EQUAL results, plus
/// forced-distinct argument values elsewhere, stays satisfiable.
#[test]
#[timeout(60_000)]
fn test_bool_var_arg_same_result_sat() {
    let smt = r#"
        (set-logic ALL)
        (declare-const p Bool)
        (declare-const q Bool)
        (declare-fun f (Bool) (_ BitVec 8))
        (assert (= (f p) #x07))
        (assert (= (f q) #x07))
        (assert p)
        (assert (not q))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["sat"]);
}

/// SAT guard for the quantified shape: over BV1 the domain has exactly 2
/// values, so BoolBox CAN be injective into Bool — genuinely satisfiable.
/// The congruence clauses must not over-constrain this into UNSAT.
#[test]
#[timeout(60_000)]
fn test_boolbox_unbox_bv1_forall_injective_sat() {
    let smt = r#"
        (set-logic ALL)
        (declare-fun BoolBox ((_ BitVec 1)) Bool)
        (declare-fun BoolUnbox (Bool) (_ BitVec 1))
        (declare-const w (_ BitVec 1))
        (assert (forall ((x (_ BitVec 1))) (! (= (BoolUnbox (BoolBox x)) x) :pattern ((BoolBox x)))))
        (assert (= (BoolBox w) true))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["sat"],
        "2-into-2 boxing is injective — must stay sat"
    );
}

/// Incremental (push/pop) route: the persistent-SAT BV pipeline
/// (`solve_bv_incremental_inner`) materializes Bool-argument literals and
/// generates the same congruence axioms. The pushed pigeonhole must be UNSAT
/// and the popped remainder SAT.
#[test]
#[timeout(60_000)]
fn test_bool_arg_pigeonhole_incremental_push_pop() {
    let smt = r#"
        (set-logic QF_UFBV)
        (declare-const p0 Bool)
        (declare-const p1 Bool)
        (declare-const p2 Bool)
        (declare-fun BoolUnbox (Bool) (_ BitVec 8))
        (assert (= (BoolUnbox p0) #x00))
        (assert (= (BoolUnbox p1) #x01))
        (push 1)
        (assert (= (BoolUnbox p2) #x02))
        (check-sat)
        (pop 1)
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["unsat", "sat"],
        "3 apps pigeonhole under push must be unsat; after pop the 2-app remainder is sat"
    );
}
