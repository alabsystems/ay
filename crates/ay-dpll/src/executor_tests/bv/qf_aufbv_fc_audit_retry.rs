// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! A substitution-lane QF_AUFBV solve whose array functional-consistency
//! audit is incomplete arms the preprocessing-free re-solve
//! (#abv-subst-model-retry, `theories/bv_cegar_array_refine.rs`).
//!
//! The store-chain fuzz file q8822_246 (z3: sat) reaches `sat` only through
//! that re-solve. Nothing but a model-validation failure on the solver's own
//! `distinct_const_array` axiom used to arm it, and ground array equalities
//! now evaluate exactly (#aufbv-const-array-equality), so the incomplete audit
//! arms it itself.

use super::*;

fn run(input: &str) -> (Vec<String>, Option<u64>) {
    let commands = parse(input).expect("invariant: valid SMT-LIB input");
    let mut exec = Executor::new();
    let out = exec
        .execute_all(&commands)
        .expect("invariant: execute succeeds");
    let retry = exec.statistics().get_int("model_validation.bv.subst_retry");
    (out, retry)
}

const Q8822_246: &str = r#"
    (set-logic QF_AUFBV)
    (declare-const a (Array (_ BitVec 4) Bool))
    (declare-const b (Array (_ BitVec 4) Bool))
    (declare-const c (Array (_ BitVec 4) Bool))
    (declare-const d (Array (_ BitVec 4) Bool))
    (declare-const e (Array (_ BitVec 4) Bool))
    (declare-const u (Array (_ BitVec 4) (_ BitVec 3)))
    (declare-const w (Array (_ BitVec 4) (_ BitVec 3)))
    (declare-const z (Array (_ BitVec 4) (_ BitVec 3)))
    (declare-const p Bool)
    (declare-const q Bool)
    (declare-const x (_ BitVec 4))
    (declare-const y (_ BitVec 4))
    (declare-const v (_ BitVec 3))
    (declare-fun f ((_ BitVec 4)) Bool)
    (declare-fun g ((_ BitVec 4)) (_ BitVec 3))
    (declare-fun h (Bool) Bool)
    (declare-fun k ((_ BitVec 3)) (_ BitVec 4))
    (assert (select d (bvadd x (_ bv3 4))))
    (assert (or (and (not (bvult x (_ bv13 4))) (= (store (store z y (_ bv2 3)) (k (_ bv7 3)) (_ bv6 3)) w)) (and (ite (not (= z u)) (= w (store u (bvadd x (_ bv3 4)) (select z (_ bv9 4)))) (not (select b x))) (ite (not (select a (_ bv2 4))) (= e ((as const (Array (_ BitVec 4) Bool)) (= (_ bv3 3) (select u (_ bv5 4))))) (= d (store ((as const (Array (_ BitVec 4) Bool)) (h (select a (_ bv7 4)))) (_ bv4 4) q)))) (select d (bvadd x (_ bv1 4)))))
    (assert (or (and (select e y) (f x) (ite (= (store (store ((as const (Array (_ BitVec 4) (_ BitVec 3))) (_ bv0 3)) (_ bv9 4) (g y)) y (_ bv4 3)) z) (= b c) (not (select e x)))) (= z ((as const (Array (_ BitVec 4) (_ BitVec 3))) (ite true (_ bv1 3) (ite q (_ bv6 3) (_ bv4 3)))))))
    (assert (= (g x) (g y)))
"#;

#[test]
fn test_incomplete_fc_audit_on_a_substitution_solve_still_answers_sat() {
    let (out, retry) = run(&format!("{Q8822_246} (check-sat)"));
    assert_eq!(out, vec!["sat"]);
    assert_eq!(retry, Some(1), "the sat comes from the armed re-solve");
}

#[test]
fn test_incomplete_fc_audit_twin_contradicting_the_read_is_unsat() {
    let input = format!("{Q8822_246} (assert (not (select d (bvadd x (_ bv3 4))))) (check-sat)");
    let (out, _) = run(&input);
    assert_eq!(out, vec!["unsat"]);
}
