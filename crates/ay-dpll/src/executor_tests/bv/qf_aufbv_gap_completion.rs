// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! QF_AUFBV gap completions are judged by the SAT funnel's own acceptance
//! (`completed_gap_model_accepted`, `model/completion.rs`). Every completion
//! revokes `last_model_validated`, so the funnel re-judges the completed
//! model. A re-check stricter than the funnel retracts a completion the
//! funnel would have published. A weaker one accepts a completion the funnel
//! then degrades, and the snapshot it would have published is lost.
//!
//! * Stricter. Completion tainted `z` (`read_conflicted`), so assertion 0
//!   cannot be evaluated by AY's evaluator, and the raw strict oracle
//!   (`arrays-read-conflict-uneval`) refused every candidate. The funnel
//!   waived that verdict on the fully evaluated independent gate and answered
//!   `sat`, but `a` was left out: "model value for array a is not available"
//!   (fuzz tN t9101_074).
//! * Weaker. A candidate for the row term `(select m0 (ite p x y))`, with
//!   `x = y`, disagreed with `m0`'s own reads at one cell. Every authored
//!   assertion still held, but the funnel's select-congruence gate degraded
//!   `sat` to `unknown` (fuzz qC q8003_191, z3 5.1.0: sat).

use super::qf_aufbv_nested_select_scan::assert_printed_model_satisfies;
use super::*;

fn run(input: &str) -> Vec<String> {
    let commands = parse(input).expect("invariant: valid SMT-LIB input");
    let mut exec = Executor::new();
    exec.execute_all(&commands)
        .expect("invariant: execute succeeds")
}

/// t9101_074, minimized: `v = 3` makes the second disjunct false, so `a` is
/// read only there and is completed by the gap pass. `z` is tainted.
const UNREAD_ARRAY_BESIDE_A_TAINTED_ONE: &str = r#"
    (set-option :produce-models true)
    (set-logic QF_AUFBV)
    (declare-const a (Array (_ BitVec 4) Bool))
    (declare-const e (Array (_ BitVec 4) Bool))
    (declare-const w (Array (_ BitVec 4) (_ BitVec 3)))
    (declare-const z (Array (_ BitVec 4) (_ BitVec 3)))
    (declare-const p Bool)
    (declare-const x (_ BitVec 4))
    (declare-const y (_ BitVec 4))
    (declare-const v (_ BitVec 3))
    (declare-fun k ((_ BitVec 3)) (_ BitVec 4))
    (assert (or (= z (store (store ((as const (Array (_ BitVec 4) (_ BitVec 3))) (bvadd (_ bv6 3) (_ bv1 3))) (k v) v) (_ bv0 4) (_ bv3 3))) (and true (= v (_ bv0 3)) (= (store (store ((as const (Array (_ BitVec 4) Bool)) (= (select z (_ bv6 4)) (select w (_ bv0 4)))) (_ bv10 4) true) (ite p x y) true) e) (ite true (select a (_ bv10 4)) true))))
    (assert (= v (_ bv3 3)))
"#;

#[test]
fn test_array_beside_a_completion_tainted_one_is_printed() {
    let source = UNREAD_ARRAY_BESIDE_A_TAINTED_ONE;
    let out = run(&format!("{source} (check-sat) (get-model)"));
    assert_eq!(out[0], "sat", "{out:?}");
    assert!(!out[1].contains("(error"), "{out:?}");
    assert!(out[1].contains("(define-fun a "), "{out:?}");
    assert_printed_model_satisfies(source, &out);
}

/// The fuzz file itself. A symbol the printed model leaves out (`f` and `g`
/// at the time of writing) stays declared in the re-check, so it is free.
const T9101_074: &str = r#"
    (set-option :produce-models true)
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
    (assert (or (and (= c d) (= q (= e ((as const (Array (_ BitVec 4) Bool)) true)))) (= c ((as const (Array (_ BitVec 4) Bool)) (= (_ bv6 3) (select z (_ bv3 4))))) (= v (_ bv0 3))))
    (assert (or (= z (store (store ((as const (Array (_ BitVec 4) (_ BitVec 3))) (bvadd (_ bv6 3) (_ bv1 3))) (k v) v) (_ bv0 4) (_ bv3 3))) (and (select a (ite p x y)) (= v (_ bv0 3)) (= (store (store ((as const (Array (_ BitVec 4) Bool)) (= (select z (_ bv6 4)) (select w (_ bv0 4)))) (_ bv10 4) (select d (_ bv11 4))) (ite p x y) (select e x)) e) (ite (= e (store (store c (bvadd x (_ bv3 4)) (not (f (_ bv9 4)))) (ite p x y) (not p))) (select a (_ bv10 4)) (= (g x) (g y))))))
    (assert (and (not (= c e)) (f x) (not (= w (store u (k (ite p (_ bv1 3) (_ bv1 3))) (_ bv5 3))))))
    (assert (= (select w (_ bv6 4)) (select w y)))
    (assert (= v (_ bv3 3)))
"#;

#[test]
fn test_t9101_074_answers_sat_with_a_printable_model() {
    let out = run(&format!("{T9101_074} (check-sat) (get-model)"));
    assert_eq!(out[0], "sat", "{out:?}");
    assert!(!out[1].contains("(error"), "{out:?}");
    assert_printed_model_satisfies(T9101_074, &out);
}

/// q8003_191, minimized: `m0[x][kk 2]` differs from `z[x]`, and `x = y`.
const ROW_TERM_READ_TWICE: &str = r#"
    (set-option :produce-models true)
    (set-logic QF_AUFBV)
    (declare-const u (Array (_ BitVec 2) (_ BitVec 2)))
    (declare-const w (Array (_ BitVec 2) (_ BitVec 2)))
    (declare-const z (Array (_ BitVec 2) (_ BitVec 2)))
    (declare-const m0 (Array (_ BitVec 2) (Array (_ BitVec 2) (_ BitVec 2))))
    (declare-const m (Array (_ BitVec 2) (Array (_ BitVec 2) (_ BitVec 2))))
    (declare-const n (Array (_ BitVec 2) (Array (_ BitVec 2) (_ BitVec 2))))
    (declare-const p Bool)
    (declare-const q Bool)
    (declare-const x (_ BitVec 2))
    (declare-const y (_ BitVec 2))
    (declare-const v (_ BitVec 2))
    (declare-fun gg ((_ BitVec 2)) (_ BitVec 2))
    (declare-fun kk ((_ BitVec 2)) (_ BitVec 2))
    (assert (= n (store (store m (ite p x y) (store (select m (kk (_ bv3 2))) y (_ bv1 2))) (_ bv1 2) ((as const (Array (_ BitVec 2) (_ BitVec 2))) (gg (bvadd x (_ bv1 2)))))))
    (assert (or (and (= (select (select m0 (ite p x y)) (_ bv0 2)) (_ bv2 2)) (= (select m y) (select n (_ bv1 2)))) (= m (store (store m0 (bvadd x (_ bv1 2)) (select m0 y)) (ite p x y) (store ((as const (Array (_ BitVec 2) (_ BitVec 2))) (select u (_ bv0 2))) (bvadd x (_ bv1 2)) (_ bv2 2)))) (and (= (select (select m (_ bv0 2)) (_ bv0 2)) (select (select m0 (ite p x y)) (_ bv1 2))) (= m (store m0 (_ bv3 2) (select m0 (kk (select w (bvadd x (_ bv1 2))))))))))
    (assert (= x y))
    (assert (not (= (select (select m0 x) (kk (_ bv2 2))) (select z x))))
    (assert (= (select n (bvadd x (_ bv1 2))) (select m0 y)))
"#;

#[test]
fn test_completion_breaking_select_congruence_keeps_the_sat_answer() {
    let out = run(&format!("{ROW_TERM_READ_TWICE} (check-sat) (get-model)"));
    assert_eq!(out[0], "sat", "{out:?}");
    assert!(!out[1].contains("(error"), "{out:?}");
    assert_printed_model_satisfies(ROW_TERM_READ_TWICE, &out);
}
