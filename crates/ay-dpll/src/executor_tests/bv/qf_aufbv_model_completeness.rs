// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! QF_AUFBV array definitions the model forces (or makes irrelevant) whose
//! interpretation the BV lane could not build, so the strict gate refused a
//! z3-`sat` query (`arrays-read-conflict-uneval`) and AY answered `unknown`:
//!
//! * a definition listed before the definition of the array it reads;
//! * an operand that is a Bool- or BV-element read of an array variable, or an
//!   uninterpreted application;
//! * an array defined only in a disjunct the model made irrelevant or whose
//!   definition atom it set false, which `sat` never needed but `(get-model)`
//!   reported as "not available";
//! * a nested `(Array BV64 (Array BV64 BV8))` definition.
//!
//! And one that must stay withheld although it now builds: a top-level
//! definition reading its own variable whose default disputes the model's
//! `(default w)` (`definition_order.rs`), which `sat` never needed.
//!
//! Every `sat` twin has an `unsat` twin contradicting the forced definition.

use super::*;

fn run(input: &str) -> Vec<String> {
    let commands = parse(input).expect("invariant: valid SMT-LIB input");
    let mut exec = Executor::new();
    exec.execute_all(&commands)
        .expect("invariant: execute succeeds")
}

/// `d := (store c 9 false)` precedes `c`'s own definition in the forced arm.
const BASE_DEFINED_LATER: &str = r#"
    (set-logic QF_AUFBV)
    (declare-const a (Array (_ BitVec 32) Bool))
    (declare-const c (Array (_ BitVec 32) Bool))
    (declare-const d (Array (_ BitVec 32) Bool))
    (assert (select a #x00000042))
    (assert (or (not (select a #x00000042))
                (and (= d (store c #x00000009 false))
                     (= c (store ((as const (Array (_ BitVec 32) Bool)) true) #x00000001 false)))))
"#;

#[test]
fn test_definition_before_its_base_definition_is_sat() {
    let input = format!("{BASE_DEFINED_LATER} (assert (select d #x00000005)) (check-sat)");
    assert_eq!(run(&input), vec!["sat"]);
}

#[test]
fn test_definition_before_its_base_definition_contradiction_is_unsat() {
    let input = format!("{BASE_DEFINED_LATER} (assert (not (select d #x00000005))) (check-sat)");
    assert_eq!(run(&input), vec!["unsat"]);
}

/// The default and the stored value are Bool-element reads of `m`.
const BOOL_READ_OPERANDS: &str = r#"
    (set-logic QF_AUFBV)
    (set-option :produce-models true)
    (declare-const x (_ BitVec 4))
    (declare-const a (Array (_ BitVec 32) Bool))
    (declare-const m (Array (_ BitVec 4) Bool))
    (declare-const z (Array (_ BitVec 4) Bool))
    (assert (select a #x00000042))
    (assert (select m #x1))
    (assert (or (not (select a #x00000042))
                (= z (store ((as const (Array (_ BitVec 4) Bool)) (select m #x1)) x (select m #x3)))))
"#;

#[test]
fn test_bool_read_operand_definition_is_sat() {
    let input = format!(
        "{BOOL_READ_OPERANDS} (assert (select z #x5)) (assert (not (= x #x5))) (check-sat)
         (get-value ((select z #x5)))"
    );
    let out = run(&input);
    assert_eq!(out[0], "sat", "{out:?}");
    assert_eq!(out[1], "(((select z #x5) true))", "{out:?}");
}

#[test]
fn test_bool_read_operand_definition_contradiction_is_unsat() {
    let input = format!(
        "{BOOL_READ_OPERANDS} (assert (not (select z #x5))) (assert (not (= x #x5))) (check-sat)"
    );
    assert_eq!(run(&input), vec!["unsat"]);
}

/// The stored value is an uninterpreted application.
const UF_OPERAND: &str = r#"
    (set-logic QF_AUFBV)
    (declare-fun g ((_ BitVec 4)) (_ BitVec 3))
    (declare-const x (_ BitVec 4))
    (declare-const a (Array (_ BitVec 32) Bool))
    (declare-const z (Array (_ BitVec 4) (_ BitVec 3)))
    (assert (select a #x00000042))
    (assert (or (not (select a #x00000042))
                (= z (store ((as const (Array (_ BitVec 4) (_ BitVec 3))) #b000) x (g x)))))
"#;

#[test]
fn test_uf_operand_definition_is_sat() {
    let input = format!("{UF_OPERAND} (assert (= (select z x) (g x))) (check-sat)");
    assert_eq!(run(&input), vec!["sat"]);
}

#[test]
fn test_uf_operand_definition_contradiction_is_unsat() {
    let input = format!("{UF_OPERAND} (assert (not (= (select z x) (g x)))) (check-sat)");
    assert_eq!(run(&input), vec!["unsat"]);
}

/// `c` is defined only in the disjunct `(bvuge x #x07)` falsifies, so its
/// definition cannot hold (here the SAT assignment also sets its atom false,
/// either of which releases `c`; the unit tests pin each rule alone).
#[test]
fn test_dead_arm_array_has_a_model_value() {
    let input = r#"
        (set-logic QF_AUFBV)
        (set-option :produce-models true)
        (declare-const x (_ BitVec 8))
        (declare-const c (Array (_ BitVec 32) (_ BitVec 8)))
        (declare-const d (Array (_ BitVec 32) (_ BitVec 8)))
        (assert (bvult x #x05))
        (assert (or (and (bvuge x #x07)
                         (= c (store ((as const (Array (_ BitVec 32) (_ BitVec 8))) #x00) #x00000001 #x05)))
                    (= d (store ((as const (Array (_ BitVec 32) (_ BitVec 8))) #x00) #x00000002 #x06))))
        (check-sat)
        (get-model)
    "#;
    let out = run(input);
    assert_eq!(out[0], "sat", "{out:?}");
    assert!(!out[1].contains("error"), "{out:?}");
    assert!(out[1].contains("(define-fun c "), "{out:?}");
    assert!(
        out[1].contains("#x00000002 #x06"),
        "d keeps its forced definition: {out:?}"
    );
}

/// `z`'s only definition is a disjunct the model must falsify, `(not (select
/// z #x3))` refutes `(const true)`: the assignment commits to `z` differing
/// from it, so `z` is an ordinary array with a model value.
const FALSIFIED_DEFINITION: &str = r#"
    (set-logic QF_AUFBV)
    (set-option :produce-models true)
    (declare-const q Bool)
    (declare-const c (Array (_ BitVec 4) Bool))
    (declare-const z (Array (_ BitVec 4) Bool))
    (assert (or (= z ((as const (Array (_ BitVec 4) Bool)) true))
                (and q (= c ((as const (Array (_ BitVec 4) Bool)) false)))))
    (assert (not (select z #x3)))
"#;

#[test]
fn test_falsified_definition_array_has_a_model_value() {
    let input = format!("{FALSIFIED_DEFINITION} (check-sat) (get-model)");
    let out = run(&input);
    assert_eq!(out[0], "sat", "{out:?}");
    assert!(!out[1].contains("error"), "{out:?}");
    assert!(out[1].contains("(define-fun z "), "{out:?}");
}

#[test]
fn test_falsified_definition_contradiction_is_unsat() {
    let input = format!("{FALSIFIED_DEFINITION} (assert (select c #x5)) (check-sat)");
    assert_eq!(run(&input), vec!["unsat"]);
}

/// A forced `(Array BV64 (Array BV64 BV8))` definition storing a whole row.
const NESTED_STORE: &str = r#"
    (set-logic QF_AUFBV)
    (declare-const a (Array (_ BitVec 64) Bool))
    (declare-const m (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 8))))
    (assert (select a #x0000000000000042))
    (assert (or (not (select a #x0000000000000042))
                (= m (store ((as const (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 8))))
                              ((as const (Array (_ BitVec 64) (_ BitVec 8))) #x00))
                            #x0000000000000001
                            (store ((as const (Array (_ BitVec 64) (_ BitVec 8))) #x00)
                                   #x0000000000000002 #x07)))))
"#;

#[test]
fn test_nested_array_store_definition_is_sat() {
    let input = format!(
        "{NESTED_STORE} (assert (= (select (select m #x0000000000000001) #x0000000000000002) #x07))
         (check-sat)"
    );
    assert_eq!(run(&input), vec!["sat"]);
}

#[test]
fn test_nested_array_store_definition_contradiction_is_unsat() {
    let input = format!(
        "{NESTED_STORE}
         (assert (not (= (select (select m #x0000000000000001) #x0000000000000002) #x07)))
         (check-sat)"
    );
    assert_eq!(run(&input), vec!["unsat"]);
}

/// `w`'s top-level definition reads `w` itself; the forced arm also defines it
/// as `(const #b101)`. The self-read builds over `u`'s guessed default, and
/// publishing it lets model completion taint `w` and `u` against the model's
/// `(default w)`: `w` stays withheld as before the self-read could resolve.
const SELF_READ_BESIDE_A_CONSTANT: &str = r#"
    (set-logic QF_AUFBV)
    (declare-const b (Array (_ BitVec 4) Bool))
    (declare-const d (Array (_ BitVec 4) Bool))
    (declare-const u (Array (_ BitVec 4) (_ BitVec 3)))
    (declare-const w (Array (_ BitVec 4) (_ BitVec 3)))
    (declare-const z (Array (_ BitVec 4) (_ BitVec 3)))
    (declare-const x (_ BitVec 4))
    (declare-const y (_ BitVec 4))
    (assert (or (and (= z ((as const (Array (_ BitVec 4) (_ BitVec 3))) (select u y)))
                     (= w ((as const (Array (_ BitVec 4) (_ BitVec 3))) #b101)))
                (= d (store b x true))))
    (assert (= (store u #xa (select w y)) w))
"#;

#[test]
fn test_self_read_definition_beside_a_constant_is_sat() {
    let input = format!("{SELF_READ_BESIDE_A_CONSTANT} (check-sat)");
    assert_eq!(run(&input), vec!["sat"]);
}

#[test]
fn test_self_read_definition_beside_a_constant_contradiction_is_unsat() {
    let input = format!(
        "{SELF_READ_BESIDE_A_CONSTANT} (assert (not (= d (store b x true))))
         (assert (not (= (select u #x3) #b101))) (check-sat)"
    );
    assert_eq!(run(&input), vec!["unsat"]);
}
