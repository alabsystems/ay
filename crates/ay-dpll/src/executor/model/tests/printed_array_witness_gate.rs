// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! AY-N9: the printed-array-witness gate compares the array `(get-model)`
//! prints through the witness builder with the value the independent gate
//! validated.
//!
//! On the SMT-COMP QF_AX swap instance the validated model held `x24` with
//! cells at both index elements `@ay!wit!xidx!0` and `@ay!wit!xidx!1`, while
//! the printer, which did not accept `@ay!wit!` elements, printed only the
//! cell it found as a direct read and `@x9!0` as default. Every gate passed
//! and Dolmen rejected the printed model. These tests pin that the printed
//! witness now denotes the validated value, and that the gate reports the
//! text the old printer produced.

use super::*;
use ay_frontend::parse;

const INSTANCE: &str = r"
(set-logic QF_AX)
(set-option :produce-models true)
(declare-sort x17 0)
(declare-sort x9 0)
(declare-fun x2 () x17)
(declare-fun x24 () (Array x17 x9))
(declare-fun x10 () x17)
(declare-fun x29 () x17)
(declare-fun x18 () x17)
(declare-fun x25 () x17)
(declare-fun x28 () x17)
(declare-fun x5 () x17)
(declare-fun x23 () (Array x17 x9))
(declare-fun x11 () x17)
(declare-fun x4 () x17)
(assert (let ((x26 (store x24 x25 (select x23 x25))) (x21 (store x23 x25 (select x24 x25)))) (let ((x16 (store x21 x2 (select x26 x2))) (x8 (store x26 x2 (select x21 x2)))) (let ((x20 (store x16 x11 (select x8 x11))) (x3 (store x8 x11 (select x16 x11)))) (let ((x12 (store x20 x29 (select x3 x29))) (x27 (store x3 x29 (select x20 x29)))) (let ((x6 (store x12 x18 (select x27 x18))) (x15 (store x27 x18 (select x12 x18)))) (let ((x19 (store x6 x28 (select x15 x28))) (x22 (store x15 x28 (select x6 x28)))) (let ((x1 (store x22 x10 (select x19 x10))) (x13 (store x19 x10 (select x22 x10)))) (let ((x14 (store x13 x4 (select x1 x4))) (x7 (store x1 x4 (select x13 x4)))) (= (store x14 x25 (select x7 x5)) (store x7 x5 (select x14 x5))))))))))))
(assert (not (= x24 x23)))
(check-sat)
";

fn solved() -> Executor {
    let commands = parse(INSTANCE).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("script executes");
    assert_eq!(outputs, vec!["sat".to_string()], "the instance is sat");
    exec
}

fn declared(exec: &Executor, name: &str) -> TermId {
    exec.ctx
        .symbol_iter()
        .find(|(symbol, _)| *symbol == name)
        .and_then(|(_, info)| info.term)
        .unwrap_or_else(|| panic!("`{name}` is declared"))
}

/// `(get-model)` prints both arrays with their cells at every witness index
/// element, and the witness builder's own text for them denotes the value the
/// gate validated.
#[test]
fn printed_witness_of_the_swap_instance_is_the_validated_array() {
    let exec = solved();
    let printed_model = exec.model();
    let x23_line = printed_model
        .split("(define-fun ")
        .find(|entry| entry.starts_with("x23 "))
        .unwrap_or_else(|| panic!("x23 is printed: {printed_model}"));
    assert!(
        x23_line.contains("@ay!wit!xidx!1"),
        "x23 must keep its cell at the second index element: {x23_line}"
    );
    let model = exec.last_model.as_ref().expect("sat leaves a model");
    for name in ["x23", "x24"] {
        let term = declared(&exec, name);
        let sort = exec.ctx.terms.sort(term).clone();
        let text = exec
            .format_array_witness_value(model, term, &sort)
            .unwrap_or_else(|| panic!("the witness builder renders {name}"));
        assert_eq!(
            exec.printed_array_witness_divergence(model, &[(term, text.clone())]),
            None,
            "{name}: {text}"
        );
    }
}

/// The text the printer produced before the fix (default `@x9!0`, one cell)
/// denotes another array than the validated `x24`; the gate names it.
#[test]
fn gate_reports_the_witness_the_old_printer_produced() {
    let exec = solved();
    let model = exec.last_model.as_ref().expect("sat leaves a model");
    let x24 = declared(&exec, "x24");
    let old_text = "(store ((as const (Array x17 x9)) (as @x9!0 x9)) \
                    (as @ay!wit!xidx!0 x17) (as @ay!wit!xval!2 x9))"
        .to_string();
    assert_eq!(
        exec.printed_array_witness_divergence(model, &[(x24, old_text)]),
        Some(x24)
    );
}
