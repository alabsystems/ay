// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `(get-model)` prints the model the validation gate checked.
//!
//! The printer used to read a constant's EUF class element ahead of every
//! theory model for any sort but Int/Real/Seq/BitVec, while get-value and the
//! gate read the evaluation chain. An FP-to-Real solve with a symbolic
//! rounding mode therefore printed `r = roundNearestTiesToEven`, the Real
//! subproblem's own EUF choice, and `x = 2.25`, which `to_fp` gives only under
//! the circuit's `roundTowardZero` (2026-09-30 FP verify). The gate had checked
//! RTZ and passed; the printed model falsified the formula.

use super::*;
use ay_fp::{FpModel, FpModelValue, RoundingMode};
use ay_frontend::parse;

fn solved(script: &str) -> Executor {
    let commands = parse(script).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execute succeeds");
    assert_eq!(outputs[0], "sat", "fixture must be sat");
    exec
}

fn declared(exec: &Executor, name: &str) -> TermId {
    exec.ctx
        .symbol_iter()
        .find(|(symbol, _)| *symbol == name)
        .and_then(|(_, info)| info.term)
        .unwrap_or_else(|| panic!("`{name}` is declared"))
}

/// `(fp #b0 #b1000 #b0010)`: 2.25 in format (4, 5), `to_fp` of 7/3 under RTZ.
fn two_and_a_quarter() -> FpModelValue {
    FpModelValue::Fp {
        sign: false,
        exponent: 8,
        significand: 2,
        eb: 4,
        sb: 5,
    }
}

const TO_FP_UNDER_A_SYMBOLIC_MODE: &str = r#"
    (set-option :produce-models true)
    (set-logic QF_FPLRA)
    (declare-const r RoundingMode)
    (declare-const x (_ FloatingPoint 4 5))
    (assert (= x ((_ to_fp 4 5) r (/ 7 3))))
    (assert (< (fp.to_real x) (/ 7 3)))
    (check-sat)
"#;

/// The FP-to-Real lane's model shape: the circuit decoded RTZ from the mode's
/// three bits and `x = 2.25`, and the Real subproblem's EUF model holds its
/// own RNE for `r` and an unrelated value for `x`. Both constants must print
/// the values the gate checks, and the gate must confirm them.
#[test]
fn get_model_prints_the_mode_and_value_the_fp_circuit_decoded() {
    let mut exec = solved(TO_FP_UNDER_A_SYMBOLIC_MODE);
    let r = declared(&exec, "r");
    let x = declared(&exec, "x");
    let model = exec.last_model.as_mut().expect("model exists");
    let fp_model = model.fp_model.get_or_insert_with(FpModel::default);
    fp_model.values.insert(x, two_and_a_quarter());
    fp_model.rm_values.insert(r, RoundingMode::RTZ);
    let euf = model.euf_model.get_or_insert_with(EufModel::default);
    euf.term_values.insert(r, "RNE".to_string());
    euf.term_values
        .insert(x, "(fp #b0 #b1000 #b0011)".to_string());
    eval_memo_clear();

    let printed = exec.model();
    assert!(
        printed.contains("(define-fun r () RoundingMode roundTowardZero)"),
        "get-model must print the circuit's mode: {printed}"
    );
    assert!(
        printed.contains("(fp #b0 #b1000 #b0010)") && !printed.contains("#b0011"),
        "get-model must print the circuit's x: {printed}"
    );
    let value = exec.values(&[("r".to_string(), r)]);
    assert!(
        value.contains("roundTowardZero"),
        "get-value must agree with get-model: {value}"
    );
    assert_eq!(
        exec.apply_independent_model_gate(SolveResult::Sat),
        SolveResult::Sat,
        "the printed model satisfies the formula and the gate confirms it"
    );
}

/// The gate checks the value get-model prints. A Bool constant still prints
/// its EUF element first; when that element contradicts the SAT model the gate
/// used to confirm the SAT model's value while get-model printed the other
/// one. It must now refuse to confirm.
#[test]
fn independent_gate_refuses_a_printed_value_it_did_not_check() {
    let mut exec = solved(
        r#"
        (set-option :produce-models true)
        (set-logic QF_UF)
        (declare-sort U 0)
        (declare-fun f (U) U)
        (declare-const a U)
        (declare-const b Bool)
        (assert (= (f a) a))
        (assert b)
        (check-sat)
    "#,
    );
    let b = declared(&exec, "b");
    let model = exec.last_model.as_mut().expect("model exists");
    let euf = model.euf_model.get_or_insert_with(EufModel::default);
    euf.term_values.insert(b, "false".to_string());
    eval_memo_clear();

    let printed = exec.model();
    assert!(
        printed.contains("(define-fun b () Bool false)"),
        "fixture: get-model prints the EUF element: {printed}"
    );
    assert_eq!(
        exec.apply_independent_model_gate(SolveResult::Sat),
        SolveResult::Unknown,
        "the gate must not confirm a model whose printed `b = false` it never checked"
    );
}
