// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Every RoundingMode value a model holds, prints and the gate checks is one of
//! the five modes (2026-09-30 FP verify 2, `abstract_rm_unused_constant.smt2`).

use super::*;
use crate::executor::model::eval_memo_clear;
use crate::executor_types::SolveResult;
use ay_fp::FpModel;
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

fn strings(values: &[&str]) -> Vec<String> {
    values.iter().map(|value| value.to_string()).collect()
}

const RNE: &str = "roundNearestTiesToEven";
const RNA: &str = "roundNearestTiesToAway";
const RTZ: &str = "roundTowardZero";

/// The verifier's repro: `r2` occurs in no assertion, the lane is FP-to-Real
/// and `g` is a UF over RoundingMode. The Real subproblem's EUF model named
/// `r2`'s class `@RoundingMode!1`, and get-model, get-value and the gate all
/// published it.
const UNUSED_MODE_CONSTANT: &str = r#"
    (set-option :produce-models true)
    (set-logic ALL)
    (declare-const r1 RoundingMode)
    (declare-const r2 RoundingMode)
    (declare-const x (_ FloatingPoint 3 5))
    (declare-const q Real)
    (declare-fun g (RoundingMode) Int)
    (assert (< (fp.to_real x) (/ 89 3)))
    (assert (< q (/ 89 3)))
    (assert (distinct r1 RNE))
    (check-sat)
"#;

#[test]
fn an_unused_mode_constant_prints_a_mode() {
    let mut exec = solved(UNUSED_MODE_CONSTANT);
    let r2 = declared(&exec, "r2");
    let printed = exec.model();
    assert!(
        !printed.contains("@RoundingMode"),
        "get-model must not publish a minted element: {printed}"
    );
    let line = printed
        .lines()
        .find(|line| line.contains("(define-fun r2 ()"))
        .unwrap_or_else(|| panic!("no r2 in the model: {printed}"));
    let mode = RM_MODES
        .iter()
        .map(|&mode| rm_long_name(mode))
        .find(|name| line.contains(&format!(" {name})")))
        .unwrap_or_else(|| panic!("r2 must print one of the five modes: {line}"));
    let value = exec.values(&[("r2".to_string(), r2)]);
    assert!(
        value.contains(&format!("(r2 {mode})")),
        "get-value must agree with get-model: {value}"
    );
    assert_eq!(
        exec.apply_independent_model_gate(SolveResult::Sat),
        SolveResult::Sat
    );
}

/// The mapping itself, on the FP-to-Real merge's shape: the Real
/// subproblem's EUF model minted a class for `r1` (decided RTZ by the circuit)
/// and one for `r2` (unconstrained), with a stale `g` row keyed by each.
#[test]
fn minted_values_become_modes_consistently() {
    let exec = solved(
        r#"
        (set-logic ALL)
        (declare-const r1 RoundingMode)
        (declare-const r2 RoundingMode)
        (declare-const r3 RoundingMode)
        (declare-const A (Array Int RoundingMode))
        (declare-fun g (RoundingMode) Int)
        (assert (= (g r1) 0))
        (check-sat)
    "#,
    );
    let (r1, r2, r3, a) = (
        declared(&exec, "r1"),
        declared(&exec, "r2"),
        declared(&exec, "r3"),
        declared(&exec, "A"),
    );
    let mut model = Model::empty();
    let mut fp = FpModel::default();
    fp.rm_values.insert(r1, RoundingMode::RTZ);
    model.fp_model = Some(fp);
    let mut euf = EufModel::default();
    euf.sort_elements.insert(
        RM_SORT_NAME.to_string(),
        strings(&[RNE, "@RoundingMode!0", RTZ, "@RoundingMode!1"]),
    );
    euf.term_values.insert(r1, "@RoundingMode!0".to_string());
    euf.term_values.insert(r2, "@RoundingMode!1".to_string());
    euf.function_tables.insert(
        "g".to_string(),
        vec![
            (strings(&["@RoundingMode!0"]), "1".to_string()),
            (strings(&[RTZ]), "0".to_string()),
            (strings(&["@RoundingMode!1"]), "7".to_string()),
        ],
    );
    euf.function_table_terms
        .insert("g".to_string(), vec![TermId(900), TermId(901), TermId(902)]);
    model.euf_model = Some(euf);
    let mut arrays = ArrayModel::default();
    arrays.array_values.insert(
        a,
        ArrayInterpretation {
            default: Some("@RoundingMode!1".to_string()),
            stores: vec![("3".to_string(), "@RoundingMode!0".to_string())],
            index_sort: Some(Sort::Int),
            element_sort: None,
        },
    );
    model.array_model = Some(arrays);
    model
        .completed_values
        .insert(r3, EvalValue::Element("@RoundingMode!1".to_string()));

    assert!(exec.concretize_rounding_mode_values(&mut model));

    let euf = model.euf_model.as_ref().expect("EUF model");
    // `@RoundingMode!0` holds r1, which the circuit decoded as RTZ;
    // `@RoundingMode!1` takes the first mode no class names.
    assert_eq!(euf.term_values[&r1], RTZ);
    assert_eq!(euf.term_values[&r2], RNA);
    assert_eq!(euf.sort_elements[RM_SORT_NAME], strings(&[RNE, RTZ, RNA]));
    // The stale row keyed by r1's class yields to the literal RTZ row; the
    // row keyed by r2's class moves to RNA, and the sources stay aligned.
    assert_eq!(
        euf.function_tables["g"],
        vec![
            (strings(&[RTZ]), "0".to_string()),
            (strings(&[RNA]), "7".to_string()),
        ]
    );
    assert_eq!(
        euf.function_table_terms["g"],
        vec![TermId(901), TermId(902)]
    );
    let interp = &model.array_model.as_ref().expect("arrays").array_values[&a];
    assert_eq!(interp.default.as_deref(), Some(RNA));
    assert_eq!(interp.stores, vec![("3".to_string(), RTZ.to_string())]);
    assert_eq!(
        model.completed_values[&r3],
        EvalValue::Element(RNA.to_string())
    );
    assert!(
        !exec.concretize_rounding_mode_values(&mut model),
        "a concrete model is left alone"
    );
}

/// Two minted classes a disequality separates stay distinct when a mode is
/// free, and an array indexed by modes drops a moved store that would shadow
/// the literal index's store.
#[test]
fn distinct_minted_values_take_distinct_modes() {
    let exec = solved(
        r#"
        (set-logic ALL)
        (declare-const r1 RoundingMode)
        (declare-const r2 RoundingMode)
        (declare-const B (Array RoundingMode Int))
        (assert (distinct r1 r2))
        (check-sat)
    "#,
    );
    let (r1, r2, b) = (
        declared(&exec, "r1"),
        declared(&exec, "r2"),
        declared(&exec, "B"),
    );
    let mut model = Model::empty();
    let mut euf = EufModel::default();
    euf.term_values.insert(r1, "@RoundingMode!0".to_string());
    euf.term_values.insert(r2, "@RoundingMode!1".to_string());
    model.euf_model = Some(euf);
    let mut arrays = ArrayModel::default();
    arrays.array_values.insert(
        b,
        ArrayInterpretation {
            default: Some("0".to_string()),
            stores: vec![
                ("@RoundingMode!0".to_string(), "5".to_string()),
                (RNE.to_string(), "6".to_string()),
                ("@RoundingMode!1".to_string(), "7".to_string()),
            ],
            index_sort: None,
            element_sort: Some(Sort::Int),
        },
    );
    model.array_model = Some(arrays);

    assert!(exec.concretize_rounding_mode_values(&mut model));
    let euf = model.euf_model.as_ref().expect("EUF model");
    // RNE is named by the array's literal index, so the minted classes take
    // the next free modes, one each.
    assert_eq!(euf.term_values[&r1], RNA);
    assert_eq!(euf.term_values[&r2], "roundTowardPositive");
    let interp = &model.array_model.as_ref().expect("arrays").array_values[&b];
    assert_eq!(
        interp.stores,
        vec![
            (RNA.to_string(), "5".to_string()),
            (RNE.to_string(), "6".to_string()),
            ("roundTowardPositive".to_string(), "7".to_string()),
        ]
    );
}

/// A minted element that survives to the gate is not a value of the sort: the
/// evaluation chain leaves the constant Unknown and the gate cannot confirm.
#[test]
fn the_gate_does_not_confirm_a_minted_mode() {
    let mut exec = solved(
        r#"
        (set-option :produce-models true)
        (set-logic ALL)
        (declare-const r RoundingMode)
        (declare-fun h (RoundingMode) Bool)
        (assert (h r))
        (assert (distinct r RNE))
        (check-sat)
    "#,
    );
    let r = declared(&exec, "r");
    let model = exec.last_model.as_mut().expect("model exists");
    if let Some(fp) = model.fp_model.as_mut() {
        fp.rm_values.remove(&r);
    }
    model
        .euf_model
        .get_or_insert_with(EufModel::default)
        .term_values
        .insert(r, "@RoundingMode!3".to_string());
    eval_memo_clear();
    let model = exec.last_model.as_ref().expect("model exists");
    assert_eq!(
        exec.evaluate_var(model, r, &crate::executor::rm_domain::rm_sort()),
        EvalValue::Unknown
    );
    assert_eq!(
        exec.apply_independent_model_gate(SolveResult::Sat),
        SolveResult::Unknown
    );
}
