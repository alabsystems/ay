// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `completed_gap_model_accepted` is the SAT funnel's acceptance: its scoped
//! strict policy, its select-congruence gate and the independent gate. The
//! end-to-end fuzz reproducers are in
//! `executor_tests/bv/qf_aufbv_gap_completion.rs`.

use super::super::{EvalValue, Model};
use crate::executor::Executor;
use crate::executor_types::SolveResult;
use ay_arrays::ArrayInterpretation;
use ay_core::{Sort, TermId};
use ay_model_check::GateVerdict;
use num_bigint::BigInt;

/// tN t9101_074, minimized (z3 5.1.0: sat). Completion taints `z`, which
/// leaves assertion 0 unevaluable to AY's own evaluator.
const TAINTED_DEFINITION: &str = r#"
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
    (check-sat)
"#;

/// qC q8003_191, minimized (z3 5.1.0: sat): `x = y`, so the row term
/// `(select m0 (ite p x y))` is the row `(select m0 x)` that `m0` is read in.
const ROW_TERM_READ_TWICE: &str = r#"
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
    (check-sat)
"#;

fn solved(source: &str) -> Executor {
    let commands = ay_frontend::parse(source).expect("fixture parses");
    let mut executor = Executor::new();
    let out = executor.execute_all(&commands).expect("fixture executes");
    assert_eq!(out, ["sat"], "fixture is sat (z3 5.1.0)");
    executor
}

/// The unique term AY prints as `spelling`.
fn term(executor: &Executor, spelling: &str) -> TermId {
    let found: Vec<TermId> = (0..executor.ctx.terms.len())
        .map(|index| TermId(index as u32))
        .filter(|&term| executor.format_term(term) == spelling)
        .collect();
    assert_eq!(found.len(), 1, "one term prints as {spelling}");
    found[0]
}

/// The strict verdicts on `model`, raw and scoped, by oracle name.
fn strict_verdicts(
    executor: &mut Executor,
    model: &Model,
) -> (Option<&'static str>, Option<&'static str>) {
    let installed = executor.last_model.replace(model.clone());
    let result = executor.last_result.replace(SolveResult::Sat);
    let raw = executor.verify_model_strict().map(|(_, oracle, _)| oracle);
    let scoped = executor
        .verify_model_strict_with_scoped_authority()
        .map(|(_, oracle, _)| oracle);
    executor.last_model = installed;
    executor.last_result = result;
    (raw, scoped)
}

fn accepted(executor: &mut Executor, model: &Model) -> bool {
    executor.completed_gap_model_accepted(&mut model.clone())
}

/// The published model, `a` included, is what the gap pass completed. The raw
/// oracle refuses it for a coverage gap no completion can close (`z` stays
/// tainted), which the funnel waives on the fully evaluated independent gate.
/// The re-check now applies the same waiver.
#[test]
fn coverage_gap_the_funnel_waives_does_not_refuse_the_completion() {
    let mut executor = solved(TAINTED_DEFINITION);
    let model = executor.last_model.clone().expect("sat keeps its model");
    let a = term(&executor, "a");
    let z = term(&executor, "z");
    let arrays = model.array_model.as_ref().expect("array model");
    assert!(arrays.read_conflicted.contains(&z), "completion tainted z");
    assert!(arrays.array_values.contains_key(&a), "a was completed");

    let (raw, scoped) = strict_verdicts(&mut executor, &model);
    assert_eq!(raw, Some("arrays-read-conflict-uneval"));
    assert_eq!(scoped, None, "the funnel waives the coverage gap");
    assert!(accepted(&mut executor, &model));
}

/// Negative twin: the waiver judges the completed model. `z[9] != z[10]` is
/// false (`z` holds 7 away from its stores at `k 3` and 0), but AY's evaluator
/// cannot read tainted `z` at a cell nothing stored, so the raw verdict is
/// still only the coverage gap. The independent view refutes it, and the
/// completion is refused. (A read pinned to a constant, `(= (select z i) c)`,
/// would not do: AY's evaluator takes the pin from the assertion itself.)
#[test]
fn coverage_gap_waiver_still_refuses_a_falsified_assertion() {
    let mut executor = solved(TAINTED_DEFINITION);
    let model = executor.last_model.clone().expect("sat keeps its model");
    let z = term(&executor, "z");
    let nine = executor.ctx.terms.mk_bitvec(BigInt::from(9u8), 4);
    let ten = executor.ctx.terms.mk_bitvec(BigInt::from(10u8), 4);
    let at_nine = executor.ctx.terms.mk_select(z, nine);
    let at_ten = executor.ctx.terms.mk_select(z, ten);
    let same = executor.ctx.terms.mk_eq(at_nine, at_ten);
    let falsified = executor.ctx.terms.mk_not(same);
    executor.ctx.assertions.push(falsified);
    if let Some(roots) = executor.independent_gate_authored_assertions.as_mut() {
        roots.push(falsified);
    }
    let installed = executor.last_model.replace(model.clone());
    let value = executor.evaluate_term(&model, falsified);
    assert!(matches!(value, EvalValue::Unknown), "{value:?}");
    assert!(matches!(
        executor.confirm_sat_with_fully_evaluated_independent_gate(),
        GateVerdict::ModelViolates { .. }
    ));
    executor.last_model = installed;

    let (raw, scoped) = strict_verdicts(&mut executor, &model);
    assert_eq!(raw, Some("arrays-read-conflict-uneval"));
    assert!(scoped.is_some(), "no waiver over a refuted assertion");
    assert!(!accepted(&mut executor, &model));
}

/// Negative twin: the waiver needs every authored assertion evaluated. An
/// assertion the model does not pin is not a refutation, but it is no
/// authority either.
#[test]
fn coverage_gap_waiver_still_refuses_an_unevaluable_assertion() {
    let mut executor = solved(TAINTED_DEFINITION);
    let model = executor.last_model.clone().expect("sat keeps its model");
    let unpinned = executor
        .ctx
        .terms
        .mk_var("gap-acceptance-unpinned", Sort::Bool);
    executor.ctx.assertions.push(unpinned);
    if let Some(roots) = executor.independent_gate_authored_assertions.as_mut() {
        roots.push(unpinned);
    }
    let (raw, scoped) = strict_verdicts(&mut executor, &model);
    assert_eq!(raw, Some("arrays-read-conflict-uneval"));
    assert!(scoped.is_some(), "no waiver without full evaluation");
    assert!(!accepted(&mut executor, &model));
}

/// A candidate for the row term `(select m0 (ite p x y))` that disagrees with
/// the model's read of the same row passes the strict policy and the
/// independent gate, but the funnel's select-congruence gate would degrade
/// it, so the re-check refuses it (and keeps the published model).
#[test]
fn completion_breaking_select_congruence_is_refused() {
    let mut executor = solved(ROW_TERM_READ_TWICE);
    let model = executor.last_model.clone().expect("sat keeps its model");
    assert!(accepted(&mut executor, &model), "the published model");
    assert!(!executor.array_select_congruence_violated(&model).unwrap());

    let row = term(&executor, "(select m0 (ite p x y))");
    let pinned = term(&executor, "(select (select m0 x) (kk #b10))");
    let EvalValue::BitVec { value, width } = executor.evaluate_term(&model, pinned) else {
        panic!("the model reads m0[x][kk 2]");
    };
    let other = (value + 1u8) % (BigInt::from(1u8) << width as usize);
    let Sort::Array(row_sort) = executor.ctx.terms.sort(row).clone() else {
        panic!("row term is an array");
    };
    let mut candidate = model.clone();
    candidate
        .array_model
        .get_or_insert_with(Default::default)
        .array_values
        .insert(
            row,
            ArrayInterpretation {
                default: Some(format!("#b{other:0>width$b}", width = width as usize)),
                stores: Vec::new(),
                index_sort: Some(row_sort.index_sort.clone()),
                element_sort: Some(row_sort.element_sort.clone()),
            },
        );
    super::super::eval_memo_clear();
    assert!(
        executor
            .array_select_congruence_violated(&candidate)
            .unwrap(),
        "fixture: the candidate splits one cell of m0"
    );
    let (_, scoped) = strict_verdicts(&mut executor, &candidate);
    assert_eq!(scoped, None, "fixture: the strict policy accepts it");
    let installed = executor.last_model.replace(candidate.clone());
    assert!(matches!(
        executor.confirm_sat_with_independent_gate(),
        GateVerdict::ConfirmedSat
    ));
    executor.last_model = installed;
    assert!(!accepted(&mut executor, &candidate));
}
