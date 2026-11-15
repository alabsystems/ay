// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use ay_core::TermData;

fn prepared_fill(lo: u64, hi: u64, expected: u8) -> Executor {
    let text = format!("(declare-fun d () (Array (_ BitVec 64) (_ BitVec 8)))
        (declare-fun w () (Array (_ BitVec 64) (_ BitVec 8))) (declare-fun byte () (_ BitVec 8))
        (assert (= byte (_ bv9 8))) (assert (= (select d (_ bv0 64)) (_ bv7 8)))
        (assert (= w (lambda ((i (_ BitVec 64))) (ite (and (bvule (_ bv{lo} 64) i) (bvult i (_ bv{hi} 64))) byte (select d i)))))
        (assert (= (select w (_ bv1 64)) (_ bv{expected} 8)))");
    let mut exec = Executor::new();
    exec.execute_all(&parse(&text).expect("original scalar fill"))
        .expect("native elaboration only");
    exec
}

fn fill_model(exec: &Executor) -> Model {
    let mut model = Model::empty();
    model.completed_values.insert(
        variable(exec, "byte"),
        EvalValue::BitVec {
            value: 9.into(),
            width: 8,
        },
    );
    exec.install_functional_array_candidate(&mut model);
    model
}

#[test]
fn original_scalar_fill_candidate_preserves_every_root_and_conflicting_read() {
    for (expected, good) in [(9, true), (7, false)] {
        let exec = prepared_fill(1, u64::MAX, expected);
        let model = fill_model(&exec);
        assert!(
            model.functional_arrays.is_some(),
            "construction remains DATA"
        );
        assert_eq!(
            matches!(confirm(&exec, &model), GateVerdict::ConfirmedSat),
            good
        );
        if !good {
            assert!(matches!(
                confirm(&exec, &model),
                GateVerdict::ModelViolates { .. }
            ));
        }
    }
}

#[test]
fn fill_empty_and_reversed_keep_full_frame_but_still_require_original_scalar() {
    for (lo, hi) in [(0, 0), (9, 3)] {
        let mut exec = prepared_fill(lo, hi, 0);
        let model = fill_model(&exec);
        assert!(model.functional_arrays.is_some());
        let original = model
            .functional_array_value(&exec, variable(&exec, "w"))
            .expect("source")
            .expect("whole frame");
        assert!(matches!(
            original
                .read(&ModelValue::bitvec(0.into(), 64), &mut 1000)
                .expect("frame key"),
            ModelValue::BitVec { width: 8, value } if value == 7.into()
        ));
        exec.execute_all(&parse("(assert false)").expect("new original root"))
            .expect("source mutation");
        assert!(model
            .functional_array_value(&exec, variable(&exec, "w"))
            .is_err());
    }
}

#[test]
fn fill_constructor_backedges_and_unknown_functions_decline_before_install() {
    for value in ["(select w (_ bv0 64))", "(opaque byte)"] {
        let source = format!("(declare-fun d () (Array (_ BitVec 64) (_ BitVec 8)))
            (declare-fun w () (Array (_ BitVec 64) (_ BitVec 8))) (declare-fun byte () (_ BitVec 8))
            (declare-fun opaque ((_ BitVec 8)) (_ BitVec 8))
            (assert (= w (lambda ((i (_ BitVec 64))) (ite (and (bvule (_ bv1 64) i) (bvult i (_ bv3 64))) {value} (select d i)))))");
        let mut exec = Executor::new();
        exec.execute_all(&parse(&source).expect("original unsupported source"))
            .expect("elaborate");
        let model = fill_model(&exec);
        assert!(model.functional_arrays.is_none());
    }
}

#[test]
fn closed_finite_fill_snapshot_reparses_and_preserves_entire_function() {
    let exec = prepared_fill(1, 3, 9);
    let model = fill_model(&exec);
    let w = variable(&exec, "w");
    let original = model
        .functional_array_value(&exec, w)
        .expect("source")
        .expect("whole fill");
    let output = exec
        .functional_array_render(&model, w)
        .expect("same owner")
        .expect("full output");
    let source = format!("(declare-fun replayed () (Array (_ BitVec 64) (_ BitVec 8))) (assert (= replayed {output}))");
    let mut replay = Executor::new();
    replay
        .execute_all(&parse(&source).expect("exact emitted function"))
        .expect("elaborate closed output");
    let root = replay.independent_gate_query_roots().unwrap()[0];
    let TermData::App(_, args) = replay.ctx.terms.get(root) else {
        panic!("actual equality");
    };
    let empty = Model::empty();
    let view = IndependentModelView::new(&replay, &empty);
    let rederived = Evaluator::new(&replay.ctx.terms, &view)
        .capture_array_snapshot(args[1])
        .expect("same whole function");
    assert!(original
        .same_function(&rederived, &mut 100_000)
        .expect("exact structural comparison"));
}

#[test]
fn fill_shared_work_refusal_latches_across_retry_and_clone() {
    let exec = prepared_fill(1, 3, 9);
    let model = fill_model(&exec);
    assert!(model.functional_arrays.is_some());
    let copied = model.clone();
    model
        .functional_arrays
        .as_ref()
        .expect("original")
        .work_used
        .store(MAX_FUNCTIONAL_WORK, Ordering::Release);
    assert!(copied
        .functional_array_value(&exec, variable(&exec, "w"))
        .is_err());
    let mut retry = Model::empty();
    exec.install_functional_array_candidate(&mut retry);
    assert!(retry.functional_arrays.is_none());
}

#[test]
fn fill_original_cancellation_after_capture_cannot_reset_into_read_authority() {
    let exec = prepared_fill(1, 3, 9);
    let model = fill_model(&exec);
    exec.record_evaluation_stop(UnknownOrigin::InterruptFlag);
    assert!(model
        .functional_array_value(&exec, variable(&exec, "w"))
        .is_err());
    assert!(!matches!(confirm(&exec, &model), GateVerdict::ConfirmedSat));
}
