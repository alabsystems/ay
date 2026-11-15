// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn scalar_declaration_classification_uses_original_guard_not_functional_quota() {
    use ay_core::resource::{ChildSpec, Guard, NodeLabel};
    use std::sync::atomic::Ordering;
    let mut exec = Executor::new();
    for index in 0..32 {
        exec.execute_all(
            &ay_frontend::parse(&format!("(declare-const scalar{index} Int)")).unwrap(),
        )
        .unwrap();
    }
    let used = exec.evaluation_attempt().functional_work_counter();
    used.store(
        super::super::super::functional_arrays::MAX_FUNCTIONAL_WORK,
        Ordering::Release,
    );
    let guard = Guard::root_child(ChildSpec::new(NodeLabel::Check).with_rlimit(Some(10_000)));
    let _entered = guard.enter();
    assert_eq!(exec.has_array_function_declarations(), Ok(false));
    let first = guard.ticks();
    assert!(first >= 32);
    for _ in 0..128 {
        assert_eq!(exec.has_array_function_declarations(), Ok(false));
    }
    assert_eq!(
        guard.ticks(),
        first + 128,
        "unchanged negative source must not repeat the declaration census"
    );
    assert_eq!(
        used.load(Ordering::Acquire),
        super::super::super::functional_arrays::MAX_FUNCTIONAL_WORK
    );
    assert_eq!(exec.evaluation_stop_origin(), None);
}

#[test]
fn negative_array_declaration_cache_tracks_registration_pop_and_foreign_context() {
    let mut exec = Executor::new();
    assert_eq!(exec.has_array_function_declarations(), Ok(false));
    exec.execute_all(
        &ay_frontend::parse("(push 1) (declare-fun view (Int) (Array Int Int))").unwrap(),
    )
    .unwrap();
    assert_eq!(exec.has_array_function_declarations(), Ok(true));
    exec.execute_all(&ay_frontend::parse("(pop 1)").unwrap())
        .unwrap();
    assert_eq!(exec.has_array_function_declarations(), Ok(false));
    let mut foreign = Executor::new();
    foreign
        .execute_all(&ay_frontend::parse("(declare-fun other (Int) (Array Int Int))").unwrap())
        .unwrap();
    exec.ctx = foreign.ctx.clone();
    assert_eq!(exec.has_array_function_declarations(), Ok(true));
}

#[test]
fn cached_negative_array_classification_still_obeys_original_cancellation() {
    use ay_core::resource::{ChildSpec, Guard, NodeLabel};
    let exec = Executor::new();
    let guard = Guard::root_child(ChildSpec::new(NodeLabel::Check));
    let _entered = guard.enter();
    assert_eq!(exec.has_array_function_declarations(), Ok(false));
    guard.cancel();
    assert_eq!(
        exec.has_array_function_declarations(),
        Err(crate::executor_types::UnknownOrigin::InterruptFlag)
    );
}

const SOURCE: &str = "
        (set-logic QF_AUFBV)
        (set-option :produce-models true)
        (declare-const x (_ BitVec 4))
        (declare-const y (_ BitVec 4))
        (declare-fun view ((_ BitVec 4)) (Array (_ BitVec 32) (_ BitVec 3)))
        (assert (bvule x y))
        (assert (bvule y x))
        (assert (= (view x)
          (store ((as const (Array (_ BitVec 32) (_ BitVec 3))) #b000)
                 #x00000001 #b111)))
        (assert (= (select (view y) #x00000002) #b000))";

#[test]
fn congruent_array_literal_public_model_and_reads_agree() {
    let mut exec = Executor::new();
    let commands = ay_frontend::parse(&format!(
        "{SOURCE} (check-sat) (get-model)
             (get-value ((select (view x) #x00000001)
                         (select (view y) #x00000001)
                         (select (view y) #x00000002)))
             (get-value ((view x) (view y)))"
    ))
    .unwrap();
    let outputs = exec.execute_all(&commands).unwrap();
    assert_eq!(outputs[0], "sat");
    assert!(outputs[1].contains("define-fun view"), "{outputs:?}");
    assert_eq!(outputs[2].matches("#b111").count(), 2, "{outputs:?}");
    assert_eq!(outputs[2].matches("#b000").count(), 1, "{outputs:?}");
    let arrays = crate::executor::model::datatype_array_fields::sexpr_items(&outputs[3]).unwrap();
    assert_eq!(arrays.len(), 2);
    let left = crate::executor::model::datatype_array_fields::sexpr_items(&arrays[0]).unwrap();
    let right = crate::executor::model::datatype_array_fields::sexpr_items(&arrays[1]).unwrap();
    assert_eq!(
        left[1], right[1],
        "congruent calls must expose the same whole array"
    );
    let commands =
        ay_frontend::parse("(assert (not (= (select (view y) #x00000001) #b111))) (check-sat)")
            .unwrap();
    assert_eq!(exec.execute_all(&commands).unwrap(), ["unsat"]);
}

#[test]
fn congruent_array_literal_does_not_waive_conflicting_reads() {
    let mut exec = Executor::new();
    let commands = ay_frontend::parse(&format!(
        "{SOURCE}
             (assert (= (select (view y) #x00000001) #b000)) (check-sat)"
    ))
    .unwrap();
    assert_eq!(exec.execute_all(&commands).unwrap(), ["unsat"]);
}

#[test]
fn congruent_array_literal_original_stop_precedes_candidate_copy() {
    let mut exec = Executor::new();
    exec.execute_all(&ay_frontend::parse(SOURCE).unwrap())
        .unwrap();
    let mut model = crate::executor::model::tests::empty_model();
    let _stop = ay_core::resource::enter_check_stop(std::sync::Arc::new(|| true));
    exec.complete_congruent_array_literals(&mut model);
    assert!(model.array_model.is_none());
    assert!(exec.evaluation_stop_origin().is_some());
}

#[test]
fn congruent_array_literal_total_table_reads_preserve_nonzero_alias_and_nested_arithmetic() {
    let mut exec = Executor::new();
    let source = "(set-logic QF_AUFBV)
            (declare-const a (Array (_ BitVec 32) (_ BitVec 3)))
            (declare-fun view ((_ BitVec 4)) (Array (_ BitVec 32) (_ BitVec 3)))
            (assert (= (view #x0) a))
            (assert (= (select a #x00000001) #b101)) (check-sat)";
    assert_eq!(
        exec.execute_all(&ay_frontend::parse(source).unwrap())
            .unwrap(),
        ["sat"]
    );
    for query in [
        "(get-value ((= (select (view #x0) #x00000001) #b101)))",
        "(get-value ((= (bvadd #b001 (select (view #x0) #x00000001)) #b110)))",
    ] {
        let output = exec
            .execute_all(&ay_frontend::parse(query).unwrap())
            .unwrap();
        assert_eq!(output.len(), 1);
        assert!(output[0].ends_with(" true))"), "{output:?}");
    }
}

#[test]
fn congruent_array_literal_competing_points_use_the_total_table_not_a_constant() {
    let mut exec = Executor::new();
    let source = "(set-logic QF_AUFBV)
        (declare-fun view ((_ BitVec 4)) (Array (_ BitVec 32) (_ BitVec 3)))
        (assert (= (view #x0) ((as const (Array (_ BitVec 32) (_ BitVec 3))) #b000)))
        (assert (= (view #x1) ((as const (Array (_ BitVec 32) (_ BitVec 3))) #b111)))
        (check-sat)";
    assert_eq!(
        exec.execute_all(&ay_frontend::parse(source).unwrap())
            .unwrap(),
        ["sat"]
    );
    assert!(!exec
        .last_model
        .as_ref()
        .unwrap()
        .has_constant_array_functions());
    for query in [
        "(get-value ((= (select (view #x0) #x00000001) #b000)))",
        "(get-value ((= (select (view #x1) #x00000001) #b111)))",
        "(get-value ((distinct (view #x0) (view #x1))))",
    ] {
        let output = exec
            .execute_all(&ay_frontend::parse(query).unwrap())
            .unwrap();
        assert_eq!(output.len(), 1);
        assert!(output[0].ends_with(" true))"), "{output:?}");
    }
}

#[test]
fn congruent_array_literal_reader_keeps_interpreted_array_selectors() {
    let mut exec = Executor::new();
    let source = "(set-logic ALL)
        (declare-datatype Box ((box (data (Array (_ BitVec 32) (_ BitVec 3))))))
        (declare-fun unused ((_ BitVec 4)) (Array (_ BitVec 32) (_ BitVec 3)))
        (declare-const b Box)
        (assert (= b (box ((as const (Array (_ BitVec 32) (_ BitVec 3))) #b000))))
        (check-sat) (get-value ((select (data b) #x00000001)))";
    let output = exec
        .execute_all(&ay_frontend::parse(source).unwrap())
        .unwrap();
    assert_eq!(output[0], "sat");
    assert!(output[1].contains("#b000"), "{output:?}");
}

#[test]
fn congruent_array_literal_renderer_refuses_before_dense_sparse_bv_output() {
    let mut exec = Executor::new();
    exec.set_term_memory_limit(Some(exec.ctx.terms.true_memory_bytes() + 4096));
    let scope = EvaluationCopyScope::enter(&exec).unwrap();
    let value = ay_model_check::ModelValue::BitVec {
        width: 4096,
        value: 1u8.into(),
    };
    assert!(exec
        .retained_array_render_value(&value, &Sort::bitvec(4096), &scope.read_admission(&exec))
        .is_err());
    assert_eq!(
        exec.evaluation_stop_origin(),
        Some(crate::executor_types::UnknownOrigin::MemoryBudget)
    );
}

#[test]
fn congruent_array_literal_renderer_keeps_integer_real_and_refuses_raw_bad_denominator() {
    let exec = Executor::new();
    let scope = EvaluationCopyScope::enter(&exec).unwrap();
    let owner = scope.read_admission(&exec);
    assert_eq!(
        exec.retained_array_render_value(
            &ay_model_check::ModelValue::Int(0u8.into()),
            &Sort::Real,
            &owner
        )
        .unwrap(),
        "0"
    );
    let invalid = ay_model_check::ModelValue::Real(BigRational::new_raw(1u8.into(), (-1).into()));
    assert!(exec
        .retained_array_render_value(&invalid, &Sort::Real, &owner)
        .is_err());
}
