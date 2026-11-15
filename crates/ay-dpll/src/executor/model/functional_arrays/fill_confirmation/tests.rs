// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
use super::*;
use ay_core::resource::enter_check_stop;
use ay_core::term::{Symbol, TermData};
use ay_core::time::Instant;
use ay_core::Sort;
use ay_frontend::parse;
use std::time::Duration;

mod nested;
mod resources;

fn source(lo: u64, hi: u64) -> String {
    format!(
        "(set-logic ALL)
      (declare-const dst (Array (_ BitVec 64) (_ BitVec 8)))
      (declare-const out (Array (_ BitVec 64) (_ BitVec 8)))
      (assert (= dst ((as const (Array (_ BitVec 64) (_ BitVec 8))) #x00)))
      (assert (= out (lambda ((k (_ BitVec 64)))
        (ite (and (bvule (_ bv{lo} 64) k) (bvult k (_ bv{hi} 64))) #x09 (select dst k)))))
      (assert (forall ((i (_ BitVec 64))) (= (select out i)
        (ite (and (bvule (_ bv{lo} 64) i) (bvult i (_ bv{hi} 64))) #x09 (select dst i)))))"
    )
}
fn loaded_source(source: &str, end: Instant) -> Executor {
    let mut exec = Executor::new();
    exec.set_term_memory_limit(Some(128 * 1024 * 1024));
    exec.set_deadline(Some(end));
    assert!(exec
        .execute_all(&parse(source).expect("original parse"))
        .expect("elaboration")
        .is_empty());
    exec.begin_external_decision_query(false);
    exec.set_deadline(Some(end));
    let mut model = Model::empty();
    exec.install_functional_array_candidate(&mut model);
    assert!(
        model.functional_arrays.is_some(),
        "actual complete producer"
    );
    exec.last_model = Some(model);
    exec
}
fn loaded(end: Instant) -> Executor {
    loaded_source(&source(1, 3), end)
}
fn root(exec: &Executor) -> TermId {
    let mut pending = exec.ctx.assertions.clone();
    while let Some(term) = pending.pop() {
        if matches!(exec.ctx.terms.get(term), TermData::Forall(..)) {
            return term;
        }
        pending.extend(exec.ctx.terms.children(term));
    }
    panic!("original universal")
}
fn confirm(exec: &Executor, term: TermId) -> bool {
    let model = exec.last_model.as_ref().expect("model");
    exec.confirm_complete_array_fill_model(term, &IndependentModelView::new(exec, model))
}
fn descriptor(exec: &Executor, term: TermId) -> [TermId; 2] {
    let model = exec.last_model.as_ref().expect("model");
    let view = IndependentModelView::new(exec, model);
    let mut admission = PinAdmission::capture(exec, model).expect("same owner");
    grammar::recognize(exec, &view, term, &mut admission)
        .expect("strict original Fill")
        .arrays
}

#[test]
fn original_partial_and_huge_fill_confirm_without_sat_publication_authority() {
    let end = Instant::now() + Duration::from_secs(20);
    let _owner = enter_check_stop(Arc::new(move || Instant::now() >= end));
    for hi in [3, u64::MAX] {
        let exec = loaded_source(&source(1, hi), end);
        let term = root(&exec);
        assert!(exec.complete_array_fill_restoration_candidate(term));
        assert!(confirm(&exec, term));
        assert!(exec.last_result.is_none());
        assert!(exec.last_sat_certificate.is_none());
    }
    assert!(Instant::now() < end);
}

#[test]
fn reversed_fill_requires_the_single_unchosen_destination_capture() {
    let end = Instant::now() + Duration::from_secs(20);
    let _owner = enter_check_stop(Arc::new(move || Instant::now() >= end));
    let mut exec = loaded_source(&source(3, 1), end);
    let term = root(&exec);
    let arrays = descriptor(&exec, term);
    assert!(confirm(&exec, term));
    let data = exec
        .last_model
        .as_mut()
        .expect("model")
        .functional_arrays
        .as_mut()
        .expect("data");
    let p = data
        .entries
        .iter()
        .position(|(id, _)| *id == arrays[1])
        .expect("destination");
    data.entries.remove(p);
    assert!(data.entries.iter().any(|(id, _)| *id == arrays[0]));
    assert!(!confirm(&exec, term));
    assert!(!exec.complete_array_fill_restoration_candidate(term));
    assert!(Instant::now() < end);
}

#[test]
fn complete_capture_arming_does_not_confirm_a_wrong_whole_model() {
    let end = Instant::now() + Duration::from_secs(20);
    let _owner = enter_check_stop(Arc::new(move || Instant::now() >= end));
    let mut exec = loaded(end);
    let term = root(&exec);
    let arrays = descriptor(&exec, term);
    assert!(confirm(&exec, term));
    let wrong = ay_model_check::ArraySnapshot::finite(
        ay_model_check::ArrayValue {
            default: ay_model_check::ModelValue::bitvec(8.into(), 8),
            store: Vec::new(),
        },
        &Sort::array(Sort::bitvec(64), Sort::bitvec(8)),
        &mut 1_000_000,
    )
    .expect("wrong complete MODEL data");
    let data = exec
        .last_model
        .as_mut()
        .expect("model")
        .functional_arrays
        .as_mut()
        .expect("data");
    data.entries
        .iter_mut()
        .find(|(id, _)| *id == arrays[0])
        .expect("target")
        .1 = wrong;
    assert!(
        exec.complete_array_fill_restoration_candidate(term),
        "arming is eligibility only"
    );
    assert!(
        !confirm(&exec, term),
        "mismatch never means Confirmed or Refuted"
    );
    assert!(Instant::now() < end);
}

#[test]
fn normalized_bool_fill_requires_actual_complete_constant_models() {
    let end = Instant::now() + Duration::from_secs(20);
    let _owner = enter_check_stop(Arc::new(move || Instant::now() >= end));
    for value in ["true", "false"] {
        let source = format!(
            "(set-logic ALL)
          (declare-const dst (Array (_ BitVec 64) Bool))
          (declare-const out (Array (_ BitVec 64) Bool))
          (assert (= dst ((as const (Array (_ BitVec 64) Bool)) {value})))
          (assert (= out ((as const (Array (_ BitVec 64) Bool)) {value})))
          (assert (forall ((i (_ BitVec 64))) (= (select out i)
            (ite (and (bvule (_ bv1 64) i) (bvult i (_ bv3 64))) {value} (select dst i)))))"
        );
        let mut exec = loaded_source(&source, end);
        let term = root(&exec);
        assert!(descriptor(&exec, term)[0] != descriptor(&exec, term)[1]);
        assert!(confirm(&exec, term));
        exec.last_model
            .as_mut()
            .expect("model")
            .functional_arrays
            .as_mut()
            .expect("data")
            .entries
            .clear();
        assert!(
            !confirm(&exec, term),
            "syntax alone cannot invent Bool interpretations"
        );
    }
    assert!(Instant::now() < end);
}

#[test]
fn de_morgan_negated_guard_is_the_only_extra_false_fill_shape() {
    let end = Instant::now() + Duration::from_secs(20);
    let _owner = enter_check_stop(Arc::new(move || Instant::now() >= end));
    let shape = |cell: &str, rhs: &str| {
        format!(
            "(set-logic ALL)
          (declare-const dst (Array (_ BitVec 64) Bool))
          (declare-const out (Array (_ BitVec 64) Bool))
          (assert (= dst ((as const (Array (_ BitVec 64) Bool)) {cell})))
          (assert (= out ((as const (Array (_ BitVec 64) Bool)) {cell})))
          (assert (forall ((i (_ BitVec 64))) (= (select out i) {rhs})))"
        )
    };
    // The elaborator's own form of (ite c false (select dst i)).
    let exact = "(and (select dst i) (or (not (bvule (_ bv1 64) i)) (not (bvult i (_ bv3 64)))))";
    let exec = loaded_source(&shape("false", exact), end);
    assert!(confirm(&exec, root(&exec)));
    // Semantic twin: over all-true arrays the same matrix is false at i = 1.
    // It must be recognized as exactly the false fill of [1, 3), and the
    // actual model must then refuse it (a wrong value or an empty range
    // would confirm here).
    let exec = loaded_source(&shape("true", exact), end);
    let term = root(&exec);
    {
        let model = exec.last_model.as_ref().expect("model");
        let view = IndependentModelView::new(&exec, model);
        let mut admission = PinAdmission::capture(&exec, model).expect("same owner");
        let fill = grammar::recognize(&exec, &view, term, &mut admission).expect("De Morgan Fill");
        assert_eq!((fill.lo, fill.hi), (1, 3));
        assert!(matches!(fill.value, ay_core::term::Constant::Bool(false)));
    }
    assert!(!confirm(&exec, term));
    // A guard left unnegated, a third disjunct, swapped guard roles.
    for rhs in [
        "(and (select dst i) (or (not (bvule (_ bv1 64) i)) (bvult i (_ bv3 64))))",
        "(and (select dst i) (or (not (bvule (_ bv1 64) i)) (not (bvult i (_ bv3 64)))
            (= i (_ bv7 64))))",
        "(and (select dst i) (or (not (bvule i (_ bv1 64))) (not (bvult (_ bv3 64) i))))",
    ] {
        let exec = loaded_source(&shape("false", rhs), end);
        let term = root(&exec);
        let model = exec.last_model.as_ref().expect("model");
        let view = IndependentModelView::new(&exec, model);
        let mut admission = PinAdmission::capture(&exec, model).expect("same owner");
        assert!(grammar::recognize(&exec, &view, term, &mut admission).is_none());
        drop((admission, view));
        assert!(!confirm(&exec, term), "{rhs}");
    }
    assert!(Instant::now() < end);
}

#[test]
fn triggers_foreign_view_projection_and_stale_source_refuse_separately() {
    let end = Instant::now() + Duration::from_secs(20);
    let _owner = enter_check_stop(Arc::new(move || Instant::now() >= end));
    let mut exec = loaded(end);
    let term = root(&exec);
    let other = loaded(end);
    let view = IndependentModelView::new(&other, other.last_model.as_ref().expect("foreign"));
    assert!(!exec.confirm_complete_array_fill_model(term, &view));
    crate::executor::model::with_scoped_term_evaluation_override_for_test(
        term,
        crate::executor::model::EvalValue::Bool(false),
        || {
            assert!(!confirm(&exec, term));
            assert!(!exec.complete_array_fill_restoration_candidate(term));
        },
    );
    assert!(confirm(&exec, term), "lexical override scope has restored");
    let mut fields = ay_core::kani_compat::DetHashMap::default();
    fields.insert(term, crate::executor::model::EvalValue::Bool(true));
    crate::executor::model::dt_model::with_dt_field_overrides_for_test(fields, || {
        assert!(!confirm(&exec, term));
        assert!(!exec.complete_array_fill_restoration_candidate(term));
    });
    assert!(confirm(&exec, term), "field override scope has restored");
    let TermData::Forall(vars, body, _) = exec.ctx.terms.get(term).clone() else {
        panic!("forall");
    };
    let triggered = exec
        .ctx
        .terms
        .mk_forall_with_triggers(vars, body, vec![vec![body]]);
    assert!(!confirm(&exec, triggered));
    exec.last_model.as_mut().expect("model").projection_ufs =
        crate::executor::model::projection_uf::ProjectionUfModel::from_test_definitions([(
            Symbol::named("projection"),
            vec![Sort::Bool],
            Sort::Bool,
            0,
        )])
        .expect("projection");
    assert!(!confirm(&exec, term));
    exec.last_model.as_mut().expect("model").projection_ufs = Default::default();
    assert!(confirm(&exec, term), "remove earlier fault");
    // An assertion invalidates the selected model, as SMT-LIB requires.
    let stale = exec.last_model.take().expect("model");
    exec.execute_all(&parse("(assert false)").expect("change"))
        .expect("elaboration");
    assert!(exec.last_model.is_none());
    // Reinstall the pre-change model as if that invalidation were missing:
    // only its source/query snapshot (`validate_functional_array_source`)
    // can refuse it now.
    exec.last_model = Some(stale);
    assert!(!confirm(&exec, term));
    assert!(!exec.complete_array_fill_restoration_candidate(term));
    assert!(Instant::now() < end);
}
