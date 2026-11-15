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

const COPY: &str =
    include_str!("../../independent_gate/complete_array_restoration/tests/copy.smt2");

fn loaded(end: Instant) -> Executor {
    loaded_source(
        COPY.strip_suffix("(check-sat)\n")
            .expect("unaltered assertions"),
        end,
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

#[test]
fn empty_copy_still_requires_the_single_unchosen_source_capture() {
    let end = Instant::now() + Duration::from_secs(20);
    let _owner = enter_check_stop(Arc::new(move || Instant::now() >= end));
    let source = "(set-logic ALL)
      (declare-const dst (Array (_ BitVec 64) (_ BitVec 8)))
      (declare-const src (Array (_ BitVec 64) (_ BitVec 8)))
      (declare-const out (Array (_ BitVec 64) (_ BitVec 8)))
      (assert (= dst ((as const (Array (_ BitVec 64) (_ BitVec 8))) #x00)))
      (assert (= src ((as const (Array (_ BitVec 64) (_ BitVec 8))) #x09)))
      (assert (= out (lambda ((k (_ BitVec 64)))
        (ite (and (bvule (_ bv3 64) k) (bvult k (_ bv1 64)))
          (select src (bvsub k (_ bv3 64))) (select dst k)))))
      (assert (forall ((i (_ BitVec 64))) (= (select out i)
        (ite (and (bvule (_ bv3 64) i) (bvult i (_ bv1 64)))
          (select src (bvsub i (_ bv3 64))) (select dst i)))))";
    let mut exec = loaded_source(source, end);
    let term = root(&exec);
    let view = IndependentModelView::new(&exec, exec.last_model.as_ref().expect("model"));
    let mut admission =
        PinAdmission::capture(&exec, exec.last_model.as_ref().expect("model")).expect("owner");
    let copy =
        grammar::recognize(&exec, &view, term, &mut admission).expect("both original arms remain");
    assert!(copy.lo >= copy.hi);
    assert!(copy.arrays[2] != copy.arrays[0] && copy.arrays[2] != copy.arrays[1]);
    drop((admission, view));
    assert!(
        confirm(&exec, term),
        "actual empty whole-copy model is eligible"
    );
    let data = exec
        .last_model
        .as_mut()
        .expect("model")
        .functional_arrays
        .as_mut()
        .expect("data");
    let position = data
        .entries
        .iter()
        .position(|(id, _)| *id == copy.arrays[2])
        .expect("single source");
    data.entries.remove(position);
    assert!(data.entries.iter().any(|(id, _)| *id == copy.arrays[0]));
    assert!(data.entries.iter().any(|(id, _)| *id == copy.arrays[1]));
    assert!(!confirm(&exec, term), "unchosen source cannot disappear");
    assert!(Instant::now() < end);
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
    let model = exec.last_model.as_ref().expect("selected model");
    exec.confirm_complete_array_copy_model(term, &IndependentModelView::new(exec, model))
}

#[test]
fn original_normalized_copy_confirms_actual_model_without_minting_sat_authority() {
    let end = Instant::now() + Duration::from_secs(20);
    let _owner = enter_check_stop(Arc::new(move || Instant::now() >= end));
    let exec = loaded(end);
    let before = exec
        .last_model
        .as_ref()
        .expect("model")
        .functional_work_left();
    assert!(confirm(&exec, root(&exec)));
    assert!(
        exec.last_model
            .as_ref()
            .expect("model")
            .functional_work_left()
            < before
    );
    assert!(exec.last_result.is_none());
    assert!(exec.last_sat_certificate.is_none());
    assert!(Instant::now() < end);
}

#[test]
fn missing_hidden_capture_and_wrong_whole_default_cannot_confirm() {
    let end = Instant::now() + Duration::from_secs(20);
    let _owner = enter_check_stop(Arc::new(move || Instant::now() >= end));
    let mut exec = loaded(end);
    let term = root(&exec);
    let model = exec.last_model.as_mut().expect("model");
    let data = model.functional_arrays.as_mut().expect("complete data");
    let removed = data.entries.pop().expect("real complete entry");
    // Every free array used by the original roots has an entry; make ALL
    // captures unavailable rather than assuming which sorted entry was used.
    let old = std::mem::take(&mut data.entries);
    assert!(!confirm(&exec, term));
    let data = exec
        .last_model
        .as_mut()
        .expect("model")
        .functional_arrays
        .as_mut()
        .expect("data");
    data.entries = old;
    data.entries.push(removed);
    assert!(
        confirm(&exec, term),
        "restored source is independently eligible"
    );
    let data = exec
        .last_model
        .as_mut()
        .expect("model")
        .functional_arrays
        .as_mut()
        .expect("data");
    let wrong = ay_model_check::ArraySnapshot::finite(
        ay_model_check::ArrayValue {
            default: ay_model_check::ModelValue::bitvec(42.into(), 8),
            store: Vec::new(),
        },
        &Sort::array(Sort::bitvec(64), Sort::bitvec(8)),
        &mut 1_000_000,
    )
    .expect("complete wrong data");
    for (_, value) in &mut data.entries {
        *value = wrong.clone();
    }
    // All equal constants actually satisfy a copy relation, so use a wrong
    // target only, selected by the exact recognized original grammar.
    let view = IndependentModelView::new(&exec, exec.last_model.as_ref().expect("model"));
    let mut admission =
        PinAdmission::capture(&exec, exec.last_model.as_ref().expect("model")).expect("owner");
    let copy = grammar::recognize(&exec, &view, term, &mut admission).expect("original shape");
    drop((admission, view));
    let data = exec
        .last_model
        .as_mut()
        .expect("model")
        .functional_arrays
        .as_mut()
        .expect("data");
    let target = data
        .entries
        .iter_mut()
        .find(|(id, _)| *id == copy.arrays[0])
        .expect("target");
    target.1 = ay_model_check::ArraySnapshot::finite(
        ay_model_check::ArrayValue {
            default: ay_model_check::ModelValue::bitvec(41.into(), 8),
            store: Vec::new(),
        },
        &Sort::array(Sort::bitvec(64), Sort::bitvec(8)),
        &mut 1_000_000,
    )
    .expect("wrong target");
    assert!(!confirm(&exec, term));
    assert!(Instant::now() < end);
}

#[test]
fn triggered_alternating_and_scalar_fill_roots_stay_outside_the_copy_slice() {
    let end = Instant::now() + Duration::from_secs(20);
    let _owner = enter_check_stop(Arc::new(move || Instant::now() >= end));
    let mut exec = loaded(end);
    let term = root(&exec);
    let TermData::Forall(vars, body, _) = exec.ctx.terms.get(term).clone() else {
        panic!("forall");
    };
    let triggered = exec
        .ctx
        .terms
        .mk_forall_with_triggers(vars.clone(), body, vec![vec![body]]);
    let exists = exec.ctx.terms.mk_exists(vars.clone(), body);
    let TermData::Ite(condition, positive, negative) = exec.ctx.terms.get(body).clone() else {
        panic!("normalized matrix");
    };
    let TermData::App(_, eq) = exec.ctx.terms.get(positive).clone() else {
        panic!("equality");
    };
    let TermData::App(_, frame) = exec.ctx.terms.get(negative).clone() else {
        panic!("frame equality");
    };
    let target = eq
        .iter()
        .copied()
        .find(|term| frame.contains(term))
        .expect("shared target");
    let nine = exec.ctx.terms.mk_bitvec(9.into(), 8);
    let literal = exec.ctx.terms.mk_eq(target, nine);
    let fill_body = exec.ctx.terms.mk_ite(condition, literal, negative);
    let fill = exec.ctx.terms.mk_forall(vars, fill_body);
    for other in [triggered, exists, fill] {
        assert!(!confirm(&exec, other));
    }
    assert!(Instant::now() < end);
}

#[test]
fn indexed_operator_projection_foreign_view_and_stale_source_never_confirm() {
    let end = Instant::now() + Duration::from_secs(20);
    let _owner = enter_check_stop(Arc::new(move || Instant::now() >= end));
    let mut exec = loaded(end);
    let term = root(&exec);
    let other = loaded(end);
    let view = IndependentModelView::new(&other, other.last_model.as_ref().expect("foreign model"));
    assert!(!exec.confirm_complete_array_copy_model(term, &view));
    let TermData::Forall(vars, body, _) = exec.ctx.terms.get(term).clone() else {
        panic!("forall");
    };
    let TermData::Ite(c, p, n) = exec.ctx.terms.get(body).clone() else {
        panic!("Bool ITE");
    };
    let malformed = exec
        .ctx
        .terms
        .mk_app(Symbol::indexed("ite", vec![7]), [c, p, n], Sort::Bool);
    let malformed = exec.ctx.terms.mk_forall(vars, malformed);
    assert!(!confirm(&exec, malformed));
    exec.last_model.as_mut().expect("model").projection_ufs =
        crate::executor::model::projection_uf::ProjectionUfModel::from_test_definitions([(
            Symbol::named("projected"),
            vec![Sort::Bool],
            Sort::Bool,
            0,
        )])
        .expect("explicit projection fault");
    assert!(!confirm(&exec, term));
    exec.last_model.as_mut().expect("model").projection_ufs =
        crate::executor::model::projection_uf::ProjectionUfModel::default();
    assert!(
        confirm(&exec, term),
        "projection fault is removed before stale-source leg"
    );
    // An assertion invalidates the selected model, as SMT-LIB requires.
    let stale = exec.last_model.take().expect("selected model");
    exec.execute_all(&parse("(assert false)").expect("source change"))
        .expect("elaborate");
    assert!(exec.last_model.is_none());
    // Reinstall the pre-change model as if that invalidation were missing:
    // only its source/query snapshot (`validate_functional_array_source`)
    // can refuse it now.
    exec.last_model = Some(stale);
    assert!(!confirm(&exec, term));
    assert!(Instant::now() < end);
}
