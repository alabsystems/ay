// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use ay_core::resource::enter_check_stop;
use ay_core::time::Instant;
use ay_frontend::parse;
use std::sync::Arc;
use std::time::Duration;

fn loaded(end: Instant, sibling: &str) -> Executor {
    let source = format!(
        "(set-logic ALL)
      (declare-const dst (Array (_ BitVec 64) (_ BitVec 8)))
      (declare-const out (Array (_ BitVec 64) (_ BitVec 8)))
      (assert (= dst ((as const (Array (_ BitVec 64) (_ BitVec 8))) #x00)))
      (assert (= out (lambda ((k (_ BitVec 64)))
        (ite (and (bvule (_ bv1 64) k) (bvult k (_ bv3 64))) #x09 (select dst k)))))
      (assert (forall ((i (_ BitVec 64))) (= (select out i)
        (ite (and (bvule (_ bv1 64) i) (bvult i (_ bv3 64))) #x09 (select dst i)))))
      {sibling}"
    );
    let mut exec = Executor::new();
    exec.set_term_memory_limit(Some(128 * 1024 * 1024));
    exec.set_deadline(Some(end));
    assert!(exec
        .execute_all(&parse(&source).expect("original roots"))
        .expect("elaboration")
        .is_empty());
    exec.begin_external_decision_query(false);
    exec.set_deadline(Some(end));
    let mut model = Model::empty();
    exec.install_functional_array_candidate(&mut model);
    assert!(model.functional_arrays.is_some());
    exec.last_model = Some(model);
    exec
}
fn original(exec: &Executor) -> TermId {
    let model = exec.last_model.as_ref().expect("model");
    let view = IndependentModelView::new(exec, model);
    let mut pending = exec.ctx.assertions.clone();
    while let Some(term) = pending.pop() {
        if matches!(exec.ctx.terms.get(term), TermData::Forall(..))
            && exec.confirm_complete_array_fill_model(term, &view)
        {
            return term;
        }
        pending.extend(exec.ctx.terms.children(term));
    }
    panic!("original complete Fill")
}

#[test]
fn original_fill_uses_actual_all_leaf_gate_without_minting_a_sat_token() {
    let end = Instant::now() + Duration::from_secs(20);
    let _owner = enter_check_stop(Arc::new(move || Instant::now() >= end));
    let mut exec = loaded(end, "");
    let fill = original(&exec);
    assert!(!exec.quantified_gate_restoration_candidate(fill));
    assert!(!exec.complete_array_restoration_candidate(fill));
    assert!(exec.complete_array_fill_restoration_candidate(fill));
    assert!(matches!(
        exec.check_quantified_conjunct_against_model(fill),
        QuantifiedModelCheck::Confirmed
    ));
    assert!(exec.quantified_model_gate_confirms_current_assertions());
    assert!(exec.last_result.is_none());
    assert!(exec.last_sat_certificate.is_none());
    assert!(Instant::now() < end);
}

#[test]
fn confirmed_fill_never_filters_a_false_original_quantified_sibling() {
    let end = Instant::now() + Duration::from_secs(20);
    let _owner = enter_check_stop(Arc::new(move || Instant::now() >= end));
    let mut exec = loaded(
        end,
        "(assert (forall ((j (_ BitVec 64))) (= (select out j) #x08)))",
    );
    let fill = original(&exec);
    assert!(matches!(
        exec.check_quantified_conjunct_against_model(fill),
        QuantifiedModelCheck::Confirmed
    ));
    assert!(!exec.quantified_model_gate_confirms_current_assertions());
    assert!(exec.last_sat_certificate.is_none());
    assert!(Instant::now() < end);
}
