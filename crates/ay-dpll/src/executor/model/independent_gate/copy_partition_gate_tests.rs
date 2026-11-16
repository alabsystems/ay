// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use ay_core::resource::enter_check_stop;
use ay_core::time::Instant;
use ay_frontend::parse;
use std::sync::Arc;
use std::time::Duration;

const COPY: &str = include_str!("complete_array_restoration/tests/copy.smt2");

fn loaded(end: Instant, sibling: &str) -> Executor {
    let source = format!(
        "{}\n{sibling}",
        COPY.strip_suffix("(check-sat)\n")
            .expect("original assertions")
    );
    let mut exec = Executor::new();
    exec.set_term_memory_limit(Some(128 * 1024 * 1024));
    exec.set_deadline(Some(end));
    assert_eq!(
        exec.execute_all(&parse(&source).expect("all original roots"))
            .expect("elaboration"),
        [] as [String; 0]
    );
    exec.begin_external_decision_query(false);
    exec.set_deadline(Some(end));
    let mut model = Model::empty();
    exec.install_functional_array_candidate(&mut model);
    assert!(model.functional_arrays.is_some());
    exec.last_model = Some(model);
    exec
}

fn original_copy(exec: &Executor) -> TermId {
    let model = exec.last_model.as_ref().expect("selected model");
    let view = IndependentModelView::new(exec, model);
    let mut pending = exec.ctx.assertions.clone();
    while let Some(term) = pending.pop() {
        if matches!(exec.ctx.terms.get(term), TermData::Forall(..))
            && exec.confirm_complete_array_copy_model(term, &view)
        {
            return term;
        }
        pending.extend(exec.ctx.terms.children(term));
    }
    panic!("eligible original copy")
}

#[test]
fn original_copy_flows_through_actual_all_quantified_conjunct_gate_without_a_token() {
    let end = Instant::now() + Duration::from_secs(20);
    let _owner = enter_check_stop(Arc::new(move || Instant::now() >= end));
    let mut exec = loaded(end, "");
    let copy = original_copy(&exec);
    assert!(matches!(
        exec.check_quantified_conjunct_against_model(copy),
        QuantifiedModelCheck::Confirmed
    ));
    assert!(exec.quantified_model_gate_confirms_current_assertions());
    assert!(exec.last_result.is_none());
    assert!(exec.last_sat_certificate.is_none());
    assert!(Instant::now() < end);
}

#[test]
fn confirmed_copy_cannot_filter_a_false_original_quantified_sibling() {
    let end = Instant::now() + Duration::from_secs(20);
    let _owner = enter_check_stop(Arc::new(move || Instant::now() >= end));
    let mut exec = loaded(
        end,
        "(assert (forall ((j (_ BitVec 64))) (= (select ay_qcex_2 j) #x08)))",
    );
    let copy = original_copy(&exec);
    assert!(matches!(
        exec.check_quantified_conjunct_against_model(copy),
        QuantifiedModelCheck::Confirmed
    ));
    assert!(
        !exec.quantified_model_gate_confirms_current_assertions(),
        "ALL authored siblings still require confirmation"
    );
    assert!(exec.last_sat_certificate.is_none());
    assert!(Instant::now() < end);
}
