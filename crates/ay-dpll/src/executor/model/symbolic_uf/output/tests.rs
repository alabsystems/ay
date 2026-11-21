// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::super::super::independent_gate::IndependentModelView;
use super::super::SymbolicAdmission;
use crate::executor::{model::Model, Executor};
use ay_model_check::ModelView;

fn source_term(executor: &mut Executor, text: &str) -> ay_core::TermId {
    let commands = ay_frontend::parse(&format!("(get-value ({text}))")).unwrap();
    let ay_frontend::Command::GetValue(terms) = &commands[0] else {
        panic!("source term")
    };
    executor.ctx.elaborate_surface_subterm(&terms[0].1).unwrap()
}

fn installed() -> (Executor, Model, SymbolicAdmission) {
    let mut executor = Executor::new();
    executor.execute_all(&ay_frontend::parse("(set-logic AUFLIA)(set-option :produce-models true)(declare-fun weather (Int) Bool)").unwrap()).unwrap();
    let root = source_term(&mut executor, "(forall ((x Int)) (= (weather x) (< x 5)))");
    executor.ctx.add_native_assertion_with_parsed(
        root,
        ay_frontend::Term::Symbol("__ay_api_assertion__".to_owned()),
    );
    executor.independent_gate_authored_assertions = Some(vec![root]);
    let (model, owner) = executor.prepare_symbolic_output_fixture(&[root]);
    (executor, model, owner)
}

#[test]
fn symbolic_uf_fixed_view_pays_source_scan_once_but_each_use_keeps_original_owner() {
    let (mut executor, model, owner) = installed();
    let term = source_term(&mut executor, "(weather 4)");
    let package = &model.certified_total_ufs.symbolic;
    let full_scan = package.lookup_work();
    let head = package.head_lookup_work("weather".len()).unwrap();
    let view = IndependentModelView::new(&executor, &model);
    let before = owner.remaining().0;
    assert!(view.symbolic_function(term).unwrap().is_some());
    let first = owner.remaining().0;
    assert_eq!(before - first, full_scan + head);
    assert!(view.symbolic_function(term).unwrap().is_some());
    let second = owner.remaining().0;
    assert_eq!(
        first - second,
        head,
        "borrowed immutable source is not re-scanned"
    );
    let other_view = IndependentModelView::new(&executor, &model);
    assert!(other_view.symbolic_function(term).unwrap().is_some());
    let third = owner.remaining().0;
    assert_eq!(
        second - third,
        full_scan + head,
        "currency receipt never crosses view lifetime"
    );
    assert!(owner.pay(third, 0));
    let error = match view.symbolic_function(term) {
        Err(error) => error,
        Ok(_) => panic!("refused owner/source must not return a function"),
    };
    assert!(error.contains("Work"), "{error}");
}

#[test]
fn symbolic_uf_fixed_view_cannot_keep_currency_after_source_mutation() {
    let (mut executor, model, owner) = installed();
    let term = source_term(&mut executor, "(weather 4)");
    {
        let view = IndependentModelView::new(&executor, &model);
        assert!(view.symbolic_function(term).unwrap().is_some());
    }
    executor
        .execute_all(&ay_frontend::parse("(push 1)(pop 1)").unwrap())
        .unwrap();
    let view = IndependentModelView::new(&executor, &model);
    let error = match view.symbolic_function(term) {
        Err(error) => error,
        Ok(_) => panic!("refused owner/source must not return a function"),
    };
    assert!(error.contains("Source"), "{error}");
    assert!(!owner.pay(0, 0));
}

#[test]
fn symbolic_uf_retained_output_preserves_quoted_head_and_exact_array_signature() {
    let mut executor = Executor::new();
    executor.execute_all(&ay_frontend::parse("(set-logic ALL)(set-option :produce-models true)(declare-fun |wind speed| ((Array Int Bool) Int) Bool)").unwrap()).unwrap();
    let root = source_term(
        &mut executor,
        "(forall ((a (Array Int Bool)) (i Int)) (= (|wind speed| a i) (select a i)))",
    );
    executor.ctx.add_native_assertion_with_parsed(
        root,
        ay_frontend::Term::Symbol("__ay_api_assertion__".to_owned()),
    );
    executor.independent_gate_authored_assertions = Some(vec![root]);
    let (model, owner) = executor.prepare_symbolic_output_fixture(&[root]);
    executor.last_result = Some(crate::executor_types::SolveResult::Sat);
    executor.last_model = Some(model);
    let before = owner.remaining();
    let output = executor.model();
    assert!(output.contains("(define-fun |wind speed|"), "{output}");
    assert!(output.contains("(Array Int Bool)"), "{output}");
    assert!(!output.contains("(error"), "{output}");
    let after = owner.remaining();
    assert!(after.0 < before.0 && after.1 < before.1);
}
