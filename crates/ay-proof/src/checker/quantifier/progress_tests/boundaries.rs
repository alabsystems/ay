// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn missing_root_and_descendant_handles_return_errors_without_indexing() {
    let fixture = Fixture::new(1);
    for bad in [TermId(fixture.terms.len() as u32), TermId(u32::MAX)] {
        let error = validate_forall_inst_with_progress(
            &fixture.terms,
            ProofId(0),
            &[bad],
            0,
            &[fixture.witness],
            &mut |_, _| true,
        )
        .expect_err("bad root");
        assert!(matches!(error, ProofCheckError::InvalidBooleanRule { .. }));
        assert!(validate_sko_forall_with_progress(
            &fixture.terms,
            ProofId(0),
            &[bad],
            0,
            &[fixture.witness],
            &mut |_, _| true
        )
        .is_err());
        for source_node in [fixture.body, fixture.instance] {
            let mut changed = Fixture::new(1);
            let mut entries = changed.terms.entries_snapshot();
            let TermData::App(_, arguments) = &mut entries[source_node.index()].0 else {
                panic!("fixture application");
            };
            arguments[0] = bad;
            changed.replace_entries(entries);
            for rule in [Rule::ForallInst, Rule::Skolem] {
                assert!(matches!(
                    changed.validate(rule, &mut |_, _| true),
                    Err(ProofCheckError::InvalidBooleanRule { .. })
                ));
            }
        }
    }
}

#[test]
fn sort_depth_is_checked_before_recursive_binder_equality() {
    let mut fixture = Fixture::new(1);
    let mut entries = fixture.terms.entries_snapshot();
    let mut deep = Sort::Int;
    for _ in 0..257 {
        deep = Sort::Seq(Box::new(deep));
    }
    let TermData::Forall(bindings, _, _) = &mut entries[fixture.quantified.index()].0 else {
        panic!("fixture forall");
    };
    bindings[0].1 = deep;
    fixture.replace_entries(entries);
    for rule in [Rule::ForallInst, Rule::Skolem] {
        assert_resource(fixture.validate(rule, &mut |_, _| true));
    }
}

#[test]
fn malformed_handle_diagnostic_is_itself_budgeted() {
    let fixture = Fixture::new(1);
    assert_resource(validate_forall_inst_with_progress(
        &fixture.terms,
        ProofId(0),
        &[TermId(u32::MAX)],
        0,
        &[fixture.witness],
        &mut |_, bytes| bytes == 0,
    ));
    assert_resource(validate_sko_forall_with_progress(
        &fixture.terms,
        ProofId(0),
        &[TermId(u32::MAX)],
        0,
        &[fixture.witness],
        &mut |_, bytes| bytes == 0,
    ));
}

#[test]
fn registered_witness_freshness_and_choice_guards_remain_load_bearing() {
    let mut fixture = Fixture::new(1);
    let mut entries = fixture.terms.entries_snapshot();
    let TermData::App(_, args) = &mut entries[fixture.body.index()].0 else {
        panic!("fixture source");
    };
    args[0] = fixture.witness;
    fixture.replace_entries(entries);
    let error = fixture
        .validate(Rule::Skolem, &mut |_, _| true)
        .expect_err("witness is not fresh");
    assert!(error.to_string().contains("fresh witness occurs"));

    let mut fixture = Fixture::new(1);
    let exists = fixture
        .terms
        .mk_exists(vec![("meter_x".to_string(), Sort::Int)], fixture.body);
    fixture.equality =
        fixture
            .terms
            .mk_app(Symbol::named("="), [exists, fixture.instance], Sort::Bool);
    assert!(
        fixture.validate(Rule::Skolem, &mut |_, _| true).is_err(),
        "marking alone does not grant a choice definition"
    );
    fixture.terms.register_skolem_choice(
        fixture.witness,
        ay_core::SkolemChoice {
            binder: "meter_x".to_string(),
            sort: Sort::Int,
            body: fixture.body,
        },
    );
    fixture
        .validate(Rule::Skolem, &mut |_, _| true)
        .expect("matching registered choice");
    fixture.terms.register_skolem_choice(
        fixture.witness,
        ay_core::SkolemChoice {
            binder: "wrong_binder".to_string(),
            sort: Sort::Int,
            body: fixture.body,
        },
    );
    assert!(fixture.validate(Rule::Skolem, &mut |_, _| true).is_err());
}

#[test]
fn simultaneous_substitution_and_nested_capture_rejections_are_unchanged() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let z = terms.mk_var("z", Sort::Int);
    let body = terms.mk_app(Symbol::named("p"), [x, y], Sort::Bool);
    let quantified = terms.mk_forall(
        vec![("x".to_string(), Sort::Int), ("y".to_string(), Sort::Int)],
        body,
    );
    let not_quantified = terms.mk_not_raw(quantified);
    let simultaneous = terms.mk_app(Symbol::named("p"), [y, z], Sort::Bool);
    let correct = terms.mk_app(
        Symbol::named("or"),
        [not_quantified, simultaneous],
        Sort::Bool,
    );
    validate_forall_inst_with_progress(&terms, ProofId(0), &[correct], 0, &[y, z], &mut |_, _| {
        true
    })
    .expect("simultaneous substitution");
    let sequential = terms.mk_app(Symbol::named("p"), [z, z], Sort::Bool);
    let wrong = terms.mk_app(
        Symbol::named("or"),
        [not_quantified, sequential],
        Sort::Bool,
    );
    assert!(validate_forall_inst_with_progress(
        &terms,
        ProofId(0),
        &[wrong],
        0,
        &[y, z],
        &mut |_, _| true
    )
    .is_err());

    let nested = terms.mk_forall(vec![("y".to_string(), Sort::Int)], body);
    let outer = terms.mk_forall(vec![("x".to_string(), Sort::Int)], nested);
    let not_outer = terms.mk_not_raw(outer);
    let captured_body = terms.mk_app(Symbol::named("p"), [y, y], Sort::Bool);
    let captured = terms.mk_forall(vec![("y".to_string(), Sort::Int)], captured_body);
    let implication = terms.mk_app(Symbol::named("or"), [not_outer, captured], Sort::Bool);
    assert!(validate_forall_inst_with_progress(
        &terms,
        ProofId(0),
        &[implication],
        0,
        &[y],
        &mut |_, _| true
    )
    .is_err());
}
