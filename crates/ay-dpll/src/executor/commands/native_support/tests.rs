// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use ay_frontend::command::Term as Parsed;

fn add_native(exec: &mut Executor, root: TermId) {
    exec.ctx.add_native_assertion_with_parsed(
        root,
        Parsed::Symbol(crate::executor::NATIVE_API_ASSERTION_PLACEHOLDER.to_owned()),
    );
}

fn capture(exec: &mut Executor) -> NativeProofSourceScope {
    exec.begin_public_solve(false);
    exec.bind_unsat_query_assumptions(&[]);
    let permit = exec.detached_authored_plain_hard_permit_for_test().unwrap();
    NativeProofSourceScope::capture(exec, &permit).unwrap()
}

#[test]
fn native_problem_projects_unused_sequence_but_refuses_a_used_sequence() {
    let mut exec = Executor::new();
    exec.execute_all(&ay_frontend::parse("(declare-const unused_sequence (Seq Int))").unwrap())
        .unwrap();
    let x = exec.ctx.terms.mk_var("__ay_native_input", Sort::Int);
    let zero = exec.ctx.terms.mk_int(0.into());
    let selected = exec.ctx.terms.mk_eq(x, zero);
    let a = exec.ctx.terms.mk_var("seq_a", Sort::seq(Sort::Int));
    let b = exec.ctx.terms.mk_var("seq_b", Sort::seq(Sort::Int));
    let sequence_root = exec.ctx.terms.mk_eq(a, b);
    add_native(&mut exec, selected);
    add_native(&mut exec, sequence_root);
    let scope = capture(&mut exec);
    let problem = exec
        .render_external_support_problem(&[selected], &[selected], &scope, None)
        .unwrap();
    assert!(problem.surface().is_supported());
    assert!(problem
        .text()
        .contains("(declare-const __ay_native_input Int)"));
    assert!(!problem.text().contains("Seq"));
    assert!(!problem.text().contains("seq_a"));
    ay_frontend::parse(problem.text()).unwrap();
    assert!(exec
        .render_external_support_problem(&[sequence_root], &[sequence_root], &scope, None)
        .is_none());
    assert!(exec
        .render_external_support_problem(&[selected], &[sequence_root], &scope, None)
        .is_none());
}

#[test]
fn native_problem_preserves_lexical_scope_and_simultaneous_let_rhs() {
    for use_let in [false, true] {
        let mut exec = Executor::new();
        let local = exec.ctx.terms.mk_var("local", Sort::Int);
        let outside = exec.ctx.terms.mk_var("outside", Sort::Int);
        let body = exec.ctx.terms.mk_lt(local, outside);
        let root = if use_let {
            exec.ctx
                .terms
                .mk_let(vec![("local".to_owned(), local)], body)
        } else {
            exec.ctx
                .terms
                .mk_forall(vec![("local".to_owned(), Sort::Int)], body)
        };
        add_native(&mut exec, root);
        let scope = capture(&mut exec);
        let problem = exec
            .render_external_support_problem(&[root], &[root], &scope, None)
            .unwrap();
        assert!(problem.text().contains("(declare-const outside Int)"));
        assert_eq!(
            problem.text().contains("(declare-const local Int)"),
            use_let
        );
        ay_frontend::parse(problem.text()).unwrap();
    }
}

#[test]
fn native_problem_refuses_distinct_free_identities_with_one_spelling() {
    let mut exec = Executor::new();
    let a = exec.ctx.terms.mk_fresh_named_var("same_name", Sort::Bool);
    let b = exec.ctx.terms.mk_fresh_named_var("same_name", Sort::Bool);
    add_native(&mut exec, a);
    add_native(&mut exec, b);
    let scope = capture(&mut exec);
    assert!(exec
        .render_external_support_problem(&[a, b], &[a, b], &scope, None)
        .is_none());
}

#[test]
fn native_problem_rejects_new_free_variables_and_noncanonical_overrides() {
    let mut exec = Executor::new();
    let root = exec.ctx.terms.mk_var("authored", Sort::Bool);
    add_native(&mut exec, root);
    let scope = capture(&mut exec);
    let derived_free = exec.ctx.terms.mk_var("derived", Sort::Bool);
    assert!(exec
        .render_external_support_problem(&[root], &[derived_free], &scope, None)
        .is_none());
    let mut overrides = DetHashMap::default();
    overrides.insert(root, "foreign".to_owned());
    assert!(exec
        .render_external_support_problem(&[root], &[root], &scope, Some(&overrides))
        .is_none());
}

#[test]
fn native_problem_binding_retires_after_source_change_and_term_slot_reuse() {
    let mut exec = Executor::new();
    let root = exec.ctx.terms.mk_var("authored", Sort::Bool);
    add_native(&mut exec, root);
    let scope = capture(&mut exec);
    let checkpoint = exec.ctx.terms.rollback_checkpoint();
    let derived = exec.ctx.terms.mk_var("derived_constant", Sort::Int);
    // A new free variable is deliberately not admitted; a proof-only integer
    // literal is allowed and still has an entry identity that can be retired.
    assert!(exec
        .render_external_support_problem(&[root], &[derived], &scope, None)
        .is_none());
    let constant = exec.ctx.terms.mk_int(12.into());
    let problem = exec
        .render_external_support_problem(&[root], &[constant], &scope, None)
        .unwrap();
    assert!(problem.is_current(&exec));
    exec.ctx.terms.rollback_to(checkpoint);
    let _replacement = exec.ctx.terms.mk_int(13.into());
    assert!(!problem.is_current(&exec));
    exec.execute_all(&ay_frontend::parse("(declare-const later Int)").unwrap())
        .unwrap();
    assert!(!problem.is_current(&exec));
}
