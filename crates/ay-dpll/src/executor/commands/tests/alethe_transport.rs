// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::super::Executor;
use ay_core::Sort;
use ay_frontend::parse;

#[test]
fn alethe_problem_declares_internal_free_constants_but_keeps_quantifier_scope() {
    let mut exec = Executor::new();
    let local = exec.ctx.terms.mk_var("__ay_local", Sort::Int);
    let free = exec.ctx.terms.mk_var("__ay_free", Sort::Int);
    let relation = exec.ctx.terms.mk_lt(local, free);
    let quantified = exec
        .ctx
        .terms
        .mk_forall(vec![("__ay_local".to_string(), Sort::Int)], relation);

    let problem = exec
        .alethe_problem_smt2_for(&[quantified], None)
        .expect("typed free constants have a proof transport");
    assert!(
        problem.contains("(declare-const __ay_free Int)"),
        "{problem}"
    );
    assert!(!problem.contains("(declare-const __ay_local"), "{problem}");
    assert!(problem.contains("(forall ((__ay_local Int))"), "{problem}");
    parse(&problem).expect("proof problem has well-formed SMT-LIB syntax");
}

#[test]
fn alethe_problem_reads_let_initializers_outside_the_binder_scope() {
    let mut exec = Executor::new();
    let outer = exec.ctx.terms.mk_var("__ay_local", Sort::Int);
    let free = exec.ctx.terms.mk_var("__ay_free", Sort::Int);
    let relation = exec.ctx.terms.mk_lt(outer, free);
    let scoped = exec
        .ctx
        .terms
        .mk_let(vec![("__ay_local".to_string(), outer)], relation);

    let problem = exec
        .alethe_problem_smt2_for(&[scoped], None)
        .expect("let initializer retains its outer free constant");
    for name in ["__ay_local", "__ay_free"] {
        assert!(
            problem.contains(&format!("(declare-const {name} Int)")),
            "{problem}"
        );
    }
    parse(&problem).expect("proof problem has well-formed SMT-LIB syntax");
}

#[test]
fn proof_transport_does_not_enable_reserved_source_declarations() {
    let mut exec = Executor::new();
    let commands =
        parse("(declare-const __ay_native_replay_var_0 Int)").expect("declaration syntax");
    assert!(exec.execute_all(&commands).is_err());
}
