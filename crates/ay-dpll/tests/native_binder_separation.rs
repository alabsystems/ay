// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Native binder separation — Option C of
//! the development design notes.
//!
//! A native quantifier or lambda that binds a DECLARED CONSTANT binds a fresh
//! twin variable instead, so one `TermId` is never both a binder and a free
//! constant. Before the separation `try_forall(&[x], ..)` over
//! `try_declare_const("x", ..)` made the constant itself the binder: the
//! E-matching ground-term index then classified `f(x)` by `TermId`, its
//! incremental and full-rebuild builders disagreed (the `ematching-differential`
//! canary LI-1/LI-2), and the refutation of an ambient-binder query depended on
//! assertion order. These tests pin the renaming itself (fresh twin, body and
//! triggers renamed, the constant untouched, no capture, idempotent), that
//! models and unsat cores still speak about the constant, and that the
//! refutation no longer depends on the order the assertions arrive in.

#![allow(clippy::panic)]

use std::collections::BTreeSet;

use ay_dpll::api::{Logic, ModelValue, Solver, Sort, Term, TermKind, VerifiedSolveResult};

fn var_name(solver: &Solver, term: Term) -> String {
    match solver.term_kind(term) {
        TermKind::Var { name } => name,
        other => panic!("expected a variable term, got {other:?}"),
    }
}

fn binders(solver: &Solver, quantifier: Term) -> Vec<String> {
    solver
        .quantifier_bound_vars(quantifier)
        .expect("a quantifier")
        .into_iter()
        .map(|(name, _)| name)
        .collect()
}

/// Every variable spelling reachable from `term`, quantifier bodies included.
fn var_names_in(solver: &Solver, term: Term) -> BTreeSet<String> {
    let mut names = BTreeSet::new();
    let mut stack = vec![term];
    while let Some(current) = stack.pop() {
        if let TermKind::Var { name } = solver.term_kind(current) {
            names.insert(name);
        }
        stack.extend(solver.term_children(current));
    }
    names
}

fn body(solver: &Solver, quantifier: Term) -> Term {
    solver.term_children(quantifier)[0]
}

fn uf_int(solver: &mut Solver, name: &str) -> ay_dpll::api::FuncDecl {
    solver
        .try_declare_fun(name, &[Sort::Int], Sort::Int)
        .expect("declare function")
}

#[test]
fn forall_over_a_declared_constant_binds_a_fresh_twin() {
    let mut solver = Solver::new(Logic::All);
    let f = uf_int(&mut solver, "f");
    let x = solver.try_declare_const("x", Sort::Int).expect("declare x");
    let f_x = solver.try_apply(&f, &[x]).expect("apply f");
    let zero = solver.int_const(0);
    let nonneg = solver.try_ge(f_x, zero).expect("ge");
    let quantifier = solver.try_forall(&[x], nonneg).expect("forall");

    let bound = binders(&solver, quantifier);
    assert_eq!(bound.len(), 1, "one binder: {bound:?}");
    let twin = &bound[0];
    assert!(
        twin != "x" && twin.starts_with("x_"),
        "the binder must be a fresh `x_<id>` twin, got {twin}"
    );
    let body_vars = var_names_in(&solver, body(&solver, quantifier));
    assert!(
        body_vars.contains(twin),
        "the body binds the twin: {body_vars:?}"
    );
    assert!(
        !body_vars.contains("x"),
        "the body never mentions the constant: {body_vars:?}"
    );

    // The constant and every term the caller built over it are untouched.
    assert_eq!(var_name(&solver, x), "x");
    assert_eq!(
        var_names_in(&solver, f_x),
        BTreeSet::from(["x".to_string()])
    );
    assert!(
        solver
            .declared_variables()
            .all(|(name, _)| name != twin.as_str()),
        "the twin is a binder, never a declared variable"
    );
}

#[test]
fn every_native_binder_constructor_separates_a_declared_constant() {
    let mut solver = Solver::new(Logic::All);
    let f = uf_int(&mut solver, "f");
    let x = solver.try_declare_const("x", Sort::Int).expect("declare x");
    let f_x = solver.try_apply(&f, &[x]).expect("apply f");
    let zero = solver.int_const(0);
    let positive = solver.try_gt(f_x, zero).expect("gt");
    let trigger = [f_x];

    let exists = solver.try_exists(&[x], positive).expect("exists");
    let forall_t = solver
        .try_forall_with_triggers(&[x], positive, &[&trigger[..]])
        .expect("forall with triggers");
    let exists_t = solver
        .try_exists_with_triggers(&[x], positive, &[&trigger[..]])
        .expect("exists with triggers");
    let ranged = solver
        .try_forall_int_range(x, 0, 1000, positive)
        .expect("forall int range");
    for quantifier in [exists, forall_t, exists_t, ranged] {
        let bound = binders(&solver, quantifier);
        assert!(
            bound[0] != "x",
            "{} kept the constant as binder",
            solver.format_term(quantifier)
        );
        let body_vars = var_names_in(&solver, body(&solver, quantifier));
        assert!(!body_vars.contains("x"), "{body_vars:?}");
    }
    for quantifier in [forall_t, exists_t] {
        let bound = binders(&solver, quantifier);
        let triggers = solver.quantifier_triggers(quantifier).expect("triggers");
        let trigger_vars = var_names_in(&solver, triggers[0][0]);
        assert_eq!(
            trigger_vars,
            BTreeSet::from([bound[0].clone()]),
            "the trigger is renamed with the body"
        );
    }

    let lambda = solver.lambda_array(x, f_x);
    let lambda_binder = solver.term_children(lambda)[0];
    assert_ne!(
        var_name(&solver, lambda_binder),
        "x",
        "the lambda binder is a twin"
    );
    let lambda_body_vars = var_names_in(&solver, solver.term_children(lambda)[1]);
    assert_eq!(
        lambda_body_vars,
        BTreeSet::from([var_name(&solver, lambda_binder)])
    );
}

#[test]
fn a_fresh_binder_is_untouched_and_rebuilding_is_idempotent() {
    let mut solver = Solver::new(Logic::All);
    let f = uf_int(&mut solver, "f");
    let bound = solver.try_fresh_var("bound", Sort::Int).expect("fresh");
    let f_bound = solver.try_apply(&f, &[bound]).expect("apply f");
    let zero = solver.int_const(0);
    let eq = solver.eq(f_bound, zero);
    let fresh_quantifier = solver.try_forall(&[bound], eq).expect("forall");
    assert_eq!(
        binders(&solver, fresh_quantifier),
        vec![var_name(&solver, bound)]
    );

    let x = solver.try_declare_const("x", Sort::Int).expect("declare x");
    let f_x = solver.try_apply(&f, &[x]).expect("apply f");
    let eq_x = solver.eq(f_x, zero);
    let first = solver.try_forall(&[x], eq_x).expect("forall");
    let second = solver.try_forall(&[x], eq_x).expect("forall again");
    assert_eq!(
        first, second,
        "one canonical twin per constant keeps hash-consing"
    );
}

#[test]
fn a_nested_rebinding_keeps_each_binder_scope() {
    let mut solver = Solver::new(Logic::All);
    let p = solver
        .try_declare_fun("p", &[Sort::Int], Sort::Bool)
        .expect("declare p");
    let q = solver
        .try_declare_fun("q", &[Sort::Int], Sort::Bool)
        .expect("declare q");
    let x = solver.try_declare_const("x", Sort::Int).expect("declare x");
    let p_x = solver.try_apply(&p, &[x]).expect("apply p");
    let q_x = solver.try_apply(&q, &[x]).expect("apply q");
    let inner = solver.try_forall(&[x], q_x).expect("inner forall");
    let conjunction = solver.and(p_x, inner);
    let outer = solver.try_forall(&[x], conjunction).expect("outer forall");

    let outer_binder = binders(&solver, outer)[0].clone();
    let inner_binder = binders(&solver, inner)[0].clone();
    assert_ne!(
        outer_binder, inner_binder,
        "each binder owns its own identity"
    );
    let rebuilt_inner = solver
        .term_children(body(&solver, outer))
        .into_iter()
        .find(|&child| solver.quantifier_bound_vars(child).is_some())
        .expect("the inner quantifier survives inside the outer body");
    assert_eq!(
        rebuilt_inner, inner,
        "the inner quantifier mentions no outer binder"
    );
    let outer_body_vars = var_names_in(&solver, body(&solver, outer));
    assert!(outer_body_vars.contains(&outer_binder) && !outer_body_vars.contains("x"));
}

#[test]
fn a_twin_spelling_already_in_the_body_is_never_captured() {
    let mut solver = Solver::new(Logic::All);
    let p = solver
        .try_declare_fun("p", &[Sort::Int], Sort::Bool)
        .expect("declare p");
    let r = solver
        .try_declare_fun("r", &[Sort::Int, Sort::Int], Sort::Bool)
        .expect("declare r");
    let x = solver.try_declare_const("x", Sort::Int).expect("declare x");
    let p_x = solver.try_apply(&p, &[x]).expect("apply p");
    let probe = solver.try_forall(&[x], p_x).expect("probe forall");
    // Recover the canonical twin's handle and bind IT (it is not a declared
    // constant, so it stays as written) around a body mentioning the constant.
    let twin = solver.term_children(body(&solver, probe))[0];
    let r_x_twin = solver.try_apply(&r, &[x, twin]).expect("apply r");
    let inner = solver.try_forall(&[twin], r_x_twin).expect("inner forall");
    assert_eq!(binders(&solver, inner), vec![var_name(&solver, twin)]);

    // Binding `x` around it must not rename `x` to the canonical twin: that
    // spelling is taken by the inner binder, which would capture it.
    let outer = solver.try_forall(&[x], inner).expect("outer forall");
    let outer_binder = binders(&solver, outer)[0].clone();
    assert_ne!(
        outer_binder,
        var_name(&solver, twin),
        "a one-off twin avoids capture"
    );
    assert_ne!(outer_binder, "x");
    let rebuilt_inner = body(&solver, outer);
    let application = body(&solver, rebuilt_inner);
    let args: Vec<String> = solver
        .term_children(application)
        .into_iter()
        .map(|arg| var_name(&solver, arg))
        .collect();
    assert_eq!(args, vec![outer_binder, var_name(&solver, twin)]);
}

fn trait_axiom_query(axiom_first: bool) -> (Solver, VerifiedSolveResult) {
    let mut solver = Solver::new(Logic::All);
    solver.set_produce_unsat_cores(true);
    let carrier = Sort::Uninterpreted("S".to_string());
    let measure = solver
        .try_declare_fun("measure", &[carrier.clone()], Sort::Int)
        .expect("declare measure");
    let receiver = solver
        .try_declare_const("self", carrier)
        .expect("declare self");
    let measure_self = solver.try_apply(&measure, &[receiver]).expect("apply");
    let zero = solver.int_const(0);
    let nonneg = solver.try_ge(measure_self, zero).expect("ge");
    let axiom = solver.try_forall(&[receiver], nonneg).expect("forall");
    let goal = solver.try_lt(measure_self, zero).expect("lt");
    let named = [(axiom, "dn0"), (goal, "dn1")];
    let order: Vec<_> = if axiom_first {
        named.to_vec()
    } else {
        named.iter().rev().copied().collect()
    };
    for (term, name) in order {
        solver.try_assert_named(term, name).expect("assert");
    }
    let result = solver.try_check_sat().expect("check-sat");
    (solver, result)
}

/// The design note's §2: before the separation, production refuted the
/// ambient-binder trait axiom only because the axiom's root was indexed first.
#[test]
fn the_ambient_binder_refutation_holds_in_either_assertion_order() {
    for axiom_first in [true, false] {
        let (solver, result) = trait_axiom_query(axiom_first);
        assert!(
            result.result().is_unsat(),
            "axiom_first={axiom_first}: `∀self. measure(self) ≥ 0` refutes \
             `measure(self) < 0`; got {result:?}"
        );
        result
            .accept_for_consumer()
            .unwrap_or_else(|e| panic!("axiom_first={axiom_first}: {e}"));
        let core: BTreeSet<String> = solver
            .try_get_unsat_core()
            .expect("unsat core")
            .into_iter()
            .collect();
        assert_eq!(
            core,
            BTreeSet::from(["dn0".to_string(), "dn1".to_string()]),
            "the core names the caller's assertions, never a twin"
        );
    }
}

#[test]
fn the_model_speaks_about_the_constant_not_its_twin() {
    let mut solver = Solver::new(Logic::All);
    let bv2 = Sort::bitvec(2);
    let f = solver
        .try_declare_fun("f", &[bv2.clone()], Sort::bitvec(2))
        .expect("declare f");
    let x = solver.try_declare_const("x", bv2).expect("declare x");
    let f_x = solver.try_apply(&f, &[x]).expect("apply f");
    let zero = solver.bv_const(0, 2);
    let one = solver.bv_const(1, 2);
    let f_x_is_zero = solver.eq(f_x, zero);
    let axiom = solver.try_forall(&[x], f_x_is_zero).expect("forall");
    let twin = binders(&solver, axiom)[0].clone();
    solver.try_assert_term(axiom).expect("assert axiom");
    let pin = solver.eq(x, one);
    solver.try_assert_term(pin).expect("assert pin");

    let result = solver.try_check_sat().expect("check-sat");
    assert!(
        result.result().is_sat(),
        "finite-domain axiom plus a pin is sat: {result:?}"
    );
    let model = solver.model_map().expect("model");
    assert!(
        matches!(model.get("x"), Some(ModelValue::BitVec { value, width: 2 }) if *value == 1.into()),
        "the model assigns the constant its pinned value: {model:?}"
    );
    assert!(
        !model.contains_key(&twin),
        "a binder twin never enters the model: {model:?}"
    );
}
