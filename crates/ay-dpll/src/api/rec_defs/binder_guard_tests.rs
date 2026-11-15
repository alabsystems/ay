// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The capture guards of recursive-definition expansion.
//!
//! Each guard refuses a quantifier that binds a spelling some constant or
//! definition also owns. The native constructors can no longer build that shape:
//! a declared-constant binder is separated to a fresh twin
//! (`api/terms/binder_separation.rs`). The Z3-compatible C API still builds it —
//! its constructors keep binder identity — and `Z3_add_rec_def` expands through
//! these guards, so each guard stays pinned on the identity-binding shape, and
//! each native twin pins that separation makes the same definition expand
//! capture-free.

#![allow(clippy::panic, clippy::unwrap_used, clippy::expect_used)]

use super::super::{Logic, Solver, Term};
use super::*;

const ROUNDS: usize = 1000;
const BUDGET: usize = 5_000_000;

fn solver() -> Solver {
    Solver::new(Logic::All)
}

fn int(s: &mut Solver, v: i64) -> Term {
    s.int_const(v)
}

/// `(forall|exists ((name Int)) body)` binding `name` BY IDENTITY, the shape
/// the Z3-compatible constructors keep.
fn identity_quantifier(s: &mut Solver, forall: bool, name: &str, body: Term) -> Term {
    let (vars, body) = (vec![(name.to_string(), Sort::Int)], body.id());
    let terms = s.terms_mut();
    let id = if forall {
        terms.mk_forall(vars, body)
    } else {
        terms.mk_exists(vars, body)
    };
    s.wrap_term(id)
}

fn defs_of(name: &str, def: RecFunDef) -> HashMap<String, RecFunDef> {
    HashMap::from([(name.to_string(), def)])
}

#[test]
fn argument_captured_by_body_binder_fails_closed() {
    // def f(x) := forall ((y Int)) (y <= x); goal f(y) with the global y:
    // substitution would capture the actual argument. Must fail closed.
    let mut s = solver();
    let f = s.declare_fun("f", &[Sort::Int], Sort::Bool);
    let x = s.declare_const("x", Sort::Int);
    let y = s.declare_const("y", Sort::Int);
    let le = s.try_le(y, x).unwrap();
    let body = identity_quantifier(&mut s, true, "y", le);
    let def = s.make_rec_fun_def(&[x], body);
    assert!(def.is_expandable(), "binder shadows no PARAM name");
    let defs = defs_of("f", def);

    let call = s.try_apply(&f, &[y]).unwrap();
    let err = s
        .try_expand_rec_defs(&[call], &defs, ROUNDS, BUDGET, None)
        .expect_err("argument capture must fail closed");
    assert!(matches!(err, RecExpandError::UnsupportedShape(_)));

    // A NON-colliding argument still expands.
    let z = s.declare_const("z", Sort::Int);
    let call_z = s.try_apply(&f, &[z]).unwrap();
    let out = s
        .try_expand_rec_defs(&[call_z], &defs, ROUNDS, BUDGET, None)
        .expect("non-capturing argument must expand");
    let le_z = s.try_le(y, z).unwrap();
    let expected = identity_quantifier(&mut s, true, "y", le_z);
    assert_eq!(out, vec![expected]);
}

#[test]
fn natively_built_body_binder_expands_the_colliding_argument_capture_free() {
    // The same definition built natively: the body binds y's twin, so the
    // global y passed as the argument stays free in the expansion.
    let mut s = solver();
    let f = s.declare_fun("f", &[Sort::Int], Sort::Bool);
    let x = s.declare_const("x", Sort::Int);
    let y = s.declare_const("y", Sort::Int);
    let le = s.try_le(y, x).unwrap();
    let body = s.try_forall(&[y], le).unwrap();
    let def = s.make_rec_fun_def(&[x], body);
    let defs = defs_of("f", def);

    let call = s.try_apply(&f, &[y]).unwrap();
    let out = s
        .try_expand_rec_defs(&[call], &defs, ROUNDS, BUDGET, None)
        .expect("a separated binder cannot capture the argument");
    // Expected: the definition body with x := y, i.e. `forall twin. twin <= y`
    // over the SAME twin the definition body binds.
    let twin = s.wrap_term(s.binder_twins.twins[&y.id()].0);
    let twin_le_y = s.try_le(twin, y).unwrap();
    let expected = s.try_forall(&[twin], twin_le_y).unwrap();
    assert_eq!(out, vec![expected]);
}

#[test]
fn goal_binder_rebinding_zero_ary_def_name_fails_closed() {
    // def c := 5; goal (exists ((c Int)) (= c 7)) — the bound c is the
    // SAME interned Var, so expansion would wrongly rewrite it to 5.
    let mut s = solver();
    let five = int(&mut s, 5);
    let defs = defs_of("c", s.make_rec_fun_def(&[], five));

    let c = s.declare_const("c", Sort::Int);
    let seven = int(&mut s, 7);
    let eq = s.try_eq(c, seven).unwrap();
    let goal = identity_quantifier(&mut s, false, "c", eq);
    let err = s
        .try_expand_rec_defs(&[goal], &defs, ROUNDS, BUDGET, None)
        .expect_err("goal binder rebinding a def name must fail closed");
    assert!(matches!(err, RecExpandError::UnsupportedShape(_)));

    // Built natively the goal binds c's twin: nothing in it names the
    // definition, so it is left exactly as written, never rewritten to 5.
    let native_goal = s.try_exists(&[c], eq).unwrap();
    let out = s
        .try_expand_rec_defs(&[native_goal], &defs, ROUNDS, BUDGET, None)
        .expect("a separated binder does not rebind the definition");
    assert_eq!(out, vec![native_goal]);
}

#[test]
fn body_binder_shadowing_param_is_not_expandable() {
    // def f(x) := forall ((x Int)) ... — the body binder shadows the
    // parameter; registration marks it non-expandable, and every use
    // fails closed.
    let mut s = solver();
    let f = s.declare_fun("f", &[Sort::Int], Sort::Bool);
    let x = s.declare_const("x", Sort::Int);
    let zero = int(&mut s, 0);
    let ge = s.try_ge(x, zero).unwrap();
    let body = identity_quantifier(&mut s, true, "x", ge);
    let def = s.make_rec_fun_def(&[x], body);
    assert!(!def.is_expandable());
    let defs = defs_of("f", def);

    let three = int(&mut s, 3);
    let call = s.try_apply(&f, &[three]).unwrap();
    let err = s
        .try_expand_rec_defs(&[call], &defs, ROUNDS, BUDGET, None)
        .expect_err("use of a non-expandable def must fail closed");
    assert!(matches!(err, RecExpandError::UnsupportedShape(_)));

    // Built natively the body binds x's twin, which shadows no parameter: the
    // definition is expandable and its closed body is the expansion.
    let native_body = s.try_forall(&[x], ge).unwrap();
    let native_def = s.make_rec_fun_def(&[x], native_body);
    assert!(native_def.is_expandable());
    let out = s
        .try_expand_rec_defs(&[call], &defs_of("f", native_def), ROUNDS, BUDGET, None)
        .expect("a separated binder shadows no parameter");
    assert_eq!(out, vec![native_body]);
}
