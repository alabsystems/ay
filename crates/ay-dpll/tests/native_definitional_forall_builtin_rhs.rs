// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Native-API definitional-forall adoption: theory-builtin right-hand sides and
//! pre-definition raw applications.
//!
//! The shape is deductive-checks's free SPEC FUNCTION with LITERAL arguments:
//!
//! ```text
//! (declare-fun add ((_ BitVec 32) (_ BitVec 32)) (_ BitVec 32))
//! (assert (= r (add #x00000002 #x00000005)))                     ; built FIRST
//! (assert (forall ((a …) (b …)) (= (add a b) (bvadd a b))))      ; definition
//! (assert (not (= r #x00000008)))                                ; violated goal
//! ```
//!
//! This must REFUTE with a witness naming `r = 7`. It used to answer
//! `unknown (incomplete)` because `try_adopt_native_definitional_forall`
//! declined twice over:
//!
//!  1. `exact_head` classified a side as an f-application purely structurally,
//!     so the theory-builtin RHS `(bvadd a b)` — the binders applied exactly, in
//!     order — matched too, both sides looked like heads, and the
//!     "exactly ONE side" disambiguation refused an unambiguous definition;
//!  2. the pre-definition raw `(add #x2 #x5)` term tripped the arena guard.
//!
//! The quantifier therefore survived to the fail-closed quantified-model gate,
//! which found no interpretation for `add`, DEFERRED, and downgraded SAT to
//! Unknown. The gate was right — a model naming no interpretation is not
//! evidence — so both producers were fixed instead: head candidacy is now
//! restricted to user-declared functions, and pre-definition raw applications
//! are PINNED to their own definitional instances rather than refused.
//!
//! Every test here carries its wrong-fact twin: a fix that only flips the
//! headline probe while the negation also "succeeds" is a wrong verdict.

#![allow(clippy::panic)]

use ay_dpll::api::{Logic, Solver, Sort, Term};

/// `r = add(2, 5)` with the definition asserted AFTER the call term is built.
/// `goal_value` is compared against `r`; the assertion is `not (r == goal_value)`.
fn literal_argument_call(
    build_call_first: bool,
    reversed_rhs: bool,
    goal_value: u64,
) -> (Solver, ay_dpll::api::VerifiedSolveResult) {
    let mut solver = Solver::new(Logic::All);
    let bv32 = Sort::bitvec(32);
    let add = solver
        .try_declare_fun("add", &[bv32.clone(), bv32.clone()], bv32.clone())
        .expect("declare add");

    let two = solver.bv_const_u64(2, 32);
    let five = solver.bv_const_u64(5, 32);

    // The ORDER under test: deductive-checks lowers the default body (and so builds and
    // asserts `add(2, 5)`) before the spec function's defining axiom reaches the
    // solver.
    let prebuilt = build_call_first.then(|| {
        let call = solver.try_apply(&add, &[two, five]).expect("apply add");
        let r = solver.try_declare_const("r", bv32.clone()).expect("r");
        let body = solver.eq(r, call);
        solver.try_assert_term(body).expect("assert body");
    });

    let a = solver.try_fresh_var("a", bv32.clone()).expect("a");
    let b = solver.try_fresh_var("b", bv32.clone()).expect("b");
    let head = solver.try_apply(&add, &[a, b]).expect("apply head");
    let rhs = if reversed_rhs {
        solver.bvadd(b, a)
    } else {
        solver.bvadd(a, b)
    };
    let definition_body = solver.eq(head, rhs);
    let definition = solver
        .try_forall_with_triggers(&[a, b], definition_body, &[&[head][..]])
        .expect("forall");
    solver
        .try_assert_term(definition)
        .expect("assert definition");

    if prebuilt.is_none() {
        let call = solver.try_apply(&add, &[two, five]).expect("apply add");
        let r = solver.try_declare_const("r", bv32.clone()).expect("r");
        let body = solver.eq(r, call);
        solver.try_assert_term(body).expect("assert body");
    }

    let r = solver.try_declare_const("r", bv32).expect("r");
    let goal = solver.bv_const_u64(goal_value, 32);
    let equality = solver.eq(r, goal);
    let negated = solver.not(equality);
    solver.try_assert_term(negated).expect("assert goal");

    let result = solver.try_check_sat().expect("check-sat");
    (solver, result)
}

fn model_of(solver: &Solver) -> String {
    solver.try_get_model_str().expect("model after sat")
}

/// THE REGRESSION. Call term built first, builtin RHS in binder order: refute
/// `r == 8` with a witness that ACTUALLY falsifies it — `r = 7`, the value
/// `add(2, 5)` really has. Merely answering Sat is not enough; a model naming no
/// value for `r`, or naming 8, would refute nothing.
#[test]
fn prebuilt_literal_call_refutes_wrong_value_with_a_falsifying_witness() {
    let (solver, result) = literal_argument_call(true, false, 8);
    assert!(
        result.result().is_sat(),
        "the violated goal must REFUTE, not degrade to unknown; got {result:?}"
    );
    let model = model_of(&solver);
    assert!(
        model.contains("(define-fun r () (_ BitVec 32) #x00000007)"),
        "the witness must pin r to 7 — the value add(2, 5) has under the \
         definition — which is what falsifies `r == 8`; model:\n{model}"
    );
    assert!(
        model.contains("(define-fun add") && model.contains("bvadd"),
        "the published interpretation of `add` must be the definition's own \
         right-hand side, read from the assertion and total over BV32 x BV32; \
         model:\n{model}"
    );
}

/// WRONG-FACT TWIN. The same query with the TRUE value: `r == 7` holds, so its
/// negation is UNSAT. If the pinned pre-definition application had been dropped
/// (leaving `add` an unconstrained UF) this would answer Sat with a fabricated
/// witness — the failure mode the arena guard originally refused to risk.
#[test]
fn prebuilt_literal_call_true_value_twin_is_unsat() {
    let (_solver, result) = literal_argument_call(true, false, 7);
    assert!(
        result.result().is_unsat(),
        "add(2, 5) == 7 is entailed by the definition even though the call term \
         predated it; the pin must still constrain it. got {result:?}"
    );
}

/// The pre-existing-application path must not be the only one that works: the
/// definition-first order refutes identically.
#[test]
fn definition_first_literal_call_refutes_with_a_falsifying_witness() {
    let (solver, result) = literal_argument_call(false, false, 8);
    assert!(
        result.result().is_sat(),
        "expected a refutation; got {result:?}"
    );
    let model = model_of(&solver);
    assert!(
        model.contains("(define-fun r () (_ BitVec 32) #x00000007)"),
        "model:\n{model}"
    );
}

#[test]
fn definition_first_literal_call_true_value_twin_is_unsat() {
    let (_solver, result) = literal_argument_call(false, false, 7);
    assert!(result.result().is_unsat(), "got {result:?}");
}

/// CONTROL. A right-hand side that is NOT the binders in order was always
/// adopted (only one side could match), and it still is — the head-candidacy
/// narrowing removed no adoption.
#[test]
fn reversed_builtin_rhs_still_refutes() {
    let (solver, result) = literal_argument_call(true, true, 8);
    assert!(result.result().is_sat(), "got {result:?}");
    let model = model_of(&solver);
    assert!(
        model.contains("(define-fun r () (_ BitVec 32) #x00000007)"),
        "model:\n{model}"
    );
}

/// NARROWNESS PIN for the head-candidacy narrowing. Two USER-DECLARED heads —
/// `forall a b. f(a, b) = g(a, b)` — are genuinely ambiguous about which symbol
/// is being defined, and adoption must keep REFUSING. Observable directly: an
/// adopted symbol is expanded by `try_apply`, so the application's head would
/// change from `f` to `g`.
#[test]
fn two_user_declared_heads_stay_ambiguous_and_are_not_adopted() {
    let mut solver = Solver::new(Logic::All);
    let bv32 = Sort::bitvec(32);
    let f = solver
        .try_declare_fun("f", &[bv32.clone(), bv32.clone()], bv32.clone())
        .expect("declare f");
    let g = solver
        .try_declare_fun("g", &[bv32.clone(), bv32.clone()], bv32.clone())
        .expect("declare g");

    let a = solver.try_fresh_var("a", bv32.clone()).expect("a");
    let b = solver.try_fresh_var("b", bv32.clone()).expect("b");
    let lhs = solver.try_apply(&f, &[a, b]).expect("f app");
    let rhs = solver.try_apply(&g, &[a, b]).expect("g app");
    let body = solver.eq(lhs, rhs);
    let definition = solver.try_forall(&[a, b], body).expect("forall");
    solver.try_assert_term(definition).expect("assert");

    let two = solver.bv_const_u64(2, 32);
    let five = solver.bv_const_u64(5, 32);
    let call = solver.try_apply(&f, &[two, five]).expect("apply f");
    let rendered = solver.assertions_sexpr(&[call]);
    assert!(
        rendered.contains("(f "),
        "`f(a, b) = g(a, b)` names no unique definiendum, so `f` must stay \
         uninterpreted — an adopted `f` would have expanded this call to `g`. \
         rendered: {rendered}"
    );
    let _ = g;
}

/// NARROWNESS PIN for the pinning path. A pre-definition raw application whose
/// argument is a VARIABLE cannot be pinned: the enclosing quantifier's other
/// instances are applications at points no ground pin covers. Adoption must keep
/// REFUSING, leaving the `forall` asserted (so the query is merely incomplete,
/// never wrongly decided).
#[test]
fn prebuilt_call_on_a_variable_argument_refuses_adoption() {
    let mut solver = Solver::new(Logic::All);
    let bv32 = Sort::bitvec(32);
    let sq = solver
        .try_declare_fun("sq", &[bv32.clone()], bv32.clone())
        .expect("declare sq");

    // A raw `sq(x)` over a declared constant, built BEFORE the definition.
    let x = solver.try_declare_const("x", bv32.clone()).expect("x");
    let call = solver.try_apply(&sq, &[x]).expect("apply sq");
    let r = solver.try_declare_const("r", bv32.clone()).expect("r");
    let body = solver.eq(r, call);
    solver.try_assert_term(body).expect("assert body");

    let v = solver.try_fresh_var("v", bv32.clone()).expect("v");
    let head = solver.try_apply(&sq, &[v]).expect("head");
    let rhs = solver.bvmul(v, v);
    let definition_body = solver.eq(head, rhs);
    let definition = solver.try_forall(&[v], definition_body).expect("forall");
    let before = solver.assertions().len();
    solver
        .try_assert_term(definition)
        .expect("assert definition");

    let rendered = solver.assertions_sexpr(&solver.assertions());
    assert_eq!(
        solver.assertions().len(),
        before + 1,
        "the definition must still be an assertion: {rendered}"
    );
    assert!(
        rendered.contains("forall"),
        "a raw application over a VARIABLE argument cannot be pinned, so the \
         quantifier must survive un-adopted rather than be discharged against \
         an incomplete pin set. rendered: {rendered}"
    );
}

/// The `sq` definition is arity-1, so its builtin RHS `(bvmul v v)` never had
/// the binder count of the head and was always adoptable — this control proves
/// the previous test's refusal comes from the VARIABLE argument, not from some
/// unrelated property of the fixture.
#[test]
fn same_definition_without_a_prebuilt_call_is_adopted() {
    let mut solver = Solver::new(Logic::All);
    let bv32 = Sort::bitvec(32);
    let sq = solver
        .try_declare_fun("sq", &[bv32.clone()], bv32.clone())
        .expect("declare sq");

    let v = solver.try_fresh_var("v", bv32.clone()).expect("v");
    let head = solver.try_apply(&sq, &[v]).expect("head");
    let rhs = solver.bvmul(v, v);
    let definition_body = solver.eq(head, rhs);
    let definition = solver.try_forall(&[v], definition_body).expect("forall");
    solver
        .try_assert_term(definition)
        .expect("assert definition");

    let rendered = solver.assertions_sexpr(&solver.assertions());
    assert!(
        !rendered.contains("forall"),
        "with no pre-definition application the definition is adopted and the \
         assertion is discharged to the tautology. rendered: {rendered}"
    );
    let _ = Term::from(head);
}
