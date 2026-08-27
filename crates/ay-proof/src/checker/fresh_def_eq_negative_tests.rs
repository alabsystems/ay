// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Adversarial negatives for the fresh-definition EQUALITY form.
//!
//! EVERY test here names a concrete falsifying assignment AND CHECKS it, using
//! the parent module's [`super::Evaluator`] — a plain-`i64`/`bool` interpreter
//! that shares no code with the registry. "Checks it" means both halves are
//! asserted by `assert_extension_refutes_a_satisfiable_problem`: the ORIGINAL
//! problem is SATISFIED at the named point, and NO value of the introduced
//! symbols satisfies the extension there, so the "definition" would refute a
//! satisfiable problem.

use ay_core::{AletheRule, Proof, ProofStep, Sort};

use super::super::{fixture, push_bound, reason, FreshDefRegistry};
use super::{assert_extension_refutes_a_satisfiable_problem, push_eq};

#[test]
fn rejects_an_equality_over_a_symbol_the_problem_constrains() {
    // REQUIRED NEGATIVE: `d` occurring in the AUTHORED problem.
    //
    // FALSIFYING ASSIGNMENT. Problem `A = { d = 5 }`, satisfied at `d = 5`.
    // The "definition" `d := 0` makes `A ∪ P` force `5 = d = 0`, UNSAT — so a
    // refutation of `A ∪ P` would publish UNSAT for a SATISFIABLE problem.
    let mut f = fixture();
    let d = f.fresh(1);
    let five = f.int(5);
    let zero = f.int(0);
    let authored = f.terms.mk_eq(d, five);
    let mut proof = Proof::new();
    push_eq(&mut proof, &mut f.terms, d, zero);
    let error = FreshDefRegistry::collect(&proof, &f.terms, Some(&[authored]))
        .expect_err("a symbol the problem constrains is not fresh");
    assert!(reason(&error).contains("NOT fresh"), "{error:?}");

    let extension = f.terms.mk_eq(d, zero);
    assert_extension_refutes_a_satisfiable_problem(
        &f.terms,
        &[authored],
        &[("x", 0), ("y", 0), ("__ay_eqdv!1", 5)],
        &[],
        &["__ay_eqdv!1"],
        &[authored, extension],
        -8..=8,
    );
}

#[test]
fn rejects_an_equality_over_a_symbol_an_assume_constrains() {
    // The same defect reached through the proof rather than the problem: a
    // caller may pass `None`, so the proof's own `assume` leaves must be a
    // freshness source in their own right.
    //
    // FALSIFYING ASSIGNMENT: `A = { d = 5 }` assumed rather than asserted,
    // satisfied at `d = 5`, refuted by `d := 0`.
    let mut f = fixture();
    let d = f.fresh(1);
    let five = f.int(5);
    let zero = f.int(0);
    let assumed = f.terms.mk_eq(d, five);
    let mut proof = Proof::new();
    proof.add_assume(assumed, None);
    push_eq(&mut proof, &mut f.terms, d, zero);
    let error = FreshDefRegistry::collect(&proof, &f.terms, None)
        .expect_err("a symbol an assume constrains is not fresh");
    assert!(reason(&error).contains("NOT fresh"), "{error:?}");

    let extension = f.terms.mk_eq(d, zero);
    assert_extension_refutes_a_satisfiable_problem(
        &f.terms,
        &[assumed],
        &[("x", 0), ("y", 0), ("__ay_eqdv!1", 5)],
        &[],
        &["__ay_eqdv!1"],
        &[assumed, extension],
        -8..=8,
    );
}

#[test]
fn rejects_two_different_equality_definitions_of_the_same_symbol() {
    // REQUIRED NEGATIVE: two definientia for one `d`.
    //
    // FALSIFYING ASSIGNMENT. Problem `A = { 0 <= x }`, satisfied at `x = 0`.
    // `d := x` AND `d := x + 1` force `x = d = x + 1`, so `A ∪ P` is UNSAT for
    // EVERY `x` — the empty clause would follow from nothing the problem said.
    let mut f = fixture();
    let d = f.fresh(1);
    let one = f.int(1);
    let x_plus_one = f.terms.mk_add(vec![f.x, one]);
    let zero = f.int(0);
    let authored = f.terms.mk_le(zero, f.x);
    let mut proof = Proof::new();
    proof.add_assume(authored, None);
    push_eq(&mut proof, &mut f.terms, d, f.x);
    push_eq(&mut proof, &mut f.terms, d, x_plus_one);
    let error = FreshDefRegistry::collect(&proof, &f.terms, Some(&[authored]))
        .expect_err("two definientia for one symbol equate their defining terms");
    assert!(reason(&error).contains("SECOND definiens"), "{error:?}");

    let first = f.terms.mk_eq(d, f.x);
    let second = f.terms.mk_eq(d, x_plus_one);
    assert_extension_refutes_a_satisfiable_problem(
        &f.terms,
        &[authored],
        &[("x", 0), ("y", 0)],
        &[],
        &["__ay_eqdv!1"],
        &[authored, first, second],
        -8..=8,
    );
}

#[test]
fn rejects_a_symbol_defined_by_an_equality_and_bounded_by_a_different_term() {
    // REQUIRED NEGATIVE, and the one that is NEW to this pass: the two rules
    // must share ONE registry. Two separate registries would each see a single
    // definition, find it unique, and accept.
    //
    // FALSIFYING ASSIGNMENT. Problem `A = { 0 <= x }`, satisfied at `x = 0`.
    // `fresh_def_eq` gives `d = x + 1`; `fresh_def_bound` gives `d <= 0`.
    // Together they force `x + 1 <= 0`, i.e. `x <= -1`, which is FALSE at
    // `x = 0` — a genuine constraint on the problem's OWN variable.
    let mut f = fixture();
    let d = f.fresh(1);
    let one = f.int(1);
    let x_plus_one = f.terms.mk_add(vec![f.x, one]);
    let zero = f.int(0);
    let authored = f.terms.mk_le(zero, f.x);
    let mut proof = Proof::new();
    proof.add_assume(authored, None);
    push_eq(&mut proof, &mut f.terms, d, x_plus_one);
    push_bound(&mut proof, &mut f.terms, d, zero, false);
    let error = FreshDefRegistry::collect(&proof, &f.terms, Some(&[authored]))
        .expect_err("an equality and a bound by a DIFFERENT term are two definitions");
    assert!(reason(&error).contains("SECOND definiens"), "{error:?}");

    let eq_atom = f.terms.mk_eq(d, x_plus_one);
    let bound_atom = f.terms.mk_le(d, zero);
    assert_extension_refutes_a_satisfiable_problem(
        &f.terms,
        &[authored],
        &[("x", 0), ("y", 0)],
        &[],
        &["__ay_eqdv!1"],
        &[authored, eq_atom, bound_atom],
        -8..=8,
    );
}

#[test]
fn rejects_an_equality_whose_symbol_occurs_in_its_own_definiens() {
    // REQUIRED NEGATIVE: `d` inside its own definiens.
    //
    // FALSIFYING ASSIGNMENT. Problem `A = { 0 <= x }`, satisfied at `x = 0`.
    // `d := d + 1` is false for EVERY integer `d`, so `A ∪ P` is UNSAT and a
    // refutation of it says nothing about `A`.
    let mut f = fixture();
    let d = f.fresh(1);
    let one = f.int(1);
    let d_plus_one = f.terms.mk_add(vec![d, one]);
    let zero = f.int(0);
    let authored = f.terms.mk_le(zero, f.x);
    let mut proof = Proof::new();
    proof.add_assume(authored, None);
    push_eq(&mut proof, &mut f.terms, d, d_plus_one);
    let error = FreshDefRegistry::collect(&proof, &f.terms, Some(&[authored]))
        .expect_err("a self-referential definition is not a definition");
    assert!(reason(&error).contains("inside a definiens"), "{error:?}");

    let atom = f.terms.mk_eq(d, d_plus_one);
    assert_extension_refutes_a_satisfiable_problem(
        &f.terms,
        &[authored],
        &[("x", 0), ("y", 0)],
        &[],
        &["__ay_eqdv!1"],
        &[authored, atom],
        -8..=8,
    );
}

#[test]
fn rejects_a_two_symbol_equality_cycle() {
    // Checking only DIRECT self-reference misses this. The guard is "no
    // introduced symbol occurs in ANY definiens", strictly stronger than
    // acyclicity and needing no graph algorithm.
    //
    // FALSIFYING ASSIGNMENT. Problem `A = { 0 <= x }`, satisfied at `x = 0`.
    // `d1 := d2 + 1` and `d2 := d1 + 1` force `d1 = d1 + 2`, UNSAT for every
    // `x` and every pair of values.
    let mut f = fixture();
    let d1 = f.fresh(1);
    let d2 = f.fresh(2);
    let one = f.int(1);
    let d2_plus_one = f.terms.mk_add(vec![d2, one]);
    let d1_plus_one = f.terms.mk_add(vec![d1, one]);
    let zero = f.int(0);
    let authored = f.terms.mk_le(zero, f.x);
    let mut proof = Proof::new();
    proof.add_assume(authored, None);
    push_eq(&mut proof, &mut f.terms, d1, d2_plus_one);
    push_eq(&mut proof, &mut f.terms, d2, d1_plus_one);
    let error = FreshDefRegistry::collect(&proof, &f.terms, Some(&[authored]))
        .expect_err("mutually recursive definitions need not admit any assignment");
    assert!(reason(&error).contains("inside a definiens"), "{error:?}");

    let first = f.terms.mk_eq(d1, d2_plus_one);
    let second = f.terms.mk_eq(d2, d1_plus_one);
    assert_extension_refutes_a_satisfiable_problem(
        &f.terms,
        &[authored],
        &[("x", 0), ("y", 0)],
        &[],
        &["__ay_eqdv!1", "__ay_eqdv!2"],
        &[authored, first, second],
        -8..=8,
    );
}

#[test]
fn rejects_an_int_symbol_defined_by_a_real_term() {
    // REQUIRED NEGATIVE: SORT, reached THROUGH the registry rather than only
    // through the shape recognizer, because the registry is what the strict
    // checker builds.
    //
    // FALSIFYING ASSIGNMENT. Problem `A = { r = r }` over a Real `r`
    // (satisfiable, and the point `r = 1/2` satisfies it). An INTEGER `d` with
    // `d = r` forces `r` integral, which `r = 1/2` refutes — a constraint on
    // the problem's own variable. The evaluator's fragment is integral by
    // construction, which is exactly why this negative is checked by SORT
    // rather than by evaluation.
    let mut f = fixture();
    let d = f.fresh(1);
    let r = f.terms.mk_var("r".to_string(), Sort::Real);
    let atom = f
        .terms
        .mk_app(ay_core::Symbol::named("="), vec![d, r], Sort::Bool);
    let mut proof = Proof::new();
    proof.add_step(ProofStep::Step {
        rule: AletheRule::FreshDefEq,
        clause: vec![atom],
        premises: Vec::new(),
        args: vec![d],
    });
    let error = FreshDefRegistry::collect(&proof, &f.terms, Some(&[]))
        .expect_err("`d : Int := r : Real` is not an assignment `d` can take");
    assert!(reason(&error).contains("own sort"), "{error:?}");
}

#[test]
fn rejects_an_equality_with_no_registry_binding() {
    // `validate_eq` must consult the registry rather than re-deciding the
    // shape locally: a step the whole-proof pass never saw has had NONE of the
    // conditions checked.
    let mut f = fixture();
    let d = f.fresh(1);
    let lin = f.diff();
    let atom = f.terms.mk_eq(d, lin);
    let empty = FreshDefRegistry::default();
    let error = empty
        .validate_eq(&f.terms, ay_core::ProofId(0), &[atom], &[], &[d])
        .expect_err("an unbound symbol has had no condition checked");
    assert!(
        reason(&error).contains("no vetted whole-proof binding"),
        "{error:?}"
    );
}

#[test]
fn rejects_an_equality_rebound_to_a_different_definiens() {
    // Belt-and-braces: even with a registry in hand, the per-step check must
    // confirm the DEFINIENS, not just the name.
    let mut f = fixture();
    let d = f.fresh(1);
    let lin = f.diff();
    let zero = f.int(0);
    let mut proof = Proof::new();
    push_eq(&mut proof, &mut f.terms, d, lin);
    let registry = FreshDefRegistry::collect(&proof, &f.terms, Some(&[]))
        .expect("the single equality is fine");
    let other = f.terms.mk_eq(d, zero);
    let error = registry
        .validate_eq(&f.terms, ay_core::ProofId(0), &[other], &[], &[d])
        .expect_err("the recorded definiens is `x - y`, not `0`");
    assert!(reason(&error).contains("different definiens"), "{error:?}");
}

#[test]
fn rejects_a_bound_step_validated_as_an_equality_and_vice_versa() {
    // The registry vets a SYMBOL, but each step is re-recognized by its OWN
    // rule's recognizer. Cross-dispatching must fail, so a producer that
    // mislabels a step cannot have it accepted by the other rule's shape gate.
    let mut f = fixture();
    let d = f.fresh(1);
    let lin = f.diff();
    let mut proof = Proof::new();
    push_eq(&mut proof, &mut f.terms, d, lin);
    push_bound(&mut proof, &mut f.terms, d, lin, false);
    let registry = FreshDefRegistry::collect(&proof, &f.terms, Some(&[])).expect("both are fine");
    let eq_atom = f.terms.mk_eq(d, lin);
    let le_atom = f.terms.mk_le(d, lin);
    assert!(registry
        .validate_bound(&f.terms, ay_core::ProofId(0), &[eq_atom], &[], &[d])
        .is_err());
    assert!(registry
        .validate_eq(&f.terms, ay_core::ProofId(1), &[le_atom], &[], &[d])
        .is_err());
}

#[test]
fn the_dispatcher_refuses_a_rule_that_is_not_a_fresh_definition_rule() {
    // Called DIRECTLY, because `collect_bindings` already filters on the rule
    // and the per-step entry points name their own rule — so the `other` arm is
    // only reachable from here today. It exists so that a future third rule
    // added to either caller's pattern cannot silently inherit a shape gate
    // that was never written for it: the fallback a reviewer would reach for
    // (`_ => recognize_fresh_def_bound(..)`) would read `(cl (= d expr))` with
    // a `<=` recognizer and reject it as malformed, but the SYMMETRIC mistake
    // — routing a `<=` step through the `=` recognizer — would accept
    // `(cl (<= x y))` for an unrelated rule if the `=` head check ever moved.
    let mut f = fixture();
    let d = f.fresh(1);
    let lin = f.diff();
    let atom = f.terms.mk_eq(d, lin);
    let error = crate::checker::fresh_def_dispatch::recognize_fresh_definition(
        &f.terms,
        &AletheRule::Trust,
        &[atom],
        0,
        &[d],
    )
    .expect_err("`trust` is not a fresh-definition rule");
    assert!(error.contains("not a fresh-definition rule"), "{error}");
    // Both real rules are still accepted by the same dispatcher.
    let _ = crate::checker::fresh_def_dispatch::recognize_fresh_definition(
        &f.terms,
        &AletheRule::FreshDefEq,
        &[atom],
        0,
        &[d],
    )
    .expect("`fresh_def_eq` dispatches to its own recognizer");
    let bound = f.terms.mk_le(d, lin);
    let _ = crate::checker::fresh_def_dispatch::recognize_fresh_definition(
        &f.terms,
        &AletheRule::FreshDefBound,
        &[bound],
        0,
        &[d],
    )
    .expect("`fresh_def_bound` dispatches to its own recognizer");
}

#[test]
fn a_non_fresh_definition_rule_is_refused_by_the_dispatcher() {
    // `recognize_fresh_definition` refuses anything that is not one of the two
    // rules rather than defaulting to the bound recognizer, so a future third
    // rule cannot silently inherit a shape gate that was never written for it.
    // Reached through `collect`, which is where a mislabelled step would land.
    let mut f = fixture();
    let d = f.fresh(1);
    let lin = f.diff();
    let atom = f.terms.mk_eq(d, lin);
    let mut proof = Proof::new();
    proof.add_step(ProofStep::Step {
        rule: AletheRule::Trust,
        clause: vec![atom],
        premises: Vec::new(),
        args: vec![d],
    });
    let registry = FreshDefRegistry::collect(&proof, &f.terms, Some(&[]))
        .expect("a `trust` step is not a fresh definition and contributes no binding");
    assert!(
        registry.is_empty(),
        "only the two fresh-definition rules may contribute bindings"
    );
    // And the per-step half refuses the same mislabelling outright.
    let error = registry
        .validate_eq(&f.terms, ay_core::ProofId(0), &[atom], &[], &[d])
        .expect_err("nothing was vetted");
    assert!(
        reason(&error).contains("no vetted whole-proof binding"),
        "{error:?}"
    );
}
