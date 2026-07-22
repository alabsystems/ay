// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Full-solver (check_sat) e-matching against a ground term asserted *inside a
//! push scope*, across domain sorts. This is the pattern deductive-checks uses for
//! postcondition / spec-function axioms:
//!
//!   assert forall x:S. {f(x)} f(x)==true
//!   push; assert f(c)==false; check_sat  -> expect UNSAT; pop
//!
//! Direct `perform_ematching` unit tests exercise the matcher in isolation;
//! these drive the whole solver incrementally, which had no direct coverage.
//!
//! Result: the uninterpreted (Poly) and Int domains work — which is what
//! matters, since deductive-checks encodes every value as the uninterpreted `Poly`
//! sort. A Bool *domain* bound variable with an explicit Bool-sorted trigger
//! and an opaque Bool constant asserted in a push scope was a known gap
//! (finite-domain expansion at {true, false} destroyed the trigger and the
//! opaque const never reached EUF's true/false class), closed by
//! #bool-ground-inst: the expansion also instantiates Bool binders at the
//! assertion set's ground Bool UF-argument terms, an equivalence-preserving
//! augmentation (see `skolemize::finite_domain`).

use ay_dpll::api::{Logic, Solver, Sort};

fn run_pushscope_case(domain: Sort, tag: &str) -> bool {
    let mut s = Solver::new(Logic::All);
    let f = s
        .try_declare_fun(
            &format!("f_{tag}"),
            std::slice::from_ref(&domain),
            Sort::Bool,
        )
        .unwrap();
    let x = s.fresh_var(&format!("__x_{tag}"), domain.clone());
    let f_x = s.try_apply(&f, &[x]).unwrap();
    let truth = s.bool_const(true);
    let eq = s.try_eq(f_x, truth).unwrap();
    let ax = s.try_forall_with_triggers(&[x], eq, &[&[f_x]]).unwrap();
    s.try_assert_term(ax).unwrap();

    let c = s.declare_const(&format!("c_{tag}"), domain);
    let f_c = s.try_apply(&f, &[c]).unwrap();
    let falsity = s.bool_const(false);

    s.try_push().unwrap();
    let claim = s.try_eq(f_c, falsity).unwrap();
    s.try_assert_term(claim).unwrap();
    let r = s.try_check_sat().unwrap();
    s.try_pop().unwrap();
    r.is_unsat()
}

#[test]
fn ematching_pushscope_poly_and_int() {
    let poly = run_pushscope_case(Sort::Uninterpreted("Poly".to_string()), "poly");
    let int = run_pushscope_case(Sort::Int, "int");
    eprintln!("UNSAT? poly={poly} int={int}");
    assert!(
        int,
        "Int domain: f(x)=true trigger must fire on f(c) -> UNSAT"
    );
    assert!(
        poly,
        "Poly (uninterpreted) domain: f(x)=true trigger must fire on f(c) -> UNSAT \
         (this is the deductive-checks postcondition-axiom pattern)"
    );
}

// Seq-sorted domain: the same uninterpreted-style trigger over a parametric
// `(Seq Int)` bound variable. Pins whether e-matching fires for SEQUENCE-sorted
// triggers (a separate question from the Poly case), which the parity program
// doc had previously attributed the symbolic-seq Unknowns to.
#[test]
fn ematching_pushscope_seq_domain() {
    let r = run_pushscope_case(Sort::Seq(Box::new(Sort::Int)), "seq");
    eprintln!("seq-domain UNSAT? {r}");
    assert!(
        r,
        "Seq-domain f(x)=true trigger must fire on f(c) -> UNSAT (e-matching is sort-agnostic)"
    );
}

// Formerly a known gap: the Bool binder is finite-domain-expanded at
// {true, false}, destroying the trigger, and the opaque push-scope const `c`
// never becomes a SAT atom, so EUF never merged it with the true/false class
// and `f(c)` floated free of `f(true)`/`f(false)` (#bool-arg-congruence; the
// eager congruence lemma is single-shot-only). Closed by #bool-ground-inst:
// the expansion now ALSO instantiates Bool binders at the assertion set's
// ground Bool UF-argument terms — equivalence-preserving (c:Bool denotes true
// or false in every model, so `P(c)` is redundant given `P(true) /\ P(false)`)
// — which hands the ground solver `f(c)=true` directly.
#[test]
fn ematching_pushscope_bool_domain_known_gap() {
    let boolean = run_pushscope_case(Sort::Bool, "bool");
    assert!(
        boolean,
        "Bool domain push-scope trigger should fire -> UNSAT"
    );
}

// Triggerless Bool-domain quantifier whose refutation needs only x:={true,false}
// instantiation (no opaque-const congruence): forall x:Bool. f(x); assert !f(true).
// This DOES work today (auto-trigger / instantiation), confirming the gap above
// is specifically the opaque-const congruence case, not Bool domains in general.
#[test]
fn instantiation_triggerless_bool_domain() {
    let mut s = Solver::new(Logic::All);
    let f = s
        .try_declare_fun("f_tb", &[Sort::Bool], Sort::Bool)
        .unwrap();
    let x = s.fresh_var("__x_tb", Sort::Bool);
    let f_x = s.try_apply(&f, &[x]).unwrap();
    let ax = s.try_forall_with_triggers(&[x], f_x, &[]).unwrap();
    s.try_assert_term(ax).unwrap();
    let truth = s.bool_const(true);
    let f_true = s.try_apply(&f, &[truth]).unwrap();
    let not_f_true = s.try_not(f_true).unwrap();
    s.try_assert_term(not_f_true).unwrap();
    assert!(
        s.try_check_sat().unwrap().is_unsat(),
        "forall x:Bool. f(x) with !f(true) must be UNSAT via x:=true"
    );
}
