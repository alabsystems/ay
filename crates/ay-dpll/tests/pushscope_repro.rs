// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! In-crate regression for the push-scope / incremental datatype completeness
//! gap fixed in `executor/theories/bv_incremental.rs`.
//!
//! Mirrors the deductive-checks reproduction
//! (`repro_enum_push_scope_incompleteness.rs`) using the raw native
//! `ay_dpll::api::Solver` with the hybrid datatype lowering (native
//! `declare_datatype` + re-declared ctor/selector/tester funcs + nested-`ite`
//! BV128 payload).
//!
//! Before the fix the incremental BV solve fed the non-BV constructor-congruence
//! pass a PRE-materialization `term_to_bits` snapshot, so a compound BV argument
//! used only as a constructor argument (the inner `ite`) had no bits, the
//! argument-difference encoding fell back to `Unencodable`, and the
//! `Accept(inner)/Accept(actual)` congruence pair was silently skipped — leaving
//! a genuinely-UNSAT obligation Unknown under `(push)` / incremental mode while
//! the base / `check_sat_assuming` solve decided UNSAT. The fix snapshots the
//! bits POST-materialization (mirroring the non-incremental path), adding the
//! missing entailed congruence clauses — sound (refute-only, never admits a
//! model).
//!
//! `repro_pushed` / `repro_all_in_push` / `repro_incremental_base` now decide
//! UNSAT (matching `repro_base` / `repro_assuming`); `repro_pushed_wrong_sat_control`
//! proves the push path still produces a GENUINE SAT model (not vacuous UNSAT)
//! for a satisfiable datatype goal firing the same congruence pair.
#![allow(clippy::panic)]

use ay_dpll::api::{DatatypeConstructor, DatatypeField, DatatypeSort, Logic, Solver, Sort, Term};

fn build_live_terms(s: &mut Solver) -> (Term, Term) {
    let bv128 = Sort::bitvec(128);
    let verdict = Sort::Uninterpreted("Verdict".to_string());

    let dt = DatatypeSort {
        name: "Verdict".to_string(),
        constructors: vec![
            DatatypeConstructor {
                name: "Verdict_Reject".to_string(),
                fields: vec![],
            },
            DatatypeConstructor {
                name: "Verdict_Accept".to_string(),
                fields: vec![DatatypeField {
                    name: "Verdict_Accept_0".to_string(),
                    sort: bv128.clone(),
                }],
            },
        ],
    };
    s.try_declare_datatype(&dt).expect("declare datatype");
    let verdict_accept = s
        .try_declare_fun("Verdict_Accept", &[bv128.clone()], verdict.clone())
        .expect("declare ctor fun");
    let _ = s.try_declare_fun("Verdict_Accept_0", &[verdict.clone()], bv128.clone());
    let _ = s.try_declare_fun("is-Verdict_Accept", &[verdict.clone()], Sort::Bool);
    let _ = s.try_declare_fun("is-Verdict_Reject", &[verdict.clone()], Sort::Bool);
    let verdict_reject = s
        .try_declare_fun("Verdict_Reject", &[], verdict.clone())
        .expect("declare nullary ctor fun");
    let verdict_reject = s
        .try_apply(&verdict_reject, &[])
        .expect("apply nullary ctor fun");

    let claimed = s.declare_const("claimed", bv128.clone());
    let result = s.declare_const("result", verdict.clone());
    let feasible = s.declare_const("feasible", Sort::Bool);
    let actual = s.declare_const("actual", bv128.clone());
    let has_claim = s.declare_const("has_claim", Sort::Bool);

    let guard = {
        let eq = s.try_eq(actual, claimed).unwrap();
        s.try_and(has_claim, eq).unwrap()
    };
    let inner = s.try_ite(guard, claimed, actual).unwrap();
    let accept_inner = s.try_apply(&verdict_accept, &[inner]).unwrap();
    let body = {
        let then_eq = s.try_eq(result, accept_inner).unwrap();
        let else_eq = s.try_eq(result, verdict_reject).unwrap();
        s.try_ite(feasible, then_eq, else_eq).unwrap()
    };
    let accept_actual = s.try_apply(&verdict_accept, &[actual]).unwrap();
    let negated = {
        let eq = s.try_eq(accept_inner, accept_actual).unwrap();
        let neq = s.try_not(eq).unwrap();
        s.try_and(feasible, neq).unwrap()
    };
    (body, negated)
}

#[test]
fn repro_base() {
    let mut s = Solver::new(Logic::All);
    let (body, negated) = build_live_terms(&mut s);
    s.try_assert_term(body).unwrap();
    s.try_assert_term(negated).unwrap();
    let r = s.check_sat();
    eprintln!("BASE = {:?}", r.result());
    assert!(r.result().is_unsat());
}

#[test]
fn repro_pushed() {
    let mut s = Solver::new(Logic::All);
    let (body, negated) = build_live_terms(&mut s);
    s.try_assert_term(body).unwrap();
    s.try_push().unwrap();
    s.try_assert_term(negated).unwrap();
    let r = s.check_sat_with_details();
    eprintln!(
        "PUSHED = {:?} reason = {:?}",
        r.result.result(),
        r.unknown_reason
    );
    assert!(
        r.result.result().is_unsat(),
        "pushed datatype obligation must be UNSAT, got {:?}",
        r.result.result()
    );
    s.try_pop().unwrap();
}

// SOUNDNESS CONTROL: a GENUINELY-SATISFIABLE datatype disequality asserted
// under (push) must still be decided SAT (with a real model), NOT vacuously
// UNSAT. Here `Accept(claimed) != Accept(actual)` is satisfiable (pick
// claimed != actual); a vacuous-UNSAT regression would wrongly refute it.
// Builds a GENUINELY-SATISFIABLE push-scope datatype goal that fires the SAME
// non-BV constructor-congruence pair the fix touches — TWO `Verdict_Accept`
// applications, one over the COMPOUND argument `inner = ite(has_claim ∧
// actual=claimed, claimed, actual)` (whose BV bits the fix now materializes),
// the other over `actual` — yet remains satisfiable:
//   (Reject != Accept(inner)) ∧ (Reject != Accept(actual)) ∧ (actual != claimed)
// Model: actual != claimed ⇒ guard false ⇒ inner = actual; both constructor
// clashes against the nullary `Reject` hold; the fired congruence clause
// `(inner != actual) ∨ Accept(inner)=Accept(actual)` is satisfied by inner =
// actual. A vacuous-UNSAT regression of the fix would wrongly refute this.
fn build_control_goal(s: &mut Solver) -> Term {
    let bv128 = Sort::bitvec(128);
    let verdict = Sort::Uninterpreted("Verdict".to_string());
    let dt = DatatypeSort {
        name: "Verdict".to_string(),
        constructors: vec![
            DatatypeConstructor {
                name: "Verdict_Reject".to_string(),
                fields: vec![],
            },
            DatatypeConstructor {
                name: "Verdict_Accept".to_string(),
                fields: vec![DatatypeField {
                    name: "Verdict_Accept_0".to_string(),
                    sort: bv128.clone(),
                }],
            },
        ],
    };
    s.try_declare_datatype(&dt).expect("declare datatype");
    let verdict_accept = s
        .try_declare_fun("Verdict_Accept", &[bv128.clone()], verdict.clone())
        .expect("declare ctor fun");
    let _ = s.try_declare_fun("Verdict_Accept_0", &[verdict.clone()], bv128.clone());
    let _ = s.try_declare_fun("is-Verdict_Accept", &[verdict.clone()], Sort::Bool);
    let _ = s.try_declare_fun("is-Verdict_Reject", &[verdict.clone()], Sort::Bool);
    let verdict_reject = s
        .try_declare_fun("Verdict_Reject", &[], verdict.clone())
        .expect("declare nullary ctor fun");
    let verdict_reject = s
        .try_apply(&verdict_reject, &[])
        .expect("apply nullary ctor fun");
    let claimed = s.declare_const("claimed", bv128.clone());
    let actual = s.declare_const("actual", bv128.clone());
    let has_claim = s.declare_const("has_claim", Sort::Bool);
    let guard = {
        let eq = s.try_eq(actual, claimed).unwrap();
        s.try_and(has_claim, eq).unwrap()
    };
    let inner = s.try_ite(guard, claimed, actual).unwrap();
    let accept_inner = s.try_apply(&verdict_accept, &[inner]).unwrap();
    let accept_actual = s.try_apply(&verdict_accept, &[actual]).unwrap();
    let clash_inner = {
        let eq = s.try_eq(verdict_reject, accept_inner).unwrap();
        s.try_not(eq).unwrap()
    };
    let clash_actual = {
        let eq = s.try_eq(verdict_reject, accept_actual).unwrap();
        s.try_not(eq).unwrap()
    };
    let neq = {
        let eq = s.try_eq(actual, claimed).unwrap();
        s.try_not(eq).unwrap()
    };
    let p = s.try_and(clash_inner, clash_actual).unwrap();
    s.try_and(p, neq).unwrap()
}

#[test]
fn repro_pushed_wrong_sat_control() {
    // Pushed/incremental path must decide this satisfiable datatype goal SAT
    // (with a genuine, independently-validated model), proving the fix did not
    // turn the push path into a vacuous-UNSAT oracle.
    let mut s = Solver::new(Logic::All);
    let goal = build_control_goal(&mut s);
    s.try_push().unwrap();
    s.try_assert_term(goal).unwrap();
    let r = s.check_sat_with_details();
    eprintln!(
        "WRONG_SAT_CONTROL = {:?} reason = {:?}",
        r.result.result(),
        r.unknown_reason
    );
    s.try_pop().unwrap();
    assert!(
        r.result.result().is_sat(),
        "push-scope control must be SAT (genuine model, NOT vacuous UNSAT), got {:?}",
        r.result.result()
    );
}

// Both assertions inside ONE pushed frame (no base/push boundary split).
#[test]
fn repro_all_in_push() {
    let mut s = Solver::new(Logic::All);
    let (body, negated) = build_live_terms(&mut s);
    s.try_push().unwrap();
    s.try_assert_term(body).unwrap();
    s.try_assert_term(negated).unwrap();
    let r = s.check_sat_with_details();
    eprintln!(
        "ALL_IN_PUSH = {:?} reason = {:?}",
        r.result.result(),
        r.unknown_reason
    );
    assert!(
        r.result.result().is_unsat(),
        "all-in-push datatype obligation must be UNSAT, got {:?}",
        r.result.result()
    );
    s.try_pop().unwrap();
}

// incremental_mode set (via push/pop) but both asserts at BASE scope.
#[test]
fn repro_incremental_base() {
    let mut s = Solver::new(Logic::All);
    let (body, negated) = build_live_terms(&mut s);
    s.try_push().unwrap();
    s.try_pop().unwrap();
    s.try_assert_term(body).unwrap();
    s.try_assert_term(negated).unwrap();
    let r = s.check_sat_with_details();
    eprintln!(
        "INCR_BASE = {:?} reason = {:?}",
        r.result.result(),
        r.unknown_reason
    );
    assert!(
        r.result.result().is_unsat(),
        "incremental base datatype obligation must be UNSAT, got {:?}",
        r.result.result()
    );
}

#[test]
fn repro_assuming() {
    let mut s = Solver::new(Logic::All);
    let (body, negated) = build_live_terms(&mut s);
    s.try_assert_term(body).unwrap();
    s.try_push().unwrap();
    s.try_assert_term(negated).unwrap();
    let pushed = s.check_sat_with_details();
    assert!(
        pushed.result.result().is_unsat(),
        "pushed datatype obligation must be UNSAT before assuming, got {:?}",
        pushed.result.result()
    );
    let fb = s.check_sat_assuming_with_details(&[negated]);
    eprintln!("ASSUMING = {:?}", fb.solve.result.result());
    assert!(
        fb.solve.result.result().is_unsat(),
        "assuming datatype obligation must be UNSAT, got {:?}",
        fb.solve.result.result()
    );
    s.try_pop().unwrap();
}
