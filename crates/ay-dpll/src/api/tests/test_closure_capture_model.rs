// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! #closure-capture-uninterp-range: a UFLIA problem with a native datatype
//! (closure environment) whose selector RANGE is an uninterpreted sort (the
//! verification-consumer `&mut` carrier) must emit a VALID `sat`, not fail-close to
//! `unknown` on the independent model-check gate.
//!
//! Mirrors the verification-consumer closures/09_fnonce_resolve outer obligation: the
//! closure env `f` is a single-constructor datatype whose capture fields are
//! `&mut` carriers (uninterpreted sort `__verification_consumer_mutref::int`), with
//! asserted capture projections `bx == closure_capture_1(f)` and the
//! constructor identity `f == mk_closure_env(c, bx, by)`.
//!
//! ROOT CAUSE — the sort name `__verification_consumer_mutref::int` needs PIPE-QUOTING
//! (`quote_symbol`: `::` is outside the simple-symbol alphabet), so the model
//! printer renders the abstract element as `(as |@__verification_consumer_mutref::int!0|
//! |__verification_consumer_mutref::int|)`. `strip_abstract_atom_ascription` only
//! recognized the UNQUOTED spelling `(as @S!n S)`, so the quoted form escaped
//! canonicalization: the independent gate's datatype-field parse kept the
//! whole `(as …)` rendering as the element token while the plain leaf carried
//! the bare `@…!0`, the string comparison saw two "different" values for the
//! SAME element, and the gate falsely refuted the asserted capture projection
//! — fail-closing a genuine `sat` to `unknown` (a completeness loss; the
//! fail-close itself was sound). FIX: unquote the pipe-quoted token in
//! `strip_abstract_atom_ascription` (executor_format).

use crate::api::*;

fn mr_sort() -> Sort {
    Sort::Uninterpreted("__verification_consumer_mutref::int".to_string())
}

fn closure_env_dt() -> DatatypeSort {
    DatatypeSort {
        name: "ClosureEnv_test".to_string(),
        constructors: vec![DatatypeConstructor {
            name: "mk_closure_env_test".to_string(),
            fields: vec![
                DatatypeField {
                    name: "closure_capture_test_0".to_string(),
                    sort: Sort::Bool,
                },
                DatatypeField {
                    name: "closure_capture_test_1".to_string(),
                    sort: mr_sort(),
                },
                DatatypeField {
                    name: "closure_capture_test_2".to_string(),
                    sort: mr_sort(),
                },
            ],
        }],
    }
}

/// The MINIMAL repro: one asserted equality between an uninterpreted-sort
/// constant and a selector application whose range is that sort. Satisfiable
/// (z3: sat); pre-fix the independent gate refuted the emitted (valid!) model
/// and fail-closed to `unknown`.
#[test]
fn selector_with_uninterp_range_emits_valid_sat() {
    let mut solver = Solver::new(Logic::Uflia);
    let dt = closure_env_dt();
    solver.declare_datatype(&dt);
    let bx = solver.declare_const("bx", mr_sort());
    let f = solver.declare_const("f", Sort::Datatype(dt.clone()));
    let cap1_f = solver.datatype_selector("closure_capture_test_1", f, mr_sort());
    let e1 = solver.eq(bx, cap1_f);
    solver.assert_term(e1);
    let d = solver.check_sat_with_details();
    assert_eq!(
        d.result,
        SolveResult::Sat,
        "capture projection over an uninterpreted range must be a valid sat \
         (diagnostic={:?})",
        d.unknown_diagnostic
    );
    assert!(
        d.result.was_model_validated(),
        "the emitted model must pass validation (strongest form)"
    );
}

/// The full closures/09 base shape: capture projections for all three fields,
/// the constructor identity, and a LIA premise. Satisfiable (z3: sat).
#[test]
fn capture_projections_with_ctor_identity_and_lia_emit_valid_sat() {
    let mut solver = Solver::new(Logic::Uflia);
    let dt = closure_env_dt();
    solver.declare_datatype(&dt);
    let bx = solver.declare_const("bx", mr_sort());
    let by = solver.declare_const("by", mr_sort());
    let c = solver.declare_const("c", Sort::Bool);
    let f = solver.declare_const("f", Sort::Datatype(dt.clone()));
    let n0 = solver.declare_const("n0", Sort::Int);
    let n1 = solver.declare_const("n1", Sort::Int);
    let sum = solver.add(n0, n1);
    let three = solver.int_const(3);
    let sum_eq = solver.eq(sum, three);
    solver.assert_term(sum_eq);
    let cap0_f = solver.datatype_selector("closure_capture_test_0", f, Sort::Bool);
    let cap1_f = solver.datatype_selector("closure_capture_test_1", f, mr_sort());
    let cap2_f = solver.datatype_selector("closure_capture_test_2", f, mr_sort());
    let e0 = solver.eq(c, cap0_f);
    solver.assert_term(e0);
    let e1 = solver.eq(bx, cap1_f);
    solver.assert_term(e1);
    let e2 = solver.eq(by, cap2_f);
    solver.assert_term(e2);
    let mk_f = solver.datatype_constructor(&dt, "mk_closure_env_test", &[c, bx, by]);
    let e3 = solver.eq(f, mk_f);
    solver.assert_term(e3);
    let d = solver.check_sat_with_details();
    assert_eq!(
        d.result,
        SolveResult::Sat,
        "the closures/09 base is satisfiable (diagnostic={:?})",
        d.unknown_diagnostic
    );
    assert!(
        d.result.was_model_validated(),
        "the emitted model must pass validation (strongest form)"
    );
}

/// The trimmed closures/09 outer-obligation event sequence: base asserts at
/// depth 0 (capture projections + constructor identity + an Int view chain +
/// one LIA sum), then the push/pop + repeated check-sat pattern the live
/// driver issues. Every check is satisfiable (z3: sat).
#[test]
fn closure_capture_uninterp_range_incremental_checks_stay_sat() {
    let mut solver = Solver::new(Logic::Uflia);
    let dt = closure_env_dt();
    solver.declare_datatype(&dt);

    let bx = solver.declare_const("bx", mr_sort());
    let by = solver.declare_const("by", mr_sort());
    let c = solver.declare_const("c", Sort::Bool);
    let f = solver.declare_const("f", Sort::Datatype(dt.clone()));

    // Int view chain (mirrors bx_current_view / bx_current / x_final).
    let bx_current_view = solver.declare_const("bx_current_view", Sort::Int);
    let bx_current = solver.declare_const("bx_current", Sort::Int);
    let x_final = solver.declare_const("x_final", Sort::Int);
    let eq1 = solver.eq(bx_current_view, bx_current);
    solver.assert_term(eq1);
    let eq2 = solver.eq(bx_current_view, x_final);
    solver.assert_term(eq2);

    // The LIA sum premise (x_final + y_final == 3 in the live VC).
    let n0 = solver.declare_const("num_coerce_0", Sort::Int);
    let n1 = solver.declare_const("old_y_view", Sort::Int);
    let sum = solver.add(n0, n1);
    let three = solver.int_const(3);
    let sum_eq = solver.eq(sum, three);
    solver.assert_term(sum_eq);

    // Capture projections + constructor identity.
    let cap0_f = solver.datatype_selector("closure_capture_test_0", f, Sort::Bool);
    let cap1_f = solver.datatype_selector("closure_capture_test_1", f, mr_sort());
    let cap2_f = solver.datatype_selector("closure_capture_test_2", f, mr_sort());
    let e0 = solver.eq(c, cap0_f);
    solver.assert_term(e0);
    let e1 = solver.eq(bx, cap1_f);
    solver.assert_term(e1);
    let e2 = solver.eq(by, cap2_f);
    solver.assert_term(e2);
    let mk_f = solver.datatype_constructor(&dt, "mk_closure_env_test", &[c, bx, by]);
    let e3 = solver.eq(f, mk_f);
    solver.assert_term(e3);

    // Prophecy-final envs with ONLY a selector app (no constructor identity).
    let f_final = solver.declare_const("f_final", Sort::Datatype(dt.clone()));
    let c_final = solver.declare_const("c_final", Sort::Bool);
    let cap0_ff = solver.datatype_selector("closure_capture_test_0", f_final, Sort::Bool);
    let e4 = solver.eq(c_final, cap0_ff);
    solver.assert_term(e4);

    // The live driver's scope pattern: push, view chain, push, negated goal,
    // check; pop; push+push, negated goal, check, check; pop, pop; push,
    // negated goal, check, check.
    solver.push();
    let bcc_view = solver.declare_const("bx_current_current_view", Sort::Int);
    let bcc = solver.declare_const("bx_current_current", Sort::Int);
    let eq3 = solver.eq(bcc_view, bcc);
    solver.assert_term(eq3);
    let eq4 = solver.eq(bx_current, bcc);
    solver.assert_term(eq4);

    let one = solver.int_const(1);
    let goal_eq = solver.eq(one, bcc_view);
    let goal_neg = solver.not(goal_eq);

    let mut verdicts = Vec::new();

    solver.push();
    solver.assert_term(goal_neg);
    verdicts.push(solver.check_sat_with_details());
    solver.pop();

    solver.push();
    solver.push();
    solver.assert_term(goal_neg);
    verdicts.push(solver.check_sat_with_details());
    verdicts.push(solver.check_sat_with_details());
    solver.pop();
    solver.pop();

    solver.push();
    solver.assert_term(goal_neg);
    verdicts.push(solver.check_sat_with_details());
    verdicts.push(solver.check_sat_with_details());

    for (i, details) in verdicts.iter().enumerate() {
        assert_eq!(
            details.result,
            SolveResult::Sat,
            "check #{i} must be a valid sat (unknown_reason={:?} diagnostic={:?})",
            details.unknown_reason,
            details.unknown_diagnostic,
        );
    }
}

/// SOUNDNESS: the canonicalization fix must NOT let a genuinely UNSAT
/// selector contradiction through. `f == mk_ce(c, bx, by)` forces
/// `cap1(f) == bx` by datatype semantics, so its negation is unsatisfiable.
#[test]
fn selector_of_constructor_contradiction_stays_unsat() {
    let mut solver = Solver::new(Logic::Uflia);
    let dt = closure_env_dt();
    solver.declare_datatype(&dt);
    let bx = solver.declare_const("bx", mr_sort());
    let by = solver.declare_const("by", mr_sort());
    let c = solver.declare_const("c", Sort::Bool);
    let f = solver.declare_const("f", Sort::Datatype(dt.clone()));
    let mk_f = solver.datatype_constructor(&dt, "mk_closure_env_test", &[c, bx, by]);
    let e3 = solver.eq(f, mk_f);
    solver.assert_term(e3);
    let cap1_f = solver.datatype_selector("closure_capture_test_1", f, mr_sort());
    let e1 = solver.eq(bx, cap1_f);
    let ne1 = solver.not(e1);
    solver.assert_term(ne1);
    assert!(
        solver.check_sat().is_unsat(),
        "cap1(mk_ce(c, bx, by)) == bx is a datatype tautology; its negation is unsat"
    );
}

/// SOUNDNESS: a genuine carrier contradiction through an Int-valued UF over
/// the uninterpreted range must stay `unsat` — element unification must not
/// paper over `cur(bx) = 1`, `cur(by) = 2`, `bx == by`.
#[test]
fn carrier_projection_contradiction_stays_unsat() {
    let mut solver = Solver::new(Logic::Uflia);
    let dt = closure_env_dt();
    solver.declare_datatype(&dt);
    let bx = solver.declare_const("bx", mr_sort());
    let by = solver.declare_const("by", mr_sort());
    let f = solver.declare_const("f", Sort::Datatype(dt.clone()));
    let cap1_f = solver.datatype_selector("closure_capture_test_1", f, mr_sort());
    let cap2_f = solver.datatype_selector("closure_capture_test_2", f, mr_sort());
    let e1 = solver.eq(bx, cap1_f);
    solver.assert_term(e1);
    let e2 = solver.eq(by, cap2_f);
    solver.assert_term(e2);
    let cur = solver.declare_fun("mut_ref_current", &[mr_sort()], Sort::Int);
    let cur_bx = solver.apply(&cur, &[bx]);
    let cur_by = solver.apply(&cur, &[by]);
    let one = solver.int_const(1);
    let two = solver.int_const(2);
    let c1 = solver.eq(cur_bx, one);
    solver.assert_term(c1);
    let c2 = solver.eq(cur_by, two);
    solver.assert_term(c2);
    let same = solver.eq(bx, by);
    solver.assert_term(same);
    assert!(
        solver.check_sat().is_unsat(),
        "bx == by forces cur(bx) == cur(by), contradicting 1 == 2"
    );
}
