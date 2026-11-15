// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! #nia-sign-cut-soundness: a LIA verdict may rest only on JUSTIFIED bounds.
//!
//! The NIA asserts model guesses (sign cuts `x >= 0`, rounding pins `x = c`)
//! into its inner LIA as bounds whose reason is the VARIABLE TERM — never an
//! asserted atom. On main `b1c1f8f201` the LIA's side checks read those
//! bounds as facts and returned the whole asserted set as a conflict, which
//! the NIA published as `unsat` on 18 satisfiable QF_NIA problems. These
//! tests inject such a bound directly, the way the NIA does, and require that
//! `check()` never refutes from it.

use super::*;
use ay_lra::GomoryCut;
use num_traits::{One, Zero};

/// Assert an NIA-shaped tentative bound: `var {>=,<=} value` with the
/// variable term itself as the only reason (exactly what
/// `inject_tentative_sign_cuts` / `apply_patch` do through `add_gomory_cut`).
fn assert_unjustified_bound(solver: &mut LiaSolver<'_>, var: TermId, value: i64, is_lower: bool) {
    let lra_var = solver.lra_solver_mut().ensure_var_registered(var);
    solver.lra_solver_mut().add_gomory_cut(
        &GomoryCut {
            coeffs: vec![(lra_var, BigRational::one())],
            bound: BigRational::from_integer(BigInt::from(value)),
            is_lower,
            reasons: Vec::new(),
            source_term: None,
        },
        var,
    );
}

fn is_unsat(result: &TheoryResult) -> bool {
    matches!(
        result,
        TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
    )
}

/// `3x + y = 1 ∧ -100 <= y <= 1` is satisfiable (x = 0, y = 1; x = 1, y = -2).
/// A pin `y = 0` with the variable term as its reason is a model GUESS. On
/// main, `check_single_equality_modular_constraints` /
/// `check_modular_for_var` read `y in [0, 0]` as a fact, found no `y ≡ 1
/// (mod 3)` in it, and returned the asserted set as a conflict — the door on
/// `sat_nia_sign_cut_1` and `_2`. The LIA must not refute from an
/// unjustified bound.
#[test]
fn unjustified_pin_does_not_refute_through_modular_check() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let one = terms.mk_int(BigInt::from(1));
    let three = terms.mk_int(BigInt::from(3));
    let neg100 = terms.mk_int(BigInt::from(-100));
    let three_x = terms.mk_mul(vec![three, x]);
    let lhs = terms.mk_add(vec![three_x, y]);
    let eq = terms.mk_eq(lhs, one);
    let y_le_1 = terms.mk_le(y, one);
    let y_ge_m100 = terms.mk_ge(y, neg100);

    let mut solver = LiaSolver::new(&terms);
    solver.assert_literal(eq, true);
    solver.assert_literal(y_le_1, true);
    solver.assert_literal(y_ge_m100, true);
    let baseline = solver.check();
    assert!(
        !is_unsat(&baseline),
        "the linear system is satisfiable: {baseline:?}"
    );

    // The NIA's tentative scope: a rounding pin y = 0 (two bounds, reason = y).
    solver.push();
    assert_unjustified_bound(&mut solver, y, 0, true);
    assert_unjustified_bound(&mut solver, y, 0, false);
    let (lb, ub) = solver.lra_solver().get_bounds(y).expect("y is registered");
    assert!(
        lb.as_ref().is_some_and(|b| !solver.bound_is_justified(b))
            && ub.as_ref().is_some_and(|b| !solver.bound_is_justified(b)),
        "a bound whose reason is the variable term is unjustified"
    );
    assert!(
        matches!(solver.justified_bounds(y), Some((None, None))),
        "justified_bounds must report the pin as absent"
    );

    let with_pin = solver.check();
    assert!(
        !is_unsat(&with_pin),
        "a model guess must never become a LIA refutation: {with_pin:?}"
    );
    solver.pop();
    let after = solver.check();
    assert!(!is_unsat(&after), "{after:?}");
}

/// `3x = z + 1 ∧ -2 <= z <= 1` is satisfiable (z = -1, x = 0). A tentative
/// sign cut `z >= 0` shrinks the direct-enumeration box to `z in [0, 1]`,
/// which holds no `z ≡ 2 (mod 3)`: on main `try_direct_enumeration` returned
/// `Unsat(conflict_from_asserted())` (`[ENUM] No valid solution`, the door on
/// gen2/h0139, h0447, h0685, ...). The box must be built from justified
/// bounds only.
#[test]
fn unjustified_sign_cut_does_not_shrink_the_enumeration_box() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let z = terms.mk_var("z", Sort::Int);
    let one = terms.mk_int(BigInt::from(1));
    let three = terms.mk_int(BigInt::from(3));
    let neg2 = terms.mk_int(BigInt::from(-2));
    let three_x = terms.mk_mul(vec![three, x]);
    let z_plus_1 = terms.mk_add(vec![z, one]);
    let eq = terms.mk_eq(three_x, z_plus_1);
    let z_ge_m2 = terms.mk_ge(z, neg2);
    let z_le_1 = terms.mk_le(z, one);

    let mut solver = LiaSolver::new(&terms);
    solver.assert_literal(eq, true);
    solver.assert_literal(z_ge_m2, true);
    solver.assert_literal(z_le_1, true);
    let baseline = solver.check();
    assert!(!is_unsat(&baseline), "{baseline:?}");

    solver.push();
    assert_unjustified_bound(&mut solver, z, 0, true); // the sign guess z >= 0
    let with_cut = solver.check();
    assert!(
        !is_unsat(&with_cut),
        "a sign guess must never become a LIA refutation: {with_cut:?}"
    );
    solver.pop();
}

/// Justified bounds are unaffected: the same pin asserted as a real atom
/// (`y = 0` asserted) makes the system genuinely UNSAT (`y ≡ 1 (mod 3)`),
/// and the refutation cites only asserted literals.
#[test]
fn asserted_pin_still_refutes_and_cites_only_live_atoms() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let zero = terms.mk_int(BigInt::zero());
    let one = terms.mk_int(BigInt::from(1));
    let three = terms.mk_int(BigInt::from(3));
    let three_x = terms.mk_mul(vec![three, x]);
    let lhs = terms.mk_add(vec![three_x, y]);
    let eq = terms.mk_eq(lhs, one);
    let y_is_0 = terms.mk_eq(y, zero);

    let mut solver = LiaSolver::new(&terms);
    solver.assert_literal(eq, true);
    solver.assert_literal(y_is_0, true);
    let result = solver.check();
    assert!(
        is_unsat(&result),
        "3x + 0 = 1 has no integer solution: {result:?}"
    );
    let lits: Vec<TheoryLit> = match result {
        TheoryResult::Unsat(l) => l,
        TheoryResult::UnsatWithFarkas(c) => c.literals,
        _ => unreachable!(),
    };
    assert!(
        solver.conflict_reasons_all_live(&lits),
        "a genuine conflict cites only live atoms: {lits:?}"
    );
    for lit in &lits {
        assert!(
            lit.term == eq || lit.term == y_is_0 || lit.term.is_sentinel(),
            "conflict literal {lit:?} is not an asserted atom"
        );
    }
}

/// The exit guard: a conflict that cites a bare variable term (the reason of
/// an NIA tentative bound, carried in by a bound-reason collector) is not a
/// clause over asserted atoms and is refused as `Unknown`; a conflict over
/// live atoms passes through untouched.
#[test]
fn exit_guard_refuses_conflicts_citing_non_atoms() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let zero = terms.mk_int(BigInt::zero());
    let x_ge_0 = terms.mk_ge(x, zero);

    let mut solver = LiaSolver::new(&terms);
    solver.assert_literal(x_ge_0, true);

    let tainted = TheoryResult::Unsat(vec![
        TheoryLit::new(x_ge_0, true),
        TheoryLit::new(x, true), // the variable term: never an asserted atom
    ]);
    let refused = solver.refuse_unjustified_conflict(tainted);
    assert!(
        matches!(refused, TheoryResult::Unknown),
        "a conflict citing a non-atom must not be published: {refused:?}"
    );
    assert_eq!(solver.unjustified_conflicts_dropped, 1);

    let genuine = TheoryResult::Unsat(vec![TheoryLit::new(x_ge_0, true)]);
    let kept = solver.refuse_unjustified_conflict(genuine);
    assert!(
        matches!(&kept, TheoryResult::Unsat(l) if l.len() == 1 && l[0].term == x_ge_0),
        "a conflict over live atoms passes: {kept:?}"
    );
    assert_eq!(solver.unjustified_conflicts_dropped, 1);

    // A retracted literal (asserted, then popped) is stale, not live.
    let stale = TheoryResult::Unsat(vec![TheoryLit::new(x_ge_0, false)]);
    let refused = solver.refuse_unjustified_conflict(stale);
    assert!(matches!(refused, TheoryResult::Unknown), "{refused:?}");
}

/// Sentinel-only bounds (factor-split case hypotheses, Gomory / HNF cuts)
/// stay justified: the enclosing exact procedure owns them, exactly as the
/// LRA's own conflict guard treats sentinels.
#[test]
fn sentinel_only_bounds_stay_justified() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let zero = terms.mk_int(BigInt::zero());
    let x_ge_0 = terms.mk_ge(x, zero);

    let mut solver = LiaSolver::new(&terms);
    solver.assert_literal(x_ge_0, true);
    let _ = solver.check();

    let lra_var = solver.lra_solver_mut().ensure_var_registered(x);
    solver.lra_solver_mut().add_cut_rat(
        vec![(lra_var, ay_lra::rational::Rational::new(1, 1))],
        ay_lra::rational::Rational::new(5, 1),
        false,
        &[(TermId::SENTINEL, true)],
        TermId::SENTINEL,
    );
    let (_, ub) = solver.lra_solver().get_bounds(x).expect("registered");
    let ub = ub.expect("the sentinel cut installed an upper bound");
    assert!(
        solver.bound_is_justified(&ub),
        "a sentinel-only bound is an axiom / hypothesis of an exact procedure"
    );
}

/// #nonlinear-shared-reasons: a shared equality that arrives with NO reason
/// literals is installed citing its `lhs` term — the same shape as a guess.
/// Outside a guess scope it is the other theory's unconditional claim and is
/// justified (main's side checks read it as a fact; rejecting it cost a
/// QF_UFLIA verdict); inside a `push_tentative` scope a guess on `lhs` would
/// cite the same term, so it is not; the pop restores it.
#[test]
fn reasonless_shared_equality_is_justified_outside_guess_scopes() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let seven = terms.mk_int(BigInt::from(7));
    let mut solver = LiaSolver::new(&terms);
    solver.assert_shared_equality(x, seven, &[]);
    let _ = solver.check();
    let (lb, ub) = solver.lra_solver().get_bounds(x).expect("x registered");
    let (lb, ub) = (lb.expect("x = 7 lower"), ub.expect("x = 7 upper"));
    assert!(solver.bound_is_justified(&lb) && solver.bound_is_justified(&ub));

    solver.push_tentative();
    assert!(
        !solver.bound_is_justified(&lb),
        "inside a guess scope the placeholder is indistinguishable from a guess on x"
    );
    solver.pop_tentative();
    assert!(
        solver.bound_is_justified(&lb),
        "the pop closes the guess scope"
    );

    // A plain (DPLL) pop that crosses an open guess scope closes it too.
    solver.push();
    solver.push_tentative();
    TheorySolver::pop(&mut solver);
    TheorySolver::pop(&mut solver);
    assert!(solver.bound_is_justified(&lb));
}
