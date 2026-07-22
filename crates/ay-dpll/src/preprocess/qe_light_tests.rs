// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Tests for the `qe-light` preprocessing pass (`qe_light.rs`).
//!
//! Coverage (structural; the SAT/UNSAT differential lives in the tactic tests):
//! - IN-FRAGMENT: an eliminable `(exists ((x Int)) φ)` is rewritten to a
//!   quantifier-free formula (the `Exists` node is gone) AND the pass reports
//!   progress.
//! - NESTING: an in-fragment exists buried under `and` is still eliminated.
//! - OUT-OF-FRAGMENT (identity, no progress): universals, multi-variable
//!   existentials, non-Int bound sorts, nested/alternating quantifiers, and
//!   non-linear matrices are all left byte-for-byte unchanged.
//!
//! (Equivalence of the eliminated formula to `∃x.φ` is enforced by Cooper's own
//! self-check before `eliminate_exists` returns `Eliminated`; the end-to-end
//! SAT/UNSAT differential is covered in `tactics_tests.rs`.)

#![allow(clippy::panic)]

use super::PreprocessingPass;
use super::QeLight;
use ay_core::term::TermData;
use ay_core::{Sort, TermId, TermStore};
use num_bigint::BigInt;

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn ivar(terms: &mut TermStore, name: &str) -> TermId {
    terms.mk_var(name, Sort::Int)
}

fn ci(terms: &mut TermStore, n: i64) -> TermId {
    terms.mk_int(BigInt::from(n))
}

/// Recursively test whether `target` (by hash-consed identity) occurs in `term`.
fn mentions_termid(terms: &TermStore, term: TermId, target: TermId) -> bool {
    if term == target {
        return true;
    }
    match terms.get(term) {
        TermData::Not(inner) => mentions_termid(terms, *inner, target),
        TermData::Ite(c, t, e) => {
            mentions_termid(terms, *c, target)
                || mentions_termid(terms, *t, target)
                || mentions_termid(terms, *e, target)
        }
        TermData::App(_, args) => args.iter().any(|&a| mentions_termid(terms, a, target)),
        TermData::Let(bindings, body) => {
            bindings
                .iter()
                .any(|(_, v)| mentions_termid(terms, *v, target))
                || mentions_termid(terms, *body, target)
        }
        TermData::Forall(_, b, _) | TermData::Exists(_, b, _) => mentions_termid(terms, *b, target),
        _ => false,
    }
}

/// Recursively test whether `term` contains any quantifier node.
fn contains_quantifier(terms: &TermStore, term: TermId) -> bool {
    match terms.get(term) {
        TermData::Forall(_, _, _) | TermData::Exists(_, _, _) => true,
        TermData::Not(inner) => contains_quantifier(terms, *inner),
        TermData::Ite(c, t, e) => {
            contains_quantifier(terms, *c)
                || contains_quantifier(terms, *t)
                || contains_quantifier(terms, *e)
        }
        TermData::App(_, args) => args.iter().any(|&a| contains_quantifier(terms, a)),
        TermData::Let(bindings, body) => {
            bindings.iter().any(|(_, v)| contains_quantifier(terms, *v))
                || contains_quantifier(terms, *body)
        }
        TermData::Const(_) | TermData::Var(_, _) => false,
        _ => false,
    }
}

// ---------------------------------------------------------------------------
// In-fragment: the quantifier is eliminated and progress is reported.
// ---------------------------------------------------------------------------

#[test]
fn eliminates_bounded_interval_exists() {
    // ∃x. (x > y) ∧ (x < y + 10)  — always SAT (e.g. x = y+1), so ≡ true.
    let mut terms = TermStore::new();
    let x = ivar(&mut terms, "x");
    let y = ivar(&mut terms, "y");
    let ten = ci(&mut terms, 10);
    let yp10 = terms.mk_add(vec![y, ten]);
    let l1 = terms.mk_gt(x, y);
    let l2 = terms.mk_lt(x, yp10);
    let body = terms.mk_and(vec![l1, l2]);
    let ex = terms.mk_exists(vec![("x".to_string(), Sort::Int)], body);

    let mut goal = vec![ex];
    let progressed = QeLight::new().apply(&mut terms, &mut goal);

    assert!(
        progressed,
        "qe-light must report progress when it eliminates"
    );
    assert_eq!(goal.len(), 1, "one assertion in, one out");
    assert!(
        !contains_quantifier(&terms, goal[0]),
        "the existential must be gone after qe-light"
    );
}

#[test]
fn eliminates_empty_interval_exists() {
    // ∃x. (x > y) ∧ (x < y)  — no integer strictly between y and y, so ≡ false.
    let mut terms = TermStore::new();
    let x = ivar(&mut terms, "x");
    let y = ivar(&mut terms, "y");
    let l1 = terms.mk_gt(x, y);
    let l2 = terms.mk_lt(x, y);
    let body = terms.mk_and(vec![l1, l2]);
    let ex = terms.mk_exists(vec![("x".to_string(), Sort::Int)], body);

    let mut goal = vec![ex];
    assert!(QeLight::new().apply(&mut terms, &mut goal));
    assert!(!contains_quantifier(&terms, goal[0]));
}

#[test]
fn eliminates_exists_with_divisibility() {
    // ∃x. (x = 2*y) ∧ (x mod 2 = 0)  — the divisibility is redundant; ≡ true.
    let mut terms = TermStore::new();
    let x = ivar(&mut terms, "x");
    let y = ivar(&mut terms, "y");
    let two = ci(&mut terms, 2);
    let twoy = terms.mk_mul(vec![two, y]);
    let l1 = terms.mk_eq(x, twoy);
    let two2 = ci(&mut terms, 2);
    let xmod2 = terms.mk_mod(x, two2);
    let zero = ci(&mut terms, 0);
    let l2 = terms.mk_eq(xmod2, zero);
    let body = terms.mk_and(vec![l1, l2]);
    let ex = terms.mk_exists(vec![("x".to_string(), Sort::Int)], body);

    let mut goal = vec![ex];
    assert!(QeLight::new().apply(&mut terms, &mut goal));
    assert!(!contains_quantifier(&terms, goal[0]));
}

#[test]
fn fresh_named_bound_var_is_eliminated_not_freed() {
    // SOUNDNESS REGRESSION. The elaborator builds bound variables with
    // `mk_fresh_var`, whose (uniquified) name is NOT registered in the
    // intern-by-name table. The pass must recover the EXACT bound-variable node
    // by scanning the body — never re-intern a phantom via `mk_var(name)`, which
    // would leave the real bound variable dangling FREE in the "eliminated"
    // result (an unsound strip, satisfiable under negation).
    let mut terms = TermStore::new();
    let x = terms.mk_fresh_var("x", Sort::Int); // e.g. "x_0", unregistered
    let name = match terms.get(x) {
        TermData::Var(n, _) => n.clone(),
        other => panic!("fresh var must be a Var, got {other:?}"),
    };
    let y = ivar(&mut terms, "y");
    let ten = ci(&mut terms, 10);
    let yp10 = terms.mk_add(vec![y, ten]);
    let l1 = terms.mk_gt(x, y);
    let l2 = terms.mk_lt(x, yp10);
    let body = terms.mk_and(vec![l1, l2]);
    let ex = terms.mk_exists(vec![(name, Sort::Int)], body);

    let mut goal = vec![ex];
    let progressed = QeLight::new().apply(&mut terms, &mut goal);

    assert!(
        progressed,
        "a fresh-named eliminable existential must still be eliminated"
    );
    assert!(
        !contains_quantifier(&terms, goal[0]),
        "the existential must be gone after qe-light"
    );
    assert!(
        !mentions_termid(&terms, goal[0], x),
        "the eliminated bound variable must NOT be left free in the result"
    );
}

// ---------------------------------------------------------------------------
// Nesting: an in-fragment exists under `and` is eliminated.
// ---------------------------------------------------------------------------

#[test]
fn eliminates_exists_nested_under_and() {
    // (and p (exists ((x Int)) (and (x>y) (x<y+5))))
    let mut terms = TermStore::new();
    let p = terms.mk_var("p", Sort::Bool);
    let x = ivar(&mut terms, "x");
    let y = ivar(&mut terms, "y");
    let five = ci(&mut terms, 5);
    let yp5 = terms.mk_add(vec![y, five]);
    let l1 = terms.mk_gt(x, y);
    let l2 = terms.mk_lt(x, yp5);
    let body = terms.mk_and(vec![l1, l2]);
    let ex = terms.mk_exists(vec![("x".to_string(), Sort::Int)], body);
    let top = terms.mk_and(vec![p, ex]);

    let mut goal = vec![top];
    assert!(QeLight::new().apply(&mut terms, &mut goal));
    assert!(
        !contains_quantifier(&terms, goal[0]),
        "nested existential must be eliminated"
    );
}

// ---------------------------------------------------------------------------
// Out-of-fragment: identity, no progress.
// ---------------------------------------------------------------------------

#[test]
fn leaves_forall_unchanged() {
    // ∀x. x = x  — universal is out of fragment.
    let mut terms = TermStore::new();
    let x = ivar(&mut terms, "x");
    let body = terms.mk_eq(x, x);
    let fa = terms.mk_forall(vec![("x".to_string(), Sort::Int)], body);

    let mut goal = vec![fa];
    let progressed = QeLight::new().apply(&mut terms, &mut goal);
    assert!(!progressed, "forall must not progress");
    assert_eq!(goal, vec![fa], "forall must be left unchanged");
}

#[test]
fn leaves_multivar_exists_unchanged() {
    // ∃x,y. x < y  — two bound variables is out of Cooper's single-var fragment.
    let mut terms = TermStore::new();
    let x = ivar(&mut terms, "x");
    let y = ivar(&mut terms, "y");
    let body = terms.mk_lt(x, y);
    let ex = terms.mk_exists(
        vec![("x".to_string(), Sort::Int), ("y".to_string(), Sort::Int)],
        body,
    );

    let mut goal = vec![ex];
    assert!(!QeLight::new().apply(&mut terms, &mut goal));
    assert_eq!(goal, vec![ex]);
    assert!(contains_quantifier(&terms, goal[0]));
}

#[test]
fn leaves_real_sorted_exists_unchanged() {
    // ∃x:Real. x < y  — non-Int bound sort is out of fragment.
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let body = terms.mk_lt(x, y);
    let ex = terms.mk_exists(vec![("x".to_string(), Sort::Real)], body);

    let mut goal = vec![ex];
    assert!(!QeLight::new().apply(&mut terms, &mut goal));
    assert_eq!(goal, vec![ex]);
    assert!(contains_quantifier(&terms, goal[0]));
}

#[test]
fn leaves_nested_alternating_quantifier_unchanged() {
    // ∃x. ∀y. (x <= y)  — the matrix is itself a quantifier (not a literal
    // conjunction), so Cooper refuses; the whole node is kept verbatim.
    let mut terms = TermStore::new();
    let x = ivar(&mut terms, "x");
    let y = ivar(&mut terms, "y");
    let le = terms.mk_le(x, y);
    let inner = terms.mk_forall(vec![("y".to_string(), Sort::Int)], le);
    let ex = terms.mk_exists(vec![("x".to_string(), Sort::Int)], inner);

    let mut goal = vec![ex];
    assert!(!QeLight::new().apply(&mut terms, &mut goal));
    assert_eq!(goal, vec![ex], "alternating quantifier must be unchanged");
}

#[test]
fn leaves_nonlinear_matrix_unchanged() {
    // ∃x. x*x = y  — non-linear matrix is out of fragment.
    let mut terms = TermStore::new();
    let x = ivar(&mut terms, "x");
    let y = ivar(&mut terms, "y");
    let xx = terms.mk_mul(vec![x, x]);
    let body = terms.mk_eq(xx, y);
    let ex = terms.mk_exists(vec![("x".to_string(), Sort::Int)], body);

    let mut goal = vec![ex];
    assert!(!QeLight::new().apply(&mut terms, &mut goal));
    assert_eq!(goal, vec![ex]);
    assert!(contains_quantifier(&terms, goal[0]));
}

#[test]
fn quantifier_free_goal_is_identity() {
    // No quantifier at all: pure identity, no progress.
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    let b = terms.mk_var("b", Sort::Bool);
    let g = terms.mk_and(vec![a, b]);
    let mut goal = vec![g];
    assert!(!QeLight::new().apply(&mut terms, &mut goal));
    assert_eq!(goal, vec![g]);
}
