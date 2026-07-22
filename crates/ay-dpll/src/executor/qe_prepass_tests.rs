// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Unit tests for the deep QE pre-pass (`qe_prepass.rs`).
//!
//! Coverage (structural; the SAT/UNSAT differential lives in the e2e
//! quantifier tests):
//! - ∀∃ same-direction alternation eliminates to a ground constant.
//! - Multi-variable existentials peel via binder currying.
//! - Three-level alternation eliminates innermost-out.
//! - REFUSAL FALL-THROUGH (identity, no progress): out-of-fragment matrices
//!   (UF), vacuous binders (conservatively KEPT), ambiguous duplicate-name
//!   bound variables, DNF cap blowups, and elimination-budget exhaustion all
//!   keep the original assertion `TermId` byte-for-byte.
//! - All-or-nothing per assertion: a partially eliminable assertion is kept
//!   verbatim.

#![allow(clippy::panic)]

use super::deep_qe;
use ay_core::term::{Constant, Symbol, TermData};
use ay_core::{Sort, TermId, TermStore};
use num_bigint::BigInt;

fn ivar(terms: &mut TermStore, name: &str) -> TermId {
    terms.mk_var(name, Sort::Int)
}

fn ci(terms: &mut TermStore, n: i64) -> TermId {
    terms.mk_int(BigInt::from(n))
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
// Elimination wins
// ---------------------------------------------------------------------------

#[test]
fn eliminates_forall_exists_same_direction() {
    // ∀x. ∃y. (y > x ∧ y > 5) — valid over Int, must eliminate to `true`.
    let mut terms = TermStore::new();
    let x = ivar(&mut terms, "x");
    let y = ivar(&mut terms, "y");
    let five = ci(&mut terms, 5);
    let l1 = terms.mk_gt(y, x);
    let l2 = terms.mk_gt(y, five);
    let body = terms.mk_and(vec![l1, l2]);
    let ex = terms.mk_exists(vec![("y".to_string(), Sort::Int)], body);
    let fa = terms.mk_forall(vec![("x".to_string(), Sort::Int)], ex);

    let mut goal = vec![fa];
    let progressed = deep_qe(&mut terms, &mut goal, None);

    assert!(progressed, "deep_qe must report progress on elimination");
    assert!(!contains_quantifier(&terms, goal[0]));
    assert!(
        matches!(terms.get(goal[0]), TermData::Const(Constant::Bool(true))),
        "∀x.∃y.(y>x ∧ y>5) must fold to true, got {:?}",
        terms.get(goal[0])
    );
}

#[test]
fn eliminates_forall_exists_empty_interval_to_false() {
    // ∀x. ∃y. (y > x ∧ y < x) — unsatisfiable body, must eliminate to `false`.
    let mut terms = TermStore::new();
    let x = ivar(&mut terms, "x");
    let y = ivar(&mut terms, "y");
    let l1 = terms.mk_gt(y, x);
    let l2 = terms.mk_lt(y, x);
    let body = terms.mk_and(vec![l1, l2]);
    let ex = terms.mk_exists(vec![("y".to_string(), Sort::Int)], body);
    let fa = terms.mk_forall(vec![("x".to_string(), Sort::Int)], ex);

    let mut goal = vec![fa];
    assert!(deep_qe(&mut terms, &mut goal, None));
    assert!(
        matches!(terms.get(goal[0]), TermData::Const(Constant::Bool(false))),
        "∀x.∃y.(y>x ∧ y<x) must fold to false, got {:?}",
        terms.get(goal[0])
    );
}

#[test]
fn deep_qe_isint_forall_valid_folds_true() {
    // ∀x. is_int(x) ⇒ is_int(x+1) — valid; is_int eliminator folds to `true`.
    use num_rational::BigRational;
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let a = terms.mk_is_int(x);
    let one = terms.mk_rational(BigRational::from_integer(BigInt::from(1)));
    let xp1 = terms.mk_add(vec![x, one]);
    let b = terms.mk_is_int(xp1);
    let imp = terms.mk_implies(a, b);
    let fa = terms.mk_forall(vec![("x".to_string(), Sort::Real)], imp);
    let mut goal = vec![fa];
    deep_qe(&mut terms, &mut goal, None);
    assert!(
        matches!(terms.get(goal[0]), TermData::Const(Constant::Bool(true))),
        "expected true, got {:?}",
        terms.get(goal[0])
    );
}

#[test]
fn deep_qe_isint_exists_sat_folds_true() {
    // ∃x. is_int(x) ∧ is_int(x+2) — sat; folds to `true`.
    use num_rational::BigRational;
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let a = terms.mk_is_int(x);
    let two = terms.mk_rational(BigRational::from_integer(BigInt::from(2)));
    let xp2 = terms.mk_add(vec![x, two]);
    let b = terms.mk_is_int(xp2);
    let body = terms.mk_and(vec![a, b]);
    let ex = terms.mk_exists(vec![("x".to_string(), Sort::Real)], body);
    let mut goal = vec![ex];
    deep_qe(&mut terms, &mut goal, None);
    assert!(
        matches!(terms.get(goal[0]), TermData::Const(Constant::Bool(true))),
        "expected true, got {:?}",
        terms.get(goal[0])
    );
}

#[test]
fn eliminates_multivar_exists_by_currying() {
    // ∃x,y. (x > y ∧ y > 5 ∧ x < y + 3) — SAT, must eliminate to `true`.
    let mut terms = TermStore::new();
    let x = ivar(&mut terms, "x");
    let y = ivar(&mut terms, "y");
    let five = ci(&mut terms, 5);
    let three = ci(&mut terms, 3);
    let yp3 = terms.mk_add(vec![y, three]);
    let l1 = terms.mk_gt(x, y);
    let l2 = terms.mk_gt(y, five);
    let l3 = terms.mk_lt(x, yp3);
    let body = terms.mk_and(vec![l1, l2, l3]);
    let ex = terms.mk_exists(
        vec![("x".to_string(), Sort::Int), ("y".to_string(), Sort::Int)],
        body,
    );

    let mut goal = vec![ex];
    assert!(deep_qe(&mut terms, &mut goal, None));
    assert!(
        matches!(terms.get(goal[0]), TermData::Const(Constant::Bool(true))),
        "multi-var exists must fully eliminate, got {:?}",
        terms.get(goal[0])
    );
}

#[test]
fn eliminates_three_level_alternation() {
    // ∀x. ∃y. ∀z. (z < y ⇒ z < x + 10) — z<y ⇒ z<x+10 valid iff y ≤ x+10
    // (Int), and ∃y always finds one, so the whole formula is `true`.
    let mut terms = TermStore::new();
    let x = ivar(&mut terms, "x");
    let y = ivar(&mut terms, "y");
    let z = ivar(&mut terms, "z");
    let ten = ci(&mut terms, 10);
    let xp10 = terms.mk_add(vec![x, ten]);
    let zy = terms.mk_lt(z, y);
    let zx = terms.mk_lt(z, xp10);
    let body = terms.mk_implies(zy, zx);
    let fa_z = terms.mk_forall(vec![("z".to_string(), Sort::Int)], body);
    let ex_y = terms.mk_exists(vec![("y".to_string(), Sort::Int)], fa_z);
    let fa_x = terms.mk_forall(vec![("x".to_string(), Sort::Int)], ex_y);

    let mut goal = vec![fa_x];
    assert!(deep_qe(&mut terms, &mut goal, None));
    assert!(
        matches!(terms.get(goal[0]), TermData::Const(Constant::Bool(true))),
        "3-level LIA alternation must eliminate to true, got {:?}",
        terms.get(goal[0])
    );
}

#[test]
fn eliminates_disjunctive_matrix() {
    // ∃y. (y = x ∨ y > 5) — SAT for every x (witness y = x), ≡ true.
    let mut terms = TermStore::new();
    let x = ivar(&mut terms, "x");
    let y = ivar(&mut terms, "y");
    let five = ci(&mut terms, 5);
    let e1 = terms.mk_eq(y, x);
    let g1 = terms.mk_gt(y, five);
    let body = terms.mk_or(vec![e1, g1]);
    let ex = terms.mk_exists(vec![("y".to_string(), Sort::Int)], body);

    let mut goal = vec![ex];
    assert!(deep_qe(&mut terms, &mut goal, None));
    assert!(
        matches!(terms.get(goal[0]), TermData::Const(Constant::Bool(true))),
        "∃-over-∨ distribution must eliminate, got {:?}",
        terms.get(goal[0])
    );
}

// ---------------------------------------------------------------------------
// Refusal fall-through: the original assertion TermId is kept byte-for-byte.
// ---------------------------------------------------------------------------

#[test]
fn refuses_uninterpreted_function_matrix() {
    // ∃y. f(y) > 0 — UF is out of fragment; the fragment screen must refuse
    // and the assertion must be IDENTICAL (same TermId), not reshaped.
    let mut terms = TermStore::new();
    let y = ivar(&mut terms, "y");
    let fy = terms.mk_app(Symbol::named("f"), vec![y], Sort::Int);
    let zero = ci(&mut terms, 0);
    let body = terms.mk_gt(fy, zero);
    let ex = terms.mk_exists(vec![("y".to_string(), Sort::Int)], body);

    let mut goal = vec![ex];
    let progressed = deep_qe(&mut terms, &mut goal, None);

    assert!(!progressed);
    assert_eq!(
        goal[0], ex,
        "refused assertion must keep its original TermId"
    );
}

#[test]
fn keeps_vacuous_binder() {
    // ∃x. (y > 5) — x does not occur. find_bound_var → None does NOT prove
    // non-occurrence in general, so the pass must conservatively KEEP the
    // node (matching qe_light), never drop the binder.
    let mut terms = TermStore::new();
    let y = ivar(&mut terms, "y");
    let five = ci(&mut terms, 5);
    let body = terms.mk_gt(y, five);
    let ex = terms.mk_exists(vec![("x".to_string(), Sort::Int)], body);

    let mut goal = vec![ex];
    let progressed = deep_qe(&mut terms, &mut goal, None);

    assert!(!progressed);
    assert_eq!(goal[0], ex, "vacuous binder must be kept verbatim");
}

#[test]
fn refuses_ambiguous_duplicate_name_bound_var() {
    // Two DISTINCT Var nodes share the name "y" inside the matrix; recovering
    // the bound variable by name is ambiguous, so the pass must refuse.
    let mut terms = TermStore::new();
    let y1 = terms.mk_var("y", Sort::Int);
    let y2 = terms.mk_fresh_named_var("y", Sort::Int);
    assert_ne!(y1, y2, "test needs two distinct Var nodes named y");
    let five = ci(&mut terms, 5);
    let l1 = terms.mk_gt(y1, five);
    let l2 = terms.mk_lt(y2, five);
    let body = terms.mk_and(vec![l1, l2]);
    let ex = terms.mk_exists(vec![("y".to_string(), Sort::Int)], body);

    let mut goal = vec![ex];
    let progressed = deep_qe(&mut terms, &mut goal, None);

    assert!(!progressed);
    assert_eq!(goal[0], ex, "ambiguous bound-var name must refuse");
}

#[test]
fn refuses_dnf_blowup_over_disjunct_cap() {
    // ∃x. ⋀_{i=1..10} (x > aᵢ ∨ x < bᵢ) distributes to 2^10 = 1024 > 512
    // (`MAX_DNF_DISJUNCTS`, raised by #quantprod-g) disjuncts: over cap,
    // must refuse and keep the original node. The distribution loop refuses
    // as soon as the running product crosses the cap, so the test cost stays
    // bounded.
    let mut terms = TermStore::new();
    let x = ivar(&mut terms, "x");
    let mut conj: Vec<TermId> = Vec::new();
    for i in 0..10 {
        let a = ivar(&mut terms, &format!("a{i}"));
        let b = ivar(&mut terms, &format!("b{i}"));
        let g = terms.mk_gt(x, a);
        let l = terms.mk_lt(x, b);
        conj.push(terms.mk_or(vec![g, l]));
    }
    let body = terms.mk_and(conj);
    let ex = terms.mk_exists(vec![("x".to_string(), Sort::Int)], body);

    let mut goal = vec![ex];
    let progressed = deep_qe(&mut terms, &mut goal, None);

    assert!(!progressed);
    assert_eq!(goal[0], ex, "DNF blowup must refuse fail-closed");
}

#[test]
fn all_or_nothing_keeps_partially_eliminable_assertion() {
    // (and (∃y. y > 5) (∃w. f(w) > 0)) — the first exists is eliminable, the
    // second is not; the whole ASSERTION must stay byte-for-byte unchanged.
    let mut terms = TermStore::new();
    let y = ivar(&mut terms, "y");
    let w = ivar(&mut terms, "w");
    let five = ci(&mut terms, 5);
    let zero = ci(&mut terms, 0);
    let g1 = terms.mk_gt(y, five);
    let ex1 = terms.mk_exists(vec![("y".to_string(), Sort::Int)], g1);
    let fw = terms.mk_app(Symbol::named("f"), vec![w], Sort::Int);
    let g2 = terms.mk_gt(fw, zero);
    let ex2 = terms.mk_exists(vec![("w".to_string(), Sort::Int)], g2);
    let both = terms.mk_and(vec![ex1, ex2]);

    let mut goal = vec![both];
    let progressed = deep_qe(&mut terms, &mut goal, None);

    assert!(!progressed);
    assert_eq!(
        goal[0], both,
        "partially eliminable assertion must be kept verbatim (all-or-nothing)"
    );
}

#[test]
fn budget_exhaustion_degrades_to_status_quo() {
    // More eliminable assertions than the per-apply elimination budget: the
    // first TEST_BUDGET eliminate, the rest keep their original TermIds
    // (each assertion here needs exactly one elimination and is distinct,
    // defeating the memo cache). Runs through the `deep_qe_with_budget` seam
    // with a small budget: the production cap is 8192 (#quantprod-g) and
    // materializing 8200 self-checked eliminations is minutes of pure test
    // overhead for the same exhaustion code path.
    const TEST_BUDGET: usize = 64;
    let mut terms = TermStore::new();
    let n = TEST_BUDGET + 8;
    let mut goal: Vec<TermId> = Vec::with_capacity(n);
    for i in 0..n {
        let y = ivar(&mut terms, &format!("y{i}"));
        let c = ci(&mut terms, i as i64);
        let body = terms.mk_gt(y, c);
        let name = format!("y{i}");
        goal.push(terms.mk_exists(vec![(name, Sort::Int)], body));
    }
    let originals = goal.clone();

    let progressed = super::deep_qe_with_budget(&mut terms, &mut goal, None, TEST_BUDGET);
    assert!(progressed);

    let eliminated = goal
        .iter()
        .filter(|&&a| !contains_quantifier(&terms, a))
        .count();
    let kept = goal.iter().zip(&originals).filter(|(a, o)| a == o).count();
    assert_eq!(
        eliminated, TEST_BUDGET,
        "exactly the budgeted number of assertions eliminate"
    );
    assert_eq!(
        kept, 8,
        "over-budget assertions keep their original TermIds"
    );
}

// ---------------------------------------------------------------------------
// Mixed-sort quantifier blocks (to_real bridge)
// ---------------------------------------------------------------------------

#[test]
fn eliminates_mixed_sort_block_to_true() {
    // ∀n:Int. ∃r:Real. r = to_real(n) — valid, must eliminate to `true`
    // (per-var sort dispatch: LW purifies the bridge for the inner Real var,
    // the outer Int var then peels a constant matrix).
    let mut terms = TermStore::new();
    let n = ivar(&mut terms, "n");
    let r = terms.mk_var("r", Sort::Real);
    let tr = terms.mk_to_real(n);
    let body = terms.mk_eq(r, tr);
    let ex = terms.mk_exists(vec![("r".to_string(), Sort::Real)], body);
    let fa = terms.mk_forall(vec![("n".to_string(), Sort::Int)], ex);

    let mut goal = vec![fa];
    let progressed = deep_qe(&mut terms, &mut goal, None);

    assert!(progressed, "mixed-sort block must eliminate");
    assert!(
        matches!(terms.get(goal[0]), TermData::Const(Constant::Bool(true))),
        "∀n.∃r. r = to_real(n) must fold to true, got {:?}",
        terms.get(goal[0])
    );
}

#[test]
fn eliminates_mixed_sort_block_twin_to_false() {
    // ∀n:Int. ∃r:Real. (r = to_real(n) ∧ r < to_real(n)) — the inner matrix
    // is unsatisfiable for every n, must eliminate to `false` (the
    // opposite-verdict twin of the block above, exercising the purified LW
    // pipeline plus its self-check with a genuine fresh variable).
    let mut terms = TermStore::new();
    let n = ivar(&mut terms, "n");
    let r = terms.mk_var("r", Sort::Real);
    let tr = terms.mk_to_real(n);
    let eq = terms.mk_eq(r, tr);
    let lt = terms.mk_lt(r, tr);
    let body = terms.mk_and(vec![eq, lt]);
    let ex = terms.mk_exists(vec![("r".to_string(), Sort::Real)], body);
    let fa = terms.mk_forall(vec![("n".to_string(), Sort::Int)], ex);

    let mut goal = vec![fa];
    let progressed = deep_qe(&mut terms, &mut goal, None);

    assert!(progressed);
    assert!(
        matches!(terms.get(goal[0]), TermData::Const(Constant::Bool(false))),
        "twin block must fold to false, got {:?}",
        terms.get(goal[0])
    );
}

#[test]
fn multi_to_real_block_stays_unknown_not_wrong() {
    // KNOWN LIMIT pin: ∀n. ∃r. (r = to_real(n) ∧ to_real(n) - to_real(m) ≤ 1/2)
    // — the inner Real elimination succeeds, but its output contains a Real
    // atom over two to_real bridges that the constructors don't fold, so the
    // OUTER Int peel must refuse (fragment screen) and keep the ORIGINAL
    // assertion byte-for-byte: status-quo unknown, never a wrong rewrite.
    let mut terms = TermStore::new();
    let n = ivar(&mut terms, "n");
    let m = ivar(&mut terms, "m");
    let r = terms.mk_var("r", Sort::Real);
    let trn = terms.mk_to_real(n);
    let trm = terms.mk_to_real(m);
    let eq = terms.mk_eq(r, trn);
    let diff = terms.mk_sub(vec![trn, trm]);
    let half = terms.mk_rational(num_rational::BigRational::new(
        BigInt::from(1),
        BigInt::from(2),
    ));
    let le = terms.mk_le(diff, half);
    let body = terms.mk_and(vec![eq, le]);
    let ex = terms.mk_exists(vec![("r".to_string(), Sort::Real)], body);
    let fa = terms.mk_forall(vec![("n".to_string(), Sort::Int)], ex);

    let mut goal = vec![fa];
    let original = goal[0];
    let progressed = deep_qe(&mut terms, &mut goal, None);

    assert!(!progressed, "all-or-nothing: no partial rewrite adopted");
    assert_eq!(goal[0], original, "original assertion kept byte-for-byte");
}

#[test]
fn shadowed_to_real_block_stays_unknown() {
    // With a user-shadowed (uninterpreted) to_real, the bridge must NOT be
    // purified — the whole block stays quantified (status quo).
    let mut terms = TermStore::new();
    let n = ivar(&mut terms, "n");
    let r = terms.mk_var("r", Sort::Real);
    let tr = terms.mk_to_real(n);
    let body = terms.mk_eq(r, tr);
    let ex = terms.mk_exists(vec![("r".to_string(), Sort::Real)], body);
    let fa = terms.mk_forall(vec![("n".to_string(), Sort::Int)], ex);
    terms.mark_to_real_shadowed();

    let mut goal = vec![fa];
    let original = goal[0];
    let progressed = deep_qe(&mut terms, &mut goal, None);

    assert!(!progressed);
    assert_eq!(goal[0], original);
}
