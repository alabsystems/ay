// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The hub's claims, one test each: congruence inside the one search,
//! `new_eq` into arithmetic, model-based combination out of it, Boolean
//! arguments, internalized `distinct` and term-level `ite`.

use ay_cdclt::{Engine, EngineConfig, Guard, ModelVerdict, Verdict};
use ay_core::{Sort, Symbol, TermId, TermStore};
use num_bigint::BigInt;
use num_rational::BigRational;

fn q(n: i64) -> BigRational {
    BigRational::from_integer(BigInt::from(n))
}

fn app(terms: &mut TermStore, f: &str, args: Vec<TermId>, sort: Sort) -> TermId {
    terms.mk_app(Symbol::named(f), args, sort)
}

/// A check's verdict, with the unknown reason.
#[derive(Debug, PartialEq, Eq)]
enum Out {
    Sat,
    Unsat,
    Unknown(String),
}

fn run_with(
    terms: &mut TermStore,
    asserts: &[TermId],
    cfg: EngineConfig,
) -> (Out, ay_cdclt::EngineStats, Option<ModelVerdict>) {
    let mut engine = Engine::new(cfg);
    for &a in asserts {
        engine.assert(a);
    }
    let outcome = engine.check(terms, &[], &Guard::new());
    let out = match outcome.verdict {
        Verdict::Sat => Out::Sat,
        Verdict::Unsat => Out::Unsat,
        Verdict::Unknown => Out::Unknown(outcome.reason.clone().unwrap_or_default()),
    };
    let model = (out == Out::Sat).then(|| engine.check_model(terms, asserts));
    (out, outcome.stats, model)
}

/// Every hub test runs with and without the relevancy filter (KC21): the
/// verdict must not change.
fn run(
    terms: &mut TermStore,
    asserts: &[TermId],
) -> (Out, ay_cdclt::EngineStats, Option<ModelVerdict>) {
    let relevant = run_with(
        terms,
        asserts,
        EngineConfig {
            hub_relevancy: true,
            ..EngineConfig::default()
        },
    );
    let plain = run_with(terms, asserts, EngineConfig::default());
    assert_eq!(relevant.0, plain.0, "relevancy changed the verdict");
    assert_eq!(relevant.2, plain.2, "relevancy changed the model check");
    plain
}

fn u() -> Sort {
    Sort::Uninterpreted("U".to_string())
}

/// `a = b ∧ b = c ∧ f(a) ≠ f(c)`: congruence through a chain, one search.
#[test]
fn congruence_refutes_in_one_search() {
    let mut terms = TermStore::new();
    let [a, b, c] = ["a", "b", "c"].map(|n| terms.mk_var(n, u()));
    let fa = app(&mut terms, "f", vec![a], u());
    let fc = app(&mut terms, "f", vec![c], u());
    let ab = terms.mk_eq(a, b);
    let bc = terms.mk_eq(b, c);
    let fafc = terms.mk_eq(fa, fc);
    let not_fafc = terms.mk_not(fafc);
    let (outcome, stats, _) = run(&mut terms, &[ab, bc, not_fafc]);
    assert_eq!(outcome, Out::Unsat);
    assert_eq!(stats.solve_calls, 1, "{stats:?}");
    assert!(stats.hub_merges > 0, "{stats:?}");
}

/// The same with a satisfiable twist; the model is a function.
#[test]
fn congruent_sat_models_are_functions() {
    let mut terms = TermStore::new();
    let [a, b, c] = ["a", "b", "c"].map(|n| terms.mk_var(n, u()));
    let fa = app(&mut terms, "f", vec![a], u());
    let fb = app(&mut terms, "f", vec![b], u());
    let ab = terms.mk_eq(a, b);
    let ac = terms.mk_eq(a, c);
    let fafb = terms.mk_eq(fa, fb);
    let either = terms.mk_or(vec![ab, ac]);
    let not_ac = terms.mk_not(ac);
    let (outcome, _, model) = run(&mut terms, &[either, not_ac, fafb]);
    assert_eq!(outcome, Out::Sat);
    assert_eq!(model, Some(ModelVerdict::Satisfied));
}

/// `x ≤ y ∧ y ≤ x ∧ p(x) ∧ ¬p(y)` over reals: LRA alone knows `x = y`, and
/// it has no disequality to guess equalities for; the hub learns `x = y`
/// through model-based combination (H3) and refutes.
#[test]
fn arithmetic_equalities_reach_the_hub_through_combination() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let px = app(&mut terms, "p", vec![x], Sort::Bool);
    let py = app(&mut terms, "p", vec![y], Sort::Bool);
    let le1 = terms.mk_le(x, y);
    let le2 = terms.mk_le(y, x);
    let not_py = terms.mk_not(py);
    let (outcome, stats, _) = run(&mut terms, &[le1, le2, px, not_py]);
    assert_eq!(outcome, Out::Unsat);
    assert_eq!(stats.solve_calls, 1, "{stats:?}");
    assert!(stats.combination_equalities > 0, "{stats:?}");

    // With a function instead of a predicate LRA's own equality guess (it
    // holds the disequality) gets there too; either way, one search.
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let fx = app(&mut terms, "f", vec![x], Sort::Real);
    let fy = app(&mut terms, "f", vec![y], Sort::Real);
    let le1 = terms.mk_le(x, y);
    let le2 = terms.mk_le(y, x);
    let eq = terms.mk_eq(fx, fy);
    let ne = terms.mk_not(eq);
    let (outcome, stats, _) = run(&mut terms, &[le1, le2, ne]);
    assert_eq!(outcome, Out::Unsat);
    assert_eq!(stats.solve_calls, 1, "{stats:?}");

    // And satisfiable when x < y is possible: the model separates them.
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let px = app(&mut terms, "p", vec![x], Sort::Bool);
    let py = app(&mut terms, "p", vec![y], Sort::Bool);
    let le1 = terms.mk_le(x, y);
    let not_py = terms.mk_not(py);
    let (outcome, _, model) = run(&mut terms, &[le1, px, not_py]);
    assert_eq!(outcome, Out::Sat);
    assert_eq!(model, Some(ModelVerdict::Satisfied));
}

/// Tight bounds reach the hub over a pre-existing equality atom without
/// model-based combination: `5 ≤ f(x) ≤ 5 ∧ 5 ≤ f(y) ≤ 5 ∧
/// ((f(x) = f(y)) ∨ q) ∧ q ∧ p(f(x)) ∧ ¬p(f(y))`. The equality atom is
/// arithmetic-shaped, so ordinary LRA atom propagation sets it from the
/// pins and the hub refutes by congruence in-search. This pins down why
/// Nelson-Oppen sharing restricted to pre-existing atoms needs no extra
/// machinery (DR-AY-CDCLT-EQ-SHARE-EXISTING-ATOM-SUBSUMED-20261114):
/// the only sharing that adds information mints fresh atoms, and that
/// form was measured to poison sat searches
/// (DR-AY-CDCLT-EQ-SHARE-REJECTED-20261114).
#[test]
fn tight_bound_equalities_reach_hub_without_combination() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let qvar = terms.mk_var("q", Sort::Bool);
    let fx = app(&mut terms, "f", vec![x], Sort::Real);
    let fy = app(&mut terms, "f", vec![y], Sort::Real);
    let pfx = app(&mut terms, "p", vec![fx], Sort::Bool);
    let pfy = app(&mut terms, "p", vec![fy], Sort::Bool);
    let eq = terms.mk_eq(fx, fy);
    let either = terms.mk_or(vec![eq, qvar]);
    let five = terms.mk_rational(q(5));
    let fx_ge = terms.mk_ge(fx, five);
    let fx_le = terms.mk_le(fx, five);
    let fy_ge = terms.mk_ge(fy, five);
    let fy_le = terms.mk_le(fy, five);
    // A sum atom keeps the arithmetic family on the simplex plug-in
    // (pure var-vs-constant bounds would take the difference-logic lane).
    let sum = terms.mk_add(vec![fx, fy]);
    let twenty = terms.mk_rational(q(20));
    let sum_le = terms.mk_le(sum, twenty);
    let not_pfy = terms.mk_not(pfy);
    let (outcome, stats, _) = run(
        &mut terms,
        &[
            fx_ge, fx_le, fy_ge, fy_le, sum_le, either, qvar, pfx, not_pfy,
        ],
    );
    assert_eq!(outcome, Out::Unsat);
    assert_eq!(stats.solve_calls, 1, "{stats:?}");
    assert_eq!(
        stats.combination_equalities, 0,
        "existing-atom propagation must refute before H3 combination: {stats:?}"
    );
}

/// `a = b ∧ f(a) ≤ 0 ∧ f(b) ≥ 1` with `f : U -> Real`: the hub's merge
/// reaches LRA as `new_eq` and refutes.
#[test]
fn hub_equalities_reach_arithmetic_as_new_eq() {
    let mut terms = TermStore::new();
    let [a, b] = ["a", "b"].map(|n| terms.mk_var(n, u()));
    let fa = app(&mut terms, "f", vec![a], Sort::Real);
    let fb = app(&mut terms, "f", vec![b], Sort::Real);
    let zero = terms.mk_rational(q(0));
    let one = terms.mk_rational(q(1));
    let ab = terms.mk_eq(a, b);
    let lo = terms.mk_le(fa, zero);
    let hi = terms.mk_ge(fb, one);
    let (outcome, stats, _) = run(&mut terms, &[ab, lo, hi]);
    assert_eq!(outcome, Out::Unsat);
    assert!(stats.new_eqs > 0, "{stats:?}");
    // Without `a = b` it is satisfiable, and the model separates a from b.
    let mut terms = TermStore::new();
    let [a, b] = ["a", "b"].map(|n| terms.mk_var(n, u()));
    let fa = app(&mut terms, "f", vec![a], Sort::Real);
    let fb = app(&mut terms, "f", vec![b], Sort::Real);
    let zero = terms.mk_rational(q(0));
    let one = terms.mk_rational(q(1));
    let lo = terms.mk_le(fa, zero);
    let hi = terms.mk_ge(fb, one);
    let (outcome, _, model) = run(&mut terms, &[lo, hi]);
    assert_eq!(outcome, Out::Sat);
    assert_eq!(model, Some(ModelVerdict::Satisfied));
}

/// Boolean arguments: `p ∧ q ∧ g(p) ≠ g(q)` is unsat, `g(p ∧ r) ≠ g(true)`
/// forces `p ∧ r` false.
#[test]
fn boolean_arguments_join_true_and_false() {
    let mut terms = TermStore::new();
    let p = terms.mk_var("p", Sort::Bool);
    let r = terms.mk_var("r", Sort::Bool);
    let gp = app(&mut terms, "g", vec![p], u());
    let gr = app(&mut terms, "g", vec![r], u());
    let ne = {
        let eq = terms.mk_eq(gp, gr);
        terms.mk_not(eq)
    };
    let (outcome, _, _) = run(&mut terms, &[p, r, ne]);
    assert_eq!(outcome, Out::Unsat);

    let mut terms = TermStore::new();
    let p = terms.mk_var("p", Sort::Bool);
    let r = terms.mk_var("r", Sort::Bool);
    let conj = terms.mk_and(vec![p, r]);
    let t = terms.mk_bool(true);
    let gconj = app(&mut terms, "g", vec![conj], u());
    let gt = app(&mut terms, "g", vec![t], u());
    let ne = {
        let eq = terms.mk_eq(gconj, gt);
        terms.mk_not(eq)
    };
    let (outcome, _, model) = run(&mut terms, &[ne, p]);
    assert_eq!(outcome, Out::Sat);
    assert_eq!(model, Some(ModelVerdict::Satisfied));
    let mut terms2 = TermStore::new();
    let p = terms2.mk_var("p", Sort::Bool);
    let r = terms2.mk_var("r", Sort::Bool);
    let conj = terms2.mk_and(vec![p, r]);
    let t = terms2.mk_bool(true);
    let gconj = app(&mut terms2, "g", vec![conj], u());
    let gt = app(&mut terms2, "g", vec![t], u());
    let ne = {
        let eq = terms2.mk_eq(gconj, gt);
        terms2.mk_not(eq)
    };
    let (outcome, _, _) = run(&mut terms2, &[ne, p, r]);
    assert_eq!(outcome, Out::Unsat);
}

/// `distinct` over four constants of a sort with `f` mapping them into two
/// values, one of them forced: internalized pairwise, decided in one search.
#[test]
fn distinct_and_term_ite_are_internalized() {
    let mut terms = TermStore::new();
    let cs: Vec<TermId> = (0..3).map(|i| terms.mk_var(format!("c{i}"), u())).collect();
    let d = terms.mk_app(Symbol::named("distinct"), cs.clone(), Sort::Bool);
    let fc: Vec<TermId> = cs
        .iter()
        .map(|&c| app(&mut terms, "f", vec![c], u()))
        .collect();
    let e01 = terms.mk_eq(fc[0], fc[1]);
    let e12 = terms.mk_eq(fc[1], fc[2]);
    let (outcome, _, model) = run(&mut terms, &[d, e01, e12]);
    assert_eq!(outcome, Out::Sat);
    assert_eq!(model, Some(ModelVerdict::Satisfied));

    // (ite c a b) = a ∧ ¬c ∧ a ≠ b is unsat; the ite is named, not lifted.
    let mut terms = TermStore::new();
    let c = terms.mk_var("c", Sort::Bool);
    let a = terms.mk_var("a", u());
    let b = terms.mk_var("b", u());
    let ite = terms.mk_ite(c, a, b);
    let fi = app(&mut terms, "f", vec![ite], u());
    let fa = app(&mut terms, "f", vec![a], u());
    let e = terms.mk_eq(fi, fa);
    let not_e = terms.mk_not(e);
    let not_c = terms.mk_not(c);
    let ab = terms.mk_eq(a, b);
    let (outcome, _, _) = run(&mut terms, &[not_e, not_c, ab]);
    assert_eq!(outcome, Out::Unsat);
}

/// An operator no plug-in owns inside an arithmetic atom is named before
/// the search (H2), even when the rest of the check is uninterpreted.
#[test]
fn unowned_operators_inside_atoms_are_named_before_the_search() {
    let mut terms = TermStore::new();
    let n = terms.mk_var("n", Sort::Int);
    let one = terms.mk_int(BigInt::from(1));
    let fx = app(&mut terms, "f", vec![n], Sort::Int);
    let square = terms.mk_app(Symbol::named("*"), vec![n, fx], Sort::Int);
    let atom = terms.mk_le(square, one);
    let (outcome, stats, _) = run(&mut terms, &[atom]);
    match outcome {
        Out::Unknown(reason) => assert!(reason.contains("nonlinear"), "{reason}"),
        other => panic!("expected unknown, got {other:?}"),
    }
    assert_eq!(stats.solve_calls, 0);
}

/// A term-level `ite` under an application is named before the search; the
/// exact model check still judges the authored formula: `f(ite(c, x, y))`
/// takes the value the engine gave `f` of the name.
#[test]
fn the_model_check_sees_through_named_ites() {
    let mut terms = TermStore::new();
    let c = terms.mk_var("c", Sort::Bool);
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let ite = terms.mk_ite(c, x, y);
    let fi = app(&mut terms, "f", vec![ite], Sort::Int);
    let fx = app(&mut terms, "f", vec![x], Sort::Int);
    let five = terms.mk_int(BigInt::from(5));
    let one = terms.mk_int(BigInt::from(1));
    let e = terms.mk_eq(fi, five);
    let x1 = terms.mk_eq(x, one);
    let ne = {
        let eq = terms.mk_eq(fx, five);
        terms.mk_not(eq)
    };
    // f(x) ≠ 5 forces ¬c, so y ≠ x and f(y) = 5.
    let (outcome, _, model) = run(&mut terms, &[e, x1, ne]);
    assert_eq!(outcome, Out::Sat);
    assert_eq!(model, Some(ModelVerdict::Satisfied));
}

/// The diamond: `(x_i = y_i ∧ y_i = x_{i+1}) ∨ (x_i = z_i ∧ z_i = x_{i+1})`
/// for every `i < n`, and `x_0 ≠ x_n`. Without an atom naming `x_i = x_j`
/// every one of the `2^n` paths is a separate conflict; dynamic
/// transitivity lemmas name the shortcuts.
#[test]
fn diamonds_are_cut_by_transitivity_lemmas() {
    let n = 16;
    let mut terms = TermStore::new();
    let x: Vec<TermId> = (0..=n)
        .map(|i| terms.mk_var(format!("x{i}"), u()))
        .collect();
    let mut asserts = Vec::new();
    for i in 0..n {
        let y = terms.mk_var(format!("y{i}"), u());
        let z = terms.mk_var(format!("z{i}"), u());
        let up = [terms.mk_eq(x[i], y), terms.mk_eq(y, x[i + 1])];
        let down = [terms.mk_eq(x[i], z), terms.mk_eq(z, x[i + 1])];
        let (up, down) = (terms.mk_and(up.to_vec()), terms.mk_and(down.to_vec()));
        asserts.push(terms.mk_or(vec![up, down]));
    }
    let ends = terms.mk_eq(x[0], x[n]);
    asserts.push(terms.mk_not(ends));
    let (outcome, stats, _) = run(&mut terms, &asserts);
    assert_eq!(outcome, Out::Unsat);
    assert!(stats.transitivity_lemmas > 0, "{stats:?}");
}
