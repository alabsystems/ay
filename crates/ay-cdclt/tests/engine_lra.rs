// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The skeleton's claims, one test each: one search per check, splits inside
//! it, hints on every recorded clause, registration by term content.

use ay_cdclt::{Engine, EngineConfig, Guard, Verdict};
use ay_core::{Constant, Sort, Symbol, TermData, TermId, TermStore, TheoryLemmaKind};
use num_bigint::BigInt;
use num_rational::BigRational;

fn q(n: i64) -> BigRational {
    BigRational::from_integer(BigInt::from(n))
}

fn rational(terms: &TermStore, t: TermId) -> Option<BigRational> {
    match terms.get(t) {
        TermData::Const(Constant::Rational(r)) => Some(r.0.clone()),
        TermData::Const(Constant::Int(i)) => Some(BigRational::from_integer(i.clone())),
        _ => None,
    }
}

/// `x ≠ y` over the box [0,1]²: the simplex starts at x = y = 0, so the LRA
/// check must ask for a split. The split is decided inside the one search.
#[test]
fn disequality_split_stays_in_the_search() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let zero = terms.mk_rational(q(0));
    let one = terms.mk_rational(q(1));
    let eq = terms.mk_eq(x, y);
    let asserts = vec![
        terms.mk_not(eq),
        terms.mk_ge(x, zero),
        terms.mk_le(x, one),
        terms.mk_ge(y, zero),
        terms.mk_le(y, one),
    ];
    // The simplex's split; difference logic defines the equality instead.
    let mut engine = Engine::new(EngineConfig {
        difference_logic: false,
        ..EngineConfig::default()
    });
    for a in asserts {
        engine.assert(a);
    }
    assert_eq!(
        engine.check(&mut terms, &[], &Guard::new()).verdict,
        Verdict::Sat
    );
    let stats = engine.stats().clone();
    assert_eq!(stats.solve_calls, 1, "one ay-sat search per check (K1)");
    assert!(
        stats.minted_atoms >= 2,
        "split atoms minted in-search: {stats:?}"
    );
    assert!(stats.lemmas >= 1, "split lemma added in-search: {stats:?}");
    let vx = engine.model_value(&mut terms, x).expect("x has a value");
    let vy = engine.model_value(&mut terms, y).expect("y has a value");
    drop(engine);
    let (vx, vy) = (
        rational(&terms, vx).expect("x"),
        rational(&terms, vy).expect("y"),
    );
    assert_ne!(vx, vy);
    for v in [&vx, &vy] {
        assert!(*v >= q(0) && *v <= q(1), "value {v} outside the box");
    }
}

/// `x - y ≤ 0 ∧ y - x ≤ 0 ∧ x ≠ y` is unsat, again in one search.
#[test]
fn forced_equality_against_a_disequality_is_unsat() {
    for difference_logic in [true, false] {
        forced_equality_against_a_disequality(difference_logic);
    }
}

fn forced_equality_against_a_disequality(difference_logic: bool) {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let zero = terms.mk_rational(q(0));
    let xy = terms.mk_sub(vec![x, y]);
    let yx = terms.mk_sub(vec![y, x]);
    let eq = terms.mk_eq(x, y);
    let asserts = vec![
        terms.mk_le(xy, zero),
        terms.mk_le(yx, zero),
        terms.mk_not(eq),
    ];
    let mut engine = Engine::new(EngineConfig {
        difference_logic,
        ..EngineConfig::default()
    });
    for a in asserts {
        engine.assert(a);
    }
    assert_eq!(
        engine.check(&mut terms, &[], &Guard::new()).verdict,
        Verdict::Unsat
    );
    assert_eq!(engine.stats().solve_calls, 1);
}

/// With recording on, every clause the kernel adds carries a hint, and the
/// split lemma is tagged with the kind the checker validates (P1).
#[test]
fn every_recorded_clause_has_a_hint() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let zero = terms.mk_rational(q(0));
    let one = terms.mk_rational(q(1));
    let two = terms.mk_rational(q(2));
    let eq = terms.mk_eq(x, y);
    let sum = terms.mk_add(vec![x, y]);
    let asserts = vec![
        terms.mk_not(eq),
        terms.mk_ge(x, zero),
        terms.mk_ge(y, zero),
        terms.mk_le(x, one),
        terms.mk_le(y, one),
        terms.mk_ge(sum, two),
    ];
    let mut engine = Engine::new(EngineConfig {
        record_proofs: true,
        ..EngineConfig::default()
    });
    for a in asserts {
        engine.assert(a);
    }
    let outcome = engine.check(&mut terms, &[], &Guard::new());
    assert_eq!(outcome.verdict, Verdict::Unsat);
    let steps = outcome.proof.as_ref().expect("recorded").steps();
    assert!(!steps.is_empty(), "an unsat answer derived clauses");
    assert!(steps.iter().all(|s| !s.clause.is_empty()));
    assert!(
        steps
            .iter()
            .any(|s| s.hint.kind == TheoryLemmaKind::ArithDisequalitySplit),
        "the split lemma is recorded with its kind: {steps:?}"
    );
}

/// An atom no plug-in owns ends the check before the search (H2), named.
#[test]
fn unowned_atoms_are_named_before_the_search() {
    let mut terms = TermStore::new();
    let n = terms.mk_var("n", Sort::Int);
    let atom = terms.mk_app(Symbol::indexed("divisible", vec![2]), vec![n], Sort::Bool);
    let mut engine = Engine::new(EngineConfig::default());
    engine.assert(atom);
    let outcome = engine.check(&mut terms, &[], &Guard::new());
    match (outcome.verdict, outcome.reason.unwrap_or_default()) {
        (Verdict::Unknown, reason) => assert!(reason.contains("no plug-in"), "{reason}"),
        other => panic!("expected unknown, got {other:?}"),
    }
    assert_eq!(engine.stats().solve_calls, 0);
}

/// Int and Real atoms in one check need one LIRA tableau; the kernel names
/// that before the search rather than run two tableaux that share nothing.
#[test]
fn mixed_int_and_real_atoms_are_named_before_the_search() {
    let mut terms = TermStore::new();
    let n = terms.mk_var("n", Sort::Int);
    let x = terms.mk_var("x", Sort::Real);
    let three = terms.mk_int(BigInt::from(3));
    let half = terms.mk_rational(BigRational::new(BigInt::from(1), BigInt::from(2)));
    let asserts = vec![terms.mk_le(n, three), terms.mk_le(x, half)];
    let mut engine = Engine::new(EngineConfig::default());
    for a in asserts {
        engine.assert(a);
    }
    let outcome = engine.check(&mut terms, &[], &Guard::new());
    match (outcome.verdict, outcome.reason.unwrap_or_default()) {
        (Verdict::Unknown, reason) => assert!(reason.contains("LIRA"), "{reason}"),
        other => panic!("expected unknown, got {other:?}"),
    }
    assert_eq!(engine.stats().solve_calls, 0);
}

/// `1 ≤ 2n ≤ 1` over Int: the simplex says n = 1/2, and branch and bound
/// refutes both sides inside the one search (design §3.5, `NeedSplit`).
#[test]
fn branch_and_bound_stays_in_the_search() {
    let mut terms = TermStore::new();
    let n = terms.mk_var("n", Sort::Int);
    let two = terms.mk_int(BigInt::from(2));
    let one = terms.mk_int(BigInt::from(1));
    let twice = terms.mk_mul(vec![two, n]);
    let above = terms.mk_ge(twice, one);
    let below = terms.mk_le(twice, one);
    let mut engine = Engine::new(EngineConfig {
        record_proofs: true,
        ..EngineConfig::default()
    });
    engine.assert(above);
    engine.assert(below);
    let outcome = engine.check(&mut terms, &[], &Guard::new());
    assert_eq!(outcome.verdict, Verdict::Unsat);
    let stats = engine.stats().clone();
    assert_eq!(stats.solve_calls, 1, "{stats:?}");
    assert!(stats.minted_atoms >= 2, "branch atoms minted: {stats:?}");
    assert!(
        outcome
            .proof
            .as_ref()
            .expect("recorded")
            .steps()
            .iter()
            .any(|s| s.hint.kind == TheoryLemmaKind::IntBoundsTautology),
        "the branch lemma is recorded with its kind"
    );
}

/// A binary `=` over Booleans and an `ite` over Booleans are Boolean
/// structure the encoding defines completely, not atoms needing an owner.
#[test]
fn boolean_equalities_are_structure() {
    let mut terms = TermStore::new();
    let p = terms.mk_var("p", Sort::Bool);
    let r = terms.mk_var("r", Sort::Bool);
    let x = terms.mk_var("x", Sort::Real);
    let one = terms.mk_rational(q(1));
    let atom = terms.mk_le(x, one);
    let iff = terms.mk_app(Symbol::named("="), vec![p, atom], Sort::Bool);
    let choice = terms.mk_ite(r, p, atom);
    let mut engine = Engine::new(EngineConfig::default());
    engine.assert(iff);
    engine.assert(choice);
    assert_eq!(
        engine.check(&mut terms, &[], &Guard::new()).verdict,
        Verdict::Sat
    );
    assert_eq!(engine.stats().solve_calls, 1);
}

/// Pure Boolean input needs no plug-in at all.
#[test]
fn propositional_input_needs_no_plugin() {
    let mut terms = TermStore::new();
    let p = terms.mk_var("p", Sort::Bool);
    let not_p = terms.mk_not(p);
    let mut engine = Engine::new(EngineConfig::default());
    engine.assert(p);
    assert_eq!(
        engine.check(&mut terms, &[], &Guard::new()).verdict,
        Verdict::Sat
    );
    engine.assert(not_p);
    assert_eq!(
        engine.check(&mut terms, &[], &Guard::new()).verdict,
        Verdict::Unsat
    );
}

/// Operators no plug-in owns, inside an arithmetic atom, are named before
/// the search (H2), not discovered as an `unknown` after it.
#[test]
fn unowned_operators_inside_atoms_are_named_before_the_search() {
    let cases: [(&str, fn(&mut TermStore, TermId, TermId) -> TermId); 4] = [
        ("nonlinear", |t, x, y| t.mk_mul(vec![x, y])),
        // An uninterpreted function is the hub's (`engine_hub.rs`).
        ("`to_int`", |t, x, _| {
            t.mk_app(Symbol::named("to_int"), vec![x], Sort::Int)
        }),
        ("`div`", |t, x, y| t.mk_intdiv(x, y)),
        ("`div`", |t, x, _| {
            let zero = t.mk_int(BigInt::from(0));
            t.mk_app(Symbol::named("div"), vec![x, zero], Sort::Int)
        }),
    ];
    for (named, build) in cases {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::Int);
        let y = terms.mk_var("y", Sort::Int);
        let lhs = build(&mut terms, x, y);
        let three = terms.mk_int(BigInt::from(3));
        let atom = terms.mk_le(lhs, three);
        let mut engine = Engine::new(EngineConfig::default());
        engine.assert(atom);
        let outcome = engine.check(&mut terms, &[], &Guard::new());
        match (outcome.verdict, outcome.reason.unwrap_or_default()) {
            (Verdict::Unknown, reason) => {
                assert!(reason.contains(named), "{named}: {reason}");
            }
            other => panic!("{named}: expected unknown, got {other:?}"),
        }
        assert_eq!(engine.stats().solve_calls, 0, "{named}");
    }
}

/// Divisibility in the search: `x = 3q + 1` and `x mod 3 = 0` cannot both
/// hold, and the definitions of `mod` refute it in the one search.
#[test]
fn divisibility_is_refuted_in_the_search() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let q = terms.mk_var("q", Sort::Int);
    let (one, three, zero) = (
        terms.mk_int(BigInt::from(1)),
        terms.mk_int(BigInt::from(3)),
        terms.mk_int(BigInt::from(0)),
    );
    let three_q = terms.mk_mul(vec![three, q]);
    let rhs = terms.mk_add(vec![three_q, one]);
    let shape = terms.mk_eq(x, rhs);
    let rem = terms.mk_mod(x, three);
    let divisible = terms.mk_eq(rem, zero);
    let mut engine = Engine::new(EngineConfig::default());
    engine.assert(shape);
    engine.assert(divisible);
    assert_eq!(
        engine.check(&mut terms, &[], &Guard::new()).verdict,
        Verdict::Unsat
    );
    let stats = engine.stats().clone();
    assert_eq!(stats.solve_calls, 1, "{stats:?}");
    assert!(
        stats.definitions >= 3,
        "the mod definition entered the search: {stats:?}"
    );
}

/// A check whose every atom is a difference atom runs the arithmetic
/// plug-in's difference-logic sub-module; one other atom keeps the simplex.
#[test]
fn difference_logic_is_chosen_by_content() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let diff = terms.mk_sub(vec![x, y]);
    let one = terms.mk_rational(q(1));
    let two = terms.mk_rational(q(2));
    let bound = terms.mk_lt(diff, one);
    let reverse = terms.mk_sub(vec![y, x]);
    let other = terms.mk_le(reverse, one);
    let twice = terms.mk_mul(vec![two, x]);
    let scaled = terms.mk_add(vec![twice, y]);
    let general = terms.mk_le(scaled, one);
    let mut engine = Engine::new(EngineConfig::default());
    engine.assert(bound);
    engine.assert(other);
    assert_eq!(
        engine.check(&mut terms, &[], &Guard::new()).verdict,
        Verdict::Sat
    );
    assert_eq!(engine.plugin_names(), vec!["dl-real"]);
    engine.assert(general);
    assert_eq!(
        engine.check(&mut terms, &[], &Guard::new()).verdict,
        Verdict::Sat
    );
    assert_eq!(engine.plugin_names(), vec!["lra"]);
}

/// `2n = 1` over Int: the GCD test refutes the equality when it is
/// internalized (a unit definition), before any branching.
#[test]
fn gcd_refutes_an_equality_without_branching() {
    let mut terms = TermStore::new();
    let n = terms.mk_var("n", Sort::Int);
    let m = terms.mk_var("m", Sort::Int);
    let two = terms.mk_int(BigInt::from(2));
    let four = terms.mk_int(BigInt::from(4));
    let one = terms.mk_int(BigInt::from(1));
    let twice = terms.mk_mul(vec![two, n]);
    let fourfold = terms.mk_mul(vec![four, m]);
    let sum = terms.mk_add(vec![twice, fourfold]);
    let atom = terms.mk_eq(sum, one);
    let mut engine = Engine::new(EngineConfig {
        record_proofs: true,
        ..EngineConfig::default()
    });
    engine.assert(atom);
    let outcome = engine.check(&mut terms, &[], &Guard::new());
    assert_eq!(outcome.verdict, Verdict::Unsat);
    let stats = engine.stats().clone();
    assert_eq!(stats.solve_calls, 1, "{stats:?}");
    assert!(stats.definitions >= 1, "{stats:?}");
    assert!(
        !outcome
            .proof
            .as_ref()
            .expect("recorded")
            .steps()
            .iter()
            .any(|s| s.hint.kind == TheoryLemmaKind::IntBoundsTautology),
        "no branching was needed"
    );
}

/// A Real atom whose numeral is Int-sorted and comes first, `3 < x` over a
/// Real `x`, belongs to real arithmetic: routed by that `3` it would be
/// tightened as an integer bound (`x ≥ 4`) and `x = 3.5` would be lost.
#[test]
fn a_leading_int_numeral_does_not_make_a_real_atom_integer() {
    for difference_logic in [true, false] {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::Real);
        let three = terms.mk_int(BigInt::from(3));
        let four = terms.mk_rational(q(4));
        let above = terms.mk_app(Symbol::named("<"), vec![three, x], Sort::Bool);
        let below = terms.mk_lt(x, four);
        let mut engine = Engine::new(EngineConfig {
            difference_logic,
            ..EngineConfig::default()
        });
        engine.assert(above);
        engine.assert(below);
        assert_eq!(
            engine.check(&mut terms, &[], &Guard::new()).verdict,
            Verdict::Sat,
            "dl {difference_logic}"
        );
        let expected = if difference_logic { "dl-real" } else { "lra" };
        assert_eq!(engine.plugin_names(), vec![expected]);
    }
}

/// The LRA plug-in adds the bound axioms between the bound atoms of one
/// term, each checked T-valid first: `x ≤ 1 ∧ ¬(x ≤ 3)` stays refuted, and
/// disjunctions of bounds on one term get axioms and a model that satisfies
/// them. Bounds alone are difference atoms, which the difference-logic
/// sub-module would take, so the test keeps the simplex.
#[test]
fn bound_axioms_order_the_atoms_of_one_term() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let [c0, c1, c2, c3, c5, c6] = [0, 1, 2, 3, 5, 6].map(|n| terms.mk_rational(q(n)));
    let le1 = terms.mk_le(x, c1);
    let le3 = terms.mk_le(x, c3);
    let not_le3 = terms.mk_not(le3);
    let mut engine = Engine::new(EngineConfig {
        difference_logic: false,
        ..EngineConfig::default()
    });
    engine.assert(le1);
    engine.assert(not_le3);
    assert_eq!(
        engine.check(&mut terms, &[], &Guard::new()).verdict,
        Verdict::Unsat
    );
    drop(engine);

    let le1 = terms.mk_le(x, c1);
    let ge5 = terms.mk_ge(x, c5);
    let ge2 = terms.mk_ge(x, c2);
    let le0 = terms.mk_le(x, c0);
    let le6 = terms.mk_le(x, c6);
    let asserts = vec![
        terms.mk_or(vec![le1, ge5]),
        terms.mk_or(vec![ge2, le0]),
        le6,
    ];
    let mut engine = Engine::new(EngineConfig {
        difference_logic: false,
        ..EngineConfig::default()
    });
    for &a in &asserts {
        engine.assert(a);
    }
    assert_eq!(
        engine.check(&mut terms, &[], &Guard::new()).verdict,
        Verdict::Sat
    );
    assert_eq!(engine.plugin_names(), vec!["lra"]);
    // No disequality, so no split: every lemma here is a bound axiom.
    assert!(engine.stats().lemmas >= 1, "{:?}", engine.stats());
    assert_eq!(
        engine.check_model(&mut terms, &asserts),
        ay_cdclt::ModelVerdict::Satisfied
    );
}
