// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use std::collections::HashMap;

use ay_core::{Symbol, TermStore};
use num_rational::BigRational;

use super::*;
use crate::{evaluate_term, EvalOutcome, ModelView};

struct MapModel(HashMap<TermId, ModelValue>);

impl ModelView for MapModel {
    fn leaf_value(&self, term: TermId) -> Option<ModelValue> {
        self.0.get(&term).cloned()
    }
}

fn app(terms: &mut TermStore, name: &str, args: &[TermId]) -> TermId {
    terms.mk_app(Symbol::named(name), args, Sort::Bool)
}

fn eq(terms: &mut TermStore, a: TermId, b: TermId) -> TermId {
    app(terms, "=", &[a, b])
}

fn neq(terms: &mut TermStore, a: TermId, b: TermId) -> TermId {
    let atom = eq(terms, a, b);
    terms.mk_not_raw(atom)
}

fn real(value: i64) -> ModelValue {
    ModelValue::Real(BigRational::from_integer(BigInt::from(value)))
}

fn exists(terms: &mut TermStore, names: &[&str], sort: &Sort, body: TermId) -> TermId {
    let vars = names
        .iter()
        .map(|n| ((*n).to_string(), sort.clone()))
        .collect();
    terms.mk_exists(vars, body)
}

fn forall(terms: &mut TermStore, names: &[&str], sort: &Sort, body: TermId) -> TermId {
    let vars = names
        .iter()
        .map(|n| ((*n).to_string(), sort.clone()))
        .collect();
    terms.mk_forall(vars, body)
}

fn decide(terms: &TermStore, model: &MapModel, term: TermId) -> Option<bool> {
    match evaluate_term(terms, model, term) {
        EvalOutcome::Value(ModelValue::Bool(value)) => Some(value),
        _ => None,
    }
}

/// `∃x y. x≠y ∧ ∃z. z≠x ∧ z≠y` is TRUE over the reals: three distinct values
/// exist. The closed sentence has no comparison term at the outer level, so
/// every witness is a fresh value.
#[test]
fn closed_three_distinct_reals_exist() {
    let mut terms = TermStore::new();
    let sort = Sort::Real;
    let x = terms.mk_var("x", sort.clone());
    let y = terms.mk_var("y", sort.clone());
    let z = terms.mk_var("z", sort.clone());
    let xy = neq(&mut terms, x, y);
    let zx = neq(&mut terms, z, x);
    let zy = neq(&mut terms, z, y);
    let inner_body = app(&mut terms, "and", &[zx, zy]);
    let inner = exists(&mut terms, &["z"], &sort, inner_body);
    let body = app(&mut terms, "and", &[xy, inner]);
    let root = exists(&mut terms, &["x", "y"], &sort, body);
    let model = MapModel(HashMap::new());
    assert_eq!(decide(&terms, &model, root), Some(true));
}

/// `∀x y z. x=y ∨ y=z ∨ x=z` is FALSE over the (infinite) reals, and the
/// planner must find the three-fresh-values counterexample.
#[test]
fn closed_pigeonhole_universal_is_false_over_an_infinite_carrier() {
    let mut terms = TermStore::new();
    let sort = Sort::Real;
    let x = terms.mk_var("x", sort.clone());
    let y = terms.mk_var("y", sort.clone());
    let z = terms.mk_var("z", sort.clone());
    let xy = eq(&mut terms, x, y);
    let yz = eq(&mut terms, y, z);
    let xz = eq(&mut terms, x, z);
    let body = app(&mut terms, "or", &[xy, yz, xz]);
    let root = forall(&mut terms, &["x", "y", "z"], &sort, body);
    let model = MapModel(HashMap::new());
    assert_eq!(decide(&terms, &model, root), Some(false));
}

/// A free constant joins the support: `∀x. x = c` is false (a fresh value
/// differs from `c`), `∃x. x = c` is true (the support value itself), and
/// `∃x. x≠a ∧ x≠b` is true through a fresh value above both.
#[test]
fn free_constants_enter_the_support() {
    let mut terms = TermStore::new();
    let sort = Sort::Real;
    let x = terms.mk_var("x", sort.clone());
    let c = terms.mk_var("c", sort.clone());
    let a = terms.mk_var("a", sort.clone());
    let b = terms.mk_var("b", sort.clone());
    let xc = eq(&mut terms, x, c);
    let all_c = forall(&mut terms, &["x"], &sort, xc);
    let some_c = exists(&mut terms, &["x"], &sort, xc);
    let xa = neq(&mut terms, x, a);
    let xb = neq(&mut terms, x, b);
    let avoid_body = app(&mut terms, "and", &[xa, xb]);
    let avoid = exists(&mut terms, &["x"], &sort, avoid_body);
    let model = MapModel(HashMap::from([(c, real(5)), (a, real(1)), (b, real(2))]));
    assert_eq!(decide(&terms, &model, all_c), Some(false));
    assert_eq!(decide(&terms, &model, some_c), Some(true));
    assert_eq!(decide(&terms, &model, avoid), Some(true));
}

/// Alternation over Int: `∀x. ∃y. y≠x ∧ y≠a` is true and `∃x. ∀y. y=x ∨ y=a`
/// is false. The inner group's support includes the OUTER binder's current
/// value, which is what makes the nested plan exact.
#[test]
fn integer_alternations_are_decided_exactly() {
    let mut terms = TermStore::new();
    let sort = Sort::Int;
    let x = terms.mk_var("x", sort.clone());
    let y = terms.mk_var("y", sort.clone());
    let a = terms.mk_var("a", sort.clone());
    let yx = neq(&mut terms, y, x);
    let ya = neq(&mut terms, y, a);
    let inner_body = app(&mut terms, "and", &[yx, ya]);
    let inner = exists(&mut terms, &["y"], &sort, inner_body);
    let valid = forall(&mut terms, &["x"], &sort, inner);
    let yx_eq = eq(&mut terms, y, x);
    let ya_eq = eq(&mut terms, y, a);
    let covers_body = app(&mut terms, "or", &[yx_eq, ya_eq]);
    let covers = forall(&mut terms, &["y"], &sort, covers_body);
    let invalid = exists(&mut terms, &["x"], &sort, covers);
    let model = MapModel(HashMap::from([(a, ModelValue::Int(BigInt::from(-3)))]));
    assert_eq!(decide(&terms, &model, valid), Some(true));
    assert_eq!(decide(&terms, &model, invalid), Some(false));
}

/// Outside the fragment the evaluator stays exactly as unevaluable as before:
/// an order atom, arithmetic around a binder, and a binder under an
/// uninterpreted function all decline.
#[test]
fn non_equality_occurrences_decline() {
    let mut terms = TermStore::new();
    let sort = Sort::Real;
    let x = terms.mk_var("x", sort.clone());
    let a = terms.mk_var("a", sort.clone());
    let less = app(&mut terms, "<", &[x, a]);
    let ordered = exists(&mut terms, &["x"], &sort, less);
    let one = terms.mk_rational(BigRational::from_integer(BigInt::from(1)));
    let shifted = terms.mk_app(Symbol::named("+"), vec![x, one], sort.clone());
    let shifted_eq = eq(&mut terms, shifted, a);
    let arithmetic = exists(&mut terms, &["x"], &sort, shifted_eq);
    let fx = terms.mk_app(Symbol::named("f"), vec![x], sort.clone());
    let fx_eq = eq(&mut terms, fx, a);
    let uninterpreted = forall(&mut terms, &["x"], &sort, fx_eq);
    let model = MapModel(HashMap::from([(a, real(0))]));
    for root in [ordered, arithmetic, uninterpreted] {
        assert_eq!(decide(&terms, &model, root), None, "must stay unevaluable");
    }
}

/// A nested binder of ANOTHER sort is outside the fragment, even when the
/// outer group is equality-only.
#[test]
fn nested_binder_of_another_sort_declines() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let a = terms.mk_var("a", Sort::Real);
    let p = terms.mk_var("p", Sort::Bool);
    let xa = eq(&mut terms, x, a);
    let inner_body = app(&mut terms, "or", &[xa, p]);
    let inner = forall(&mut terms, &["p"], &Sort::Bool, inner_body);
    let root = exists(&mut terms, &["x"], &Sort::Real, inner);
    let model = MapModel(HashMap::from([(a, real(0))]));
    assert_eq!(decide(&terms, &model, root), None);
}

/// Review counterexample (1): with `y = 7` free, the nested `∀y` SHADOWS the
/// free constant. `∀x. (x = y) = (∀y. y ≠ x)` is FALSE (take `x = 7`: the
/// left side is true, the right side false). A name-based audit treated the
/// outer `y` as a binder occurrence, never put `7` in the support, and
/// answered TRUE. The scope-aware audit declines.
#[test]
fn nested_binder_shadowing_a_free_constant_is_never_decided_true() {
    let mut terms = TermStore::new();
    let sort = Sort::Real;
    let x = terms.mk_var("x", sort.clone());
    let y = terms.mk_var("y", sort.clone());
    let xy = eq(&mut terms, x, y);
    let yx = neq(&mut terms, y, x);
    let inner = forall(&mut terms, &["y"], &sort, yx);
    let iff = eq(&mut terms, xy, inner);
    let root = forall(&mut terms, &["x"], &sort, iff);
    let model = MapModel(HashMap::from([(y, real(7))]));
    let verdict = decide(&terms, &model, root);
    assert_ne!(
        verdict,
        Some(true),
        "a FALSE sentence must never evaluate true"
    );
    assert!(matches!(verdict, None | Some(false)));
}

/// Review counterexample (2): `∀y. y = 5 ∨ ¬∀x. (x = y) = (∀y. y ≠ x)` is
/// VALID (for every `y`, `x = y` falsifies the inner universal). Inside the
/// `∀x` group the `y` of `x = y` is the OUTER binder, not the shadowing inner
/// one; a name-based audit left its value out of the support and answered
/// FALSE.
#[test]
fn nested_binder_shadowing_an_outer_binder_is_never_decided_false() {
    let mut terms = TermStore::new();
    let sort = Sort::Real;
    let x = terms.mk_var("x", sort.clone());
    let y = terms.mk_var("y", sort.clone());
    let five = terms.mk_rational(BigRational::from_integer(BigInt::from(5)));
    let xy = eq(&mut terms, x, y);
    let yx = neq(&mut terms, y, x);
    let inner = forall(&mut terms, &["y"], &sort, yx);
    let iff = eq(&mut terms, xy, inner);
    let middle = forall(&mut terms, &["x"], &sort, iff);
    let not_middle = terms.mk_not_raw(middle);
    let y5 = eq(&mut terms, y, five);
    let body = app(&mut terms, "or", &[y5, not_middle]);
    let root = forall(&mut terms, &["y"], &sort, body);
    let model = MapModel(HashMap::new());
    let verdict = decide(&terms, &model, root);
    assert_ne!(
        verdict,
        Some(false),
        "a VALID sentence must never evaluate false"
    );
    assert!(matches!(verdict, None | Some(true)));
}

/// Hash-consing gives the atom `x = y` ONE `TermId` both inside the
/// shadowing `∀y` (both sides bound) and outside it (`y` the free constant).
/// With `y = 7`, `∀x. (x = y) = (∀y. x = y)` is FALSE (`x = 7`: true vs
/// false). An audit whose visited set ignored the scope accepted the inner
/// visit, skipped the outer one, and answered TRUE.
#[test]
fn one_atom_under_two_scopes_is_audited_in_each() {
    let mut terms = TermStore::new();
    let sort = Sort::Real;
    let x = terms.mk_var("x", sort.clone());
    let y = terms.mk_var("y", sort.clone());
    let xy = eq(&mut terms, x, y);
    let inner = forall(&mut terms, &["y"], &sort, xy);
    let iff = eq(&mut terms, xy, inner);
    let root = forall(&mut terms, &["x"], &sort, iff);
    let model = MapModel(HashMap::from([(y, real(7))]));
    let verdict = decide(&terms, &model, root);
    assert_ne!(
        verdict,
        Some(true),
        "a FALSE sentence must never evaluate true"
    );
}

/// Shadowing BETWEEN binders of the group is resolved by scope, not
/// declined: in `∀x. x = c ∨ ∃x. x = c` every `x` is bound where it occurs,
/// so the sentence (TRUE: the inner `∃x` picks `c`) is still decided.
#[test]
fn a_nested_binder_reusing_a_group_binder_name_is_still_decided() {
    let mut terms = TermStore::new();
    let sort = Sort::Real;
    let x = terms.mk_var("x", sort.clone());
    let c = terms.mk_var("c", sort.clone());
    let xc = eq(&mut terms, x, c);
    let inner = exists(&mut terms, &["x"], &sort, xc);
    let body = app(&mut terms, "or", &[xc, inner]);
    let root = forall(&mut terms, &["x"], &sort, body);
    let model = MapModel(HashMap::from([(c, real(3))]));
    assert_eq!(decide(&terms, &model, root), Some(true));
}

/// Deterministic generator for the differential test below.
struct Lcg(u64);

impl Lcg {
    fn next(&mut self, bound: u64) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        (self.0 >> 33) % bound
    }
}

/// Random equality formula over the variables in `scope` and `consts`.
///
/// `fresh` counts binders (the brute-force carrier width depends on it). With
/// `collide`, a binder REUSES an existing name about half the time: a free
/// constant's (`c0`, `c1`), the root's, or one already in scope, so nested
/// binders shadow constants, outer binders and each other.
fn random_formula(
    terms: &mut TermStore,
    rng: &mut Lcg,
    scope: &mut Vec<String>,
    consts: &[TermId],
    fresh: &mut usize,
    depth: u32,
    collide: bool,
) -> TermId {
    let sort = Sort::Int;
    let pick = |terms: &mut TermStore, rng: &mut Lcg, scope: &[String]| {
        let total = scope.len() + consts.len();
        let index = rng.next(total as u64) as usize;
        if index < scope.len() {
            terms.mk_var(&scope[index], sort.clone())
        } else {
            consts[index - scope.len()]
        }
    };
    let choice = if depth == 0 { 0 } else { rng.next(5) };
    match choice {
        0 => {
            let lhs = pick(terms, rng, scope);
            let rhs = pick(terms, rng, scope);
            eq(terms, lhs, rhs)
        }
        1 => {
            let inner = random_formula(terms, rng, scope, consts, fresh, depth - 1, collide);
            terms.mk_not_raw(inner)
        }
        2 | 3 => {
            let lhs = random_formula(terms, rng, scope, consts, fresh, depth - 1, collide);
            let rhs = random_formula(terms, rng, scope, consts, fresh, depth - 1, collide);
            app(terms, if choice == 2 { "and" } else { "or" }, &[lhs, rhs])
        }
        _ => {
            let name = if collide && rng.next(2) == 0 {
                let pool = ["c0", "c1", "root"];
                let index = rng.next((pool.len() + scope.len()) as u64) as usize;
                pool.get(index)
                    .map_or_else(|| scope[index - pool.len()].clone(), |n| (*n).to_string())
            } else {
                format!("v{fresh}")
            };
            *fresh += 1;
            scope.push(name.clone());
            let body = random_formula(terms, rng, scope, consts, fresh, depth - 1, collide);
            scope.pop();
            let vars = vec![(name, sort.clone())];
            if rng.next(2) == 0 {
                terms.mk_forall(vars, body)
            } else {
                terms.mk_exists(vars, body)
            }
        }
    }
}

/// Brute-force truth over the finite carrier `0..width` (with the model's
/// constant values). For an equality formula with `k` binders and constants
/// valued in `0..c`, any carrier of size at least `c + k + 1` is
/// elementarily equivalent to the integers FOR THAT FORMULA (the same
/// renaming argument as the planner's), so this is an independent oracle.
fn brute(
    terms: &TermStore,
    term: TermId,
    env: &mut Vec<(String, i64)>,
    consts: &HashMap<TermId, i64>,
    width: i64,
) -> bool {
    let value = |term: TermId, env: &Vec<(String, i64)>| -> i64 {
        // Innermost binder first: a binder named like a constant SHADOWS it
        // (the two share one hash-consed `TermId`).
        if let TermData::Var(name, _) = terms.get(term) {
            if let Some((_, v)) = env.iter().rev().find(|(n, _)| n == name) {
                return *v;
            }
        }
        *consts.get(&term).expect("free constant")
    };
    match terms.get(term).clone() {
        TermData::Const(ay_core::term::Constant::Bool(b)) => b,
        TermData::Not(inner) => !brute(terms, inner, env, consts, width),
        TermData::App(symbol, args) => match symbol.name() {
            "=" => value(args[0], env) == value(args[1], env),
            "and" => args.iter().all(|&a| brute(terms, a, env, consts, width)),
            "or" => args.iter().any(|&a| brute(terms, a, env, consts, width)),
            other => panic!("unexpected {other}"),
        },
        TermData::Forall(vars, body, _) | TermData::Exists(vars, body, _) => {
            let universal = matches!(terms.get(term), TermData::Forall(..));
            let name = vars[0].0.clone();
            let mut result = universal;
            for v in 0..width {
                env.push((name.clone(), v));
                let r = brute(terms, body, env, consts, width);
                env.pop();
                if universal && !r {
                    result = false;
                    break;
                }
                if !universal && r {
                    result = true;
                    break;
                }
            }
            result
        }
        other => panic!("unexpected {other:?}"),
    }
}

/// One differential round: a random formula under a random root quantifier.
/// Returns (planner verdict, brute-force truth).
fn differential_round(rng: &mut Lcg, collide: bool) -> (Option<bool>, bool) {
    let mut terms = TermStore::new();
    let consts: Vec<TermId> = (0..2)
        .map(|i| terms.mk_var(&format!("c{i}"), Sort::Int))
        .collect();
    let mut values = HashMap::new();
    for &c in &consts {
        values.insert(c, rng.next(3) as i64);
    }
    let name = "root".to_string();
    let mut scope = vec![name.clone()];
    let mut fresh = 0usize;
    let body = random_formula(&mut terms, rng, &mut scope, &consts, &mut fresh, 4, collide);
    let root = if rng.next(2) == 0 {
        terms.mk_forall(vec![(name, Sort::Int)], body)
    } else {
        terms.mk_exists(vec![(name, Sort::Int)], body)
    };
    let model = MapModel(
        values
            .iter()
            .map(|(t, v)| (*t, ModelValue::Int(BigInt::from(*v))))
            .collect(),
    );
    let width = 3 + fresh as i64 + 2;
    let expected = brute(&terms, root, &mut Vec::new(), &values, width);
    (decide(&terms, &model, root), expected)
}

/// Differential check of the planner against brute force over a carrier
/// large enough to be exact, on random nested equality formulas with free
/// constants. Every sampled formula must be DECIDED and agree.
#[test]
fn planner_agrees_with_brute_force_on_random_equality_formulas() {
    let mut rng = Lcg(0x5eed_1234);
    let mut decided = 0;
    for round in 0..300 {
        let (actual, expected) = differential_round(&mut rng, false);
        assert_eq!(actual, Some(expected), "round {round}");
        decided += 1;
    }
    assert_eq!(decided, 300);
}

/// The same differential with binder names that COLLIDE with the free
/// constants, the root binder and binders already in scope. A shadowed free
/// name may make the planner decline, but every verdict it does give must
/// agree with brute force; both outcomes must actually be exercised.
#[test]
fn planner_agrees_with_brute_force_when_binder_names_shadow() {
    let mut rng = Lcg(0x5a0d_0f1e);
    let (mut decided, mut declined) = (0, 0);
    for round in 0..600 {
        let (actual, expected) = differential_round(&mut rng, true);
        match actual {
            Some(verdict) => {
                assert_eq!(verdict, expected, "round {round}");
                decided += 1;
            }
            None => declined += 1,
        }
    }
    assert!(decided >= 300, "decided {decided}, declined {declined}");
    assert!(declined >= 20, "decided {decided}, declined {declined}");
}
