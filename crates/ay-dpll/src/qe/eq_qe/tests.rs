// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use ay_core::term::Constant;
use num_bigint::BigInt;

fn app(terms: &mut TermStore, name: &str, args: &[TermId]) -> TermId {
    terms.mk_app(Symbol::named(name), args, Sort::Bool)
}

fn eq(terms: &mut TermStore, a: TermId, b: TermId) -> TermId {
    app(terms, "=", &[a, b])
}

fn elim(terms: &mut TermStore, root: TermId) -> Option<TermId> {
    eliminate_equality_quantifiers(terms, root, &mut EqQeBudget::new(1 << 20))
}

/// Brute-force truth over the carrier `0..width`, reading free constants from
/// `consts`. With `k` binders and constants valued in `0..c`, a carrier of
/// size at least `c + k + 1` decides an equality formula exactly as the
/// integers do, so this is an oracle independent of the elimination.
fn brute(
    terms: &TermStore,
    term: TermId,
    env: &mut Vec<(String, i64)>,
    consts: &[(TermId, i64)],
    width: i64,
) -> bool {
    let value = |term: TermId, env: &Vec<(String, i64)>| -> i64 {
        if let Some((_, v)) = consts.iter().find(|(t, _)| *t == term) {
            return *v;
        }
        match terms.get(term) {
            TermData::Var(name, _) => env
                .iter()
                .rev()
                .find(|(n, _)| n == name)
                .map(|(_, v)| *v)
                .expect("bound variable"),
            TermData::Const(Constant::Int(v)) => i64::try_from(v).expect("small"),
            other => panic!("unexpected value term {other:?}"),
        }
    };
    match terms.get(term).clone() {
        TermData::Const(Constant::Bool(b)) => b,
        TermData::Not(inner) => !brute(terms, inner, env, consts, width),
        TermData::Ite(c, a, b) => {
            if brute(terms, c, env, consts, width) {
                brute(terms, a, env, consts, width)
            } else {
                brute(terms, b, env, consts, width)
            }
        }
        TermData::App(symbol, args) => match symbol.name() {
            "=" if terms.sort(args[0]) == &Sort::Bool => {
                brute(terms, args[0], env, consts, width)
                    == brute(terms, args[1], env, consts, width)
            }
            "=" => value(args[0], env) == value(args[1], env),
            "distinct" => value(args[0], env) != value(args[1], env),
            "and" => args.iter().all(|&a| brute(terms, a, env, consts, width)),
            "or" => args.iter().any(|&a| brute(terms, a, env, consts, width)),
            "=>" => {
                !brute(terms, args[0], env, consts, width)
                    || brute(terms, args[1], env, consts, width)
            }
            other => panic!("unexpected connective {other}"),
        },
        TermData::Forall(vars, body, _) | TermData::Exists(vars, body, _) => {
            let universal = matches!(terms.get(term), TermData::Forall(..));
            fn go(
                terms: &TermStore,
                vars: &[(String, Sort)],
                body: TermId,
                universal: bool,
                env: &mut Vec<(String, i64)>,
                consts: &[(TermId, i64)],
                width: i64,
            ) -> bool {
                let Some(((name, _), rest)) = vars.split_first() else {
                    return brute(terms, body, env, consts, width);
                };
                for v in 0..width {
                    env.push((name.clone(), v));
                    let r = go(terms, rest, body, universal, env, consts, width);
                    env.pop();
                    if r != universal {
                        return r;
                    }
                }
                universal
            }
            go(terms, &vars, body, universal, env, consts, width)
        }
        other => panic!("unexpected formula {other:?}"),
    }
}

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

fn random_formula(
    terms: &mut TermStore,
    rng: &mut Lcg,
    scope: &mut Vec<String>,
    consts: &[TermId],
    binders: &mut usize,
    depth: u32,
) -> TermId {
    let pick = |terms: &mut TermStore, rng: &mut Lcg, scope: &[String]| {
        let total = scope.len() + consts.len();
        let index = rng.next(total as u64) as usize;
        if index < scope.len() {
            terms.mk_var(scope[index].clone(), Sort::Int)
        } else {
            consts[index - scope.len()]
        }
    };
    let choice = if depth == 0 { 0 } else { rng.next(6) };
    match choice {
        0 => {
            let lhs = pick(terms, rng, scope);
            let rhs = pick(terms, rng, scope);
            if rng.next(4) == 0 {
                app(terms, "distinct", &[lhs, rhs])
            } else {
                eq(terms, lhs, rhs)
            }
        }
        1 => {
            let inner = random_formula(terms, rng, scope, consts, binders, depth - 1);
            terms.mk_not_raw(inner)
        }
        2 | 3 => {
            let lhs = random_formula(terms, rng, scope, consts, binders, depth - 1);
            let rhs = random_formula(terms, rng, scope, consts, binders, depth - 1);
            app(terms, if choice == 2 { "and" } else { "or" }, &[lhs, rhs])
        }
        _ => {
            let width = 1 + rng.next(2) as usize;
            let mut vars = Vec::new();
            for _ in 0..width {
                let name = format!("v{binders}");
                *binders += 1;
                scope.push(name.clone());
                vars.push((name, Sort::Int));
            }
            let body = random_formula(terms, rng, scope, consts, binders, depth - 1);
            for _ in 0..width {
                scope.pop();
            }
            if choice == 4 {
                terms.mk_forall(vars, body)
            } else {
                terms.mk_exists(vars, body)
            }
        }
    }
}

/// The elimination is an EQUIVALENCE: on random nested equality formulas
/// over two free constants, the eliminated quantifier-free formula agrees
/// with brute force on the original under EVERY assignment of the constants.
#[test]
fn elimination_is_equivalent_on_random_equality_formulas() {
    let mut rng = Lcg(0xe90e_1234);
    let mut quantified = 0;
    for round in 0..400 {
        let mut terms = TermStore::new();
        let consts: Vec<TermId> = (0..2)
            .map(|i| terms.mk_var(format!("c{i}"), Sort::Int))
            .collect();
        let mut binders = 0usize;
        let root = random_formula(
            &mut terms,
            &mut rng,
            &mut Vec::new(),
            &consts,
            &mut binders,
            5,
        );
        if crate::ematching::contains_quantifier(&terms, root) {
            quantified += 1;
        }
        let eliminated = elim(&mut terms, root).expect("equality fragment eliminates");
        assert!(
            !crate::ematching::contains_quantifier(&terms, eliminated),
            "round {round}: residual quantifier"
        );
        let width = 2 + binders as i64 + 2;
        for a in 0..2 {
            for b in 0..2 {
                let values = [(consts[0], a), (consts[1], b)];
                let expected = brute(&terms, root, &mut Vec::new(), &values, width);
                let actual = brute(&terms, eliminated, &mut Vec::new(), &values, width);
                assert_eq!(actual, expected, "round {round} c0={a} c1={b}");
            }
        }
    }
    assert!(quantified > 100, "the generator must exercise quantifiers");
}

/// Closed sentences decide to constants: `∃x y. x≠y ∧ ∃z. z≠x ∧ z≠y` is
/// `true` and `∀x y z. x=y ∨ y=z ∨ x=z` is `false` over an infinite sort.
#[test]
fn closed_sentences_decide_to_constants() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let z = terms.mk_var("z", Sort::Real);
    let xy = eq(&mut terms, x, y);
    let zx = eq(&mut terms, z, x);
    let zy = eq(&mut terms, z, y);
    let nxy = terms.mk_not_raw(xy);
    let nzx = terms.mk_not_raw(zx);
    let nzy = terms.mk_not_raw(zy);
    let inner_body = app(&mut terms, "and", &[nzx, nzy]);
    let inner = terms.mk_exists(vec![("z".into(), Sort::Real)], inner_body);
    let body = app(&mut terms, "and", &[nxy, inner]);
    let three = terms.mk_exists(
        vec![("x".into(), Sort::Real), ("y".into(), Sort::Real)],
        body,
    );
    let t = terms.mk_bool(true);
    assert_eq!(elim(&mut terms, three), Some(t));
    let pigeon_body = app(&mut terms, "or", &[xy, zy, zx]);
    let pigeon = terms.mk_forall(
        vec![
            ("x".into(), Sort::Real),
            ("y".into(), Sort::Real),
            ("z".into(), Sort::Real),
        ],
        pigeon_body,
    );
    let f = terms.mk_bool(false);
    assert_eq!(elim(&mut terms, pigeon), Some(f));
}

/// Out-of-fragment occurrences decline: an order atom, arithmetic around the
/// binder, a UF argument, and a Bool binder.
#[test]
fn out_of_fragment_declines() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let a = terms.mk_var("a", Sort::Real);
    let less = terms.mk_lt(x, a);
    let ordered = terms.mk_exists(vec![("x".into(), Sort::Real)], less);
    assert_eq!(elim(&mut terms, ordered), None);
    let one = terms.mk_rational(num_rational::BigRational::from_integer(BigInt::from(1)));
    let shifted = terms.mk_app(Symbol::named("+"), vec![x, one], Sort::Real);
    let shifted_eq = eq(&mut terms, shifted, a);
    let arithmetic = terms.mk_forall(vec![("x".into(), Sort::Real)], shifted_eq);
    assert_eq!(elim(&mut terms, arithmetic), None);
    let fx = terms.mk_app(Symbol::named("f"), vec![x], Sort::Real);
    let fx_eq = eq(&mut terms, fx, a);
    let uf = terms.mk_forall(vec![("x".into(), Sort::Real)], fx_eq);
    assert_eq!(elim(&mut terms, uf), None);
    let p = terms.mk_var("p", Sort::Bool);
    let q = terms.mk_var("q", Sort::Bool);
    let pq = app(&mut terms, "or", &[p, q]);
    let boolean = terms.mk_forall(vec![("p".into(), Sort::Bool)], pq);
    assert_eq!(elim(&mut terms, boolean), None);
}

/// A comparison term may be an arbitrary ground term (here `(+ a 1)`): the
/// binder is still only compared for equality with it.
#[test]
fn arithmetic_comparands_are_admitted() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let a = terms.mk_var("a", Sort::Real);
    let one = terms.mk_rational(num_rational::BigRational::from_integer(BigInt::from(1)));
    let shifted = terms.mk_app(Symbol::named("+"), vec![a, one], Sort::Real);
    let xa = eq(&mut terms, x, a);
    let xs = eq(&mut terms, x, shifted);
    let body = app(&mut terms, "and", &[xa, xs]);
    let root = terms.mk_exists(vec![("x".into(), Sort::Real)], body);
    let eliminated = elim(&mut terms, root).expect("admitted");
    assert!(!crate::ematching::contains_quantifier(&terms, eliminated));
}
