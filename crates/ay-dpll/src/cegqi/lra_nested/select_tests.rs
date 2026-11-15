// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Property tests for the midpoint selection (plan §3.4 step 4):
//! model preservation, CE-freeness and finiteness over random linear bodies
//! and random counterexample models.

use ay_core::kani_compat::DetHashSet as HashSet;
use ay_core::{Sort, TermId, TermStore};
use num_bigint::BigInt;
use num_rational::BigRational;

use super::implicant::{Assignment, Walker};
use super::select::{select_tuple, tuple_terms, Selected};
use super::tree::instantiate;

struct SplitMix64(u64);

impl SplitMix64 {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }
    fn range(&mut self, lo: i64, hi: i64) -> i64 {
        lo + (self.next() % ((hi - lo + 1) as u64)) as i64
    }
}

fn rat(n: i64) -> BigRational {
    BigRational::from_integer(BigInt::from(n))
}

/// Random linear term `Σ c·v + k` over `vars`.
fn random_lin(terms: &mut TermStore, rng: &mut SplitMix64, vars: &[TermId]) -> TermId {
    let mut summands = Vec::new();
    for &v in vars {
        let c = rng.range(-2, 2);
        if c != 0 {
            let coeff = terms.mk_rational(rat(c));
            summands.push(terms.mk_mul(vec![coeff, v]));
        }
    }
    summands.push(terms.mk_rational(rat(rng.range(-3, 3))));
    if summands.len() == 1 {
        summands[0]
    } else {
        terms.mk_add(summands)
    }
}

fn random_atom(terms: &mut TermStore, rng: &mut SplitMix64, vars: &[TermId]) -> TermId {
    let l = random_lin(terms, rng, vars);
    let r = random_lin(terms, rng, vars);
    match rng.range(0, 5) {
        0 => terms.mk_lt(l, r),
        1 => terms.mk_le(l, r),
        2 => terms.mk_gt(l, r),
        3 => terms.mk_ge(l, r),
        4 => terms.mk_eq(l, r),
        _ => {
            let eq = terms.mk_eq(l, r);
            terms.mk_not(eq)
        }
    }
}

/// Random body: an `or` of `and`s of atoms (DNF), optionally under `not`.
fn random_body(terms: &mut TermStore, rng: &mut SplitMix64, vars: &[TermId]) -> TermId {
    let disjuncts: Vec<TermId> = (0..rng.range(1, 3))
        .map(|_| {
            let conj: Vec<TermId> = (0..rng.range(1, 3))
                .map(|_| random_atom(terms, rng, vars))
                .collect();
            terms.mk_and(conj)
        })
        .collect();
    let body = terms.mk_or(disjuncts);
    if rng.range(0, 1) == 0 {
        body
    } else {
        terms.mk_not(body)
    }
}

struct Fixture {
    terms: TermStore,
    consts: Vec<TermId>,
    binders: Vec<(String, Sort)>,
    ce: Vec<TermId>,
}

fn fixture(nbinders: usize) -> Fixture {
    let mut terms = TermStore::new();
    let consts = vec![
        terms.mk_var("qa", Sort::Real),
        terms.mk_var("qb", Sort::Real),
    ];
    let binders: Vec<(String, Sort)> = (0..nbinders)
        .map(|i| (format!("qx{i}"), Sort::Real))
        .collect();
    let ce = (0..nbinders)
        .map(|i| terms.mk_var(format!("qlra!e!qx{i}"), Sort::Real))
        .collect();
    Fixture {
        terms,
        consts,
        binders,
        ce,
    }
}

/// Runs `rounds` random (body, model) trials; returns trials that selected.
fn run_property(seed: u64, nbinders: usize, trials: usize) -> usize {
    let mut rng = SplitMix64(seed);
    let mut f = fixture(nbinders);
    let mut selected = 0;
    for _ in 0..trials {
        let binder_vars: Vec<TermId> = f
            .binders
            .iter()
            .map(|(n, s)| f.terms.mk_var(n.clone(), s.clone()))
            .collect();
        let mut vars = f.consts.clone();
        vars.extend(&binder_vars);
        let body = random_body(&mut f.terms, &mut rng, &vars);
        let Some(ce_body) = instantiate(&mut f.terms, body, &f.binders, &f.ce) else {
            continue;
        };
        let mut model = Assignment::default();
        for &v in f.consts.iter().chain(&f.ce) {
            model.reals.insert(v, rat(rng.range(-4, 4)));
        }
        let mut walker = Walker {
            terms: &f.terms,
            model: &model,
            ce_vars: &f.ce,
            work: 0,
            max_work: 1 << 16,
        };
        if walker.eval(ce_body) != Some(false) {
            continue; // not a counterexample model
        }
        let sorts: Vec<Sort> = f.binders.iter().map(|(_, s)| s.clone()).collect();
        let chosen = select_tuple(&f.terms, ce_body, &f.ce, &sorts, &model, 1 << 16)
            .expect("a counterexample model of a linear body must select");
        let tuple = tuple_terms(&mut f.terms, &chosen);
        // CE-freeness.
        for sel in &chosen {
            if let Selected::Real(lin) = sel {
                assert!(
                    lin.coeffs.keys().all(|v| !f.ce.contains(v)),
                    "CE leak: {lin:?}"
                );
            }
        }
        // Model preservation: I |= not body[t].
        let instance = instantiate(&mut f.terms, body, &f.binders, &tuple).expect("ground tuple");
        let mut walker = Walker {
            terms: &f.terms,
            model: &model,
            ce_vars: &f.ce,
            work: 0,
            max_work: 1 << 16,
        };
        assert_eq!(
            walker.eval(instance),
            Some(false),
            "selected instance must stay false under the counterexample model"
        );
        selected += 1;
    }
    selected
}

#[test]
fn midpoint_selection_preserves_the_model_single_binder() {
    let n = run_property(0x51, 1, 400);
    assert!(
        n >= 50,
        "anti-vacuity: only {n} counterexample trials selected"
    );
}

#[test]
fn midpoint_selection_preserves_the_model_two_binders() {
    let n = run_property(0x52, 2, 400);
    assert!(
        n >= 50,
        "anti-vacuity: only {n} counterexample trials selected"
    );
}

#[test]
fn midpoint_selection_preserves_the_model_three_binders() {
    let n = run_property(0x53, 3, 300);
    assert!(
        n >= 30,
        "anti-vacuity: only {n} counterexample trials selected"
    );
}

/// FINITENESS: for one fixed body, the tuples selected over many different
/// counterexample models range over a set bounded by the midpoint/±1
/// combinations of the body's bound terms, not over the models.
#[test]
fn midpoint_selection_ranges_over_a_finite_term_set() {
    let mut rng = SplitMix64(0x77);
    let mut f = fixture(1);
    let x = f.terms.mk_var("qx0", Sort::Real);
    let vars = [f.consts[0], f.consts[1], x];
    // Fixed body with 4 atoms, all mentioning x.
    let atoms: Vec<TermId> = (0..4)
        .map(|_| random_atom(&mut f.terms, &mut rng, &vars))
        .collect();
    let (a01, a23) = (
        f.terms.mk_and(atoms[..2].to_vec()),
        f.terms.mk_and(atoms[2..].to_vec()),
    );
    let body = f.terms.mk_or(vec![a01, a23]);
    let ce_body = instantiate(&mut f.terms, body, &f.binders, &f.ce).expect("instantiate");
    let mut distinct: HashSet<TermId> = HashSet::default();
    let mut hits = 0;
    for _ in 0..2_000 {
        let mut model = Assignment::default();
        for &v in f.consts.iter().chain(&f.ce) {
            let num = rng.range(-40, 40);
            model.reals.insert(
                v,
                BigRational::new(BigInt::from(num), BigInt::from(rng.range(1, 4))),
            );
        }
        let mut walker = Walker {
            terms: &f.terms,
            model: &model,
            ce_vars: &f.ce,
            work: 0,
            max_work: 1 << 16,
        };
        if walker.eval(ce_body) != Some(false) {
            continue;
        }
        let chosen =
            select_tuple(&f.terms, ce_body, &f.ce, &[Sort::Real], &model, 1 << 16).expect("select");
        let tuple = tuple_terms(&mut f.terms, &chosen);
        distinct.insert(tuple[0]);
        hits += 1;
    }
    // At most 4 bound terms: 4 solved + 16 midpoints + 4 lower+1 + 4 upper-1 + 0.
    assert!(hits >= 100, "anti-vacuity: {hits} counterexample models");
    assert!(
        distinct.len() <= 4 + 16 + 4 + 4 + 1,
        "{} distinct selections from {hits} models: selection is not finite",
        distinct.len()
    );
}

/// `#cegqi-ce-var-selection`: `(forall ((a Real) (b Real)) (= a b))` — the
/// solved equality for `a` mentions the later counterexample constant `b`;
/// back-substitution must remove it.
#[test]
fn back_substitution_removes_later_counterexample_constants() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("qa0", Sort::Real);
    let b = terms.mk_var("qb0", Sort::Real);
    let body = terms.mk_eq(a, b);
    let binders = vec![
        ("qa0".to_string(), Sort::Real),
        ("qb0".to_string(), Sort::Real),
    ];
    let ea = terms.mk_var("qlra!e!qa0", Sort::Real);
    let eb = terms.mk_var("qlra!e!qb0", Sort::Real);
    let ce = vec![ea, eb];
    let ce_body = instantiate(&mut terms, body, &binders, &ce).expect("instantiate");
    let mut model = Assignment::default();
    model.reals.insert(ea, rat(3));
    model.reals.insert(eb, rat(7));
    let chosen = select_tuple(
        &terms,
        ce_body,
        &ce,
        &[Sort::Real, Sort::Real],
        &model,
        1 << 16,
    )
    .expect("select");
    for sel in &chosen {
        let Selected::Real(lin) = sel else {
            panic!("real binder")
        };
        assert!(lin.coeffs.is_empty(), "tuple must be closed: {lin:?}");
    }
    let tuple = tuple_terms(&mut terms, &chosen);
    let instance = instantiate(&mut terms, body, &binders, &tuple).expect("ground");
    let empty = Assignment::default();
    let mut walker = Walker {
        terms: &terms,
        model: &empty,
        ce_vars: &ce,
        work: 0,
        max_work: 1 << 16,
    };
    assert_eq!(
        walker.eval(instance),
        Some(false),
        "instance must refute the universal"
    );
}

/// Bool binders take their model value; the instance stays false.
#[test]
fn bool_binders_take_their_model_value() {
    let mut terms = TermStore::new();
    let c = terms.mk_var("qc", Sort::Real);
    let q = terms.mk_var("qq", Sort::Bool);
    let x = terms.mk_var("qx", Sort::Real);
    let gt = terms.mk_gt(x, c);
    let body = terms.mk_implies(q, gt);
    let binders = vec![
        ("qq".to_string(), Sort::Bool),
        ("qx".to_string(), Sort::Real),
    ];
    let eq = terms.mk_var("qlra!e!qq", Sort::Bool);
    let ex = terms.mk_var("qlra!e!qx", Sort::Real);
    let ce = vec![eq, ex];
    let ce_body = instantiate(&mut terms, body, &binders, &ce).expect("instantiate");
    let mut model = Assignment::default();
    model.bools.insert(eq, true);
    model.reals.insert(ex, rat(-5));
    model.reals.insert(c, rat(2));
    let chosen = select_tuple(
        &terms,
        ce_body,
        &ce,
        &[Sort::Bool, Sort::Real],
        &model,
        1 << 16,
    )
    .expect("select");
    assert_eq!(chosen[0], Selected::Bool(true));
    let tuple = tuple_terms(&mut terms, &chosen);
    let instance = instantiate(&mut terms, body, &binders, &tuple).expect("ground");
    let mut walker = Walker {
        terms: &terms,
        model: &model,
        ce_vars: &ce,
        work: 0,
        max_work: 1 << 16,
    };
    assert_eq!(walker.eval(instance), Some(false));
}
