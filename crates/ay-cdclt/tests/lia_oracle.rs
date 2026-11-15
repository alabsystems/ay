// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Linear integer arithmetic with `div`, `mod` (by non-zero numerals,
//! negative ones included) and `abs`, decided by the kernel (simplex in
//! integer mode, branch and bound and the operators' definitions in the one
//! search) and by brute force over a box.
//!
//! Every `sat` model is checked here in exact integers with SMT-LIB's
//! Euclidean `div`/`mod`, and by the engine's own exact model check.

use ay_cdclt::{Engine, EngineConfig, Guard, ModelVerdict, Verdict};
use ay_core::{Constant, Sort, TermData, TermId, TermStore};
use num_bigint::BigInt;

const BOX: i64 = 5;

/// An integer term over the variables.
#[derive(Clone, Debug)]
enum Expr {
    /// `a·x_u + b·x_v + c`
    Lin(i64, usize, i64, usize, i64),
    Div(Box<Expr>, i64),
    Mod(Box<Expr>, i64),
    Abs(Box<Expr>),
}

fn euclid(a: i64, k: i64) -> (i64, i64) {
    let r = a.rem_euclid(k.abs());
    ((a - r) / k, r)
}

impl Expr {
    fn eval(&self, xs: &[i64]) -> i64 {
        match self {
            Self::Lin(a, u, b, v, c) => a * xs[*u] + b * xs[*v] + c,
            Self::Div(e, k) => euclid(e.eval(xs), *k).0,
            Self::Mod(e, k) => euclid(e.eval(xs), *k).1,
            Self::Abs(e) => e.eval(xs).abs(),
        }
    }

    fn term(&self, terms: &mut TermStore, xs: &[TermId]) -> TermId {
        match self {
            Self::Lin(a, u, b, v, c) => {
                let (a, b, c) = (int(terms, *a), int(terms, *b), int(terms, *c));
                let ax = terms.mk_mul(vec![a, xs[*u]]);
                let by = terms.mk_mul(vec![b, xs[*v]]);
                terms.mk_add(vec![ax, by, c])
            }
            Self::Div(e, k) => {
                let (e, k) = (e.term(terms, xs), int(terms, *k));
                terms.mk_intdiv(e, k)
            }
            Self::Mod(e, k) => {
                let (e, k) = (e.term(terms, xs), int(terms, *k));
                terms.mk_mod(e, k)
            }
            Self::Abs(e) => {
                let e = e.term(terms, xs);
                terms.mk_app(ay_core::Symbol::named("abs"), vec![e], Sort::Int)
            }
        }
    }
}

/// `e ≤ c` or `e = c`.
#[derive(Clone, Debug)]
struct Atom {
    e: Expr,
    c: i64,
    eq: bool,
}

impl Atom {
    fn holds(&self, xs: &[i64]) -> bool {
        let v = self.e.eval(xs);
        if self.eq {
            v == self.c
        } else {
            v <= self.c
        }
    }
}

struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
    fn range(&mut self, lo: i64, hi: i64) -> i64 {
        let width = u64::try_from(hi - lo + 1).unwrap_or(1);
        lo + i64::try_from(self.next() % width).unwrap_or(0)
    }
}

fn random_lin(rng: &mut Rng) -> Expr {
    let u = usize::try_from(rng.range(0, 2)).unwrap_or(0);
    let v = usize::try_from(rng.range(0, 2)).unwrap_or(0);
    Expr::Lin(rng.range(-3, 3), u, rng.range(-2, 2), v, rng.range(-3, 3))
}

fn random_divisor(rng: &mut Rng) -> i64 {
    let k = rng.range(2, 4);
    if rng.range(0, 3) == 0 {
        -k
    } else {
        k
    }
}

fn random_expr(rng: &mut Rng) -> Expr {
    let base = random_lin(rng);
    match rng.range(0, 4) {
        0 => base,
        1 => Expr::Div(Box::new(base), random_divisor(rng)),
        2 => Expr::Mod(Box::new(base), random_divisor(rng)),
        3 => Expr::Abs(Box::new(base)),
        _ => Expr::Mod(
            Box::new(Expr::Div(Box::new(base), random_divisor(rng))),
            random_divisor(rng),
        ),
    }
}

struct Instance {
    atoms: Vec<Atom>,
    clauses: Vec<Vec<(usize, bool)>>,
}

fn random_instance(rng: &mut Rng) -> Instance {
    let atoms: Vec<Atom> = (0..5)
        .map(|_| Atom {
            e: random_expr(rng),
            c: rng.range(-3, 3),
            eq: rng.range(0, 2) == 0,
        })
        .collect();
    let clauses = (0..rng.range(2, 6))
        .map(|_| {
            (0..rng.range(1, 3))
                .map(|_| {
                    (
                        usize::try_from(rng.range(0, 4)).unwrap_or(0),
                        rng.range(0, 1) == 0,
                    )
                })
                .collect()
        })
        .collect();
    Instance { atoms, clauses }
}

fn satisfied(inst: &Instance, xs: &[i64]) -> bool {
    inst.clauses
        .iter()
        .all(|c| c.iter().any(|&(a, pos)| inst.atoms[a].holds(xs) == pos))
}

fn oracle(inst: &Instance) -> bool {
    let range = -BOX..=BOX;
    range.clone().any(|x| {
        range
            .clone()
            .any(|y| range.clone().any(|z| satisfied(inst, &[x, y, z])))
    })
}

fn int(terms: &mut TermStore, n: i64) -> TermId {
    terms.mk_int(BigInt::from(n))
}

/// The instance's assertions over `xs`: the box bounds, then its clauses.
fn encode(terms: &mut TermStore, inst: &Instance, xs: &[TermId]) -> Vec<TermId> {
    let mut roots = Vec::new();
    for &x in xs {
        let (lo, hi) = (int(terms, -BOX), int(terms, BOX));
        roots.push(terms.mk_ge(x, lo));
        roots.push(terms.mk_le(x, hi));
    }
    let atom_terms: Vec<TermId> = inst
        .atoms
        .iter()
        .map(|atom| {
            let e = atom.e.term(terms, xs);
            let c = int(terms, atom.c);
            if atom.eq {
                terms.mk_eq(e, c)
            } else {
                terms.mk_le(e, c)
            }
        })
        .collect();
    for clause in &inst.clauses {
        let lits = clause
            .iter()
            .map(|&(a, pos)| {
                if pos {
                    atom_terms[a]
                } else {
                    terms.mk_not(atom_terms[a])
                }
            })
            .collect();
        roots.push(terms.mk_or(lits));
    }
    roots
}

#[test]
fn defined_operators_agree_with_the_integer_box() {
    let mut rng = Rng(0x94D0_49BB_1331_11EB);
    let (mut sat, mut unsat, mut unknown) = (0, 0, 0);
    for round in 0..700 {
        let inst = random_instance(&mut rng);
        let expected = oracle(&inst);
        let mut terms = TermStore::new();
        let xs: Vec<TermId> = (0..3)
            .map(|i| terms.mk_var(format!("x{i}"), Sort::Int))
            .collect();
        let roots = encode(&mut terms, &inst, &xs);
        let mut engine = Engine::new(EngineConfig::default());
        for &r in &roots {
            engine.assert(r);
        }
        let outcome = engine.check(&mut terms, &[], &Guard::new());
        assert!(engine.stats().solve_calls <= 1, "round {round}: one search");
        let (values, verdict) = if outcome.verdict == Verdict::Sat {
            let values: Vec<Option<TermId>> = xs
                .iter()
                .map(|&x| engine.model_value(&mut terms, x))
                .collect();
            (Some(values), Some(engine.check_model(&mut terms, &roots)))
        } else {
            (None, None)
        };
        drop(engine);
        match (outcome.verdict, outcome.reason) {
            (Verdict::Sat, _) => {
                assert!(
                    expected,
                    "round {round}: wrong sat on {:?} {:?}",
                    inst.atoms, inst.clauses
                );
                let model: Vec<i64> = values
                    .expect("values")
                    .iter()
                    .map(|v| match v.map(|t| terms.get(t)) {
                        Some(TermData::Const(Constant::Int(i))) => {
                            i64::try_from(i).unwrap_or(i64::MAX)
                        }
                        None => 0,
                        other => panic!("round {round}: non-integer Int value {other:?}"),
                    })
                    .collect();
                assert!(
                    satisfied(&inst, &model),
                    "round {round}: model {model:?} fails {:?} {:?}",
                    inst.atoms,
                    inst.clauses
                );
                assert_eq!(verdict, Some(ModelVerdict::Satisfied), "round {round}");
                sat += 1;
            }
            (Verdict::Unsat, _) => {
                assert!(
                    !expected,
                    "round {round}: wrong unsat on {:?} {:?}",
                    inst.atoms, inst.clauses
                );
                unsat += 1;
            }
            (Verdict::Unknown, reason) => {
                eprintln!("round {round}: unknown ({reason:?})");
                unknown += 1;
            }
        }
    }
    eprintln!("lia oracle: {sat} sat, {unsat} unsat, {unknown} unknown");
    assert_eq!(unknown, 0, "every check decided");
    assert!(
        sat > 100 && unsat > 100,
        "a useful mix: {sat} sat, {unsat} unsat"
    );
}
