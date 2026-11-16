// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Random Boolean combinations of difference atoms `s - t ≤ c` and
//! `s - t = c` over reals and applications of an uninterpreted
//! `f : Real -> Real`, nested (`f(f(x))`), decided by the engine (the hub,
//! EUF, LRA attached through the hub, model-based combination in the
//! search) and by an independent oracle.
//!
//! Oracle (Ackermann's reduction): every term is a real variable, and for
//! each two applications `f(s)`, `f(t)` one of `s < t`, `s > t`, or
//! `s = t ∧ f(s) = f(t)` must hold. The input is satisfiable iff some atom
//! assignment satisfying the clauses, together with one such choice per
//! application pair, is a feasible set of difference constraints with
//! strict edges (Floyd-Warshall) whose disequalities each leave it off
//! their hyperplane (a convex set is not covered by finitely many
//! hyperplanes that do not contain it). Every `sat` model is re-checked
//! here in exact rationals, including that `f` is a function, and by the
//! engine's own evaluator.

use ay_cdclt::{Engine, EngineConfig, Guard, ModelVerdict, Verdict};
use ay_core::{Constant, Sort, Symbol, TermData, TermId, TermStore};
use num_bigint::BigInt;
use num_rational::BigRational;

/// Terms: 0..3 are `x0..x2`, then `f(x0)`, `f(x1)`, `f(x2)`, `f(f(x0))`.
const TERMS: usize = 7;
/// The argument of each application term.
const APPS: [(usize, usize); 4] = [(3, 0), (4, 1), (5, 2), (6, 3)];

#[derive(Clone, Copy, Debug)]
enum Atom {
    Le(usize, usize, i64),
    Eq(usize, usize, i64),
}

/// `t_u - t_v ≤ c` (or `< c` when strict).
type Edge = (usize, usize, i64, bool);

struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
    fn below(&mut self, n: u64) -> usize {
        usize::try_from(self.next() % n).unwrap_or(0)
    }
}

fn feasible(edges: &[Edge]) -> bool {
    const INF: (i64, i64) = (i64::MAX / 4, 0);
    let n = TERMS;
    let mut d = vec![vec![INF; n]; n];
    for (i, row) in d.iter_mut().enumerate() {
        row[i] = (0, 0);
    }
    for &(u, v, c, strict) in edges {
        let w = (c, -i64::from(strict));
        if w < d[v][u] {
            d[v][u] = w;
        }
    }
    for k in 0..n {
        for i in 0..n {
            for j in 0..n {
                if d[i][k] == INF || d[k][j] == INF {
                    continue;
                }
                let via = (d[i][k].0 + d[k][j].0, d[i][k].1 + d[k][j].1);
                if via < d[i][j] {
                    d[i][j] = via;
                }
            }
        }
    }
    (0..n).all(|i| d[i][i] >= (0, 0))
}

fn theory_sat(edges: &[Edge], diseqs: &[(usize, usize, i64)]) -> bool {
    feasible(edges)
        && diseqs.iter().all(|&(u, v, c)| {
            let below: Vec<Edge> = edges.iter().copied().chain([(u, v, c, true)]).collect();
            let above: Vec<Edge> = edges.iter().copied().chain([(v, u, -c, true)]).collect();
            feasible(&below) || feasible(&above)
        })
}

/// The application pairs of the terms that occur in the instance.
fn app_pairs(used: &[bool]) -> Vec<(usize, usize)> {
    let apps: Vec<(usize, usize)> = APPS.iter().copied().filter(|&(a, _)| used[a]).collect();
    let mut pairs = Vec::new();
    for i in 0..apps.len() {
        for j in i + 1..apps.len() {
            pairs.push((apps[i].0, apps[j].0));
        }
    }
    pairs
}

fn arg_of(app: usize) -> usize {
    APPS.iter()
        .find(|&&(a, _)| a == app)
        .map(|&(_, x)| x)
        .expect("an application")
}

/// Terms an instance mentions, closed under arguments.
fn used_terms(atoms: &[Atom]) -> Vec<bool> {
    let mut used = vec![false; TERMS];
    for &a in atoms {
        let (Atom::Le(u, v, _) | Atom::Eq(u, v, _)) = a;
        used[u] = true;
        used[v] = true;
    }
    for &(app, arg) in APPS.iter().rev() {
        if used[app] {
            used[arg] = true;
        }
    }
    for &(app, arg) in &APPS {
        if used[app] {
            used[arg] = true;
        }
    }
    used
}

fn oracle(atoms: &[Atom], clauses: &[Vec<(usize, bool)>]) -> bool {
    let pairs = app_pairs(&used_terms(atoms));
    let choices = 3usize.pow(u32::try_from(pairs.len()).unwrap_or(0));
    (0..1u32 << atoms.len()).any(|values| {
        let bool_ok = clauses
            .iter()
            .all(|c| c.iter().any(|&(a, pos)| (values >> a & 1 == 1) == pos));
        if !bool_ok {
            return false;
        }
        let mut edges = Vec::new();
        let mut diseqs = Vec::new();
        for (i, &atom) in atoms.iter().enumerate() {
            match (atom, values >> i & 1 == 1) {
                (Atom::Le(u, v, c), true) => edges.push((u, v, c, false)),
                (Atom::Le(u, v, c), false) => edges.push((v, u, -c, true)),
                (Atom::Eq(u, v, c), true) => edges.extend([(u, v, c, false), (v, u, -c, false)]),
                (Atom::Eq(u, v, c), false) => diseqs.push((u, v, c)),
            }
        }
        (0..choices).any(|mut choice| {
            let mut all = edges.clone();
            for &(fa, fb) in &pairs {
                let (a, b) = (arg_of(fa), arg_of(fb));
                match choice % 3 {
                    0 => all.push((a, b, 0, true)),
                    1 => all.push((b, a, 0, true)),
                    _ => all.extend([
                        (a, b, 0, false),
                        (b, a, 0, false),
                        (fa, fb, 0, false),
                        (fb, fa, 0, false),
                    ]),
                }
                choice /= 3;
            }
            theory_sat(&all, &diseqs)
        })
    })
}

fn q(n: i64) -> BigRational {
    BigRational::from_integer(BigInt::from(n))
}

fn random_instance(rng: &mut Rng) -> (Vec<Atom>, Vec<Vec<(usize, bool)>>) {
    let n_atoms = 4 + rng.below(3);
    let mut atoms = Vec::new();
    while atoms.len() < n_atoms {
        let (u, v) = (rng.below(TERMS as u64), rng.below(TERMS as u64));
        if u == v {
            continue;
        }
        let c = i64::try_from(rng.below(3)).unwrap_or(0) - 1;
        atoms.push(if rng.below(3) == 0 {
            Atom::Eq(u, v, c)
        } else {
            Atom::Le(u, v, c)
        });
    }
    let clauses = (0..3 + rng.below(5))
        .map(|_| {
            (0..=rng.below(3))
                .map(|_| (rng.below(n_atoms as u64), rng.below(2) == 0))
                .collect()
        })
        .collect();
    (atoms, clauses)
}

fn build(terms: &mut TermStore) -> Vec<TermId> {
    let xs: Vec<TermId> = (0..3)
        .map(|i| terms.mk_var(format!("x{i}"), Sort::Real))
        .collect();
    let f =
        |terms: &mut TermStore, a: TermId| terms.mk_app(Symbol::named("f"), vec![a], Sort::Real);
    let fx0 = f(terms, xs[0]);
    let fx1 = f(terms, xs[1]);
    let fx2 = f(terms, xs[2]);
    let ffx0 = f(terms, fx0);
    vec![xs[0], xs[1], xs[2], fx0, fx1, fx2, ffx0]
}

fn value(terms: &TermStore, t: TermId) -> Option<BigRational> {
    match terms.get(t) {
        TermData::Const(Constant::Rational(r)) => Some(r.0.clone()),
        TermData::Const(Constant::Int(i)) => Some(BigRational::from_integer(i.clone())),
        _ => None,
    }
}

/// The clauses as assertions over the atoms' terms.
fn encode(
    terms: &mut TermStore,
    ts: &[TermId],
    atoms: &[Atom],
    clauses: &[Vec<(usize, bool)>],
) -> Vec<TermId> {
    let atom_terms: Vec<TermId> = atoms
        .iter()
        .map(|&a| {
            let (Atom::Le(u, v, c) | Atom::Eq(u, v, c)) = a;
            let diff = terms.mk_sub(vec![ts[u], ts[v]]);
            let k = terms.mk_rational(q(c));
            match a {
                Atom::Le(..) => terms.mk_le(diff, k),
                Atom::Eq(..) => terms.mk_eq(diff, k),
            }
        })
        .collect();
    clauses
        .iter()
        .map(|c| {
            let lits = c
                .iter()
                .map(|&(a, pos)| {
                    if pos {
                        atom_terms[a]
                    } else {
                        terms.mk_not(atom_terms[a])
                    }
                })
                .collect();
            terms.mk_or(lits)
        })
        .collect()
}

#[test]
fn engine_agrees_with_the_ackermann_oracle() {
    let mut rng = Rng(0x9E37_79B9_7F4A_7C15 ^ 0x5151);
    let (mut sat, mut unsat, mut new_eqs, mut combos) = (0, 0, 0, 0);
    for round in 0..1500 {
        let (atoms, clauses) = random_instance(&mut rng);
        let expected = oracle(&atoms, &clauses);
        let mut terms = TermStore::new();
        let ts = build(&mut terms);
        let roots = encode(&mut terms, &ts, &atoms, &clauses);
        // Odd rounds filter by relevancy (KC21); half run the simplex.
        let mut engine = Engine::new(EngineConfig {
            hub_relevancy: round % 2 == 1,
            difference_logic: round % 4 < 2,
            ..EngineConfig::default()
        });
        for &r in &roots {
            engine.assert(r);
        }
        let checked = engine.check(&mut terms, &[], &Guard::new());
        let stats = checked.stats.clone();
        let outcome = match checked.verdict {
            Verdict::Sat => Out::Sat,
            Verdict::Unsat => Out::Unsat,
            Verdict::Unknown => Out::Unknown(checked.reason.clone().unwrap_or_default()),
        };
        assert!(stats.solve_calls <= 1, "round {round}: {stats:?}");
        new_eqs += stats.new_eqs;
        combos += stats.combination_equalities;
        match outcome {
            Out::Sat => {
                assert!(
                    expected,
                    "round {round}: wrong sat on {atoms:?} {clauses:?}"
                );
                assert_eq!(
                    engine.check_model(&mut terms, &roots),
                    ModelVerdict::Satisfied,
                    "round {round}: engine model check on {atoms:?} {clauses:?}"
                );
                let vals: Vec<Option<TermId>> = ts
                    .iter()
                    .map(|&t| engine.model_value(&mut terms, t))
                    .collect();
                drop(engine);
                let xs: Vec<BigRational> = vals
                    .iter()
                    .map(|v| v.and_then(|t| value(&terms, t)).unwrap_or_else(|| q(0)))
                    .collect();
                // The clauses hold, and f is a function on the terms the
                // engine saw (a term only in a clause the encoding folded
                // away, like `a ∨ ¬a`, has no value and is free).
                let used: Vec<bool> = vals.iter().map(Option::is_some).collect();
                for clause in &clauses {
                    let ok = clause.iter().any(|&(a, pos)| {
                        let holds = match atoms[a] {
                            Atom::Le(u, v, c) => &xs[u] - &xs[v] <= q(c),
                            Atom::Eq(u, v, c) => &xs[u] - &xs[v] == q(c),
                        };
                        holds == pos
                    });
                    assert!(ok, "round {round}: model violates {clause:?}: {xs:?}");
                }
                for &(fa, a) in &APPS {
                    for &(fb, b) in &APPS {
                        if used[fa] && used[fb] && used[a] && used[b] && xs[a] == xs[b] {
                            assert_eq!(
                                xs[fa], xs[fb],
                                "round {round}: f is not a function: {xs:?} on {atoms:?} {clauses:?} ({stats:?})"
                            );
                        }
                    }
                }
                sat += 1;
            }
            Out::Unsat => {
                assert!(
                    !expected,
                    "round {round}: wrong unsat on {atoms:?} {clauses:?}"
                );
                unsat += 1;
            }
            Out::Unknown(reason) => {
                panic!("round {round}: unknown ({reason}) on {atoms:?} {clauses:?}")
            }
        }
    }
    eprintln!(
        "uflra oracle: {sat} sat, {unsat} unsat, {new_eqs} new_eq events, \
         {combos} combination equalities"
    );
    assert!(
        sat > 200 && unsat > 200,
        "a useful mix: {sat} sat, {unsat} unsat"
    );
    assert!(
        new_eqs > 0 && combos > 0,
        "both directions of combination ran"
    );
}

/// A check's verdict, with the unknown reason.
#[derive(Debug)]
enum Out {
    Sat,
    Unsat,
    Unknown(String),
}
