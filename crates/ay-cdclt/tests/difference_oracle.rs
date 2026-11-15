// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Random Boolean combinations of real difference atoms `x - y ≤ c` and
//! `x - y = c`, decided by the engine and by an independent oracle.
//!
//! Oracle: enumerate atom assignments; for each propositional model, the
//! difference constraints (with strict edges for negated `≤`) are feasible
//! iff Floyd-Warshall over lexicographic (value, -strictness) weights finds no
//! negative cycle; each disequality `x - y ≠ c` must additionally leave the
//! feasible set off its hyperplane, which for a convex set means one of the
//! two strict sides is feasible on its own. Every `sat` model is re-checked
//! against the atoms' arithmetic with exact rationals.

use ay_cdclt::{CheckOutcome, Engine, EngineConfig, EngineStats, Guard, Verdict};
use ay_core::{Constant, Sort, TermData, TermId, TermStore};
use num_bigint::BigInt;
use num_rational::BigRational;

#[derive(Clone, Copy, Debug)]
enum Atom {
    Le(usize, usize, i64),
    Eq(usize, usize, i64),
}

/// `x_u - x_v ≤ c` (or `< c` when strict).
type Edge = (usize, usize, i64, bool);

struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
    fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }
}

fn feasible(n: usize, edges: &[Edge]) -> bool {
    const INF: (i64, i64) = (i64::MAX / 4, 0);
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

fn theory_sat(n: usize, atoms: &[Atom], values: u32) -> bool {
    let mut edges = Vec::new();
    let mut diseqs = Vec::new();
    for (i, &atom) in atoms.iter().enumerate() {
        let on = values >> i & 1 == 1;
        match (atom, on) {
            (Atom::Le(u, v, c), true) => edges.push((u, v, c, false)),
            (Atom::Le(u, v, c), false) => edges.push((v, u, -c, true)),
            (Atom::Eq(u, v, c), true) => edges.extend([(u, v, c, false), (v, u, -c, false)]),
            (Atom::Eq(u, v, c), false) => diseqs.push((u, v, c)),
        }
    }
    if !feasible(n, &edges) {
        return false;
    }
    diseqs.iter().all(|&(u, v, c)| {
        let below: Vec<Edge> = edges.iter().copied().chain([(u, v, c, true)]).collect();
        let above: Vec<Edge> = edges.iter().copied().chain([(v, u, -c, true)]).collect();
        feasible(n, &below) || feasible(n, &above)
    })
}

fn oracle(n: usize, atoms: &[Atom], clauses: &[Vec<(usize, bool)>]) -> bool {
    (0..1u32 << atoms.len()).any(|values| {
        let bool_ok = clauses
            .iter()
            .all(|c| c.iter().any(|&(a, pos)| (values >> a & 1 == 1) == pos));
        bool_ok && theory_sat(n, atoms, values)
    })
}

fn q(n: i64) -> BigRational {
    BigRational::from_integer(BigInt::from(n))
}

fn atom_holds(atom: Atom, xs: &[BigRational]) -> bool {
    match atom {
        Atom::Le(u, v, c) => &xs[u] - &xs[v] <= q(c),
        Atom::Eq(u, v, c) => &xs[u] - &xs[v] == q(c),
    }
}

struct Instance {
    n: usize,
    atoms: Vec<Atom>,
    clauses: Vec<Vec<(usize, bool)>>,
}

fn random_instance(rng: &mut Rng) -> Instance {
    let n = 3 + usize::try_from(rng.below(2)).unwrap_or(0);
    let pick = |rng: &mut Rng| usize::try_from(rng.below(n as u64)).unwrap_or(0);
    let mut atoms = Vec::new();
    while atoms.len() < 6 {
        let (u, v) = (pick(rng), pick(rng));
        if u == v {
            continue;
        }
        let c = i64::try_from(rng.below(5)).unwrap_or(0) - 2;
        atoms.push(if rng.below(3) == 0 {
            Atom::Eq(u, v, c)
        } else {
            Atom::Le(u, v, c)
        });
    }
    let clauses = (0..3 + rng.below(6))
        .map(|_| {
            (0..1 + rng.below(3))
                .map(|_| {
                    (
                        usize::try_from(rng.below(6)).unwrap_or(0),
                        rng.below(2) == 0,
                    )
                })
                .collect()
        })
        .collect();
    Instance { n, atoms, clauses }
}

fn run(
    inst: &Instance,
    difference_logic: bool,
) -> (CheckOutcome, EngineStats, Option<Vec<BigRational>>) {
    let mut terms = TermStore::new();
    let xs: Vec<TermId> = (0..inst.n)
        .map(|i| terms.mk_var(format!("x{i}"), Sort::Real))
        .collect();
    let atom_terms: Vec<TermId> = inst
        .atoms
        .iter()
        .map(|&a| {
            let (Atom::Le(u, v, c) | Atom::Eq(u, v, c)) = a;
            let diff = terms.mk_sub(vec![xs[u], xs[v]]);
            let k = terms.mk_rational(q(c));
            match a {
                Atom::Le(..) => terms.mk_le(diff, k),
                Atom::Eq(..) => terms.mk_eq(diff, k),
            }
        })
        .collect();
    let roots: Vec<TermId> = inst
        .clauses
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
        .collect();
    let mut engine = Engine::new(EngineConfig {
        difference_logic,
        ..EngineConfig::default()
    });
    for r in roots {
        engine.assert(r);
    }
    let outcome = engine.check(&mut terms, &[], &Guard::new());
    let stats = engine.stats().clone();
    let expected_plugin = if difference_logic { "dl-real" } else { "lra" };
    assert_eq!(engine.plugin_names(), vec![expected_plugin]);
    let values: Option<Vec<TermId>> = if outcome.verdict == Verdict::Sat {
        xs.iter()
            .map(|&x| engine.model_value(&mut terms, x).or(Some(x)))
            .collect()
    } else {
        None
    };
    drop(engine);
    let model = values.map(|vals| {
        vals.iter()
            .map(|&t| match terms.get(t) {
                TermData::Const(Constant::Rational(r)) => r.0.clone(),
                _ => q(0), // a variable in no atom: any value does
            })
            .collect()
    });
    (outcome, stats, model)
}

/// The difference-logic sub-module (every atom here is a difference atom).
#[test]
fn engine_agrees_with_the_difference_oracle() {
    agree_with_the_oracle(true);
}

/// The same draws through the simplex: the control arm.
#[test]
fn simplex_agrees_with_the_difference_oracle() {
    agree_with_the_oracle(false);
}

fn agree_with_the_oracle(difference_logic: bool) {
    let mut rng = Rng(0x9E37_79B9_7F4A_7C15);
    let (mut sat, mut unsat, mut minted, mut conflicts) = (0, 0, 0, 0);
    for round in 0..2000 {
        let inst = random_instance(&mut rng);
        let expected = oracle(inst.n, &inst.atoms, &inst.clauses);
        let (outcome, stats, model) = run(&inst, difference_logic);
        assert_eq!(stats.solve_calls, 1, "round {round}: one search per check");
        minted += stats.minted_atoms;
        conflicts += stats.conflicts;
        match (outcome.verdict, outcome.reason) {
            (Verdict::Sat, _) => {
                assert!(
                    expected,
                    "round {round}: wrong sat on {:?} {:?}",
                    inst.atoms, inst.clauses
                );
                let xs = model.expect("sat has a model");
                for clause in &inst.clauses {
                    let ok = clause
                        .iter()
                        .any(|&(a, pos)| atom_holds(inst.atoms[a], &xs) == pos);
                    assert!(ok, "round {round}: model violates {clause:?}: {xs:?}");
                }
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
            (Verdict::Unknown, reason) => panic!(
                "round {round}: unknown ({reason:?}) {:?} {:?} n={}",
                inst.atoms, inst.clauses, inst.n
            ),
        }
    }
    eprintln!(
        "oracle (difference logic {difference_logic}): {sat} sat, {unsat} unsat, \
         {minted} atoms minted, {conflicts} theory conflicts"
    );
    assert!(
        sat > 300 && unsat > 300,
        "a useful mix: {sat} sat, {unsat} unsat"
    );
    assert!(
        minted > 0 && conflicts > 0,
        "splits and theory conflicts were exercised: {minted} minted, {conflicts} conflicts"
    );
}
