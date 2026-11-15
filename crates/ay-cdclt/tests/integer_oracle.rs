// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Random Boolean combinations of two-variable integer atoms
//! `a·x + b·y ≤ c` and `a·x + b·y = c` over three Ints in the box [-3, 3]³,
//! decided by the engine (LRA in integer mode, branch and bound in the
//! search) and by brute force over the 343 points of the box.
//!
//! Every `sat` model is re-checked twice: against the atoms in exact
//! integers here, and by the engine's own independent evaluator
//! (`Engine::check_model`).

use ay_cdclt::{CheckOutcome, Engine, EngineConfig, Guard, ModelVerdict, Verdict};
use ay_core::{Constant, Sort, TermData, TermId, TermStore, TheoryLemmaKind};
use num_bigint::BigInt;

const BOX: i64 = 3;

#[derive(Clone, Copy, Debug)]
struct Atom {
    a: i64,
    u: usize,
    b: i64,
    v: usize,
    c: i64,
    eq: bool,
}

impl Atom {
    fn holds(self, xs: &[i64]) -> bool {
        let lhs = self.a * xs[self.u] + self.b * xs[self.v];
        if self.eq {
            lhs == self.c
        } else {
            lhs <= self.c
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

struct Instance {
    atoms: Vec<Atom>,
    clauses: Vec<Vec<(usize, bool)>>,
}

fn random_instance(rng: &mut Rng) -> Instance {
    let mut atoms = Vec::new();
    while atoms.len() < 6 {
        let (u, v) = (rng.range(0, 2) as usize, rng.range(0, 2) as usize);
        let (a, b) = (rng.range(-3, 3), rng.range(-3, 3));
        if u == v || a == 0 || b == 0 {
            continue;
        }
        let c = rng.range(-4, 4);
        let eq = rng.range(0, 2) == 0;
        atoms.push(Atom { a, u, b, v, c, eq });
    }
    let clauses = (0..rng.range(3, 8))
        .map(|_| {
            (0..rng.range(1, 3))
                .map(|_| (rng.range(0, 5) as usize, rng.range(0, 1) == 0))
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

struct Run {
    outcome: CheckOutcome,
    model: Option<Vec<i64>>,
    verdict: Option<ModelVerdict>,
    branches: usize,
    solve_calls: u64,
}

fn run(inst: &Instance) -> Run {
    let mut terms = TermStore::new();
    let xs: Vec<TermId> = (0..3)
        .map(|i| terms.mk_var(format!("x{i}"), Sort::Int))
        .collect();
    let mut roots = Vec::new();
    for &x in &xs {
        let (lo, hi) = (int(&mut terms, -BOX), int(&mut terms, BOX));
        roots.push(terms.mk_ge(x, lo));
        roots.push(terms.mk_le(x, hi));
    }
    let atom_terms: Vec<TermId> = inst
        .atoms
        .iter()
        .map(|atom| {
            let (a, b) = (int(&mut terms, atom.a), int(&mut terms, atom.b));
            let ax = terms.mk_mul(vec![a, xs[atom.u]]);
            let by = terms.mk_mul(vec![b, xs[atom.v]]);
            let sum = terms.mk_add(vec![ax, by]);
            let c = int(&mut terms, atom.c);
            if atom.eq {
                terms.mk_eq(sum, c)
            } else {
                terms.mk_le(sum, c)
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
    let mut engine = Engine::new(EngineConfig {
        record_proofs: true,
        ..EngineConfig::default()
    });
    for &r in &roots {
        engine.assert(r);
    }
    let outcome = engine.check(&mut terms, &[], &Guard::new());
    let branches = outcome
        .proof
        .as_ref()
        .map_or(&[][..], |p| p.steps())
        .iter()
        .filter(|s| s.hint.kind == TheoryLemmaKind::IntBoundsTautology)
        .count();
    let solve_calls = engine.stats().solve_calls;
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
    let model = values.map(|vals| {
        vals.iter()
            .map(|v| match v.map(|t| terms.get(t)) {
                Some(TermData::Const(Constant::Int(i))) => i64::try_from(i).unwrap_or(i64::MAX),
                // A variable in no atom: any value does, and 0 is in the box.
                None => 0,
                other => panic!("an Int model value must be an integer, got {other:?}"),
            })
            .collect()
    });
    Run {
        outcome,
        model,
        verdict,
        branches,
        solve_calls,
    }
}

#[test]
fn engine_agrees_with_the_integer_box_oracle() {
    let mut rng = Rng(0x2545_F491_4F6C_DD1D);
    let (mut sat, mut unsat, mut branches) = (0, 0, 0);
    for round in 0..1500 {
        let inst = random_instance(&mut rng);
        let expected = oracle(&inst);
        let result = run(&inst);
        assert_eq!(result.solve_calls, 1, "round {round}: one search per check");
        branches += result.branches;
        match (result.outcome.verdict, result.outcome.reason) {
            (Verdict::Sat, _) => {
                assert!(expected, "round {round}: wrong sat on {:?}", inst.atoms);
                let xs = result.model.expect("sat has a model");
                assert!(xs.iter().all(|x| x.abs() <= BOX), "round {round}: {xs:?}");
                assert!(satisfied(&inst, &xs), "round {round}: model {xs:?} fails");
                assert_eq!(result.verdict, Some(ModelVerdict::Satisfied));
                sat += 1;
            }
            (Verdict::Unsat, _) => {
                assert!(!expected, "round {round}: wrong unsat on {:?}", inst.atoms);
                unsat += 1;
            }
            (Verdict::Unknown, reason) => {
                panic!("round {round}: unknown ({reason:?}) {:?}", inst.atoms)
            }
        }
    }
    eprintln!("integer oracle: {sat} sat, {unsat} unsat, {branches} branch lemmas");
    assert!(
        sat > 200 && unsat > 200,
        "a useful mix: {sat} sat, {unsat} unsat"
    );
    assert!(branches > 0, "branch and bound was exercised");
}
