// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Integer difference logic through the kernel's difference-logic
//! sub-module, against brute force.
//!
//! Random Boolean combinations of `x − y ⋈ c` and `x ⋈ c` with every
//! operator (`≤ < ≥ > =`, so strict bounds exercise integer tightening and
//! `=` its in-search definition) over three or four Ints in the box
//! [-3, 3], decided by the engine and by enumerating the box. Every `sat`
//! model is integral, satisfies every clause here, and passes the engine's
//! own exact model check. The simplex arm runs the same draws as a control.

use ay_cdclt::{CheckOutcome, Engine, EngineConfig, Guard, ModelVerdict, Verdict};
use ay_core::{Constant, Sort, TermData, TermId, TermStore};
use num_bigint::BigInt;

const BOX: i64 = 3;

#[derive(Clone, Copy, Debug)]
enum Op {
    Le,
    Lt,
    Ge,
    Gt,
    Eq,
}

/// `x_u − x_v ⋈ c`, or `x_u ⋈ c` when `v` is `None`.
#[derive(Clone, Copy, Debug)]
struct Atom {
    u: usize,
    v: Option<usize>,
    op: Op,
    c: i64,
}

impl Atom {
    fn holds(self, xs: &[i64]) -> bool {
        let lhs = xs[self.u] - self.v.map_or(0, |v| xs[v]);
        match self.op {
            Op::Le => lhs <= self.c,
            Op::Lt => lhs < self.c,
            Op::Ge => lhs >= self.c,
            Op::Gt => lhs > self.c,
            Op::Eq => lhs == self.c,
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
    n: usize,
    atoms: Vec<Atom>,
    clauses: Vec<Vec<(usize, bool)>>,
}

fn random_instance(rng: &mut Rng) -> Instance {
    let n = usize::try_from(rng.range(3, 4)).unwrap_or(3);
    let top = i64::try_from(n).unwrap_or(3) - 1;
    let mut atoms = Vec::new();
    while atoms.len() < 7 {
        let u = usize::try_from(rng.range(0, top)).unwrap_or(0);
        let v = if rng.range(0, 3) == 0 {
            None
        } else {
            let v = usize::try_from(rng.range(0, top)).unwrap_or(0);
            if v == u {
                continue;
            }
            Some(v)
        };
        let op = match rng.range(0, 4) {
            0 => Op::Le,
            1 => Op::Lt,
            2 => Op::Ge,
            3 => Op::Gt,
            _ => Op::Eq,
        };
        atoms.push(Atom {
            u,
            v,
            op,
            c: rng.range(-3, 3),
        });
    }
    let clauses = (0..rng.range(3, 9))
        .map(|_| {
            (0..rng.range(1, 3))
                .map(|_| {
                    (
                        usize::try_from(rng.range(0, 6)).unwrap_or(0),
                        rng.range(0, 1) == 0,
                    )
                })
                .collect()
        })
        .collect();
    Instance { n, atoms, clauses }
}

fn satisfied(inst: &Instance, xs: &[i64]) -> bool {
    inst.clauses
        .iter()
        .all(|c| c.iter().any(|&(a, pos)| inst.atoms[a].holds(xs) == pos))
}

fn oracle(inst: &Instance) -> bool {
    let mut xs = vec![-BOX; inst.n];
    loop {
        if satisfied(inst, &xs) {
            return true;
        }
        let mut i = 0;
        loop {
            if i == inst.n {
                return false;
            }
            if xs[i] < BOX {
                xs[i] += 1;
                break;
            }
            xs[i] = -BOX;
            i += 1;
        }
    }
}

fn int(terms: &mut TermStore, n: i64) -> TermId {
    terms.mk_int(BigInt::from(n))
}

struct Run {
    outcome: CheckOutcome,
    model: Option<Vec<i64>>,
    verdict: Option<ModelVerdict>,
    plugins: Vec<&'static str>,
    solve_calls: u64,
}

fn run(inst: &Instance, difference_logic: bool) -> Run {
    let mut terms = TermStore::new();
    let xs: Vec<TermId> = (0..inst.n)
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
            let lhs = match atom.v {
                Some(v) => terms.mk_sub(vec![xs[atom.u], xs[v]]),
                None => xs[atom.u],
            };
            let c = int(&mut terms, atom.c);
            match atom.op {
                Op::Le => terms.mk_le(lhs, c),
                Op::Lt => terms.mk_lt(lhs, c),
                Op::Ge => terms.mk_ge(lhs, c),
                Op::Gt => terms.mk_gt(lhs, c),
                Op::Eq => terms.mk_eq(lhs, c),
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
        difference_logic,
        record_proofs: true,
        ..EngineConfig::default()
    });
    for &r in &roots {
        engine.assert(r);
    }
    let outcome = engine.check(&mut terms, &[], &Guard::new());
    let solve_calls = engine.stats().solve_calls;
    let plugins = engine.plugin_names();
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
                None => 0,
                other => panic!("an Int model value must be an integer, got {other:?}"),
            })
            .collect()
    });
    Run {
        outcome,
        model,
        verdict,
        plugins,
        solve_calls,
    }
}

fn agree(difference_logic: bool, rounds: usize) {
    let mut rng = Rng(0xD1B5_4A32_D192_ED03);
    let (mut sat, mut unsat) = (0, 0);
    for round in 0..rounds {
        let inst = random_instance(&mut rng);
        let expected = oracle(&inst);
        let result = run(&inst, difference_logic);
        assert_eq!(result.solve_calls, 1, "round {round}: one search per check");
        let want = if difference_logic {
            "dl-int"
        } else {
            "lia-on-lra"
        };
        assert_eq!(result.plugins, vec![want], "round {round}");
        match (result.outcome.verdict, result.outcome.reason) {
            (Verdict::Sat, _) => {
                assert!(
                    expected,
                    "round {round}: wrong sat on {:?} {:?}",
                    inst.atoms, inst.clauses
                );
                let xs = result.model.expect("sat has a model");
                assert!(xs.iter().all(|x| x.abs() <= BOX), "round {round}: {xs:?}");
                assert!(satisfied(&inst, &xs), "round {round}: model {xs:?} fails");
                assert_eq!(
                    result.verdict,
                    Some(ModelVerdict::Satisfied),
                    "round {round}"
                );
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
                panic!("round {round}: unknown ({reason:?}) {:?}", inst.atoms)
            }
        }
    }
    eprintln!("idl oracle (difference logic {difference_logic}): {sat} sat, {unsat} unsat");
    assert!(
        sat > rounds / 8 && unsat > rounds / 8,
        "a useful mix: {sat} sat, {unsat} unsat"
    );
}

#[test]
fn difference_logic_agrees_with_the_integer_box() {
    agree(true, 2000);
}

#[test]
fn simplex_agrees_with_the_integer_box() {
    agree(false, 600);
}
