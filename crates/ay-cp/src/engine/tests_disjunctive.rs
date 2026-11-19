// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Disjunctive models solved end to end against brute force.
//!
//! The optimisation runs the way the FlatZinc front end drives the engine:
//! one engine, solve, tighten the objective bound, solve again, so every
//! clause a propagator explained in an earlier solve stays learned. An
//! unsound explanation then shows up as a false UNSAT or a wrong optimum
//! (MiniZinc Challenge rect-euler/3venn, 2026-11-18).

use super::*;
use crate::domain::Domain;
use crate::engine::CpSolveResult;

/// xorshift64*: a fixed-seed generator, so a failure names its seed.
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 >> 12;
        self.0 ^= self.0 << 25;
        self.0 ^= self.0 >> 27;
        self.0.wrapping_mul(0x2545_f491_4f6c_dd1d)
    }

    fn range(&mut self, lo: i64, hi: i64) -> i64 {
        let span = u64::try_from(hi - lo + 1).expect("non-empty range");
        lo + i64::try_from(self.next() % span).expect("small range")
    }

    fn index(&mut self, len: usize) -> usize {
        usize::try_from(self.next() % u64::try_from(len).expect("small")).expect("small")
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Sense {
    Minimize,
    Maximize,
}

/// `s_a - s_b <= c`.
#[derive(Debug, Clone, Copy)]
struct Precedence {
    a: usize,
    b: usize,
    c: i64,
}

#[derive(Debug)]
struct Model {
    root: Vec<(i64, i64)>,
    durations: Vec<i64>,
    precedences: Vec<Precedence>,
    weights: Vec<i64>,
    sense: Sense,
}

impl Model {
    fn random(rng: &mut Rng) -> Self {
        let n = usize::try_from(rng.range(3, 4)).expect("small");
        let horizon = rng.range(8, 13);
        let mut root = Vec::with_capacity(n);
        let mut durations = Vec::with_capacity(n);
        let mut weights = Vec::with_capacity(n);
        for _ in 0..n {
            let lb = rng.range(0, 3);
            let ub = rng.range(horizon - 3, horizon);
            root.push((lb, ub));
            durations.push(rng.range(1, 5));
            weights.push(rng.range(-3, 3));
        }
        let mut precedences = Vec::new();
        for _ in 0..rng.range(0, 2) {
            let a = rng.index(n);
            let b = rng.index(n);
            if a != b {
                precedences.push(Precedence {
                    a,
                    b,
                    c: rng.range(-6, 2),
                });
            }
        }
        let sense = if rng.next() % 2 == 0 {
            Sense::Minimize
        } else {
            Sense::Maximize
        };
        Self {
            root,
            durations,
            precedences,
            weights,
            sense,
        }
    }

    fn feasible(&self, s: &[i64]) -> bool {
        let n = s.len();
        let disjoint = (0..n).all(|i| {
            ((i + 1)..n)
                .all(|j| s[i] + self.durations[i] <= s[j] || s[j] + self.durations[j] <= s[i])
        });
        disjoint && self.precedences.iter().all(|p| s[p.a] - s[p.b] <= p.c)
    }

    fn objective(&self, s: &[i64]) -> i64 {
        s.iter().zip(&self.weights).map(|(v, w)| v * w).sum()
    }

    /// Optimum by enumeration, `None` if infeasible.
    fn brute_force(&self) -> Option<i64> {
        let mut best: Option<i64> = None;
        let mut s = vec![0; self.root.len()];
        self.enumerate(0, &mut s, &mut best);
        best
    }

    fn enumerate(&self, k: usize, s: &mut [i64], best: &mut Option<i64>) {
        if k == s.len() {
            if self.feasible(s) {
                let value = self.objective(s);
                *best = Some(match (*best, self.sense) {
                    (None, _) => value,
                    (Some(b), Sense::Minimize) => b.min(value),
                    (Some(b), Sense::Maximize) => b.max(value),
                });
            }
            return;
        }
        let (lb, ub) = self.root[k];
        for v in lb..=ub {
            s[k] = v;
            self.enumerate(k + 1, s, best);
        }
    }

    /// Optimum by the engine's incremental bound-tightening loop.
    fn solve(&self) -> Option<i64> {
        let mut engine = CpSatEngine::new();
        let starts: Vec<IntVarId> = self
            .root
            .iter()
            .enumerate()
            .map(|(i, &(lb, ub))| engine.new_int_var(Domain::new(lb, ub), Some(&format!("s{i}"))))
            .collect();
        let span: i64 = self
            .root
            .iter()
            .zip(&self.weights)
            .map(|(&(lb, ub), &w)| (lb * w).abs().max((ub * w).abs()))
            .sum();
        let obj = engine.new_int_var(Domain::new(-span, span), Some("obj"));
        engine.add_constraint(Constraint::Disjunctive {
            starts: starts.clone(),
            durations: self.durations.clone(),
        });
        for p in &self.precedences {
            engine.add_constraint(Constraint::LinearLe {
                coeffs: vec![1, -1],
                vars: vec![starts[p.a], starts[p.b]],
                rhs: p.c,
            });
        }
        let mut coeffs = self.weights.clone();
        coeffs.push(-1);
        let mut vars = starts.clone();
        vars.push(obj);
        engine.add_constraint(Constraint::LinearEq {
            coeffs,
            vars,
            rhs: 0,
        });
        engine.set_objective(obj, self.sense == Sense::Minimize);

        let mut best = None;
        for _ in 0..200 {
            match engine.solve() {
                CpSolveResult::Sat(assignment) => {
                    let value_of = |v: IntVarId| {
                        assignment
                            .iter()
                            .find(|(x, _)| *x == v)
                            .expect("assigned")
                            .1
                    };
                    let s: Vec<i64> = starts.iter().map(|&v| value_of(v)).collect();
                    assert!(
                        self.feasible(&s),
                        "engine returned an infeasible schedule {s:?}"
                    );
                    let value = value_of(obj);
                    assert_eq!(value, self.objective(&s), "objective value mismatch");
                    best = Some(value);
                    match self.sense {
                        Sense::Minimize => engine.add_upper_bound(obj, value - 1),
                        Sense::Maximize => engine.add_lower_bound(obj, value + 1),
                    }
                }
                CpSolveResult::Unsat => return best,
                CpSolveResult::Unknown => panic!("Unknown on a tiny model"),
            }
        }
        panic!("optimisation did not converge");
    }
}

/// Random small machines with side constraints and a weighted objective:
/// the engine's verdict and optimum must equal brute force.
#[test]
fn test_random_disjunctive_optimum_matches_brute_force() {
    for seed in 1..=400u64 {
        let mut rng = Rng(seed.wrapping_mul(0x9e37_79b9_7f4a_7c15) | 1);
        let model = Model::random(&mut rng);
        let expected = model.brute_force();
        let got = model.solve();
        assert_eq!(got, expected, "seed {seed}: model {model:?}");
    }
}
