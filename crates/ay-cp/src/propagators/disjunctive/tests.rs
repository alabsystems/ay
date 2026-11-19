// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Soundness tests for the Disjunctive propagator's explanations.
//!
//! Every clause a propagator hands to the SAT core (a propagation reason or a
//! conflict) is kept as a learned clause, so it must hold in EVERY solution
//! of the constraint over the root domains, not only in the solutions that
//! agree with the current search state. These tests check exactly that by
//! enumerating all solutions of small instances.

use super::*;
use ay_sat::Solver as SatSolver;

struct Instance {
    trail: IntegerTrail,
    encoder: IntegerEncoder,
    starts: Vec<IntVarId>,
    durations: Vec<i64>,
    root: Vec<(i64, i64)>,
}

impl Instance {
    fn new(root: &[(i64, i64)], durations: &[i64]) -> Self {
        let mut trail = IntegerTrail::new();
        let mut encoder = IntegerEncoder::new();
        let mut sat = SatSolver::new(0);
        let starts = root
            .iter()
            .map(|&(lb, ub)| {
                let var = trail.register(lb, ub);
                let enc = encoder.register_var(lb, ub);
                assert_eq!(var, enc);
                var
            })
            .collect();
        encoder.pre_allocate_all(&mut sat);
        Self {
            trail,
            encoder,
            starts,
            durations: durations.to_vec(),
            root: root.to_vec(),
        }
    }

    /// Tighten task `task` to `[lb, ub]` at a new decision level, the way a
    /// search decision would.
    fn tighten(&mut self, task: usize, lb: i64, ub: i64) {
        self.trail.push_level();
        let var = self.starts[task];
        let ge = self.encoder.lookup_ge(var, lb).expect("ge literal");
        let le = self.encoder.lookup_le(var, ub).expect("le literal");
        self.trail.set_lb(var, lb, ge, None).expect("lb in domain");
        self.trail.set_ub(var, ub, le, None).expect("ub in domain");
    }

    fn propagator(&self) -> Disjunctive {
        Disjunctive::new(self.starts.clone(), self.durations.clone())
    }

    fn literal_holds(&self, lit: Literal, values: &[i64]) -> bool {
        let bound = self
            .encoder
            .decode(lit.variable())
            .expect("disjunctive clauses use only order-encoding literals");
        let task = self
            .starts
            .iter()
            .position(|&s| s == bound.var)
            .expect("literal on a task start");
        assert!(bound.is_ge);
        let ge = values[task] >= bound.value;
        if lit.is_positive() {
            ge
        } else {
            !ge
        }
    }

    /// Every assignment of the root domains in which no two tasks overlap.
    fn solutions(&self) -> Vec<Vec<i64>> {
        let mut out = Vec::new();
        let mut current = Vec::with_capacity(self.root.len());
        self.enumerate(&mut current, &mut out);
        out
    }

    fn enumerate(&self, current: &mut Vec<i64>, out: &mut Vec<Vec<i64>>) {
        let k = current.len();
        if k == self.root.len() {
            out.push(current.clone());
            return;
        }
        let (lb, ub) = self.root[k];
        for v in lb..=ub {
            let overlaps = (0..k)
                .any(|i| current[i] < v + self.durations[k] && v < current[i] + self.durations[i]);
            if !overlaps {
                current.push(v);
                self.enumerate(current, out);
                current.pop();
            }
        }
    }

    /// The first solution of the constraint that falsifies `clause`, if any.
    fn counterexample(&self, clause: &[Literal]) -> Option<Vec<i64>> {
        self.solutions()
            .into_iter()
            .find(|values| clause.iter().all(|&lit| !self.literal_holds(lit, values)))
    }

    fn describe(&self, clause: &[Literal]) -> String {
        clause
            .iter()
            .map(|&lit| {
                let b = self.encoder.decode(lit.variable()).expect("decodable");
                let task = self.starts.iter().position(|&s| s == b.var).expect("task");
                if lit.is_positive() {
                    format!("[s{task} >= {}]", b.value)
                } else {
                    format!("[s{task} <= {}]", b.value - 1)
                }
            })
            .collect::<Vec<_>>()
            .join(" | ")
    }

    /// Run the propagator and return every clause it produced, with a flag
    /// saying whether it was a conflict.
    fn clauses(&self) -> Vec<(bool, Vec<Literal>)> {
        let mut prop = self.propagator();
        match prop.propagate(&self.trail, &self.encoder) {
            PropagationResult::NoChange => Vec::new(),
            PropagationResult::Propagated(clauses) => {
                clauses.into_iter().map(|c| (false, c)).collect()
            }
            PropagationResult::Conflict(clause) => vec![(true, clause)],
        }
    }

    /// Check the shape a CDCL core relies on: a conflict clause is false on
    /// the current trail; a propagation clause has its first literal unset or
    /// true and every other literal false.
    fn assert_clause_shape(&self, conflict: bool, clause: &[Literal]) {
        let current = |lit: Literal| -> Option<bool> {
            let b = self.encoder.decode(lit.variable()).expect("decodable");
            let (lb, ub) = (self.trail.lb(b.var), self.trail.ub(b.var));
            let ge = if lb >= b.value {
                Some(true)
            } else if ub < b.value {
                Some(false)
            } else {
                None
            };
            ge.map(|g| g == lit.is_positive())
        };
        let reasons = if conflict { clause } else { &clause[1..] };
        for &lit in reasons {
            assert_eq!(
                current(lit),
                Some(false),
                "reason literal not false on the trail in {}",
                self.describe(clause)
            );
        }
    }
}

/// Edge-finding derives `s1 >= 5` from task 0 being confined to `[0, 1]`
/// (task 1 is too long to precede it; comparing with lct(Theta) it also
/// cannot precede task 2, giving `s1 >= 6`). The reason must bound task 0's
/// completion: before the fix it named only lower bounds, giving the clause
/// `[s1 >= 5] | [s0 <= -1] | [s2 <= -1] | [s1 >= 21]`, which the solution
/// `s0 = 8, s1 = 0, s2 = 7` falsifies. Learned at the root it removes
/// every schedule in which task 1 runs first.
#[test]
fn test_edge_finding_reason_names_theta_upper_bounds() {
    let mut inst = Instance::new(&[(0, 20), (0, 20), (0, 10)], &[5, 7, 1]);
    inst.tighten(0, 0, 1);
    let clauses = inst.clauses();
    assert!(
        clauses.iter().any(|(conflict, c)| !conflict
            && inst.literal_holds(c[0], &[0, 20, 0])
            && !inst.literal_holds(c[0], &[0, 4, 0])),
        "edge-finding should still derive s1 >= 5 (or more)"
    );
    for (conflict, clause) in &clauses {
        inst.assert_clause_shape(*conflict, clause);
        assert_eq!(
            inst.counterexample(clause),
            None,
            "unsound clause {}",
            inst.describe(clause)
        );
    }
}

/// Vilím's edge-finding compares `ect(Θ ∪ {i})` with `lct(Θ)`, the latest
/// completion still in Theta. Task 0 is confined to `[0, 1]`, so task 1
/// (`d = 3`) cannot precede it and must start at 5 or later. Comparing with
/// the lct of the task just moved to Lambda instead (23, before 2026-11-18)
/// never detects it.
#[test]
fn test_edge_finding_compares_with_theta_lct() {
    let mut inst = Instance::new(&[(0, 20), (0, 20)], &[5, 3]);
    inst.tighten(0, 0, 1);
    let clauses = inst.clauses();
    assert!(
        clauses.iter().any(|(conflict, c)| !conflict
            && inst.literal_holds(c[0], &[0, 5])
            && !inst.literal_holds(c[0], &[0, 4])),
        "edge-finding should derive s1 >= 5: {:?}",
        clauses
            .iter()
            .map(|(_, c)| inst.describe(c))
            .collect::<Vec<_>>()
    );
    for (conflict, clause) in &clauses {
        inst.assert_clause_shape(*conflict, clause);
        assert_eq!(
            inst.counterexample(clause),
            None,
            "unsound clause {}",
            inst.describe(clause)
        );
    }
}

/// Mirror image (`s -> 30 - s - d`) of the test above: task 0 confined to
/// `[24, 25]` forces the long task 1 to finish before task 0 starts, so
/// `s1 <= 18`; the reason must name task 0's lower bound.
#[test]
fn test_edge_finding_upper_reason_names_theta_lower_bounds() {
    let mut inst = Instance::new(&[(5, 25), (3, 23), (19, 29)], &[5, 7, 1]);
    inst.tighten(0, 24, 25);
    let clauses = inst.clauses();
    assert!(
        clauses.iter().any(|(conflict, c)| !conflict
            && inst.literal_holds(c[0], &[24, 3, 19])
            && !inst.literal_holds(c[0], &[24, 19, 19])),
        "edge-finding should still derive s1 <= 18 (or less)"
    );
    for (conflict, clause) in &clauses {
        inst.assert_clause_shape(*conflict, clause);
        assert_eq!(
            inst.counterexample(clause),
            None,
            "unsound clause {}",
            inst.describe(clause)
        );
    }
}

/// An overload conflict over a subset of the tasks must hold whatever the
/// other tasks do: it may only name the bounds of the overloaded tasks, and
/// those must make the overload real.
#[test]
fn test_overload_conflict_is_valid() {
    let mut inst = Instance::new(&[(0, 9), (0, 9), (0, 9)], &[3, 3, 2]);
    inst.tighten(0, 0, 1);
    inst.tighten(1, 0, 1);
    let clauses = inst.clauses();
    assert!(clauses.iter().any(|(conflict, _)| *conflict));
    for (conflict, clause) in &clauses {
        inst.assert_clause_shape(*conflict, clause);
        assert_eq!(
            inst.counterexample(clause),
            None,
            "unsound clause {}",
            inst.describe(clause)
        );
    }
}

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
}

/// Random small machines, random search states: every reason and conflict
/// clause must be satisfied by every solution of the constraint over the
/// root domains (brute force), and must have the shape the SAT core needs.
#[test]
fn test_random_disjunctive_clauses_hold_in_every_solution() {
    let mut checked = 0usize;
    for seed in 1..=3000u64 {
        let mut rng = Rng(seed.wrapping_mul(0x9e37_79b9_7f4a_7c15) | 1);
        let n = usize::try_from(rng.range(2, 4)).expect("small");
        let horizon = rng.range(6, 14);
        let mut root = Vec::with_capacity(n);
        let mut durations = Vec::with_capacity(n);
        for _ in 0..n {
            let lb = rng.range(0, horizon / 2);
            let ub = rng.range(lb, horizon);
            root.push((lb, ub));
            durations.push(rng.range(1, 5));
        }
        let mut inst = Instance::new(&root, &durations);
        for _ in 0..rng.range(0, 3) {
            let task =
                usize::try_from(rng.range(0, i64::try_from(n).expect("small") - 1)).expect("small");
            let (lb, ub) = (
                inst.trail.lb(inst.starts[task]),
                inst.trail.ub(inst.starts[task]),
            );
            let new_lb = rng.range(lb, ub);
            let new_ub = rng.range(new_lb, ub);
            inst.tighten(task, new_lb, new_ub);
        }
        for (conflict, clause) in inst.clauses() {
            checked += 1;
            inst.assert_clause_shape(conflict, &clause);
            if let Some(values) = inst.counterexample(&clause) {
                panic!(
                    "seed {seed}: root {root:?} durations {durations:?}: {} clause {} \
                     is falsified by the solution {values:?}",
                    if conflict { "conflict" } else { "reason" },
                    inst.describe(&clause)
                );
            }
        }
    }
    assert!(checked > 200, "too few clauses exercised: {checked}");
}
