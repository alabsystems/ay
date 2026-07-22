// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Differential fuzz for the push/pop learned-clause leak (soundness).
//!
//! Contract under test: after `pop()`, NO trace of the popped scope may flip
//! a later `check-sat` from SAT to UNSAT (or vice versa). Every verdict must
//! be derivable from the currently-asserted formula alone.
//!
//! Strategy: random small CNFs solved in a multi-scope incremental session
//! are compared against a fresh single-shot solver per scope. Any verdict
//! mismatch is a state leak across `pop()`.

use crate::solver::types::SatResult;
use crate::solver::Solver;
use crate::{Literal, Variable};

/// xorshift64* — deterministic, no external deps.
struct Rng(u64);

impl Rng {
    fn new(seed: u64) -> Self {
        Rng(seed.wrapping_mul(2685821657736338717).max(1))
    }
    fn next(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x >> 12;
        x ^= x << 25;
        x ^= x >> 27;
        self.0 = x;
        x.wrapping_mul(2685821657736338717)
    }
    fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }
}

const NVARS: usize = 6;

fn random_clause(rng: &mut Rng) -> Vec<Literal> {
    let len = 1 + rng.below(3) as usize;
    let mut lits = Vec::with_capacity(len);
    for _ in 0..len {
        let var = Variable(rng.below(NVARS as u64) as u32);
        let lit = if rng.below(2) == 0 {
            Literal::positive(var)
        } else {
            Literal::negative(var)
        };
        if !lits.contains(&lit) && !lits.contains(&lit.negated()) {
            lits.push(lit);
        }
    }
    if lits.is_empty() {
        lits.push(Literal::positive(Variable(0)));
    }
    lits
}

fn random_clauses(rng: &mut Rng, min: usize, extra: u64) -> Vec<Vec<Literal>> {
    let n = min + rng.below(extra) as usize;
    (0..n).map(|_| random_clause(rng)).collect()
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Verdict {
    Sat,
    Unsat,
    Unknown,
}

fn verdict(result: &SatResult) -> Verdict {
    match result {
        SatResult::Sat(_) => Verdict::Sat,
        SatResult::Unsat(_) => Verdict::Unsat,
        SatResult::Unknown => Verdict::Unknown,
    }
}

fn solve_verdict(solver: &mut Solver) -> Verdict {
    verdict(solver.solve().result())
}

/// Single-shot reference: fresh solver, all clauses, one solve.
fn reference_verdict(clause_sets: &[&[Vec<Literal>]]) -> Verdict {
    let mut solver = Solver::new(NVARS);
    for set in clause_sets {
        for clause in *set {
            solver.add_clause(clause.clone());
        }
    }
    solve_verdict(&mut solver)
}

/// Sequential scopes at depth 1: (push A check pop)(push B check pop)...
/// This is exactly the downstream k-induction multi-property script shape.
fn run_sequential_session(seed: u64, lrat: bool) {
    let mut rng = Rng::new(seed);
    let base = random_clauses(&mut rng, 0, 3);
    let scopes: Vec<Vec<Vec<Literal>>> = (0..4).map(|_| random_clauses(&mut rng, 2, 7)).collect();

    let mut solver = if lrat {
        let mut s = Solver::new(NVARS);
        s.enable_lrat();
        s
    } else {
        Solver::new(NVARS)
    };
    for clause in &base {
        solver.add_clause(clause.clone());
    }

    for (i, scope) in scopes.iter().enumerate() {
        solver.push();
        for clause in scope {
            solver.add_clause(clause.clone());
        }
        let incremental = solve_verdict(&mut solver);
        let reference = reference_verdict(&[&base, scope]);
        assert!(
            incremental == reference
                || incremental == Verdict::Unknown
                || reference == Verdict::Unknown,
            "push/pop state leak (seed={seed}, scope={i}, lrat={lrat}): \
             incremental={incremental:?} but fresh-solver reference={reference:?}\n\
             base={base:?}\nscope={scope:?}",
        );
        assert!(solver.pop());
    }
}

/// Nested scopes to depth 4 — exercises the 2-bit scope_lim saturation
/// boundary (stamps >= 3 are ambiguous).
fn run_nested_session(seed: u64) {
    let mut rng = Rng::new(seed);
    let base = random_clauses(&mut rng, 0, 3);
    // Two rounds of depth-4 nesting with checks at every level on the way
    // down and after every pop on the way back up.
    let mut solver = Solver::new(NVARS);
    for clause in &base {
        solver.add_clause(clause.clone());
    }

    for round in 0..2 {
        let levels: Vec<Vec<Vec<Literal>>> =
            (0..4).map(|_| random_clauses(&mut rng, 1, 5)).collect();
        // Push down.
        for (depth, level) in levels.iter().enumerate() {
            solver.push();
            for clause in level {
                solver.add_clause(clause.clone());
            }
            let incremental = solve_verdict(&mut solver);
            let mut sets: Vec<&[Vec<Literal>]> = vec![&base];
            for l in &levels[..=depth] {
                sets.push(l);
            }
            let reference = reference_verdict(&sets);
            assert!(
                incremental == reference
                    || incremental == Verdict::Unknown
                    || reference == Verdict::Unknown,
                "nested push leak (seed={seed}, round={round}, depth={}): \
                 incremental={incremental:?} reference={reference:?}\n\
                 base={base:?}\nlevels={levels:?}",
                depth + 1,
            );
        }
        // Pop back up, re-checking at every level.
        for depth in (0..levels.len()).rev() {
            assert!(solver.pop());
            let incremental = solve_verdict(&mut solver);
            let mut sets: Vec<&[Vec<Literal>]> = vec![&base];
            for l in &levels[..depth] {
                sets.push(l);
            }
            let reference = reference_verdict(&sets);
            assert!(
                incremental == reference
                    || incremental == Verdict::Unknown
                    || reference == Verdict::Unknown,
                "nested pop leak (seed={seed}, round={round}, post-pop depth={depth}): \
                 incremental={incremental:?} reference={reference:?}\n\
                 base={base:?}\nlevels={levels:?}",
            );
        }
    }
}

#[test]
fn fuzz_pushpop_sequential_depth1_default() {
    for seed in 0..400 {
        run_sequential_session(seed, false);
    }
}

#[test]
fn fuzz_pushpop_sequential_depth1_lrat() {
    for seed in 0..400 {
        run_sequential_session(seed, true);
    }
}

#[test]
fn fuzz_pushpop_nested_depth4() {
    for seed in 0..300 {
        run_nested_session(seed);
    }
}

// ---------------------------------------------------------------------------
// Hard-instance variant: near-phase-transition 3-SAT scopes over shared vars
// to force real CDCL conflict learning inside scopes (units, long resolution
// chains), then verify later scopes against a fresh solver.
// ---------------------------------------------------------------------------

const HARD_NVARS: usize = 30;

fn hard_clause(rng: &mut Rng) -> Vec<Literal> {
    let mut lits = Vec::with_capacity(3);
    while lits.len() < 3 {
        let var = Variable(rng.below(HARD_NVARS as u64) as u32);
        let lit = if rng.below(2) == 0 {
            Literal::positive(var)
        } else {
            Literal::negative(var)
        };
        if !lits.contains(&lit) && !lits.contains(&lit.negated()) {
            lits.push(lit);
        }
    }
    lits
}

fn hard_clauses(rng: &mut Rng, n: usize) -> Vec<Vec<Literal>> {
    (0..n).map(|_| hard_clause(rng)).collect()
}

fn hard_reference_verdict(clause_sets: &[&[Vec<Literal>]]) -> Verdict {
    let mut solver = Solver::new(HARD_NVARS);
    for set in clause_sets {
        for clause in *set {
            solver.add_clause(clause.clone());
        }
    }
    solve_verdict(&mut solver)
}

/// Hard sequential session: scope 1 is clause-heavy (usually UNSAT, forcing
/// heavy conflict learning), later scopes are lighter (usually SAT). A leaked
/// scope-1-derived clause flips a later SAT verdict to UNSAT.
fn run_hard_sequential_session(seed: u64, lrat: bool) {
    let mut rng = Rng::new(seed ^ 0xDEAD_BEEF);
    // Sparse base so scopes dominate.
    let base = hard_clauses(&mut rng, 20);
    // Scope clause counts: first heavy (ratio ~5.3 incl. base → mostly UNSAT),
    // later light (mostly SAT).
    let counts = [140usize, 60, 90, 40];
    let scopes: Vec<Vec<Vec<Literal>>> =
        counts.iter().map(|&n| hard_clauses(&mut rng, n)).collect();

    let mut solver = if lrat {
        let mut s = Solver::new(HARD_NVARS);
        s.enable_lrat();
        s
    } else {
        Solver::new(HARD_NVARS)
    };
    for clause in &base {
        solver.add_clause(clause.clone());
    }

    for (i, scope) in scopes.iter().enumerate() {
        solver.push();
        for clause in scope {
            solver.add_clause(clause.clone());
        }
        // Solve twice: the second solve exercises the incremental-reset path
        // with learned state from the first.
        let _ = solver.solve();
        let incremental = solve_verdict(&mut solver);
        let reference = hard_reference_verdict(&[&base, scope]);
        assert!(
            incremental == reference
                || incremental == Verdict::Unknown
                || reference == Verdict::Unknown,
            "hard push/pop state leak (seed={seed}, scope={i}, lrat={lrat}): \
             incremental={incremental:?} but fresh-solver reference={reference:?}",
        );
        assert!(solver.pop());
    }

    // Final base-only check: all scopes popped, verdict must match base alone.
    let incremental = solve_verdict(&mut solver);
    let reference = hard_reference_verdict(&[&base]);
    assert!(
        incremental == reference
            || incremental == Verdict::Unknown
            || reference == Verdict::Unknown,
        "hard post-pop base leak (seed={seed}, lrat={lrat}): \
         incremental={incremental:?} reference={reference:?}",
    );
}

#[test]
fn fuzz_pushpop_hard_sequential_default() {
    for seed in 0..60 {
        run_hard_sequential_session(seed, false);
    }
}

#[test]
fn fuzz_pushpop_hard_sequential_lrat() {
    for seed in 0..60 {
        run_hard_sequential_session(seed, true);
    }
}

/// Hard nested session at depth 4 (past the 2-bit scope_lim saturation):
/// inner scopes force conflict learning; verify on the way back up.
fn run_hard_nested_session(seed: u64) {
    let mut rng = Rng::new(seed ^ 0xFEED_FACE);
    let base = hard_clauses(&mut rng, 20);
    let counts = [40usize, 40, 40, 60];
    let levels: Vec<Vec<Vec<Literal>>> =
        counts.iter().map(|&n| hard_clauses(&mut rng, n)).collect();

    let mut solver = Solver::new(HARD_NVARS);
    for clause in &base {
        solver.add_clause(clause.clone());
    }

    for level in &levels {
        solver.push();
        for clause in level {
            solver.add_clause(clause.clone());
        }
        let _ = solver.solve();
    }
    // Pop back up, checking against fresh reference at every level.
    for depth in (0..levels.len()).rev() {
        assert!(solver.pop());
        let incremental = solve_verdict(&mut solver);
        let mut sets: Vec<&[Vec<Literal>]> = vec![&base];
        for l in &levels[..depth] {
            sets.push(l);
        }
        let reference = hard_reference_verdict(&sets);
        assert!(
            incremental == reference
                || incremental == Verdict::Unknown
                || reference == Verdict::Unknown,
            "hard nested pop leak (seed={seed}, post-pop depth={depth}): \
             incremental={incremental:?} reference={reference:?}",
        );
    }
}

#[test]
fn fuzz_pushpop_hard_nested_depth4() {
    for seed in 0..40 {
        run_hard_nested_session(seed);
    }
}
