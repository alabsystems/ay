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

// ---------------------------------------------------------------------------
// #unguarded-tvalid-lemmas: permanent retention of T-valid theory conflict
// lemmas (`add_theory_conflict_lemma` + `unguarded_theory_conflict_lemmas`).
//
// Contract under test:
// (1) flag-on vs flag-off VERDICT IDENTITY per check — a persisted T-valid
//     lemma may only prune assignments the theory forbids anyway;
// (2) flag-on cross-solve carryover is real and observable: from cycle 2 on,
//     conflicts fire on clauses born in a PRIOR solve
//     (`conflicts_from_prior_solve_clauses` > 0), which is impossible in the
//     scoped regime where the lemma pool dies at every pop.
// ---------------------------------------------------------------------------

/// Deterministic .ind-shaped session: base assertions, then k cycles of
/// (push; assert property of alternating polarity; check; pop). The "theory"
/// contributes two tautologies over the atom vars p1, p2:
///   L+ = (¬p1 ∨ ¬p2)   and   L- = (p1 ∨ p2)
/// (i.e. the theory forbids p1 ∧ p2 and ¬p1 ∧ ¬p2 — think of two
/// contradictory bound conjunctions). Odd cycles assert the property
/// {p1, p2} (conflicts L+), even cycles assert {¬p1, ¬p2} (conflicts L-),
/// so EVERY cycle is theory-UNSAT while the base alone stays SAT.
///
/// Flag ON models permanent retention: the lemmas are injected once (cycle 1)
/// and must keep answering every later cycle. Flag OFF models the scoped
/// regime: the pool dies at each pop, so the lemmas are re-injected each
/// cycle (what the theory re-derivation does today).
fn run_ind_shaped_session(unguarded: bool, k: usize) -> (Vec<Verdict>, Vec<u64>) {
    let p1 = Literal::positive(Variable(0));
    let p2 = Literal::positive(Variable(1));
    let q = Literal::positive(Variable(2));

    let mut solver = Solver::new(3);
    // Production inc-engine profile (the lane where the flag ships): the
    // ic3-style state-preserving incremental reset is what carries learned
    // clauses across check-sats. A plain solver would drop ALL learned
    // clauses at the next full reset after pop() (ledger-census destructive
    // rebuild), masking the retention under test.
    solver.set_ic3_mode();
    solver.set_bve_enabled(false);
    solver.set_inc_engine_reset_mode(true);
    solver.set_unguarded_theory_conflict_lemmas(unguarded);
    // Base assertion (benign; keeps the base formula non-empty and SAT).
    assert!(solver.add_clause(vec![q, p1]));

    let mut verdicts = Vec::with_capacity(k);
    let mut prior_solve_conflicts = Vec::with_capacity(k);
    for cycle in 1..=k {
        solver.push();
        // Property of alternating polarity, asserted scoped (dies with pop).
        if cycle % 2 == 1 {
            assert!(solver.add_clause(vec![p1]));
            assert!(solver.add_clause(vec![p2]));
        } else {
            assert!(solver.add_clause(vec![p1.negated()]));
            assert!(solver.add_clause(vec![p2.negated()]));
        }
        // Theory conflict lemmas: once in cycle 1 when persisted, every
        // cycle when scoped (the scoped pool is deleted at each pop).
        if !unguarded || cycle == 1 {
            solver.add_theory_conflict_lemma(vec![p1.negated(), p2.negated()]);
            solver.add_theory_conflict_lemma(vec![p1, p2]);
        }
        verdicts.push(solve_verdict(&mut solver));
        prior_solve_conflicts.push(solver.conflicts_from_prior_solve_clauses());
        assert!(solver.pop());
    }

    // Base-only postlude: all scopes popped. The persisted tautologies must
    // NOT over-constrain the base formula (q ∨ p1 plus p1 XOR p2 is SAT).
    verdicts.push(solve_verdict(&mut solver));
    prior_solve_conflicts.push(solver.conflicts_from_prior_solve_clauses());
    (verdicts, prior_solve_conflicts)
}

#[test]
fn unguarded_tvalid_lemma_ind_shaped_verdict_identity_and_carryover() {
    const K: usize = 6;
    let (verdicts_on, prior_on) = run_ind_shaped_session(true, K);
    let (verdicts_off, _prior_off) = run_ind_shaped_session(false, K);

    // (1) Verdict identity flag-on vs flag-off, per check.
    assert_eq!(
        verdicts_on, verdicts_off,
        "unguarded T-valid lemma retention changed a verdict"
    );
    // Shape sanity: every property cycle is theory-UNSAT, the base-only
    // postlude is SAT.
    for (i, v) in verdicts_on.iter().enumerate().take(K) {
        assert_eq!(*v, Verdict::Unsat, "cycle {} must be UNSAT", i + 1);
    }
    assert_eq!(
        verdicts_on[K],
        Verdict::Sat,
        "base-only check after all pops must be SAT (persisted tautologies must not over-constrain)"
    );

    // (2) Flag-on carryover: from cycle 2 on, the UNSAT conflicts fire on
    // the lemmas born in cycle 1 — conflicts_from_prior_solve_clauses must
    // be nonzero and non-decreasing from cycle 2 onwards.
    assert!(
        prior_on[1] > 0,
        "cycle 2 must conflict on a prior-solve clause (persisted lemma), got {prior_on:?}"
    );
    for i in 2..K {
        assert!(
            prior_on[i] > prior_on[i - 1],
            "cycle {} must add prior-solve conflicts (persisted lemma re-fires), got {prior_on:?}",
            i + 1
        );
    }
}

#[test]
fn unguarded_tvalid_lemma_ind_shaped_assumption_level_conflicts_counted() {
    // Companion replay counter: the .ind-shaped conflicts fire inside the
    // scope-selector assumption prefix, so assumption_level_conflicts must
    // be nonzero already in cycle 1 (both flag settings).
    for unguarded in [false, true] {
        let p1 = Literal::positive(Variable(0));
        let p2 = Literal::positive(Variable(1));
        let mut solver = Solver::new(2);
        solver.set_unguarded_theory_conflict_lemmas(unguarded);
        solver.push();
        assert!(solver.add_clause(vec![p1]));
        assert!(solver.add_clause(vec![p2]));
        solver.add_theory_conflict_lemma(vec![p1.negated(), p2.negated()]);
        assert_eq!(solve_verdict(&mut solver), Verdict::Unsat);
        assert!(
            solver.assumption_level_conflicts() > 0,
            "conflict inside the scope-selector prefix must be counted (unguarded={unguarded})"
        );
        assert!(solver.pop());
    }
}

// ---------------------------------------------------------------------------
// Differential fuzz: flag-on vs flag-off over random push/assert/check/pop
// sequences with a simulated DPLL(T) refinement loop.
//
// A random fixed "theory" (a set of clauses over the atom vars) is treated as
// ground truth. Each check runs the classic lazy refinement loop: solve; if
// SAT, look for a theory clause violated by the model; if found, inject it
// via add_theory_conflict_lemma (a T-valid lemma — it is a clause of the
// theory) and re-solve. The fixpoint verdict equals
// verdict(base ∪ live-scoped ∪ theory) regardless of which lemmas were
// already persisted, so flag-on, flag-off, and a fresh reference solver must
// all agree on every check.
// ---------------------------------------------------------------------------

fn model_violates(model: &[bool], clause: &[Literal]) -> bool {
    clause.iter().all(|lit| {
        let idx = lit.variable().index();
        idx < model.len() && model[idx] != lit.is_positive()
    })
}

/// Lazy DPLL(T)-style refinement: solve, inject the first violated theory
/// clause, repeat to fixpoint. Returns the theory-consistent verdict.
fn theory_refine_solve(solver: &mut Solver, theory: &[Vec<Literal>]) -> Verdict {
    // Generous cap: each round either terminates or injects a violated
    // clause; re-violation of an injected clause within one check requires
    // it to have been deleted (deletable tier), which small tests never hit.
    for _round in 0..(4 * theory.len() + 8) {
        match solver.solve().into_inner() {
            SatResult::Unsat(_) => return Verdict::Unsat,
            SatResult::Unknown => return Verdict::Unknown,
            SatResult::Sat(model) => {
                let violated = theory.iter().find(|c| model_violates(&model, c));
                match violated {
                    None => return Verdict::Sat,
                    Some(clause) => {
                        solver.add_theory_conflict_lemma(clause.clone());
                    }
                }
            }
        }
    }
    Verdict::Unknown
}

/// Reference: fresh solver on base ∪ live scoped sets ∪ FULL theory.
fn theory_reference_verdict(
    base: &[Vec<Literal>],
    scoped: &[Vec<Vec<Literal>>],
    theory: &[Vec<Literal>],
) -> Verdict {
    let mut solver = Solver::new(NVARS);
    for clause in base.iter().chain(theory.iter()) {
        solver.add_clause(clause.clone());
    }
    for set in scoped {
        for clause in set {
            solver.add_clause(clause.clone());
        }
    }
    solve_verdict(&mut solver)
}

fn run_unguarded_differential_session(seed: u64) {
    let mut rng = Rng::new(seed ^ 0xC0FF_EE00);
    let base = random_clauses(&mut rng, 1, 3);
    // Fixed random theory: 2-5 clauses over the same atom vars. These are the
    // "T-valid lemmas" the simulated theory can report.
    let theory: Vec<Vec<Literal>> = (0..(2 + rng.below(4) as usize))
        .map(|_| random_clause(&mut rng))
        .collect();

    // Both arms use the production inc-engine profile (see the .ind-shaped
    // test above): the incremental reset is what lets flag-on lemmas persist.
    let mk = |unguarded: bool| {
        let mut s = Solver::new(NVARS);
        s.set_ic3_mode();
        s.set_bve_enabled(false);
        s.set_inc_engine_reset_mode(true);
        s.set_unguarded_theory_conflict_lemmas(unguarded);
        s
    };
    let mut s_off = mk(false);
    let mut s_on = mk(true);
    for clause in &base {
        s_off.add_clause(clause.clone());
        s_on.add_clause(clause.clone());
    }

    let mut scoped_stack: Vec<Vec<Vec<Literal>>> = Vec::new();
    let ok = |a: Verdict, b: Verdict| a == b || a == Verdict::Unknown || b == Verdict::Unknown;

    for step in 0..14 {
        // Force a final check so every session compares at least once.
        let op = if step == 13 { 2 } else { rng.below(3) };
        match op {
            0 if scoped_stack.len() < 3 => {
                s_off.push();
                s_on.push();
                let clauses = random_clauses(&mut rng, 1, 3);
                for clause in &clauses {
                    s_off.add_clause(clause.clone());
                    s_on.add_clause(clause.clone());
                }
                scoped_stack.push(clauses);
            }
            1 if !scoped_stack.is_empty() => {
                assert!(s_off.pop());
                assert!(s_on.pop());
                scoped_stack.pop();
            }
            2 => {
                let v_off = theory_refine_solve(&mut s_off, &theory);
                let v_on = theory_refine_solve(&mut s_on, &theory);
                let reference = theory_reference_verdict(&base, &scoped_stack, &theory);
                assert!(
                    ok(v_on, v_off) && ok(v_on, reference) && ok(v_off, reference),
                    "unguarded T-valid lemma differential mismatch \
                     (seed={seed}, step={step}, depth={}): \
                     flag_on={v_on:?} flag_off={v_off:?} reference={reference:?}\n\
                     base={base:?}\ntheory={theory:?}\nscoped={scoped_stack:?}",
                    scoped_stack.len(),
                );
            }
            _ => {}
        }
    }
}

#[test]
fn fuzz_unguarded_tvalid_lemma_differential() {
    for seed in 0..300 {
        run_unguarded_differential_session(seed);
    }
}
/// Regression (found by the differential fuzz above, seed 16): under the
/// inc-engine deferral, clauses added in still-live OUTER scopes must survive
/// a `pop()` of an inner scope that happens BEFORE the next solve. The old
/// `pop()` boundary sync (`boundary = ledger.num_clauses()`) marked the
/// deferred outer-scope clauses "already attached", so they never reached the
/// arena — wrong SAT with a model violating a live scoped clause.
#[test]
fn inc_engine_deferred_clauses_survive_pop_before_solve() {
    let x0 = Literal::positive(Variable(0));
    let x1 = Literal::positive(Variable(1));

    let mut solver = Solver::new(2);
    solver.set_ic3_mode();
    solver.set_bve_enabled(false);
    solver.set_inc_engine_reset_mode(true);

    assert!(solver.add_clause(vec![x0]));
    // Establish the incremental session (first solve attaches the base).
    assert_eq!(solve_verdict(&mut solver), Verdict::Sat);

    // Outer scope: deferred clauses (no solve before the inner pop!).
    solver.push();
    assert!(solver.add_clause(vec![x0.negated(), x1]));
    assert!(solver.add_clause(vec![x1.negated(), x0.negated()]));
    // Inner scope: pushed and popped without an intervening check.
    solver.push();
    assert!(solver.add_clause(vec![x1]));
    assert!(solver.pop());

    // The outer scope asserts x0 => x1 and x1 => !x0, with base x0: UNSAT.
    // Before the pop() boundary clamp, the two deferred outer clauses were
    // swallowed and this returned SAT.
    assert_eq!(
        solve_verdict(&mut solver),
        Verdict::Unsat,
        "deferred outer-scope clauses must survive an inner pop before the next solve"
    );

    assert!(solver.pop());
    assert_eq!(solve_verdict(&mut solver), Verdict::Sat);
}
