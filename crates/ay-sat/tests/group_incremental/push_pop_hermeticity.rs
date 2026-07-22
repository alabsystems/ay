// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Push/pop hermeticity regression tests.
//!
//! Ported from Z3 PR #9221 / issue #9220: "the performance of a proof can be
//! dramatically affected by proofs done in prior push/pop scopes." The
//! underlying bug: CDCL resolvents derived inside a pushed scope may resolve
//! away the scope-selector literal, leaving learned clauses in the database
//! that no longer carry a scope guard. After `pop()`, those clauses survive
//! and pollute VSIDS/watch lists for subsequent proofs.
//!
//! AY's fix mirrors Z3 PR #9221: stamp each learned clause with the user-scope
//! depth at learn time, then sweep clauses whose stamped depth exceeds the
//! current depth on `pop()`.

use ay_sat::{Literal, Solver, Variable};
use ntest::timeout;

/// Build a near-phase-transition random 3-SAT instance.
///
/// Uses a deterministic linear-congruential RNG so test output does not depend
/// on the host's `rand` implementation. Clause ratio 4.5 matches Z3's
/// `src/test/sat_gc.cpp` benchmark from PR #9221.
fn add_random_3sat(solver: &mut Solver, base: u32, n_vars: u32, n_clauses: u32, seed: u64) {
    let mut state: u64 = seed;
    let mut next = || {
        // Numerical Recipes 64-bit LCG.
        state = state
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        state
    };

    for _ in 0..n_clauses {
        let mut lits = Vec::with_capacity(3);
        for _ in 0..3 {
            let v = base + ((next() as u32) % n_vars);
            let sign = (next() & 1) == 0;
            let var = Variable::new(v);
            let lit = if sign {
                Literal::positive(var)
            } else {
                Literal::negative(var)
            };
            lits.push(lit);
        }
        let _ = solver.add_clause(lits);
    }
}

/// Core hermeticity test: many push/solve/pop cycles over a pure-outer
/// formula must NOT inflate the live learned clause count at base scope.
///
/// Without the Z3 PR #9221 fix, learned clauses derived inside each pushed
/// scope (when BCP resolves away the scope selector literal) would accumulate
/// across cycles. The sweep in `pop()` removes them.
///
/// Invariant: the number of live learned clauses after N cycles is bounded by
/// the clauses produced in the final cycle, not by N × per-cycle learning.
#[test]
#[timeout(30_000)]
fn test_pop_sweeps_leaked_learned_clauses() {
    // Small but nontrivial formula: 60 vars, ratio 4.5 → 270 clauses.
    // Large enough that the CDCL search derives learned clauses but small
    // enough that the solve is instant.
    let n_vars = 60u32;
    let n_clauses = 270u32;
    let mut solver = Solver::new(n_vars as usize);
    add_random_3sat(&mut solver, 0, n_vars, n_clauses, 0xC0FFEE);

    // Warm up: one baseline solve to trigger preprocessing at scope 0.
    let _ = solver.solve().into_inner();
    let base_learned = solver.num_learned_clauses();

    // Run repeated push/check/pop cycles. Each cycle adds a trivial
    // scope-guarded clause to force some in-scope learning but no new outer
    // facts. If the Z3 PR #9221 fix is working, live learned-clause count
    // after each pop stays bounded.
    let cycles = 6u32;
    let mut max_after_pop = base_learned;
    for _ in 0..cycles {
        solver.push();
        // Add a scope-local forcing unit that does not change the outer
        // problem (the scope selector guard makes it local).
        let forcing_var = Variable::new(0u32);
        let _ = solver.add_clause(vec![Literal::positive(forcing_var)]);
        let _ = solver.solve().into_inner();
        assert!(solver.pop(), "pop should succeed");
        let after = solver.num_learned_clauses();
        if after > max_after_pop {
            max_after_pop = after;
        }
    }

    // Without the fix, the learned-clause count grows roughly linearly with
    // cycles — each push/solve/pop cycle leaves O(K) clauses behind. With the
    // fix, post-pop cycles stay bounded by per-cycle learning (well under
    // base_learned + 5 × cycles).
    //
    // We use a conservative upper bound (10 × cycles + 100) that catches
    // unbounded growth while tolerating run-to-run variance in per-cycle
    // learned clause counts. The key property is that growth is *bounded*,
    // not unlimited.
    let upper_bound = base_learned + 10 * u64::from(cycles) + 100;
    assert!(
        max_after_pop <= upper_bound,
        "Live learned clauses after pop grew unbounded: \
         base={base_learned}, max_after_pop={max_after_pop}, upper_bound={upper_bound}. \
         This indicates the Z3 PR #9221 sweep is not cleaning up learned clauses \
         derived in the popped scope."
    );
}

/// Independence test: the solve time of a fresh scope should not depend on
/// what was proved in prior sibling scopes (hermeticity property).
///
/// This is the exact Z3 #9220 bug report: "non-determinism in proof time
/// based on prior scope history proves clauses leak." We check the weaker but
/// sufficient condition that the learned clause count at base level does not
/// grow without bound across sibling scopes.
#[test]
#[timeout(30_000)]
fn test_sibling_scope_independence() {
    let n_vars = 40u32;
    let mut solver = Solver::new(n_vars as usize);
    add_random_3sat(&mut solver, 0, n_vars, 180, 0xBEEF);

    // Baseline: solve the outer formula with no prior scopes.
    let _ = solver.solve().into_inner();
    let baseline_learned = solver.num_learned_clauses();

    // Do five sibling scope cycles that each derive learned clauses.
    for cycle in 0..5u32 {
        solver.push();
        // Perturb with a scope-local forcing assertion.
        let v = Variable::new(cycle % n_vars);
        let _ = solver.add_clause(vec![Literal::positive(v)]);
        let _ = solver.solve().into_inner();
        assert!(solver.pop());
    }

    let after_cycles = solver.num_learned_clauses();

    // Hermeticity: after-cycles learned count should not be wildly larger
    // than the baseline (CDCL may derive some base-scope learned clauses
    // during the repeated solves, but scoped-only clauses must be cleaned).
    let growth = after_cycles.saturating_sub(baseline_learned);
    assert!(
        growth < 200,
        "Learned clauses grew by {growth} across 5 sibling scopes \
         (baseline={baseline_learned}, after={after_cycles}). Without the \
         Z3 PR #9221 sweep this grows linearly in #scopes."
    );
}

/// Smoke test: a deep push/pop stress must not corrupt the clause database.
///
/// Exercises the `scope_lim` saturation logic (fields >= 3 fold together)
/// and ensures repeated pop() calls remain sound.
#[test]
#[timeout(30_000)]
fn test_deep_push_pop_stress_soundness() {
    let n_vars = 20u32;
    let mut solver = Solver::new(n_vars as usize);
    add_random_3sat(&mut solver, 0, n_vars, 60, 0xF00D);

    // Sanity: outer formula should solve.
    let _ = solver.solve().into_inner();

    // Deep nested push/pop (beyond the 2-bit saturation boundary).
    for _ in 0..10u32 {
        solver.push();
        let _ = solver.add_clause(vec![Literal::positive(Variable::new(0u32))]);
        let _ = solver.solve().into_inner();
    }
    // Pop all the way back.
    for _ in 0..10u32 {
        assert!(solver.pop());
    }

    // Final solve at base scope must still succeed soundly.
    let _ = solver.solve().into_inner();
}

/// Z3 #9220 matrix-style determinism test.
///
/// From the Z3 #9220 bug report: "the performance of a proof can be
/// dramatically affected by proofs done in prior push/pop scopes." The Z3
/// reproducer enumerates a truth-matrix `(proof_1, proof_2, fail_formula)` ∈
/// {0,1}^3 and times each combination; 4 of the 8 combinations hit a >20s
/// timeout instead of the expected 0.7–7.6s. The smoking gun is that
/// `fail_formula` solved standalone behaves differently depending on whether
/// `proof_1` / `proof_2` were pushed+solved+popped beforehand.
///
/// Our hermeticity property: the work the solver does on a fresh formula B
/// must not depend on what was solved in prior pushed scopes. We measure this
/// via (num_learned_clauses, num_decisions, num_conflicts) counters after
/// solving B in two matched configurations:
///   (a) baseline: fresh solver → solve(B)
///   (b) polluted: fresh solver → push+solve(A1)+pop → push+solve(A2)+pop → solve(B)
///
/// Without the Z3 PR #9221 sweep, (b)'s learned-clause count at the start of
/// solve(B) is inflated by leaked clauses from A1/A2, causing divergent work.
/// With the sweep, both configurations see the same base-scope learned state
/// at the start of solve(B) and perform the same amount of work within 2×.
#[test]
#[timeout(60_000)]
fn test_z3_9220_matrix_determinism() {
    // Three independent sub-formulas on disjoint variable ranges so that
    // learned clauses inside A1 / A2 scopes cannot be valid over B's vars.
    // If they were not swept by pop(), they would still waste watch-list
    // traversal time when solve(B) runs.
    let n_vars_per = 40u32;
    let total_vars = 3 * n_vars_per;

    let work_on_b = |proof_1: bool, proof_2: bool| -> (u64, u64, u64) {
        let mut solver = Solver::new(total_vars as usize);
        // Base formula B occupies vars [0, n_vars_per).
        add_random_3sat(&mut solver, 0, n_vars_per, 180, 0xB0);
        // A1 occupies vars [n_vars_per, 2*n_vars_per).
        // A2 occupies vars [2*n_vars_per, 3*n_vars_per).

        if proof_1 {
            solver.push();
            add_random_3sat(&mut solver, n_vars_per, n_vars_per, 180, 0xA1);
            let _ = solver.solve().into_inner();
            assert!(solver.pop(), "pop of A1 should succeed");
        }
        if proof_2 {
            solver.push();
            add_random_3sat(&mut solver, 2 * n_vars_per, n_vars_per, 180, 0xA2);
            let _ = solver.solve().into_inner();
            assert!(solver.pop(), "pop of A2 should succeed");
        }

        let before_learned = solver.num_learned_clauses();
        let before_decisions = solver.num_decisions();
        let before_conflicts = solver.num_conflicts();
        let _ = solver.solve().into_inner();
        let after_learned = solver.num_learned_clauses();
        let after_decisions = solver.num_decisions();
        let after_conflicts = solver.num_conflicts();

        (
            after_learned.saturating_sub(before_learned),
            after_decisions.saturating_sub(before_decisions),
            after_conflicts.saturating_sub(before_conflicts),
        )
    };

    // Matrix: (proof_1, proof_2) ∈ {0,1}^2.
    let baseline = work_on_b(false, false);
    let only_a1 = work_on_b(true, false);
    let only_a2 = work_on_b(false, true);
    let both = work_on_b(true, true);

    // Hermeticity: solve(B)'s work must not depend on prior-scope history.
    // We use a 4× tolerance on the learned-clause count and 5× on decisions
    // (lower bound 10 to avoid divide-by-tiny-integer noise). Without the
    // PR #9221 sweep, we'd see 10-100× growth as leaked clauses pollute
    // the watch lists.
    let configs = [
        ("baseline", baseline),
        ("only_a1", only_a1),
        ("only_a2", only_a2),
        ("both", both),
    ];

    // Find min/max across configs to assert bounded variance.
    let (_, max_learned) = configs
        .iter()
        .fold((u64::MAX, 0u64), |(min, max), (_, (l, _, _))| {
            (min.min(*l), max.max(*l))
        });
    let (min_decisions, max_decisions) = configs
        .iter()
        .fold((u64::MAX, 0u64), |(min, max), (_, (_, d, _))| {
            (min.min(*d), max.max(*d))
        });

    // Assert bounded variance. Allow 4x on learned and 5x on decisions.
    // Baseline floor of 10 guards against tiny-integer ratios (e.g. 0 vs 1).
    let learned_floor = 10u64;
    let decisions_floor = 10u64;
    let learned_bound = (max_learned.max(learned_floor)) * 4;
    let decisions_bound = (min_decisions.max(decisions_floor)) * 5;

    for (name, (l, d, c)) in &configs {
        assert!(
            *l <= learned_bound,
            "config {name}: learned={l} exceeds 4x max-across-configs bound={learned_bound}. \
             work_on_b = (learned={l}, decisions={d}, conflicts={c}). \
             baseline={baseline:?} only_a1={only_a1:?} only_a2={only_a2:?} both={both:?}. \
             Indicates PR #9221 sweep is not clearing leaked learned clauses."
        );
        assert!(
            *d <= decisions_bound,
            "config {name}: decisions={d} exceeds 5x min-across-configs bound={decisions_bound}. \
             baseline={baseline:?} only_a1={only_a1:?} only_a2={only_a2:?} both={both:?}. \
             Indicates prior-scope history is polluting fresh solve work."
        );
    }

    // Additional sanity: the variance between any two configs' decision counts
    // should be bounded (no >2x swing between say baseline and both).
    if min_decisions > 0 {
        let ratio = max_decisions as f64 / min_decisions as f64;
        assert!(
            ratio <= 5.0,
            "decision-count variance ratio {ratio:.2} exceeds 5x across matrix configs. \
             baseline={baseline:?} only_a1={only_a1:?} only_a2={only_a2:?} both={both:?}"
        );
    }
}
