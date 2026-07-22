// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bench 2 Loop A: per-BCP `check_during_propagate` cost on a DRAGON-shaped
//! assertion set (the development design notes §2).
//!
//! Shape mirrors the lustre/DRAGON vmt-chc class: a wide next-state
//! transition relation (linear equality definitions of width 3-40 over a
//! shared Int state vector), several hundred inequality bound atoms, and a
//! Bool control block. The hot loop measures the eager-DPLL(T) per-decision
//! pattern: `push(); assert a few atoms; check_during_propagate(); pop();`.
//!
//! `#[ignore]`d: run explicitly with
//! `cargo test -p ay-lia --release bench2_loop_a -- --ignored --nocapture`.
//! Iteration count can be overridden via `AY_LIA_HOT_LOOP_ITERS`.

use super::*;
use ay_core::time::Instant;
use ay_core::Sort;

const NUM_STATE_VARS: usize = 160;
const NUM_BOOL_VARS: usize = 64;
const NUM_DEF_EQUALITIES: usize = 220;
const NUM_POOL_EQUALITIES: usize = 50;
const NUM_POOL_BOUNDS: usize = 200;

struct DragonShape {
    terms: TermStore,
    /// Atoms asserted once at scope 0 (next-state defs + bounds + bools).
    base_atoms: Vec<(TermId, bool)>,
    /// Held-out equality atoms asserted one-per-iteration inside the loop.
    pool_equalities: Vec<TermId>,
    /// Held-out bound atoms asserted four-per-iteration inside the loop.
    pool_bounds: Vec<TermId>,
}

/// Synthesize the DRAGON-shaped assertion set against a fresh TermStore:
/// 160 Int state vars + 64 Bool vars, 220 linear equality definitions of
/// width 3-40 (each defining a distinct def var, like ITE-lifted next-state
/// definitions), ~400 inequality bound atoms, constants in i32 range.
/// The set is satisfiable so the loop exercises the full BCP cascade
/// (gcd test, equality-key/dioph, bounds, modular) instead of
/// short-circuiting on an early conflict.
fn build_dragon_shape() -> DragonShape {
    let mut terms = TermStore::new();

    let state_vars: Vec<TermId> = (0..NUM_STATE_VARS)
        .map(|i| terms.mk_var(format!("x{i}"), Sort::Int))
        .collect();
    let bool_vars: Vec<TermId> = (0..NUM_BOOL_VARS)
        .map(|i| terms.mk_var(format!("b{i}"), Sort::Bool))
        .collect();
    // Next-state definition targets (one per equality, like primed state).
    let def_vars: Vec<TermId> = (0..NUM_DEF_EQUALITIES)
        .map(|i| terms.mk_var(format!("d{i}"), Sort::Int))
        .collect();

    let mut base_atoms: Vec<(TermId, bool)> = Vec::new();

    // ~220 linear equality definitions of width 3-40:
    //   d_i = c0 + sum_j coeff_j * x_{(...)%160}
    for (i, &lhs) in def_vars.iter().enumerate() {
        let width = 3 + (i * 7) % 38;
        let mut sum_args = Vec::with_capacity(width);
        for j in 1..width {
            let var = state_vars[(i * 13 + j * 29) % NUM_STATE_VARS];
            let coeff = 1 + ((i + j) % 5) as i64;
            let coeff_term = terms.mk_int(BigInt::from(coeff));
            let prod = terms.mk_mul(vec![coeff_term, var]);
            sum_args.push(prod);
        }
        let c = (i as i64 * 7919) % 60_000 - 30_000;
        sum_args.push(terms.mk_int(BigInt::from(c)));
        let rhs = terms.mk_add(sum_args);
        let eq = terms.mk_eq(lhs, rhs);
        base_atoms.push((eq, true));
    }

    // ~400 inequality bound atoms over the state vars (mutually consistent).
    for (k, &v) in state_vars.iter().enumerate() {
        let lo = terms.mk_int(BigInt::from(-(100_000 + k as i64)));
        let hi = terms.mk_int(BigInt::from(100_000 + k as i64));
        let ge = terms.mk_ge(v, lo);
        let le = terms.mk_le(v, hi);
        base_atoms.push((ge, true));
        base_atoms.push((le, true));
    }
    for k in 0..80usize {
        let v = state_vars[(k * 31) % NUM_STATE_VARS];
        let b = terms.mk_int(BigInt::from(-95_000 + (k as i64 * 1009) % 4000));
        let ge = terms.mk_ge(v, b);
        base_atoms.push((ge, true));
    }

    // Bool control block (opaque to LIA, present in the asserted trail like
    // the DRAGON Bool state bits).
    for (k, &b) in bool_vars.iter().enumerate() {
        base_atoms.push((b, k % 3 != 0));
    }

    // Held-out per-iteration equalities: y_k = x_a + x_b + c with fresh y_k,
    // always satisfiable against the base system.
    let pool_targets: Vec<TermId> = (0..NUM_POOL_EQUALITIES)
        .map(|i| terms.mk_var(format!("y{i}"), Sort::Int))
        .collect();
    let mut pool_equalities = Vec::with_capacity(NUM_POOL_EQUALITIES);
    for (i, &y) in pool_targets.iter().enumerate() {
        let a = state_vars[(i * 3) % NUM_STATE_VARS];
        let b = state_vars[(i * 5 + 1) % NUM_STATE_VARS];
        let c = terms.mk_int(BigInt::from((i as i64 % 7) - 3));
        let rhs = terms.mk_add(vec![a, b, c]);
        let eq = terms.mk_eq(y, rhs);
        pool_equalities.push(eq);
    }

    // Held-out per-iteration bound atoms: consistent tightenings of the
    // base ranges on rotating state vars.
    let mut pool_bounds = Vec::with_capacity(NUM_POOL_BOUNDS);
    for i in 0..NUM_POOL_BOUNDS {
        let v = state_vars[(i * 17) % NUM_STATE_VARS];
        if i % 2 == 0 {
            let b = terms.mk_int(BigInt::from(-90_000 + (i as i64 * 13) % 1000));
            let ge = terms.mk_ge(v, b);
            pool_bounds.push(ge);
        } else {
            let b = terms.mk_int(BigInt::from(90_000 - (i as i64 * 13) % 1000));
            let le = terms.mk_le(v, b);
            pool_bounds.push(le);
        }
    }

    DragonShape {
        terms,
        base_atoms,
        pool_equalities,
        pool_bounds,
    }
}

fn percentile_ns(sorted: &[u128], pct: f64) -> u128 {
    if sorted.is_empty() {
        return 0;
    }
    let rank = ((sorted.len() as f64 - 1.0) * pct).round() as usize;
    sorted[rank.min(sorted.len() - 1)]
}

#[test]
#[ignore = "Bench 2 Loop A perf microbenchmark; run explicitly with --ignored --nocapture"]
fn bench2_loop_a_check_during_propagate_hot_loop() {
    let shape = build_dragon_shape();
    let mut solver = LiaSolver::new(&shape.terms);

    for &(atom, value) in &shape.base_atoms {
        solver.register_atom(atom);
        solver.assert_literal(atom, value);
    }
    // Warm up: one full BCP-time check at scope 0.
    let warm = solver.check_during_propagate();
    eprintln!(
        "[bench2-loop-a] base atoms={} warm result={warm:?}",
        shape.base_atoms.len()
    );

    let iters: usize = std::env::var("AY_LIA_HOT_LOOP_ITERS")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(1000);

    solver.reset_timings();
    let mut samples_ns: Vec<u128> = Vec::with_capacity(iters);
    let loop_start = Instant::now();
    for it in 0..iters {
        solver.push();
        // Assert 5 atoms: 1 equality + 4 bound tightenings (rotating pools).
        let eq = shape.pool_equalities[it % shape.pool_equalities.len()];
        solver.assert_literal(eq, true);
        for j in 0..4usize {
            let bound = shape.pool_bounds[(it * 4 + j) % shape.pool_bounds.len()];
            solver.assert_literal(bound, true);
        }
        let t0 = Instant::now();
        let result = solver.check_during_propagate();
        samples_ns.push(t0.elapsed().as_nanos());
        debug_assert!(
            !matches!(
                result,
                TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
            ),
            "bench shape must stay satisfiable, got {result:?} at iteration {it}"
        );
        solver.pop();
    }
    let total = loop_start.elapsed();

    samples_ns.sort_unstable();
    let median = percentile_ns(&samples_ns, 0.50);
    let p99 = percentile_ns(&samples_ns, 0.99);
    let mean = samples_ns.iter().sum::<u128>() / samples_ns.len().max(1) as u128;
    eprintln!(
        "[bench2-loop-a] iters={iters} median={median}ns p99={p99}ns mean={mean}ns total_loop={total:?}"
    );
    let timings = solver.timings();
    eprintln!(
        "[bench2-loop-a] phase totals: simplex={:?} gomory={:?} hnf={:?} dioph={:?}",
        timings.simplex, timings.gomory, timings.hnf, timings.dioph
    );

    // Generous ceiling: regression tripwire only (plan targets <=5us median
    // after the full Phase C; baseline before fixes is in the 100us-1ms class).
    assert!(
        median < 200_000_000,
        "Bench 2 Loop A median {median}ns exceeded generous 200ms ceiling"
    );
}
