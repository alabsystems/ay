// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bench 2 Loop B (the development design notes §2):
//! per-iteration cost of the lazy DPLL(T) split loop's "fresh theory solver
//! per iteration" pattern, isolating Fix A1 (theory-prop JIT recompilation).
//!
//! Synthesizes a DRAGON-shaped QF_LIA assertion set (160 Int + 64 Bool vars,
//! ~220 linear equalities of width 3-40 consistent with a known integer
//! solution, ~400 single-variable bound atoms, all constants in i32 range),
//! then times 100 iterations of:
//!
//!   fresh solver -> register all atoms -> assert all atoms -> check()
//!
//! Three lanes:
//!   1. fresh `LiaSolver` per iteration (the production lazy-arm shape; LIA
//!      has no structural snapshot yet — plan Phase A2),
//!   2. fresh `LraSolver` (integer mode) per iteration without snapshot,
//!   3. `LraSolver::from_snapshot` per iteration (the A1 JIT-persistence path).
//!
//! Prints ms/iteration to stderr and asserts only generous ceilings so the
//! test doubles as an explicit-run regression tripwire.
//!
//! Run with:
//! ```text
//! cargo test -p ay-lia --release bench_loop_b -- --ignored --nocapture
//! ```
//!
//! DRAGON Bool state variables become SAT-level variables that the arithmetic
//! theory never sees; they are created in the TermStore for DAG-shape fidelity
//! but are not registered with the theory solver.

use super::*;
use ay_core::time::Instant;
use ay_core::Sort;
use ay_lra::LraSolver;
use num_bigint::BigInt;

/// Deterministic xorshift64* PRNG so the synthesized problem is identical
/// across runs and machines.
struct XorShift(u64);

impl XorShift {
    fn next(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        self.0 = x;
        x.wrapping_mul(0x2545_F491_4F6C_DD1D)
    }

    fn below(&mut self, m: u64) -> u64 {
        self.next() % m
    }
}

const NUM_INT_VARS: usize = 160;
const NUM_BOOL_VARS: usize = 64;
const NUM_EQUALITIES: usize = 220;
const NUM_BOUND_ATOMS: usize = 400;

/// Iterations per lane (default 100; override with AY_BENCH_LOOP_B_ITERS for
/// quick probes).
fn iterations() -> usize {
    std::env::var("AY_BENCH_LOOP_B_ITERS")
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(100)
}

/// Synthesize the DRAGON-shaped atom set. Returns `(atoms, value)` pairs to
/// assert. The system is satisfiable by construction: every equality and
/// bound is consistent with the base integer solution `x_i = (37*i % 2000) - 1000`.
fn synth_dragon_shape(terms: &mut TermStore) -> Vec<(TermId, bool)> {
    let mut rng = XorShift(0x9E37_79B9_7F4A_7C15);

    let int_vars: Vec<TermId> = (0..NUM_INT_VARS)
        .map(|i| terms.mk_var(format!("x{i}"), Sort::Int))
        .collect();
    // Bool state vars: present in the term DAG (shape fidelity) but never
    // registered with the arithmetic theory — DRAGON's Bool state lives at
    // the SAT level.
    let _bool_vars: Vec<TermId> = (0..NUM_BOOL_VARS)
        .map(|i| terms.mk_var(format!("b{i}"), Sort::Bool))
        .collect();

    // Known integer solution, all values in i32 range.
    let base: Vec<i64> = (0..NUM_INT_VARS)
        .map(|i| ((i as i64) * 37 % 2000) - 1000)
        .collect();

    let mut atoms: Vec<(TermId, bool)> = Vec::new();

    // ~220 linear equalities of width 3-40, shaped like DRAGON's transition
    // relation: *definitional* rows `x_d = sum(c_k * x_k) + const` where every
    // RHS variable has a strictly lower index than the defined variable
    // (next-state vars defined from current-state vars — a triangular
    // dependency DAG, no cycles). Coefficients are unit-ish ({-2,-1,1,2},
    // lia-hot-loop-plan.md §C3) and widths are narrow-biased (3-6 typical,
    // up to 40 occasionally). This keeps the LP itself trivial — as it is for
    // DRAGON, where z3 solves the whole query in ~20ms — so the per-iteration
    // cost stays dominated by the register/assert/JIT-compile phases that
    // this bench isolates. Dense random systems instead blow up simplex
    // fill-in into BigRational arithmetic and measure the wrong thing.
    let mut e = 0usize;
    'outer: loop {
        for d in 4..NUM_INT_VARS {
            if e >= NUM_EQUALITIES {
                break 'outer;
            }
            // Row width including the defined variable: typically 3-6,
            // occasionally wide (up to 40), always <= d so RHS indices can
            // stay strictly below the defined variable.
            let wide_cap = 3 + (e % 38);
            let narrow_cap = 3 + (e % 4);
            let width = (if e.is_multiple_of(8) {
                wide_cap
            } else {
                narrow_cap
            })
            .min(d);
            let rhs_width = width - 1;

            // Pick `rhs_width` distinct indices strictly below `d` via a
            // partial Fisher-Yates shuffle of 0..d.
            let mut pool: Vec<usize> = (0..d).collect();
            for k in 0..rhs_width {
                let j = k + rng.below((d - k) as u64) as usize;
                pool.swap(k, j);
            }
            let rhs_indices = &pool[..rhs_width];

            let mut summands: Vec<TermId> = Vec::with_capacity(rhs_width + 1);
            let mut rhs_value: i64 = 0;
            for &vi in rhs_indices {
                // Nonzero coefficient in {-2, -1, 1, 2}.
                let mut c = (rng.below(5) as i64) - 2;
                if c == 0 {
                    c = 1;
                }
                rhs_value += c * base[vi];
                let coeff = terms.mk_int(BigInt::from(c));
                let prod = terms.mk_mul(vec![coeff, int_vars[vi]]);
                summands.push(prod);
            }
            // Defined variable with coefficient -1: x_d - RHS = -const.
            let neg_one = terms.mk_int(BigInt::from(-1i64));
            let neg_d = terms.mk_mul(vec![neg_one, int_vars[d]]);
            summands.push(neg_d);
            rhs_value -= base[d];

            let lhs = terms.mk_add(summands);
            let rhs = terms.mk_int(BigInt::from(rhs_value));
            let eq = terms.mk_eq(lhs, rhs);
            atoms.push((eq, true));
            e += 1;
        }
    }

    // ~400 single-variable bound atoms, all satisfied by the base solution.
    for b in 0..NUM_BOUND_ATOMS {
        let vi = (b * 7) % NUM_INT_VARS;
        let margin = 1 + rng.below(50) as i64;
        let atom = if b % 2 == 0 {
            let c = terms.mk_int(BigInt::from(base[vi] + margin));
            terms.mk_le(int_vars[vi], c)
        } else {
            let c = terms.mk_int(BigInt::from(base[vi] - margin));
            terms.mk_ge(int_vars[vi], c)
        };
        atoms.push((atom, true));
    }

    atoms
}

fn assert_not_unsat(result: &TheoryResult, lane: &str) {
    assert!(
        !matches!(
            result,
            TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
        ),
        "{lane}: synthesized system is satisfiable by construction, got {result:?}"
    );
}

/// Lane 1: fresh `LiaSolver` per iteration (production lazy-arm shape).
fn run_fresh_lia(terms: &TermStore, atoms: &[(TermId, bool)]) -> f64 {
    let iters = iterations();
    let start = Instant::now();
    for _ in 0..iters {
        let mut solver = LiaSolver::new(terms);
        for &(a, _) in atoms {
            solver.register_atom(a);
        }
        for &(a, v) in atoms {
            solver.assert_literal(a, v);
        }
        let result = solver.check();
        assert_not_unsat(&result, "fresh LiaSolver");
    }
    start.elapsed().as_secs_f64() * 1000.0 / iters as f64
}

/// Lane 2: fresh `LraSolver` (integer mode) per iteration, no snapshot.
fn run_fresh_lra(terms: &TermStore, atoms: &[(TermId, bool)]) -> f64 {
    let iters = iterations();
    let start = Instant::now();
    for _ in 0..iters {
        let mut solver = LraSolver::new(terms);
        solver.set_integer_mode(true);
        for &(a, _) in atoms {
            solver.register_atom(a);
        }
        for &(a, v) in atoms {
            solver.assert_literal(a, v);
        }
        let result = solver.check();
        assert_not_unsat(&result, "fresh LraSolver");
    }
    start.elapsed().as_secs_f64() * 1000.0 / iters as f64
}

/// Per-phase accumulated times for the snapshot lane, in milliseconds per
/// iteration. `first_assert` is the first `assert_literal` of each iteration:
/// that call triggers the lazy theory-prop JIT compile in
/// `propagate_var_atoms`, so it isolates the Fix A1 recompile cost (baseline:
/// full table rebuild + per-variable native emission each iteration; post-A1:
/// fingerprint match, compile skipped).
struct SnapshotLanePhases {
    total: f64,
    import: f64,
    register: f64,
    first_assert: f64,
    assert_rest: f64,
    check: f64,
    export: f64,
}

/// Lane 3: `LraSolver::from_snapshot` per iteration (A1 persistence path).
/// Mirrors the lazy split-loop wiring: each iteration imports the previous
/// iteration's structural snapshot, re-registers every atom, asserts, checks,
/// and exports a snapshot for the next iteration.
fn run_snapshot_lra(terms: &TermStore, atoms: &[(TermId, bool)]) -> SnapshotLanePhases {
    // Warm-up iteration to produce the initial snapshot (not timed; the
    // production loop pays this once per solve, not per iteration).
    let mut snapshot = {
        let mut solver = LraSolver::new(terms);
        solver.set_integer_mode(true);
        for &(a, _) in atoms {
            solver.register_atom(a);
        }
        for &(a, v) in atoms {
            solver.assert_literal(a, v);
        }
        let result = solver.check();
        assert_not_unsat(&result, "snapshot warm-up LraSolver");
        solver
            .export_structural_snapshot()
            .expect("snapshot export should succeed with registered atoms")
    };

    let iters = iterations();
    let (mut t_import, mut t_register, mut t_first, mut t_rest, mut t_check, mut t_export) =
        (0.0f64, 0.0f64, 0.0f64, 0.0f64, 0.0f64, 0.0f64);
    let start = Instant::now();
    for _ in 0..iters {
        let p0 = Instant::now();
        let mut solver =
            LraSolver::from_snapshot(terms, snapshot).expect("snapshot import should succeed");
        solver.set_integer_mode(true);
        let p1 = Instant::now();
        for &(a, _) in atoms {
            solver.register_atom(a);
        }
        let p2 = Instant::now();
        let (first, rest) = atoms.split_first().expect("atom set is non-empty");
        solver.assert_literal(first.0, first.1);
        let p3 = Instant::now();
        for &(a, v) in rest {
            solver.assert_literal(a, v);
        }
        let p4 = Instant::now();
        let result = solver.check();
        assert_not_unsat(&result, "snapshot LraSolver");
        let p5 = Instant::now();
        snapshot = solver
            .export_structural_snapshot()
            .expect("snapshot re-export should succeed");
        let p6 = Instant::now();
        t_import += (p1 - p0).as_secs_f64();
        t_register += (p2 - p1).as_secs_f64();
        t_first += (p3 - p2).as_secs_f64();
        t_rest += (p4 - p3).as_secs_f64();
        t_check += (p5 - p4).as_secs_f64();
        t_export += (p6 - p5).as_secs_f64();
    }
    let per_iter = 1000.0 / iters as f64;
    SnapshotLanePhases {
        total: start.elapsed().as_secs_f64() * per_iter,
        import: t_import * per_iter,
        register: t_register * per_iter,
        first_assert: t_first * per_iter,
        assert_rest: t_rest * per_iter,
        check: t_check * per_iter,
        export: t_export * per_iter,
    }
}

#[test]
#[ignore = "perf micro-bench: run explicitly with --ignored --nocapture (release)"]
fn bench_loop_b_fresh_solver_iteration_cost() {
    let mut terms = TermStore::new();
    let atoms = synth_dragon_shape(&mut terms);
    eprintln!(
        "[bench_loop_b] synthesized {} atoms ({} equalities width 3-40, {} bounds) over {} Int vars",
        atoms.len(),
        NUM_EQUALITIES,
        NUM_BOUND_ATOMS,
        NUM_INT_VARS,
    );

    // Optional lane filter for profiling runs, e.g. AY_BENCH_LOOP_B_LANES=3.
    let lanes = std::env::var("AY_BENCH_LOOP_B_LANES").unwrap_or_else(|_| "123".into());

    let mut lia_ms = 0.0;
    if lanes.contains('1') {
        lia_ms = run_fresh_lia(&terms, &atoms);
        eprintln!("[bench_loop_b] lane 1 fresh LiaSolver:          {lia_ms:.3} ms/iteration");
    }

    if lanes.contains('2') {
        let lra_ms = run_fresh_lra(&terms, &atoms);
        eprintln!("[bench_loop_b] lane 2 fresh LraSolver:          {lra_ms:.3} ms/iteration");
    }

    if lanes.contains('3') {
        let snap = run_snapshot_lra(&terms, &atoms);
        eprintln!(
            "[bench_loop_b] lane 3 snapshot-import LraSolver: {:.3} ms/iteration",
            snap.total
        );
        eprintln!(
            "[bench_loop_b] lane 3 phases (ms/iteration): import={:.3} register={:.3} \
             first-assert(JIT-compile)={:.3} assert-rest={:.3} check={:.3} export={:.3}",
            snap.import,
            snap.register,
            snap.first_assert,
            snap.assert_rest,
            snap.check,
            snap.export,
        );

        // Generous ceiling only — this is a tripwire, not a benchmark gate.
        assert!(
            snap.total < 100.0,
            "snapshot LraSolver iteration regressed: {:.3} ms/iteration (ceiling 100 ms)",
            snap.total
        );
    }

    // Generous ceilings only — this is a tripwire, not a benchmark gate.
    // Plan baseline expectation: ~10-30 ms/iteration dominated by JIT
    // recompilation in the lazy loop's theory time.
    if lanes.contains('1') {
        assert!(
            lia_ms < 250.0,
            "fresh LiaSolver iteration regressed: {lia_ms:.3} ms/iteration (ceiling 250 ms)"
        );
    }
}
