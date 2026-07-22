// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Integration guard for the BUMP LU base factor in `refactorize`
//! (`AY_MILP_NO_BUMP_LU` is its kill switch; here the lever is FORCED onto
//! tiny LPs instead: the triangular-crash peel on, the bump floor at 1, the
//! refactor cadence at 1 so every pivot rebuilds through the peel + bump-LU
//! path). A cycle system's basis is one whole SCC — the peel finds no
//! singletons and the entire basis is bump — so these solves exercise the
//! gather, the Markowitz elimination, the L/U eta emission, and the
//! backs-after-bump interplay on every single pivot, with the exact lane
//! (which decides every answer) as the checker.
//!
//! Env forcing is per-process; this file is its own test binary, so nothing
//! leaks into other suites.

use ay_milp::{BabSession, LpSession, Model, Outcome, Sense, SolveOpts};
use num_rational::BigRational;

fn rat(n: i64) -> BigRational {
    BigRational::from_integer(n.into())
}

fn force_bump_lu_env() {
    std::env::set_var("AY_MILP_TRI_CRASH", "1");
    std::env::set_var("AY_MILP_BUMP_LU_MIN", "1");
    std::env::set_var("AY_MILP_REFACTOR_EVERY", "1");
}

/// Odd cycle x_i + x_{i+1 mod n} = 2 has the unique solution x == 1; the
/// basis holding all n structurals is a single SCC (every row and column of
/// the block has exactly two entries — no singleton front or back exists).
#[test]
fn cycle_lp_solves_exactly_under_forced_bump_lu() {
    force_bump_lu_env();
    let n = 9usize;
    let mut m = Model::new();
    let cols: Vec<_> = (0..n).map(|_| m.add_col(0.0, 10.0)).collect();
    for i in 0..n {
        m.add_row(2.0, 2.0, &[(cols[i], 1.0), (cols[(i + 1) % n], 1.0)]);
    }
    let mut s = LpSession::new(&m, &SolveOpts::new()).unwrap();
    match s.optimize(cols[0], Sense::Minimize).unwrap() {
        Outcome::Optimal {
            value,
            model_values,
            ..
        } => {
            assert_eq!(value, rat(1), "unique point of the odd cycle is x == 1");
            m.check_point(&model_values).unwrap();
        }
        other => panic!("expected Optimal, got {other:?}"),
    }
}

/// The same forced lane on a small MIP: two interlocked odd cycles plus
/// binaries choosing their right-hand sides. Optimum known by construction.
#[test]
fn cycle_mip_solves_exactly_under_forced_bump_lu() {
    force_bump_lu_env();
    let n = 7usize;
    let mut m = Model::new();
    let x: Vec<_> = (0..n).map(|_| m.add_col(0.0, 10.0)).collect();
    let b = m.add_binary_col();
    // x_i + x_{i+1} - 2 b = 0: feasible only with every x_i == b; the
    // objective pushes x_0 up, so the optimum picks b == 1, x == 1.
    for i in 0..n {
        m.add_row(0.0, 0.0, &[(x[i], 1.0), (x[(i + 1) % n], 1.0), (b, -2.0)]);
    }
    m.set_objective(&[(x[0], 1.0)], Sense::Maximize);
    let mut s = BabSession::new(m.clone(), &SolveOpts::new()).unwrap();
    match s.check().unwrap() {
        Outcome::Optimal { value, .. } => {
            assert_eq!(value, rat(1), "b=1 forces x == 1 around the odd cycle");
        }
        other => panic!("expected Optimal, got {other:?}"),
    }
}
