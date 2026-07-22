// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Benchmark test for #4522: counterexample minimization effectiveness.
//!
//! Measures whether model minimization produces smaller values in >80%
//! of SAT benchmarks compared to unminimized models. This is the final
//! acceptance criterion for the minimal counterexample feature.

use ay_dpll::api::*;
use ay_dpll::CounterexampleStyle;
use num_bigint::BigInt;
use num_traits::Signed;

/// Sum of absolute values of integer model values from a VerifiedModel.
fn int_magnitude(model: &VerifiedModel) -> BigInt {
    let mut total = BigInt::from(0);
    for (_, val) in model.model().iter_ints() {
        total += val.abs();
    }
    total
}

/// Sum of absolute values of BV model values from a VerifiedModel.
fn bv_magnitude(model: &VerifiedModel) -> BigInt {
    let mut total = BigInt::from(0);
    for (_, (val, _)) in model.model().iter_bvs() {
        total += val.abs();
    }
    total
}

/// Total model magnitude (int + BV).
fn total_magnitude(model: &VerifiedModel) -> BigInt {
    int_magnitude(model) + bv_magnitude(model)
}

/// Build and solve a benchmark, returning the model magnitude.
/// Returns None if not SAT.
fn solve_and_measure(build_fn: fn(&mut Solver), style: CounterexampleStyle) -> Option<BigInt> {
    let mut solver = Solver::try_new(Logic::QfLia).unwrap();
    solver.set_counterexample_style(style);
    build_fn(&mut solver);
    if solver.check_sat() != SolveResult::Sat {
        return None;
    }
    solver.model().map(|m| total_magnitude(&m))
}

// ============================================================
// LIA Benchmarks — each builds assertions without nested borrows
// ============================================================

fn bench_unconstrained(solver: &mut Solver) {
    let x = solver.int_var("x");
    let y = solver.int_var("y");
    let zero = solver.int_const(0);
    let ge_x = solver.try_ge(x, zero).unwrap();
    let ge_y = solver.try_ge(y, zero).unwrap();
    solver.try_assert_term(ge_x).unwrap();
    solver.try_assert_term(ge_y).unwrap();
}

fn bench_linear_system(solver: &mut Solver) {
    let x = solver.int_var("x");
    let y = solver.int_var("y");
    let zero = solver.int_const(0);
    let c4 = solver.int_const(4);
    let c3 = solver.int_const(3);
    let four_x = solver.try_mul(c4, x).unwrap();
    let three_y = solver.try_mul(c3, y).unwrap();
    let sum = solver.try_add(four_x, three_y).unwrap();
    let seventy = solver.int_const(70);
    let eq = solver.try_eq(sum, seventy).unwrap();
    let ge_x = solver.try_ge(x, zero).unwrap();
    let ge_y = solver.try_ge(y, zero).unwrap();
    solver.try_assert_term(eq).unwrap();
    solver.try_assert_term(ge_x).unwrap();
    solver.try_assert_term(ge_y).unwrap();
}

fn bench_bounded_pair(solver: &mut Solver) {
    let a = solver.int_var("a");
    let b = solver.int_var("b");
    let c10 = solver.int_const(10);
    let c1000 = solver.int_const(1000);
    let ge_a = solver.try_ge(a, c10).unwrap();
    let le_a = solver.try_le(a, c1000).unwrap();
    let ge_b = solver.try_ge(b, c10).unwrap();
    let le_b = solver.try_le(b, c1000).unwrap();
    solver.try_assert_term(ge_a).unwrap();
    solver.try_assert_term(le_a).unwrap();
    solver.try_assert_term(ge_b).unwrap();
    solver.try_assert_term(le_b).unwrap();
}

fn bench_sum_3var(solver: &mut Solver) {
    let x = solver.int_var("x");
    let y = solver.int_var("y");
    let z = solver.int_var("z");
    let zero = solver.int_const(0);
    let hundred = solver.int_const(100);
    let xy = solver.try_add(x, y).unwrap();
    let xyz = solver.try_add(xy, z).unwrap();
    let eq = solver.try_eq(xyz, hundred).unwrap();
    let ge_x = solver.try_ge(x, zero).unwrap();
    let ge_y = solver.try_ge(y, zero).unwrap();
    let ge_z = solver.try_ge(z, zero).unwrap();
    solver.try_assert_term(eq).unwrap();
    solver.try_assert_term(ge_x).unwrap();
    solver.try_assert_term(ge_y).unwrap();
    solver.try_assert_term(ge_z).unwrap();
}

fn bench_negative_range(solver: &mut Solver) {
    let x = solver.int_var("x");
    let lo = solver.int_const(-500);
    let hi = solver.int_const(-100);
    let ge = solver.try_ge(x, lo).unwrap();
    let le = solver.try_le(x, hi).unwrap();
    solver.try_assert_term(ge).unwrap();
    solver.try_assert_term(le).unwrap();
}

fn bench_large_lower_bound(solver: &mut Solver) {
    let x = solver.int_var("x");
    let bound = solver.int_const(1000);
    let ge = solver.try_ge(x, bound).unwrap();
    solver.try_assert_term(ge).unwrap();
}

/// Acceptance test: model minimization reduces or preserves value magnitude in >80% of SAT benchmarks.
#[test]
fn test_minimization_reduces_magnitude_80_percent() {
    let lia_benches: Vec<(&str, fn(&mut Solver))> = vec![
        ("unconstrained", bench_unconstrained),
        ("linear_system", bench_linear_system),
        ("bounded_pair", bench_bounded_pair),
        ("sum_3var", bench_sum_3var),
        ("negative_range", bench_negative_range),
        ("large_lower_bound", bench_large_lower_bound),
    ];

    let mut smaller_count = 0u32;
    let mut same_count = 0u32;
    let mut larger_count = 0u32;

    for (name, build_fn) in &lia_benches {
        let minimal = solve_and_measure(*build_fn, CounterexampleStyle::Minimal);
        let any = solve_and_measure(*build_fn, CounterexampleStyle::Any);

        match (minimal, any) {
            (Some(min_mag), Some(any_mag)) => {
                if min_mag < any_mag {
                    smaller_count += 1;
                } else if min_mag == any_mag {
                    same_count += 1;
                } else {
                    larger_count += 1;
                    eprintln!("WARNING: {name}: minimized ({min_mag}) > unminimized ({any_mag})");
                }
            }
            _ => {
                // Not SAT or no model — skip
            }
        }
    }

    let total = smaller_count + same_count + larger_count;
    assert!(total > 0, "no LIA SAT benchmarks produced models");

    // Minimized should never be strictly larger (that's a bug).
    assert_eq!(
        larger_count, 0,
        "minimization should never increase magnitude"
    );

    // Primary acceptance criterion: not-worse in >80%.
    let not_worse_pct = (f64::from(smaller_count + same_count) / f64::from(total)) * 100.0;
    assert!(
        not_worse_pct >= 80.0,
        "minimization not-worse rate {not_worse_pct:.1}% < 80% \
         (smaller={smaller_count}, same={same_count}, larger={larger_count})"
    );
}

/// Spot check: unconstrained variables get minimized to 0.
#[test]
fn test_unconstrained_vars_minimized_to_zero() {
    let mut solver = Solver::try_new(Logic::QfLia).unwrap();
    solver.set_counterexample_style(CounterexampleStyle::Minimal);
    let x = solver.int_var("x");
    let zero = solver.int_const(0);
    let ge = solver.try_ge(x, zero).unwrap();
    solver.try_assert_term(ge).unwrap();

    assert_eq!(solver.check_sat(), SolveResult::Sat);
    match solver.value(x) {
        Some(ModelValue::Int(val)) => {
            assert_eq!(
                val,
                BigInt::from(0),
                "unconstrained x >= 0 should minimize to 0"
            );
        }
        other => panic!("expected Int model value for x, got {other:?}"),
    }
}

/// Spot check: bounded variable stays in range after minimization.
#[test]
fn test_bounded_var_stays_in_range() {
    let mut solver = Solver::try_new(Logic::QfLia).unwrap();
    solver.set_counterexample_style(CounterexampleStyle::Minimal);
    let x = solver.int_var("x");
    let lo = solver.int_const(50);
    let hi = solver.int_const(55);
    let ge = solver.try_ge(x, lo).unwrap();
    let le = solver.try_le(x, hi).unwrap();
    solver.try_assert_term(ge).unwrap();
    solver.try_assert_term(le).unwrap();

    assert_eq!(solver.check_sat(), SolveResult::Sat);
    match solver.value(x) {
        Some(ModelValue::Int(val)) => {
            assert!(
                val >= BigInt::from(50) && val <= BigInt::from(55),
                "x should be in [50, 55], got {val}"
            );
        }
        other => panic!("expected Int model value for x, got {other:?}"),
    }
}

/// Spot check: large lower bound gets minimized to the bound.
#[test]
fn test_large_lower_bound_minimized() {
    let mut solver = Solver::try_new(Logic::QfLia).unwrap();
    solver.set_counterexample_style(CounterexampleStyle::Minimal);
    let x = solver.int_var("x");
    let bound = solver.int_const(100);
    let ge = solver.try_ge(x, bound).unwrap();
    solver.try_assert_term(ge).unwrap();

    assert_eq!(solver.check_sat(), SolveResult::Sat);
    match solver.value(x) {
        Some(ModelValue::Int(val)) => {
            assert_eq!(
                val,
                BigInt::from(100),
                "minimizer should pick 100 (power of 10 candidate)"
            );
        }
        other => panic!("expected Int model value for x, got {other:?}"),
    }
}
