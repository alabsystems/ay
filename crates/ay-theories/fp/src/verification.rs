// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Kani verification harnesses for the standalone FP solver shell.

use super::*;

/// Verify push increments stack depth.
#[kani::proof]
fn proof_push_increments_stack_depth() {
    let mut solver = FpSolverStandalone::new();
    let initial_depth = solver.trail_stack.len();
    solver.push();
    assert_eq!(solver.trail_stack.len(), initial_depth + 1);
}

/// Verify pop decrements stack depth (when non-empty).
#[kani::proof]
fn proof_pop_decrements_stack_depth() {
    let mut solver = FpSolverStandalone::new();
    solver.push();
    let depth_after_push = solver.trail_stack.len();
    solver.pop();
    assert_eq!(solver.trail_stack.len(), depth_after_push - 1);
}

/// Verify pop on empty stack is safe (no panic).
#[kani::proof]
fn proof_pop_empty_is_safe() {
    let mut solver = FpSolverStandalone::new();
    solver.pop();
    assert_eq!(solver.trail_stack.len(), 0);
}

/// Verify reset clears all state.
#[kani::proof]
fn proof_reset_clears_state() {
    let mut solver = FpSolverStandalone::new();
    solver.push();
    solver.push();
    solver.reset();
    assert!(solver.clauses.is_empty());
    assert!(solver.trail.is_empty());
    assert!(solver.trail_stack.is_empty());
    assert_eq!(solver.next_var, 1);
}

/// Verify nested push/pop maintains correct depth.
#[kani::proof]
fn proof_nested_push_pop_depth() {
    let mut solver = FpSolverStandalone::new();
    solver.push();
    solver.push();
    solver.push();
    assert_eq!(solver.trail_stack.len(), 3);
    solver.pop();
    assert_eq!(solver.trail_stack.len(), 2);
    solver.pop();
    assert_eq!(solver.trail_stack.len(), 1);
    solver.pop();
    assert_eq!(solver.trail_stack.len(), 0);
}

/// Verify push/pop restore original depth.
#[kani::proof]
fn proof_push_pop_restores_depth() {
    let mut solver = FpSolverStandalone::new();
    let original_depth = solver.trail_stack.len();
    solver.push();
    solver.pop();
    assert_eq!(solver.trail_stack.len(), original_depth);
}

/// Verify `FpPrecision::exponent_bits` is positive for standard types.
#[kani::proof]
fn proof_precision_exponent_positive() {
    let precisions = [
        FpPrecision::Float16,
        FpPrecision::Float32,
        FpPrecision::Float64,
        FpPrecision::Float128,
    ];
    for prec in precisions {
        assert!(prec.exponent_bits() > 0);
    }
}

/// Verify `FpPrecision::significand_bits` is positive for standard types.
#[kani::proof]
fn proof_precision_significand_positive() {
    let precisions = [
        FpPrecision::Float16,
        FpPrecision::Float32,
        FpPrecision::Float64,
        FpPrecision::Float128,
    ];
    for prec in precisions {
        assert!(prec.significand_bits() > 0);
    }
}

/// Verify `total_bits = exponent_bits + significand_bits`.
#[kani::proof]
fn proof_total_bits_formula() {
    let precisions = [
        FpPrecision::Float16,
        FpPrecision::Float32,
        FpPrecision::Float64,
        FpPrecision::Float128,
    ];
    for prec in precisions {
        assert_eq!(
            prec.total_bits(),
            prec.exponent_bits() + prec.significand_bits()
        );
    }
}

/// Verify bias formula: `2^(eb-1) - 1`.
#[kani::proof]
fn proof_bias_formula() {
    assert_eq!(FpPrecision::Float32.bias(), (1u32 << 7) - 1);
    assert_eq!(FpPrecision::Float64.bias(), (1u32 << 10) - 1);
}

/// Verify `RoundingMode::from_name` is the inverse of `name()`.
#[kani::proof]
fn proof_rounding_mode_roundtrip() {
    let modes = [
        RoundingMode::RNE,
        RoundingMode::RNA,
        RoundingMode::RTP,
        RoundingMode::RTN,
        RoundingMode::RTZ,
    ];
    for mode in modes {
        assert_eq!(RoundingMode::from_name(mode.name()), Some(mode));
    }
}
