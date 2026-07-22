// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

fn setup_store() -> TermStore {
    TermStore::new()
}

/// Proof: push/pop maintains stack consistency
#[kani::proof]
fn proof_push_pop_stack_depth() {
    let store = setup_store();
    let mut solver = BvSolver::new(&store);

    let num_pushes: u8 = kani::any();
    kani::assume(num_pushes <= 10);
    let num_pops: u8 = kani::any();
    kani::assume(num_pops <= num_pushes);

    // Push n times
    for _ in 0..num_pushes {
        solver.push();
    }
    assert_eq!(solver.trail_stack.len(), num_pushes as usize);

    // Pop m times (m <= n)
    for _ in 0..num_pops {
        solver.pop();
    }
    assert_eq!(solver.trail_stack.len(), (num_pushes - num_pops) as usize);
}

/// Proof: pop on empty stack is safe (no-op)
#[kani::proof]
fn proof_pop_empty_is_safe() {
    let store = setup_store();
    let mut solver = BvSolver::new(&store);

    // Pop on empty stack should do nothing
    let trail_len_before = solver.trail.len();
    let asserted_len_before = solver.asserted.len();

    solver.pop();

    // State should be unchanged
    assert_eq!(solver.trail.len(), trail_len_before);
    assert_eq!(solver.asserted.len(), asserted_len_before);
    assert!(solver.trail_stack.is_empty());
}

/// Proof: reset clears all mutable state
#[kani::proof]
fn proof_reset_clears_state() {
    let store = setup_store();
    let mut solver = BvSolver::new(&store);

    // Add some state
    solver.push();
    let _ = solver.fresh_var();
    let _ = solver.fresh_var();
    solver.push();

    // Reset should clear everything
    solver.reset();

    assert!(
        solver.term_to_bits.is_empty(),
        "reset must clear term_to_bits"
    );
    assert!(solver.clauses.is_empty(), "reset must clear clauses");
    assert_eq!(solver.next_var, 1, "reset must reset next_var to 1");
    assert!(solver.trail.is_empty(), "reset must clear trail");
    assert!(
        solver.trail_stack.is_empty(),
        "reset must clear trail_stack"
    );
    assert!(solver.asserted.is_empty(), "reset must clear asserted");
}

/// Proof: fresh_var is monotonically increasing
#[kani::proof]
fn proof_fresh_var_monotonic() {
    let store = setup_store();
    let mut solver = BvSolver::new(&store);

    let initial = solver.next_var;
    let v1 = solver.fresh_var();
    let mid = solver.next_var;
    let v2 = solver.fresh_var();

    // Each call should return unique, increasing values
    assert!(v1 > 0);
    assert!(v2 > v1);
    assert!(mid > initial);
    assert!(solver.next_var > mid);
}

/// Proof: const_bits returns correct number of bits
#[kani::proof]
fn proof_const_bits_width() {
    let store = setup_store();
    let mut solver = BvSolver::new(&store);

    let value: u64 = kani::any();
    let width: usize = kani::any();
    kani::assume(width > 0 && width <= 16);

    let bits = solver.const_bits(value, width);

    assert_eq!(
        bits.len(),
        width,
        "const_bits must return correct number of bits"
    );
}

/// Proof: num_vars returns correct count
#[kani::proof]
fn proof_num_vars_correct() {
    let store = setup_store();
    let mut solver = BvSolver::new(&store);

    assert_eq!(solver.num_vars(), 0);

    let n: u8 = kani::any();
    kani::assume(n > 0 && n <= 20);

    for _ in 0..n {
        let _ = solver.fresh_var();
    }

    assert_eq!(solver.num_vars(), n as u32);
}

/// Proof: trail_stack markers are valid positions
#[kani::proof]
#[kani::unwind(6)]
fn proof_trail_stack_markers_valid() {
    let store = setup_store();
    let mut solver = BvSolver::new(&store);

    let depth: u8 = kani::any();
    kani::assume(depth > 0 && depth <= 5);

    // Push multiple times
    let mut expected_markers: Vec<usize> = Vec::new();
    for _ in 0..depth {
        expected_markers.push(solver.trail.len());
        solver.push();
    }

    // Verify markers are correct and in ascending order
    for i in 0..depth as usize {
        assert_eq!(solver.trail_stack[i], expected_markers[i]);
        if i > 0 {
            assert!(solver.trail_stack[i] >= solver.trail_stack[i - 1]);
        }
    }
}

/// Proof: bitblast_and preserves width
#[kani::proof]
fn proof_bitblast_and_width() {
    let store = setup_store();
    let mut solver = BvSolver::new(&store);

    let width: usize = kani::any();
    kani::assume(width > 0 && width <= 8);

    let a = solver.const_bits(0, width);
    let b = solver.const_bits(0, width);

    let result = solver.bitblast_and(&a, &b);

    assert_eq!(result.len(), width, "AND must preserve width");
}

/// Proof: bitblast_or preserves width
#[kani::proof]
fn proof_bitblast_or_width() {
    let store = setup_store();
    let mut solver = BvSolver::new(&store);

    let width: usize = kani::any();
    kani::assume(width > 0 && width <= 8);

    let a = solver.const_bits(0, width);
    let b = solver.const_bits(0, width);

    let result = solver.bitblast_or(&a, &b);

    assert_eq!(result.len(), width, "OR must preserve width");
}

/// Proof: bitblast_xor preserves width
#[kani::proof]
fn proof_bitblast_xor_width() {
    let store = setup_store();
    let mut solver = BvSolver::new(&store);

    let width: usize = kani::any();
    kani::assume(width > 0 && width <= 8);

    let a = solver.const_bits(0, width);
    let b = solver.const_bits(0, width);

    let result = solver.bitblast_xor(&a, &b);

    assert_eq!(result.len(), width, "XOR must preserve width");
}

/// Proof: bitblast_not preserves width
#[kani::proof]
fn proof_bitblast_not_width() {
    let store = setup_store();
    let mut solver = BvSolver::new(&store);

    let width: usize = kani::any();
    kani::assume(width > 0 && width <= 8);

    let a = solver.const_bits(0, width);

    let result = BvSolver::bitblast_not(&a);

    assert_eq!(result.len(), width, "NOT must preserve width");
}

/// Proof: bitblast_add preserves width
#[kani::proof]
fn proof_bitblast_add_width() {
    let store = setup_store();
    let mut solver = BvSolver::new(&store);

    let width: usize = kani::any();
    kani::assume(width > 0 && width <= 8);

    let a = solver.const_bits(0, width);
    let b = solver.const_bits(0, width);

    let result = solver.bitblast_add(&a, &b);

    assert_eq!(result.len(), width, "ADD must preserve width");
}

/// Proof: clauses are only added, never removed (except reset)
#[kani::proof]
fn proof_clauses_monotonic() {
    let store = setup_store();
    let mut solver = BvSolver::new(&store);

    let initial_clauses = solver.clauses.len();

    // Generate some bits (which adds clauses)
    let _ = solver.const_bits(5, 4);

    let after_const = solver.clauses.len();

    // Push/pop should not affect clauses
    solver.push();
    let after_push = solver.clauses.len();
    solver.pop();
    let after_pop = solver.clauses.len();

    assert!(after_const >= initial_clauses);
    assert_eq!(after_push, after_const);
    assert_eq!(after_pop, after_push);
}
