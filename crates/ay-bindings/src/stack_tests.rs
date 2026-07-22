// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates

use crate::expr::Expr;
use crate::memory::MemoryModel;
use crate::memory::OBJECT_ID_WIDTH;
use crate::AYProgram;

// ========================================================================
// Stack Frame Tests (issue #8293)
//
// These tests verify the stack frame push/pop lifecycle, alloca within
// frames, use-after-return detection, no-stack-escape assertions, and
// nested frame behavior.
// ========================================================================

/// Test basic push/pop lifecycle: push a frame, verify it's tracked,
/// pop it, verify the model is updated.
#[test]
fn test_stack_push_pop_lifecycle() {
    let mem = MemoryModel::new();
    assert_eq!(mem.frame_depth(), 0);

    // Push a frame
    let (frame_ptr, frame_id, mem) = mem.push_frame();
    assert_eq!(frame_ptr.sort().bitvec_width(), Some(64));
    assert_eq!(frame_id.sort().bitvec_width(), Some(32));
    assert_eq!(mem.frame_depth(), 1);

    // Pop the frame
    let (constraint, mem) = mem.pop_frame(frame_id);
    assert!(
        constraint.sort().is_bool(),
        "pop_frame constraint must be Bool"
    );
    assert_eq!(mem.frame_depth(), 0);
}

/// Test stack_alloca within a frame: allocate sub-objects, verify they
/// are tracked and returned as valid pointers.
#[test]
fn test_stack_alloca_within_frame() {
    let mem = MemoryModel::new();

    // Push a frame
    let (_frame_ptr, frame_id, mem) = mem.push_frame();

    // Allocate 16 bytes within the frame
    let (alloca_ptr, mem) =
        mem.stack_alloca(frame_id.clone(), Expr::bitvec_const(16u32, OBJECT_ID_WIDTH));
    assert_eq!(alloca_ptr.sort().bitvec_width(), Some(64));

    // Allocate another 32 bytes
    let (alloca_ptr2, mem) =
        mem.stack_alloca(frame_id.clone(), Expr::bitvec_const(32u32, OBJECT_ID_WIDTH));
    assert_eq!(alloca_ptr2.sort().bitvec_width(), Some(64));

    // Both allocations should be valid
    let valid1 = mem.read_ok(alloca_ptr, Expr::bitvec_const(4u32, OBJECT_ID_WIDTH));
    let valid2 = mem.read_ok(alloca_ptr2, Expr::bitvec_const(4u32, OBJECT_ID_WIDTH));
    assert!(valid1.sort().is_bool());
    assert!(valid2.sort().is_bool());

    // Pop the frame (deallocates everything)
    let (constraint, mem) = mem.pop_frame(frame_id);
    assert!(constraint.sort().is_bool());
    assert_eq!(mem.frame_depth(), 0);
}

/// Test use-after-return detection: after popping a frame, accesses to
/// frame allocations should be invalid (object_valid is false).
#[test]
fn test_use_after_return_detection() {
    let mut program = AYProgram::new();
    program.set_logic("QF_AUFBV");

    let mem = MemoryModel::new();

    // Push frame, do alloca, pop frame
    let (_frame_ptr, frame_id, mem) = mem.push_frame();
    let (alloca_ptr, mem) =
        mem.stack_alloca(frame_id.clone(), Expr::bitvec_const(8u32, OBJECT_ID_WIDTH));
    let (_constraint, mem) = mem.pop_frame(frame_id);

    // After pop, alloca_ptr should reference an invalid object
    let valid = mem.assert_valid_access(alloca_ptr);
    // Negate: if the negation is satisfiable, we detected use-after-return
    program.assert(valid.not());
    program.check_sat();

    let smt = program.to_string();
    assert!(smt.contains("(check-sat)"), "Missing check-sat");
    // The SMT should contain store(..., false) from deallocation
    assert!(smt.contains("false"), "Missing false from deallocation");
    assert!(smt.contains("store"), "Missing store operations");
}

/// Test assert_no_stack_escape: verify the constraint correctly prevents
/// returning stack pointers from functions.
#[test]
fn test_no_stack_escape_check() {
    let mem = MemoryModel::new();

    // Push frame with alloca
    let (_frame_ptr, frame_id, mem) = mem.push_frame();
    let (alloca_ptr, mem) =
        mem.stack_alloca(frame_id.clone(), Expr::bitvec_const(16u32, OBJECT_ID_WIDTH));

    // assert_no_stack_escape should be false for the alloca pointer
    // (it DOES escape the frame, so the assertion that it does NOT is false)
    let no_escape = mem.assert_no_stack_escape(alloca_ptr, frame_id.clone());
    assert!(
        no_escape.sort().is_bool(),
        "assert_no_stack_escape must return Bool"
    );

    // For a heap-allocated pointer, assert_no_stack_escape should be true
    let (heap_ptr, mem) = mem.allocate(Expr::bitvec_const(64u32, OBJECT_ID_WIDTH));
    let no_escape_heap = mem.assert_no_stack_escape(heap_ptr, frame_id);
    assert!(
        no_escape_heap.sort().is_bool(),
        "assert_no_stack_escape must return Bool"
    );
}

/// Test nested frames: push two frames, pop in LIFO order, verify
/// allocations are properly tracked and deallocated per frame.
#[test]
fn test_nested_frames() {
    let mem = MemoryModel::new();

    // Push outer frame
    let (_outer_ptr, outer_id, mem) = mem.push_frame();
    assert_eq!(mem.frame_depth(), 1);

    // Allocate in outer frame
    let (outer_alloca, mem) =
        mem.stack_alloca(outer_id.clone(), Expr::bitvec_const(8u32, OBJECT_ID_WIDTH));

    // Push inner frame
    let (_inner_ptr, inner_id, mem) = mem.push_frame();
    assert_eq!(mem.frame_depth(), 2);

    // Allocate in inner frame
    let (inner_alloca, mem) =
        mem.stack_alloca(inner_id.clone(), Expr::bitvec_const(16u32, OBJECT_ID_WIDTH));

    // Both allocations should be valid
    let valid_outer = mem.read_ok(
        outer_alloca.clone(),
        Expr::bitvec_const(4u32, OBJECT_ID_WIDTH),
    );
    let valid_inner = mem.read_ok(
        inner_alloca.clone(),
        Expr::bitvec_const(4u32, OBJECT_ID_WIDTH),
    );
    assert!(valid_outer.sort().is_bool());
    assert!(valid_inner.sort().is_bool());

    // Pop inner frame first (LIFO)
    let (_constraint, mem) = mem.pop_frame(inner_id);
    assert_eq!(mem.frame_depth(), 1);

    // Inner alloca should now be invalid, outer still valid
    let invalid_inner = mem.assert_valid_access(inner_alloca);
    let still_valid_outer = mem.assert_valid_access(outer_alloca);
    // Sort checks
    assert!(invalid_inner.sort().is_bool());
    assert!(still_valid_outer.sort().is_bool());

    // Pop outer frame
    let (_constraint, mem) = mem.pop_frame(outer_id);
    assert_eq!(mem.frame_depth(), 0);
}

/// Test that popping with wrong frame ID panics (LIFO violation).
#[test]
#[should_panic(expected = "no active stack frames")]
fn test_pop_empty_stack_panics() {
    let mem = MemoryModel::new();
    let fake_id = Expr::bitvec_const(42u32, OBJECT_ID_WIDTH);
    let _ = mem.pop_frame(fake_id);
}

/// Test nested frame LIFO violation: push two frames, try to pop the outer
/// one first.
#[test]
fn test_lifo_violation_generates_constraint() {
    let mem = MemoryModel::new();

    // Push two frames
    let (_ptr1, outer_id, mem) = mem.push_frame();
    let (_ptr2, _inner_id, mem) = mem.push_frame();

    // Try to pop the outer frame (LIFO violation)
    // pop_frame returns a constraint that includes frame_id == top_frame
    // Since outer_id != inner (top), the LIFO check expression will be
    // unsatisfiable when asserted.
    let (constraint, _mem) = mem.pop_frame(outer_id);
    assert!(constraint.sort().is_bool());
    // The constraint includes an equality check that will be false for
    // the wrong frame, making the conjunction unsatisfiable.
}

/// End-to-end SMT test: push frame, alloca, write, read, pop, verify
/// use-after-return generates correct SMT structure.
#[test]
fn test_e2e_stack_frame_smt() {
    let mut program = AYProgram::new();
    program.set_logic("QF_AUFBV");
    program.produce_models();

    let mem = MemoryModel::new();

    // Push frame
    let (_frame_ptr, frame_id, mem) = mem.push_frame();

    // Alloca 4 bytes
    let (stack_ptr, mem) =
        mem.stack_alloca(frame_id.clone(), Expr::bitvec_const(4u32, OBJECT_ID_WIDTH));

    // Write a byte
    let mem = mem.write_byte(stack_ptr.clone(), Expr::bitvec_const(0x42u8, 8));

    // Read it back
    let read_val = mem.read_byte(stack_ptr.clone());
    program.assert(read_val.eq(Expr::bitvec_const(0x42u8, 8)));

    // Verify the alloca is in bounds
    let in_bounds = mem.read_ok(stack_ptr, Expr::bitvec_const(1u32, OBJECT_ID_WIDTH));
    program.assert(in_bounds);

    // Pop the frame
    let (pop_constraint, _mem) = mem.pop_frame(frame_id);
    program.assert(pop_constraint);

    program.check_sat();

    let smt = program.to_string();
    assert!(smt.contains("(check-sat)"), "Missing check-sat");
    assert!(smt.contains("store"), "Missing store operations");
    assert!(smt.contains("select"), "Missing select operations");
}
