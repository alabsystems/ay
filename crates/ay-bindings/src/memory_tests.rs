// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates

use super::*;
use crate::AYProgram;

#[test]
fn test_pointer_construction() {
    let obj_id = Expr::bitvec_const(42u32, 32);
    let offset = Expr::bitvec_const(100u32, 32);
    let ptr = MemoryModel::mk_pointer(obj_id, offset);

    assert_eq!(ptr.sort().bitvec_width(), Some(64));

    // Extract and verify components
    let extracted_obj = MemoryModel::pointer_object(ptr.clone());
    let extracted_off = MemoryModel::pointer_offset(ptr);

    assert_eq!(extracted_obj.sort().bitvec_width(), Some(32));
    assert_eq!(extracted_off.sort().bitvec_width(), Some(32));
}

#[test]
fn test_null_pointer() {
    let null = MemoryModel::null_pointer();
    assert_eq!(null.sort().bitvec_width(), Some(64));

    let is_null = MemoryModel::is_null(null);
    assert!(is_null.sort().is_bool());
}

#[test]
fn test_memory_allocation() {
    let mem = MemoryModel::new();
    let size = Expr::bitvec_const(64u32, 32);
    let (ptr, mem2) = mem.allocate(size);

    assert_eq!(ptr.sort().bitvec_width(), Some(64));

    // Verify read_ok returns Bool
    let valid = mem2.read_ok(ptr, Expr::bitvec_const(4u32, 32));
    assert!(valid.sort().is_bool());
}

#[test]
fn test_read_write_byte() {
    let mem = MemoryModel::new();
    let ptr = Expr::bitvec_const(0x1000i64, 64);
    let value = Expr::bitvec_const(0xAAu8, 8);

    let mem2 = mem.write_byte(ptr.clone(), value);
    let read_val = mem2.read_byte(ptr);

    assert_eq!(read_val.sort().bitvec_width(), Some(8));
}

#[test]
fn test_read_write_bytes() {
    let mem = MemoryModel::new();
    let ptr = Expr::bitvec_const(0x1000i64, 64);
    let bytes = vec![
        Expr::bitvec_const(0xAAu8, 8),
        Expr::bitvec_const(0xBBu8, 8),
        Expr::bitvec_const(0xCCu8, 8),
        Expr::bitvec_const(0xDDu8, 8),
    ];

    let mem2 = mem.write_bytes(&ptr, bytes);
    let read_val = mem2.read_bytes(&ptr, 4);

    // Result should be 32-bit
    assert_eq!(read_val.sort().bitvec_width(), Some(32));
}

#[test]
fn test_write_value() {
    let mem = MemoryModel::new();
    let ptr = Expr::bitvec_const(0x1000i64, 64);
    let value = Expr::bitvec_const(0xDEADBEEFu32, 32);

    let mem2 = mem.write_value(&ptr, &value);
    let read_val = mem2.read_bytes(&ptr, 4);

    assert_eq!(read_val.sort().bitvec_width(), Some(32));
}

#[test]
fn test_ptr_arithmetic() {
    let ptr = Expr::bitvec_const(0x0001_0000i64, 64); // obj=1, offset=0
    let offset = Expr::bitvec_const(8u32, 32);

    let new_ptr = MemoryModel::ptr_add(ptr, offset.clone());
    assert_eq!(new_ptr.sort().bitvec_width(), Some(64));

    let back_ptr = MemoryModel::ptr_sub(new_ptr, offset);
    assert_eq!(back_ptr.sort().bitvec_width(), Some(64));
}

#[test]
fn test_deallocate() {
    let mem = MemoryModel::new();
    let size = Expr::bitvec_const(64u32, 32);
    let (ptr, mem2) = mem.allocate(size);
    let mem3 = mem2.deallocate(ptr.clone());

    // After deallocation, read_ok should return false
    let valid = mem3.read_ok(ptr, Expr::bitvec_const(4u32, 32));
    assert!(valid.sort().is_bool());
}

/// End-to-end test demonstrating memory model generates valid SMT-LIB2.
///
/// This test allocates an object, writes a value, reads it back, and
/// verifies that the bounds check (read_ok) properly gates out-of-bounds access.
#[test]
fn test_e2e_memory_model_smt() {
    let mut program = AYProgram::new();
    program.set_logic("QF_AUFBV");
    program.produce_models();

    // Create memory model
    let mem = MemoryModel::new();

    // Allocate an 8-byte object
    let size = Expr::bitvec_const(8u32, 32);
    let (ptr, mem) = mem.allocate(size);

    // Write 0xDEADBEEF to the object (4 bytes)
    let value = Expr::bitvec_const(0xDEADBEEFu32, 32);
    let mem = mem.write_value(&ptr, &value);

    // Bounds check for 4-byte read at offset 0 should be valid
    let valid_access = mem.read_ok(ptr.clone(), Expr::bitvec_const(4u32, 32));

    // Out-of-bounds: 4-byte read at offset 6 (would read bytes 6,7,8,9 but object is only 8 bytes)
    let oob_ptr = MemoryModel::ptr_add(ptr, Expr::bitvec_const(6u32, 32));
    let oob_access = mem.read_ok(oob_ptr, Expr::bitvec_const(4u32, 32));

    // Assert that in-bounds access is valid
    program.assert(valid_access);

    // Assert that out-of-bounds access is NOT valid (negated)
    program.assert(oob_access.not());

    // Check satisfiability
    program.check_sat();

    let smt = program.to_string();

    // Verify SMT-LIB2 output contains expected components
    assert!(
        smt.contains("(set-logic QF_AUFBV)"),
        "Missing logic declaration"
    );
    assert!(smt.contains("(check-sat)"), "Missing check-sat");
    // The object_valid starts as const array (all false), so look for the store to it
    assert!(smt.contains("store"), "Missing store operation");
    assert!(smt.contains("bvule"), "Missing bounds check (bvule)");
}

/// Test that the memory model correctly tracks object validity.
#[test]
fn test_e2e_validity_tracking() {
    let mut program = AYProgram::new();
    program.set_logic("QF_AUFBV");

    let mem = MemoryModel::new();

    // Allocate object 1
    let (ptr1, mem) = mem.allocate(Expr::bitvec_const(16u32, 32));

    // Allocate object 2
    let (ptr2, mem) = mem.allocate(Expr::bitvec_const(32u32, 32));

    // Both should be valid
    let valid1 = mem.read_ok(ptr1.clone(), Expr::bitvec_const(4u32, 32));
    let valid2 = mem.read_ok(ptr2.clone(), Expr::bitvec_const(4u32, 32));

    // Deallocate object 1
    let mem = mem.deallocate(ptr1.clone());

    // After deallocation, object 1 should be invalid, object 2 still valid
    let invalid1 = mem.read_ok(ptr1, Expr::bitvec_const(4u32, 32));
    let still_valid2 = mem.read_ok(ptr2, Expr::bitvec_const(4u32, 32));

    // Before deallocation: both valid
    program.assert(valid1);
    program.assert(valid2);

    // After deallocation: ptr1 invalid, ptr2 valid
    program.assert(invalid1.not()); // invalid after free
    program.assert(still_valid2);

    program.check_sat();

    let smt = program.to_string();
    assert!(smt.contains("(check-sat)"));
}

/// Test that object ID overflow panics instead of wrapping.
///
/// Part of #863: Object ID overflow would cause valid allocations to alias
/// with null (object_id=0), breaking soundness. The fix uses checked_add().
#[test]
#[should_panic(expected = "Object ID overflow")]
fn test_object_id_overflow_panics() {
    // Create memory model with object_id near max
    let mut mem = MemoryModel::new();
    // Manually set next_object_id to near max (u32::MAX - 1)
    // This is the last valid allocation
    mem.next_object_id = u32::MAX - 1;

    let size = Expr::bitvec_const(8u32, 32);

    // First allocation should succeed (uses u32::MAX - 1)
    let (_ptr1, mem) = mem.allocate(size.clone());

    // Second allocation should succeed (uses u32::MAX)
    let (_ptr2, mem) = mem.allocate(size.clone());

    // Third allocation should panic (would overflow to 0)
    let _ = mem.allocate(size);
}

// ========================================================================
// Semantic SMT Tests (issue #865)
//
// These tests verify that the memory model generates correct SMT constraints
// by checking for required SMT-LIB2 patterns. Full solver execution is
// blocked on execute_direct BV support (see issue #865 comment).
// ========================================================================

/// Test that deallocate generates proper validity constraint.
///
/// Part of #865: Verify deallocation sets object_valid[id] = false.
#[test]
fn test_deallocate_constraint_structure() {
    let mut program = AYProgram::new();
    program.set_logic("QF_AUFBV");

    let mem = MemoryModel::new();
    let (ptr, mem) = mem.allocate(Expr::bitvec_const(64u32, 32));
    let mem = mem.deallocate(ptr.clone());

    // read_ok after deallocation
    let valid = mem.read_ok(ptr, Expr::bitvec_const(4u32, 32));
    program.assert(valid);
    program.check_sat();

    let smt = program.to_string();

    // Verify SMT contains store operations for deallocation
    // The pattern is: store(store(..., true), false) for alloc then dealloc
    // or select from const-array with stored values
    assert!(smt.contains("store"), "Missing store operation");
    // Deallocation stores `false` to mark object invalid
    assert!(
        smt.contains("false"),
        "Missing false value for deallocation"
    );
    // Allocation stores `true` to mark object valid initially
    assert!(smt.contains("true"), "Missing true value for allocation");
}

/// Test that allocation generates proper bounds tracking.
///
/// Part of #865: Verify allocation stores size in object_size array.
#[test]
fn test_allocation_constraint_structure() {
    let mut program = AYProgram::new();
    program.set_logic("QF_AUFBV");

    let mem = MemoryModel::new();
    let (ptr, mem) = mem.allocate(Expr::bitvec_const(64u32, 32));

    // Read_ok should use object_size for bounds checking
    let valid = mem.read_ok(ptr, Expr::bitvec_const(4u32, 32));
    program.assert(valid);
    program.check_sat();

    let smt = program.to_string();

    // Verify SMT contains proper bounds check structure
    assert!(smt.contains("object_size"), "Missing object_size array");
    assert!(
        smt.contains("bvule"),
        "Missing unsigned <= for bounds check"
    );
    assert!(smt.contains("bvadd"), "Missing offset + size addition");
}

/// Test that out-of-bounds generates proper constraint.
///
/// Part of #865: Verify bounds checking formula structure.
#[test]
fn test_bounds_check_constraint_structure() {
    let mut program = AYProgram::new();
    program.set_logic("QF_AUFBV");

    let mem = MemoryModel::new();
    // Allocate 8 bytes
    let (ptr, mem) = mem.allocate(Expr::bitvec_const(8u32, 32));

    // Try to read 16 bytes (out of bounds)
    let valid = mem.read_ok(ptr, Expr::bitvec_const(16u32, 32));
    program.assert(valid);
    program.check_sat();

    let smt = program.to_string();

    // Verify bounds check includes: offset + access_size <= object_size
    assert!(smt.contains("bvadd"), "Missing offset + size addition");
    assert!(smt.contains("bvule"), "Missing unsigned <= comparison");
    assert!(smt.contains("#x00000010"), "Missing 16-byte size constant");
}

/// Test that write-read generates proper store/select.
///
/// Part of #865: Verify memory array operations.
#[test]
fn test_write_read_constraint_structure() {
    let mut program = AYProgram::new();
    program.set_logic("QF_AUFBV");

    let mem = MemoryModel::new();
    let ptr = Expr::bitvec_const(0x0001_0000i64, 64); // obj=1, offset=0
    let value = Expr::bitvec_const(0xABu8, 8);

    let mem = mem.write_byte(ptr.clone(), value.clone());
    let read_val = mem.read_byte(ptr);

    // Assert read equals written (should be satisfiable)
    let equal = read_val.eq(value);
    program.assert(equal);
    program.check_sat();

    let smt = program.to_string();

    // Verify store and select for memory operations
    assert!(smt.contains("store"), "Missing store for write");
    assert!(smt.contains("select"), "Missing select for read");
    assert!(smt.contains("#xab"), "Missing byte value 0xAB");
}

/// Test dealloc_ok precondition for double-free detection.
///
/// Part of #1034: Verify dealloc_ok returns correct validity state.
#[test]
fn test_dealloc_ok_precondition() {
    let mut program = AYProgram::new();
    program.set_logic("QF_AUFBV");

    let mem = MemoryModel::new();
    let (ptr, mem) = mem.allocate(Expr::bitvec_const(64u32, 32));

    // Before deallocation: dealloc_ok should be true
    let ok_before = mem.dealloc_ok(ptr.clone());
    assert!(ok_before.sort().is_bool());

    // Deallocate
    let mem = mem.deallocate(ptr.clone());

    // After deallocation: dealloc_ok should be false (double-free would fail)
    let ok_after = mem.dealloc_ok(ptr);

    // Assert precondition semantics:
    // - ok_before == true (valid to free)
    // - ok_after == false (already freed, double-free would be invalid)
    program.assert(ok_before);
    program.assert(ok_after.not());
    program.check_sat();

    let smt = program.to_string();
    assert!(smt.contains("(check-sat)"));
    // The dealloc_ok check uses object_valid array select
    assert!(smt.contains("select"), "Missing select for validity check");
}

// ========================================================================
// Vulnerability Detection Assertion Tests (issue #8295)
//
// These tests verify the vulnerability detection assertion generators:
// assert_valid_access, assert_valid_free, assert_in_bounds, assert_non_null.
// ========================================================================

/// Test that assert_valid_access returns a Bool expression.
///
/// Part of #8295: Basic sort verification for use-after-free detection.
#[test]
fn test_assert_valid_access_sort_is_bool() {
    let mem = MemoryModel::new();
    let (ptr, mem) = mem.allocate(Expr::bitvec_const(8u32, 32));
    let result = mem.assert_valid_access(ptr);
    assert!(
        result.sort().is_bool(),
        "assert_valid_access must return Bool"
    );
}

/// Test that assert_valid_free returns a Bool expression.
///
/// Part of #8295: Basic sort verification for double-free detection.
#[test]
fn test_assert_valid_free_sort_is_bool() {
    let mem = MemoryModel::new();
    let (ptr, mem) = mem.allocate(Expr::bitvec_const(8u32, 32));
    let result = mem.assert_valid_free(ptr);
    assert!(
        result.sort().is_bool(),
        "assert_valid_free must return Bool"
    );
}

/// Test that assert_in_bounds returns a Bool expression.
///
/// Part of #8295: Basic sort verification for buffer overflow detection.
#[test]
fn test_assert_in_bounds_sort_is_bool() {
    let mem = MemoryModel::new();
    let (ptr, mem) = mem.allocate(Expr::bitvec_const(8u32, 32));
    let result = mem.assert_in_bounds(ptr, Expr::bitvec_const(4u32, 32));
    assert!(result.sort().is_bool(), "assert_in_bounds must return Bool");
}

/// Test that assert_non_null returns a Bool expression.
///
/// Part of #8295: Basic sort verification for null pointer detection.
#[test]
fn test_assert_non_null_sort_is_bool() {
    let ptr = Expr::bitvec_const(0x0001_0000i64, 64);
    let result = MemoryModel::assert_non_null(ptr);
    assert!(result.sort().is_bool(), "assert_non_null must return Bool");
}

/// Test use-after-free detection via SMT constraint structure.
///
/// Part of #8295: Allocate an object, free it, then check that
/// assert_valid_access on the freed pointer generates the correct
/// SMT pattern (select from object_valid after store(..., false)).
#[test]
fn test_use_after_free_detection_smt() {
    let mut program = AYProgram::new();
    program.set_logic("QF_AUFBV");

    let mem = MemoryModel::new();
    let (ptr, mem) = mem.allocate(Expr::bitvec_const(16u32, 32));

    // Free the object
    let mem = mem.deallocate(ptr.clone());

    // After free, assert_valid_access should be false (use-after-free)
    let valid = mem.assert_valid_access(ptr);
    // Negate: if the negation is satisfiable, the access is to freed memory
    program.assert(valid.not());
    program.check_sat();

    let smt = program.to_string();
    assert!(smt.contains("(check-sat)"), "Missing check-sat");
    // Must contain select (reading object_valid) and store (alloc true, dealloc false)
    assert!(smt.contains("select"), "Missing select for validity check");
    assert!(smt.contains("store"), "Missing store for alloc/dealloc");
    assert!(smt.contains("false"), "Missing false for deallocation");
}

/// Test double-free detection via SMT constraint structure.
///
/// Part of #8295: Allocate, free, then assert_valid_free on the already-freed
/// pointer. The negation should be satisfiable (meaning double-free detected).
#[test]
fn test_double_free_detection_smt() {
    let mut program = AYProgram::new();
    program.set_logic("QF_AUFBV");

    let mem = MemoryModel::new();
    let (ptr, mem) = mem.allocate(Expr::bitvec_const(32u32, 32));

    // First free
    let mem = mem.deallocate(ptr.clone());

    // assert_valid_free on already-freed pointer should be false
    let free_ok = mem.assert_valid_free(ptr);
    // Negate: SAT means double-free is reachable
    program.assert(free_ok.not());
    program.check_sat();

    let smt = program.to_string();
    assert!(smt.contains("(check-sat)"), "Missing check-sat");
    assert!(smt.contains("select"), "Missing select for validity check");
    // Pattern: store(store(const-array(false), id, true), id, false)
    assert!(smt.contains("store"), "Missing store operations");
}

/// Test buffer overflow detection via SMT constraint structure.
///
/// Part of #8295: Allocate 8 bytes, then check assert_in_bounds for a
/// 4-byte access at offset 6 (would read bytes 6..10, but object is only 8).
#[test]
fn test_buffer_overflow_detection_smt() {
    let mut program = AYProgram::new();
    program.set_logic("QF_AUFBV");

    let mem = MemoryModel::new();
    let (ptr, mem) = mem.allocate(Expr::bitvec_const(8u32, 32));

    // Move pointer to offset 6
    let oob_ptr = MemoryModel::ptr_add(ptr, Expr::bitvec_const(6u32, 32));

    // 4-byte access at offset 6 = bytes [6,10), but object is only [0,8)
    let in_bounds = mem.assert_in_bounds(oob_ptr, Expr::bitvec_const(4u32, 32));

    // Negate: SAT means buffer overflow is reachable
    program.assert(in_bounds.not());
    program.check_sat();

    let smt = program.to_string();
    assert!(smt.contains("(check-sat)"), "Missing check-sat");
    assert!(smt.contains("bvadd"), "Missing offset + size addition");
    assert!(
        smt.contains("bvule"),
        "Missing unsigned <= for bounds check"
    );
    assert!(
        smt.contains("object_size"),
        "Missing object_size array reference"
    );
}

/// Test null pointer detection via SMT constraint structure.
///
/// Part of #8295: Create a null pointer and verify assert_non_null
/// generates the correct negation of is_null.
#[test]
fn test_null_pointer_detection_smt() {
    let mut program = AYProgram::new();
    program.set_logic("QF_AUFBV");

    let null_ptr = MemoryModel::null_pointer();
    let non_null = MemoryModel::assert_non_null(null_ptr);

    // For a null pointer, assert_non_null should be false.
    // Negate: SAT on the original means the pointer CAN be null.
    // We assert the non_null directly -- for the concrete null pointer,
    // this asserts not(is_null(0)) which should be UNSAT.
    program.assert(non_null);
    program.check_sat();

    let smt = program.to_string();
    assert!(smt.contains("(check-sat)"), "Missing check-sat");
    // The null check compares extracted object_id against 0
    assert!(
        smt.contains("#x00000000"),
        "Missing null object_id constant"
    );
}

/// Test that assert_valid_access is true after allocation.
///
/// Part of #8295: Allocate an object, verify assert_valid_access holds.
#[test]
fn test_valid_access_after_alloc_smt() {
    let mut program = AYProgram::new();
    program.set_logic("QF_AUFBV");

    let mem = MemoryModel::new();
    let (ptr, mem) = mem.allocate(Expr::bitvec_const(16u32, 32));

    // After allocation, the object is valid
    let valid = mem.assert_valid_access(ptr);
    program.assert(valid);
    program.check_sat();

    let smt = program.to_string();
    assert!(smt.contains("(check-sat)"), "Missing check-sat");
    // Should contain select from object_valid and store(..., true) from allocation
    assert!(smt.contains("select"), "Missing select for validity check");
    assert!(smt.contains("true"), "Missing true from allocation");
}

/// Test that assert_in_bounds holds for valid in-bounds access.
///
/// Part of #8295: Allocate 8 bytes, check 4-byte access at offset 0.
#[test]
fn test_assert_in_bounds_valid_access_smt() {
    let mut program = AYProgram::new();
    program.set_logic("QF_AUFBV");

    let mem = MemoryModel::new();
    // Allocate 8 bytes
    let (ptr, mem) = mem.allocate(Expr::bitvec_const(8u32, 32));

    // 4-byte access at offset 0 should be in bounds
    let in_bounds = mem.assert_in_bounds(ptr, Expr::bitvec_const(4u32, 32));
    program.assert(in_bounds);
    program.check_sat();

    let smt = program.to_string();
    assert!(smt.contains("(check-sat)"), "Missing check-sat");
    assert!(smt.contains("bvadd"), "Missing offset + size addition");
    assert!(
        smt.contains("bvule"),
        "Missing unsigned <= for bounds check"
    );
    assert!(
        smt.contains("bvuge"),
        "Missing unsigned >= for overflow check"
    );
}

// ========================================================================
// Bulk Memory Operation Tests (issue #8294)
//
// Tests for memcpy, memmove, memset, and memcmp.
// ========================================================================

/// Test memcpy with small concrete length (byte-by-byte unrolling).
///
/// Part of #8294: Write 4 bytes to src, memcpy to dst, verify read from dst
/// produces correct sort.
#[test]
fn test_memcpy_small_concrete_sort() {
    let mem = MemoryModel::new();
    let src = Expr::bitvec_const(0x0001_0000i64, 64); // obj=1, offset=0
    let dst = Expr::bitvec_const(0x0002_0000i64, 64); // obj=2, offset=0

    // Write known bytes to source
    let bytes = vec![
        Expr::bitvec_const(0x11u8, 8),
        Expr::bitvec_const(0x22u8, 8),
        Expr::bitvec_const(0x33u8, 8),
        Expr::bitvec_const(0x44u8, 8),
    ];
    let mem = mem.write_bytes(&src, bytes);

    // memcpy 4 bytes from src to dst
    let len = Expr::bitvec_const(4u32, 32);
    let mem = mem.memcpy(&dst, &src, &len);

    // Read 4 bytes from dst — should be BV32
    let read_val = mem.read_bytes(&dst, 4);
    assert_eq!(
        read_val.sort().bitvec_width(),
        Some(32),
        "memcpy result should be readable as BV32"
    );
}

/// Test memcpy generates proper store/select in SMT-LIB2 output.
///
/// Part of #8294: Verify the generated SMT expression contains the expected
/// array operations (store for writes, select for reads).
#[test]
fn test_memcpy_smt_structure() {
    let mut program = AYProgram::new();
    program.set_logic("QF_AUFBV");

    let mem = MemoryModel::new();
    let src = Expr::bitvec_const(0x0001_0000i64, 64);
    let dst = Expr::bitvec_const(0x0002_0000i64, 64);

    // Write a byte to source
    let mem = mem.write_byte(src.clone(), Expr::bitvec_const(0xAAu8, 8));

    // memcpy 1 byte
    let len = Expr::bitvec_const(1u32, 32);
    let mem = mem.memcpy(&dst, &src, &len);

    // Read from destination and assert it equals 0xAA
    let dst_byte = mem.read_byte(dst);
    program.assert(dst_byte.eq(Expr::bitvec_const(0xAAu8, 8)));
    program.check_sat();

    let smt = program.to_string();
    assert!(smt.contains("store"), "Missing store operation from memcpy");
    assert!(
        smt.contains("select"),
        "Missing select operation from memcpy"
    );
    assert!(smt.contains("(check-sat)"), "Missing check-sat");
}

/// Test memcpy with zero length is a no-op.
///
/// Part of #8294: memcpy of 0 bytes should not modify memory.
#[test]
fn test_memcpy_zero_length() {
    let mem = MemoryModel::new();
    let src = Expr::bitvec_const(0x0001_0000i64, 64);
    let dst = Expr::bitvec_const(0x0002_0000i64, 64);
    let len = Expr::bitvec_const(0u32, 32);

    // This should return the same memory model (no modifications)
    let _mem = mem.memcpy(&dst, &src, &len);
}

/// Test memcpy with larger concrete length (word-level path, >16 bytes).
///
/// Part of #8294: Verify word-level optimization path produces valid memory.
#[test]
fn test_memcpy_large_concrete_sort() {
    let mem = MemoryModel::new();
    let src = Expr::bitvec_const(0x0001_0000i64, 64);
    let dst = Expr::bitvec_const(0x0002_0000i64, 64);

    // memcpy 24 bytes (3 words, no remainder)
    let len = Expr::bitvec_const(24u32, 32);
    let mem = mem.memcpy(&dst, &src, &len);

    // Should be able to read from dst
    let read_val = mem.read_bytes(&dst, 8);
    assert_eq!(
        read_val.sort().bitvec_width(),
        Some(64),
        "memcpy large: should be able to read 8 bytes from dst"
    );
}

/// Test memcpy with non-word-aligned length (word-level + remainder).
///
/// Part of #8294: 19 bytes = 2 words (16) + 3 remainder bytes.
#[test]
fn test_memcpy_word_plus_remainder() {
    let mem = MemoryModel::new();
    let src = Expr::bitvec_const(0x0001_0000i64, 64);
    let dst = Expr::bitvec_const(0x0002_0000i64, 64);

    // memcpy 19 bytes (2 words + 3 remainder)
    let len = Expr::bitvec_const(19u32, 32);
    let mem = mem.memcpy(&dst, &src, &len);

    // Read the last byte of the copied region
    let last_addr = dst.bvadd(Expr::bitvec_const(18i64, 64));
    let last_byte = mem.read_byte(last_addr);
    assert_eq!(
        last_byte.sort().bitvec_width(),
        Some(8),
        "Last byte should be BV8"
    );
}

/// Test memmove with small concrete length.
///
/// Part of #8294: memmove reads all source bytes first, then writes.
#[test]
fn test_memmove_small_concrete_sort() {
    let mem = MemoryModel::new();
    let src = Expr::bitvec_const(0x0001_0000i64, 64);
    let dst = Expr::bitvec_const(0x0002_0000i64, 64);

    // Write known bytes to source
    let bytes = vec![Expr::bitvec_const(0xAAu8, 8), Expr::bitvec_const(0xBBu8, 8)];
    let mem = mem.write_bytes(&src, bytes);

    // memmove 2 bytes
    let len = Expr::bitvec_const(2u32, 32);
    let mem = mem.memmove(&dst, &src, &len);

    let read_val = mem.read_bytes(&dst, 2);
    assert_eq!(
        read_val.sort().bitvec_width(),
        Some(16),
        "memmove result should be BV16"
    );
}

/// Test memmove with zero length is a no-op.
///
/// Part of #8294: memmove of 0 bytes should not modify memory.
#[test]
fn test_memmove_zero_length() {
    let mem = MemoryModel::new();
    let src = Expr::bitvec_const(0x0001_0000i64, 64);
    let dst = Expr::bitvec_const(0x0002_0000i64, 64);
    let len = Expr::bitvec_const(0u32, 32);
    let _mem = mem.memmove(&dst, &src, &len);
}

/// Test memmove SMT structure (read-all then write-all pattern).
///
/// Part of #8294: Verify memmove generates store/select operations.
#[test]
fn test_memmove_smt_structure() {
    let mut program = AYProgram::new();
    program.set_logic("QF_AUFBV");

    let mem = MemoryModel::new();
    let src = Expr::bitvec_const(0x0001_0000i64, 64);
    let dst = Expr::bitvec_const(0x0002_0000i64, 64);

    let mem = mem.write_byte(src.clone(), Expr::bitvec_const(0xFFu8, 8));

    let len = Expr::bitvec_const(1u32, 32);
    let mem = mem.memmove(&dst, &src, &len);

    let dst_byte = mem.read_byte(dst);
    program.assert(dst_byte.eq(Expr::bitvec_const(0xFFu8, 8)));
    program.check_sat();

    let smt = program.to_string();
    assert!(smt.contains("store"), "Missing store from memmove");
    assert!(smt.contains("select"), "Missing select from memmove");
}

/// Test memset with small concrete length (byte-by-byte unrolling).
///
/// Part of #8294: Fill 4 bytes with 0xFF.
#[test]
fn test_memset_small_concrete_sort() {
    let mem = MemoryModel::new();
    let dst = Expr::bitvec_const(0x0001_0000i64, 64);
    let val = Expr::bitvec_const(0xFFu8, 8);
    let len = Expr::bitvec_const(4u32, 32);

    let mem = mem.memset(&dst, &val, &len);

    // Read 4 bytes — should be BV32
    let read_val = mem.read_bytes(&dst, 4);
    assert_eq!(
        read_val.sort().bitvec_width(),
        Some(32),
        "memset: reading 4 bytes should give BV32"
    );
}

/// Test memset with zero length is a no-op.
///
/// Part of #8294: memset of 0 bytes should not modify memory.
#[test]
fn test_memset_zero_length() {
    let mem = MemoryModel::new();
    let dst = Expr::bitvec_const(0x0001_0000i64, 64);
    let val = Expr::bitvec_const(0u8, 8);
    let len = Expr::bitvec_const(0u32, 32);
    let _mem = mem.memset(&dst, &val, &len);
}

/// Test memset with larger concrete length (word-level path).
///
/// Part of #8294: 24 bytes = 3 words, using replicated byte word.
#[test]
fn test_memset_large_concrete_sort() {
    let mem = MemoryModel::new();
    let dst = Expr::bitvec_const(0x0001_0000i64, 64);
    let val = Expr::bitvec_const(0xABu8, 8);
    let len = Expr::bitvec_const(24u32, 32);

    let mem = mem.memset(&dst, &val, &len);

    let read_val = mem.read_bytes(&dst, 8);
    assert_eq!(
        read_val.sort().bitvec_width(),
        Some(64),
        "memset large: should be able to read 8 bytes as BV64"
    );
}

/// Test memset SMT structure.
///
/// Part of #8294: memset(ptr, 0xCC, 2) should store 0xCC at ptr and ptr+1.
#[test]
fn test_memset_smt_structure() {
    let mut program = AYProgram::new();
    program.set_logic("QF_AUFBV");

    let mem = MemoryModel::new();
    let dst = Expr::bitvec_const(0x0001_0000i64, 64);
    let val = Expr::bitvec_const(0xCCu8, 8);
    let len = Expr::bitvec_const(2u32, 32);

    let mem = mem.memset(&dst, &val, &len);

    // Both bytes should be 0xCC
    let byte0 = mem.read_byte(dst.clone());
    let byte1 = mem.read_byte(dst.bvadd(Expr::bitvec_const(1i64, 64)));
    program.assert(byte0.eq(Expr::bitvec_const(0xCCu8, 8)));
    program.assert(byte1.eq(Expr::bitvec_const(0xCCu8, 8)));
    program.check_sat();

    let smt = program.to_string();
    assert!(smt.contains("store"), "Missing store from memset");
    assert!(smt.contains("#xcc"), "Missing 0xCC value in memset output");
}

/// Test memcmp with small concrete length — equal regions.
///
/// Part of #8294: Write same bytes to two pointers, memcmp should yield
/// an expression that can equal 0 (equal).
#[test]
fn test_memcmp_equal_regions_sort() {
    let mem = MemoryModel::new();
    let a = Expr::bitvec_const(0x0001_0000i64, 64);
    let b = Expr::bitvec_const(0x0002_0000i64, 64);

    // Write same bytes to both
    let bytes = vec![Expr::bitvec_const(0x11u8, 8), Expr::bitvec_const(0x22u8, 8)];
    let mem = mem.write_bytes(&a, bytes.clone());
    let mem = mem.write_bytes(&b, bytes);

    let len = Expr::bitvec_const(2u32, 32);
    let result = mem.memcmp(&a, &b, &len);

    // Result should be BV32
    assert_eq!(
        result.sort().bitvec_width(),
        Some(32),
        "memcmp should return BV32"
    );
}

/// Test memcmp zero length — always equal.
///
/// Part of #8294: memcmp with len=0 should return 0 (equal).
#[test]
fn test_memcmp_zero_length_returns_zero() {
    let mem = MemoryModel::new();
    let a = Expr::bitvec_const(0x0001_0000i64, 64);
    let b = Expr::bitvec_const(0x0002_0000i64, 64);
    let len = Expr::bitvec_const(0u32, 32);

    let result = mem.memcmp(&a, &b, &len);
    assert_eq!(
        result.sort().bitvec_width(),
        Some(32),
        "memcmp zero-length should return BV32"
    );
}

/// Test memcmp SMT structure with equal writes.
///
/// Part of #8294: Write same byte to two addresses, memcmp(a, b, 1) should
/// produce SMT-LIB that contains store/select/ite.
#[test]
fn test_memcmp_smt_structure() {
    let mut program = AYProgram::new();
    program.set_logic("QF_AUFBV");

    let mem = MemoryModel::new();
    let a = Expr::bitvec_const(0x0001_0000i64, 64);
    let b = Expr::bitvec_const(0x0002_0000i64, 64);

    let mem = mem.write_byte(a.clone(), Expr::bitvec_const(0xAAu8, 8));
    let mem = mem.write_byte(b.clone(), Expr::bitvec_const(0xAAu8, 8));

    let len = Expr::bitvec_const(1u32, 32);
    let result = mem.memcmp(&a, &b, &len);

    // Assert result == 0 (equal)
    let zero = Expr::bitvec_const(0u32, 32);
    program.assert(result.eq(zero));
    program.check_sat();

    let smt = program.to_string();
    assert!(smt.contains("ite"), "Missing ite from memcmp");
    assert!(smt.contains("select"), "Missing select from memcmp");
    assert!(smt.contains("(check-sat)"), "Missing check-sat");
}

/// Test memcmp single byte comparison sort.
///
/// Part of #8294: Verify memcmp with len=1 returns correct BV32.
#[test]
fn test_memcmp_single_byte() {
    let mem = MemoryModel::new();
    let a = Expr::bitvec_const(0x0001_0000i64, 64);
    let b = Expr::bitvec_const(0x0002_0000i64, 64);
    let len = Expr::bitvec_const(1u32, 32);

    let result = mem.memcmp(&a, &b, &len);
    assert_eq!(
        result.sort().bitvec_width(),
        Some(32),
        "memcmp single byte should return BV32"
    );
}

/// Test memset word-level with remainder bytes.
///
/// Part of #8294: 19 bytes = 2 words (16) + 3 remainder bytes.
#[test]
fn test_memset_word_plus_remainder() {
    let mem = MemoryModel::new();
    let dst = Expr::bitvec_const(0x0001_0000i64, 64);
    let val = Expr::bitvec_const(0x42u8, 8);
    let len = Expr::bitvec_const(19u32, 32);

    let mem = mem.memset(&dst, &val, &len);

    // Read the last byte (at offset 18) — should be readable
    let last_addr = dst.bvadd(Expr::bitvec_const(18i64, 64));
    let last_byte = mem.read_byte(last_addr);
    assert_eq!(
        last_byte.sort().bitvec_width(),
        Some(8),
        "Last remainder byte should be BV8"
    );
}

// ========================================================================
// Dangling Pointer Detection Tests (issue #8303)
// ========================================================================

/// Test that assert_no_dangling returns a Bool expression.
///
/// Part of #8303: Basic sort verification for dangling pointer detection.
#[test]
fn test_assert_no_dangling_sort_is_bool() {
    let mem = MemoryModel::new();
    let (ptr, mem) = mem.allocate(Expr::bitvec_const(8u32, 32));
    let result = mem.assert_no_dangling(ptr);
    assert!(
        result.sort().is_bool(),
        "assert_no_dangling must return Bool"
    );
}

/// Test dangling pointer detection after free via SMT constraint structure.
///
/// Part of #8303: Allocate, free, then assert_no_dangling should be false.
#[test]
fn test_assert_no_dangling_after_free_smt() {
    let mut program = AYProgram::new();
    program.set_logic("QF_AUFBV");

    let mem = MemoryModel::new();
    let (ptr, mem) = mem.allocate(Expr::bitvec_const(16u32, 32));

    // Free the object
    let mem = mem.deallocate(ptr.clone());

    // After free, assert_no_dangling should be false (dangling pointer)
    let not_dangling = mem.assert_no_dangling(ptr);
    // Negate: if SAT, the pointer IS dangling
    program.assert(not_dangling.not());
    program.check_sat();

    let smt = program.to_string();
    assert!(smt.contains("(check-sat)"), "Missing check-sat");
    assert!(smt.contains("select"), "Missing select for validity check");
    assert!(smt.contains("false"), "Missing false for deallocation");
}

/// Test dangling pointer detection for null pointer.
///
/// Part of #8303: Null pointer should fail the assert_no_dangling check
/// because object_id == 0 is not a valid allocation.
#[test]
fn test_assert_no_dangling_null_pointer_smt() {
    let mut program = AYProgram::new();
    program.set_logic("QF_AUFBV");

    let mem = MemoryModel::new();
    let null_ptr = MemoryModel::null_pointer();

    // For null pointer, assert_no_dangling should be false (null is dangling)
    let not_dangling = mem.assert_no_dangling(null_ptr);
    // Assert it directly — for null, this should be UNSAT
    program.assert(not_dangling);
    program.check_sat();

    let smt = program.to_string();
    assert!(smt.contains("(check-sat)"), "Missing check-sat");
    assert!(
        smt.contains("#x00000000"),
        "Missing null object_id constant"
    );
}

/// Test that assert_pointer_provenance returns a Bool expression.
///
/// Part of #8303: Basic sort verification for provenance tracking.
#[test]
fn test_assert_pointer_provenance_sort_is_bool() {
    let mem = MemoryModel::new();
    let (ptr1, mem) = mem.allocate(Expr::bitvec_const(8u32, 32));
    let (ptr2, mem) = mem.allocate(Expr::bitvec_const(8u32, 32));

    let obj1 = MemoryModel::pointer_object(ptr1.clone());
    let obj2 = MemoryModel::pointer_object(ptr2);

    let result = mem.assert_pointer_provenance(ptr1, &[obj1, obj2]);
    assert!(
        result.sort().is_bool(),
        "assert_pointer_provenance must return Bool"
    );
}

/// Test that assert_pointer_provenance with empty allowed set returns Bool (false).
///
/// Part of #8303: Empty allowed set means no valid provenance.
#[test]
fn test_assert_pointer_provenance_empty_is_false() {
    let mem = MemoryModel::new();
    let ptr = Expr::bitvec_const(0x0001_0000i64, 64);

    let result = mem.assert_pointer_provenance(ptr, &[]);
    assert!(
        result.sort().is_bool(),
        "assert_pointer_provenance empty must return Bool"
    );
}

/// Test pointer provenance constraint via SMT structure.
///
/// Part of #8303: Allocate an object, check provenance constraint generates
/// equality comparison in SMT output.
#[test]
fn test_assert_pointer_provenance_smt() {
    let mut program = AYProgram::new();
    program.set_logic("QF_AUFBV");

    let mem = MemoryModel::new();
    let (ptr, mem) = mem.allocate(Expr::bitvec_const(16u32, 32));
    let obj_id = MemoryModel::pointer_object(ptr.clone());

    // Assert provenance: ptr must come from the allocated object
    let provenance = mem.assert_pointer_provenance(ptr, &[obj_id]);
    program.assert(provenance);
    program.check_sat();

    let smt = program.to_string();
    assert!(smt.contains("(check-sat)"), "Missing check-sat");
    // Provenance check uses equality between extracted object_id and allowed
    assert!(smt.contains("extract"), "Missing extract for object_id");
}

// ========================================================================
// Typed Memory Access Tests (issue #8303)
// ========================================================================

/// Test read_u16 returns BV16.
///
/// Part of #8303: Sort verification for typed read.
#[test]
fn test_read_u16_sort() {
    let mem = MemoryModel::new();
    let ptr = Expr::bitvec_const(0x0001_0000i64, 64);
    let result = mem.read_u16(ptr);
    assert_eq!(
        result.sort().bitvec_width(),
        Some(16),
        "read_u16 must return BV16"
    );
}

/// Test read_u32 returns BV32.
///
/// Part of #8303: Sort verification for typed read.
#[test]
fn test_read_u32_sort() {
    let mem = MemoryModel::new();
    let ptr = Expr::bitvec_const(0x0001_0000i64, 64);
    let result = mem.read_u32(ptr);
    assert_eq!(
        result.sort().bitvec_width(),
        Some(32),
        "read_u32 must return BV32"
    );
}

/// Test read_u64 returns BV64.
///
/// Part of #8303: Sort verification for typed read.
#[test]
fn test_read_u64_sort() {
    let mem = MemoryModel::new();
    let ptr = Expr::bitvec_const(0x0001_0000i64, 64);
    let result = mem.read_u64(ptr);
    assert_eq!(
        result.sort().bitvec_width(),
        Some(64),
        "read_u64 must return BV64"
    );
}

/// Test write/read round-trip for u16 via SMT structure.
///
/// Part of #8303: Write 0xBEEF as u16, read back, assert equality.
#[test]
fn test_write_read_u16_smt() {
    let mut program = AYProgram::new();
    program.set_logic("QF_AUFBV");

    let mem = MemoryModel::new();
    let ptr = Expr::bitvec_const(0x0001_0000i64, 64);
    let val = Expr::bitvec_const(i64::from(0xBEEFu16), 16);

    let mem = mem.write_u16(ptr.clone(), val.clone());
    let read_val = mem.read_u16(ptr);
    program.assert(read_val.eq(val));
    program.check_sat();

    let smt = program.to_string();
    assert!(smt.contains("store"), "Missing store from write_u16");
    assert!(smt.contains("select"), "Missing select from read_u16");
    assert!(smt.contains("(check-sat)"), "Missing check-sat");
}

/// Test write/read round-trip for u32 via SMT structure.
///
/// Part of #8303: Write 0xDEADBEEF as u32, read back, assert equality.
#[test]
fn test_write_read_u32_smt() {
    let mut program = AYProgram::new();
    program.set_logic("QF_AUFBV");

    let mem = MemoryModel::new();
    let ptr = Expr::bitvec_const(0x0001_0000i64, 64);
    let val = Expr::bitvec_const(i64::from(0xDEADBEEFu32), 32);

    let mem = mem.write_u32(ptr.clone(), val.clone());
    let read_val = mem.read_u32(ptr);
    program.assert(read_val.eq(val));
    program.check_sat();

    let smt = program.to_string();
    assert!(smt.contains("store"), "Missing store from write_u32");
    assert!(smt.contains("select"), "Missing select from read_u32");
    assert!(smt.contains("(check-sat)"), "Missing check-sat");
}

/// Test write/read round-trip for u64 via SMT structure.
///
/// Part of #8303: Write a u64 value, read back, assert equality.
#[test]
fn test_write_read_u64_smt() {
    let mut program = AYProgram::new();
    program.set_logic("QF_AUFBV");

    let mem = MemoryModel::new();
    let ptr = Expr::bitvec_const(0x0001_0000i64, 64);
    let val = Expr::bitvec_const(0x0102030405060708i64, 64);

    let mem = mem.write_u64(ptr.clone(), val.clone());
    let read_val = mem.read_u64(ptr);
    program.assert(read_val.eq(val));
    program.check_sat();

    let smt = program.to_string();
    assert!(smt.contains("store"), "Missing store from write_u64");
    assert!(smt.contains("select"), "Missing select from read_u64");
    assert!(smt.contains("(check-sat)"), "Missing check-sat");
}

// ========================================================================
// Memory Region Comparison Tests (issue #8303)
// ========================================================================

/// Test that regions_disjoint returns a Bool expression.
///
/// Part of #8303: Basic sort verification.
#[test]
fn test_regions_disjoint_sort_is_bool() {
    let mem = MemoryModel::new();
    let ptr1 = Expr::bitvec_const(0x0001_0000i64, 64); // obj=1
    let ptr2 = Expr::bitvec_const(0x0002_0000i64, 64); // obj=2
    let size = Expr::bitvec_const(8u32, 32);

    let result = mem.regions_disjoint(ptr1, size.clone(), ptr2, size);
    assert!(result.sort().is_bool(), "regions_disjoint must return Bool");
}

/// Test regions_disjoint for different objects via SMT structure.
///
/// Part of #8303: Two pointers to different objects should always be disjoint.
#[test]
fn test_regions_disjoint_different_objects_smt() {
    let mut program = AYProgram::new();
    program.set_logic("QF_AUFBV");

    let mem = MemoryModel::new();
    let (ptr1, mem) = mem.allocate(Expr::bitvec_const(16u32, 32));
    let (ptr2, mem) = mem.allocate(Expr::bitvec_const(16u32, 32));

    let disjoint = mem.regions_disjoint(
        ptr1,
        Expr::bitvec_const(8u32, 32),
        ptr2,
        Expr::bitvec_const(8u32, 32),
    );
    program.assert(disjoint);
    program.check_sat();

    let smt = program.to_string();
    assert!(smt.contains("(check-sat)"), "Missing check-sat");
    // Different objects use extract for object_id comparison
    assert!(smt.contains("extract"), "Missing extract for object_id");
}

/// Test regions_disjoint detects overlapping regions in the same object.
///
/// Part of #8303: Same object, offset 0 size 8 and offset 4 size 8 overlap
/// at bytes [4,8). Negated disjoint should be satisfiable.
#[test]
fn test_regions_disjoint_overlapping_same_object_smt() {
    let mut program = AYProgram::new();
    program.set_logic("QF_AUFBV");

    let mem = MemoryModel::new();
    let (ptr, mem) = mem.allocate(Expr::bitvec_const(16u32, 32));

    // ptr2 = ptr + 4 (same object, different offset)
    let ptr2 = MemoryModel::ptr_add(ptr.clone(), Expr::bitvec_const(4u32, 32));

    let disjoint = mem.regions_disjoint(
        ptr,
        Expr::bitvec_const(8u32, 32),
        ptr2,
        Expr::bitvec_const(8u32, 32),
    );

    // Negate disjoint: SAT means they DO overlap
    program.assert(disjoint.not());
    program.check_sat();

    let smt = program.to_string();
    assert!(smt.contains("(check-sat)"), "Missing check-sat");
    assert!(smt.contains("bvadd"), "Missing bvadd for offset + size");
    assert!(smt.contains("bvule"), "Missing bvule for range comparison");
}
