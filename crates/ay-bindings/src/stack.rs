// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates
//
//! Stack frame push/pop for function call modeling.
//!
//! Extends [`MemoryModel`] with stack frame semantics for modeling C/C++/Rust
//! function calls. Each `push_frame` creates a new stack frame object, and
//! `pop_frame` deallocates the frame and all its sub-allocations (alloca).
//!
//! ## Stack Frame Lifecycle
//!
//! ```text
//! push_frame()   →  frame object allocated, tracked on stack
//! stack_alloca() →  sub-objects allocated within frame
//! pop_frame()    →  all sub-objects + frame object deallocated
//! ```
//!
//! ## Use-After-Return Detection
//!
//! `assert_no_stack_escape(ptr, frame_id)` returns a constraint that the
//! pointer does NOT reference any object belonging to the given frame.
//! This detects dangling stack pointers returned from functions.
//!
//! ## LIFO Enforcement
//!
//! Frames must be popped in reverse order of creation (LIFO). `pop_frame`
//! validates that the frame being popped is the most recently pushed frame.

use crate::expr::Expr;
use crate::memory::{MemoryModel, OBJECT_ID_WIDTH, OFFSET_WIDTH, POINTER_WIDTH};

/// Default stack frame size in bytes (symbolic, but we use a reasonable default).
/// Stack frames are objects in the memory model; their size governs how much
/// alloca space is available before an out-of-bounds occurs.
const DEFAULT_FRAME_SIZE: u32 = 4096;

impl MemoryModel {
    // ===== Stack Frame Operations =====

    /// Push a new stack frame onto the call stack.
    ///
    /// Allocates a new memory object to represent the stack frame and records
    /// it in the frame tracking structures. The frame object has a default size
    /// of 4096 bytes.
    ///
    /// # Returns
    /// A tuple of:
    /// - `frame_pointer` — pointer to the frame object (BitVec64, offset=0)
    /// - `frame_object_id` — the object ID of the frame (BitVec32)
    /// - Updated `MemoryModel` with the frame tracked
    ///
    /// ENSURES: result.0.sort().bitvec_width() == Some(64)
    /// ENSURES: result.1.sort().bitvec_width() == Some(32)
    /// ENSURES: result.2.stack_frames.last() == Some(frame_object_id_value)
    #[must_use]
    pub fn push_frame(self) -> (Expr, Expr, Self) {
        let frame_size = Expr::bitvec_const(DEFAULT_FRAME_SIZE, OBJECT_ID_WIDTH);
        // The object ID that will be assigned is self.next_object_id
        let frame_obj_id_val = self.next_object_id;
        let (frame_ptr, mut model) = self.allocate(frame_size);
        let frame_object_id = Expr::bitvec_const(frame_obj_id_val, OBJECT_ID_WIDTH);

        // Track this frame
        model.stack_frames.push(frame_obj_id_val);
        model.frame_allocations.push(Vec::new());

        (frame_ptr, frame_object_id, model)
    }

    /// Pop the top stack frame, deallocating it and all its sub-allocations.
    ///
    /// Validates LIFO ordering: the `frame_id` must correspond to the most
    /// recently pushed frame. All objects allocated via `stack_alloca` within
    /// this frame are deallocated before the frame itself.
    ///
    /// # Arguments
    /// * `frame_id` - The object ID of the frame to pop (BitVec32).
    ///   Must match the top of the frame stack.
    ///
    /// # Returns
    /// A tuple of:
    /// - `constraint` — Bool expression that all deallocated objects were valid
    ///   at the time of deallocation (conjunction of dealloc_ok checks)
    /// - Updated `MemoryModel` with the frame and sub-allocations deallocated
    ///
    /// REQUIRES: frame_id.sort().bitvec_width() == Some(32)
    /// REQUIRES: self.stack_frames is non-empty
    /// ENSURES: result.0.sort().is_bool()
    ///
    /// # Panics
    /// - Panics if `frame_id` is not BitVec(32).
    /// - Panics if there are no active stack frames.
    /// - Panics if `frame_id` does not match the top frame (LIFO violation).
    #[must_use]
    pub fn pop_frame(mut self, frame_id: Expr) -> (Expr, Self) {
        assert!(
            frame_id.sort().is_bitvec() && frame_id.sort().bitvec_width() == Some(OBJECT_ID_WIDTH),
            "pop_frame frame_id requires BitVec(32), got {:?}",
            frame_id.sort()
        );

        let top_frame = self
            .stack_frames
            .last()
            .copied()
            .expect("pop_frame: no active stack frames");

        // LIFO validation: the frame being popped must be the top frame.
        // We check the concrete value since frame IDs are assigned deterministically.
        let top_id_expr = Expr::bitvec_const(top_frame, OBJECT_ID_WIDTH);
        let lifo_check = frame_id.eq(top_id_expr);

        // Collect dealloc_ok constraints for all sub-allocations and the frame itself
        let mut constraints = vec![lifo_check];

        // Pop the frame's sub-allocations
        let sub_allocs = self
            .frame_allocations
            .pop()
            .expect("pop_frame: frame_allocations out of sync with stack_frames");

        // Deallocate each sub-allocation
        for alloc_id in &sub_allocs {
            let alloc_ptr = Self::mk_pointer(
                Expr::bitvec_const(*alloc_id, OBJECT_ID_WIDTH),
                Expr::bitvec_const(0u32, OFFSET_WIDTH),
            );
            let ok = self.dealloc_ok(alloc_ptr.clone());
            constraints.push(ok);
            self = self.deallocate(alloc_ptr);
        }

        // Deallocate the frame object itself
        let frame_ptr = Self::mk_pointer(
            Expr::bitvec_const(top_frame, OBJECT_ID_WIDTH),
            Expr::bitvec_const(0u32, OFFSET_WIDTH),
        );
        let ok = self.dealloc_ok(frame_ptr.clone());
        constraints.push(ok);
        self = self.deallocate(frame_ptr);

        // Pop the frame from the stack
        self.stack_frames.pop();

        // Combine all constraints
        let constraint = Expr::and_many(constraints);

        (constraint, self)
    }

    /// Allocate memory within a stack frame (like C's `alloca`).
    ///
    /// Creates a new memory object of the given size and associates it with
    /// the specified stack frame. When the frame is popped, this allocation
    /// will be automatically deallocated.
    ///
    /// # Arguments
    /// * `frame_id` - The object ID of the owning frame (BitVec32)
    /// * `size` - Size of the allocation in bytes (BitVec32)
    ///
    /// # Returns
    /// A tuple of:
    /// - Pointer to the allocated memory (BitVec64, offset=0)
    /// - Updated `MemoryModel` with the allocation tracked
    ///
    /// REQUIRES: frame_id.sort().bitvec_width() == Some(32)
    /// REQUIRES: size.sort().bitvec_width() == Some(32)
    /// ENSURES: result.0.sort().bitvec_width() == Some(64)
    ///
    /// # Panics
    /// - Panics if `frame_id` is not BitVec(32).
    /// - Panics if `size` is not BitVec(32).
    /// - Panics if `frame_id` does not match any active frame.
    #[must_use]
    pub fn stack_alloca(mut self, frame_id: Expr, size: Expr) -> (Expr, Self) {
        assert!(
            frame_id.sort().is_bitvec() && frame_id.sort().bitvec_width() == Some(OBJECT_ID_WIDTH),
            "stack_alloca frame_id requires BitVec(32), got {:?}",
            frame_id.sort()
        );
        assert!(
            size.sort().is_bitvec() && size.sort().bitvec_width() == Some(OBJECT_ID_WIDTH),
            "stack_alloca size requires BitVec(32), got {:?}",
            size.sort()
        );

        // Record the object ID that will be assigned
        let alloc_obj_id = self.next_object_id;

        // Allocate via the standard allocator
        let (ptr, model) = self.allocate(size);
        self = model;

        // Find the frame index to associate this allocation with
        let frame_idx = self
            .stack_frames
            .iter()
            .position(|&fid| {
                // frame_id is a concrete BV32 constant matching fid
                fid == extract_concrete_u32(&frame_id)
            })
            .expect("stack_alloca: frame_id does not match any active frame");

        self.frame_allocations[frame_idx].push(alloc_obj_id);

        (ptr, self)
    }

    /// Assert that a pointer does NOT escape a stack frame.
    ///
    /// Returns a Bool constraint that is true iff `ptr` does not point to
    /// the frame object or any of its sub-allocations. This is used to detect
    /// dangling stack pointers returned from functions.
    ///
    /// # Arguments
    /// * `ptr` - Pointer to check (BitVec64)
    /// * `frame_id` - Object ID of the stack frame (BitVec32)
    ///
    /// # Returns
    /// Bool expression: `pointer_object(ptr) != frame_id AND
    ///                   pointer_object(ptr) != alloca_id_1 AND ... `
    ///
    /// REQUIRES: ptr.sort().bitvec_width() == Some(64)
    /// REQUIRES: frame_id.sort().bitvec_width() == Some(32)
    /// ENSURES: result.sort().is_bool()
    ///
    /// # Panics
    /// - Panics if `ptr` is not BitVec(64).
    /// - Panics if `frame_id` is not BitVec(32).
    #[must_use]
    pub fn assert_no_stack_escape(&self, ptr: Expr, frame_id: Expr) -> Expr {
        assert!(
            ptr.sort().is_bitvec() && ptr.sort().bitvec_width() == Some(POINTER_WIDTH),
            "assert_no_stack_escape ptr requires BitVec(64), got {:?}",
            ptr.sort()
        );
        assert!(
            frame_id.sort().is_bitvec() && frame_id.sort().bitvec_width() == Some(OBJECT_ID_WIDTH),
            "assert_no_stack_escape frame_id requires BitVec(32), got {:?}",
            frame_id.sort()
        );

        let ptr_obj = Self::pointer_object(ptr);

        // The pointer must not reference the frame object itself
        let not_frame = ptr_obj.clone().eq(frame_id.clone()).not();

        // The pointer must not reference any sub-allocation of this frame
        let frame_id_val = extract_concrete_u32(&frame_id);
        let frame_idx = self
            .stack_frames
            .iter()
            .position(|&fid| fid == frame_id_val);

        match frame_idx {
            Some(idx) => {
                let mut constraints = vec![not_frame];
                for &alloc_id in &self.frame_allocations[idx] {
                    let alloc_id_expr = Expr::bitvec_const(alloc_id, OBJECT_ID_WIDTH);
                    constraints.push(ptr_obj.clone().eq(alloc_id_expr).not());
                }
                Expr::and_many(constraints)
            }
            None => {
                // Frame not found in active frames — could have been popped already.
                // Just check against the frame object ID itself.
                not_frame
            }
        }
    }

    /// Returns the number of active stack frames.
    #[must_use]
    pub fn frame_depth(&self) -> usize {
        self.stack_frames.len()
    }
}

#[cfg(test)]
#[path = "stack_tests.rs"]
mod tests;

/// Extract a concrete u32 value from a bitvec constant expression.
///
/// This is used internally for frame tracking where frame IDs are always
/// concrete constants assigned by `allocate()`.
///
/// # Panics
/// Panics if the expression is not a concrete bitvec constant.
fn extract_concrete_u32(expr: &Expr) -> u32 {
    // Frame IDs are always created via Expr::bitvec_const(id, 32) where id is
    // the next_object_id at allocation time. We need to extract this concrete
    // value for frame tracking.
    //
    // The Expr type stores bitvec constants as BigInt internally. We use the
    // Display/to_string representation to extract the value, or we can match
    // on the ExprValue variant directly.
    use crate::expr::ExprValue;
    match expr.value() {
        ExprValue::BitVecConst { value, .. } => {
            use num_traits::ToPrimitive;
            value
                .to_u32()
                .expect("extract_concrete_u32: frame ID exceeds u32 range")
        }
        _ => panic!("extract_concrete_u32: expected concrete bitvec constant, got {expr:?}"),
    }
}
