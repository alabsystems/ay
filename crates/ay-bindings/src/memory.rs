// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates
//
//! Memory model for AY backend verification.
//!
//! Implements a split-pointer memory model where pointers are represented as
//! `(object_id, offset)` pairs encoded in a 64-bit bitvector:
//!
//! - High 32 bits: `object_id` (0 reserved for null)
//! - Low 32 bits: `offset` in bytes within the object
//!
//! This design provides:
//! - **Non-aliasing by construction**: Different objects can't alias unless `object_id` matches
//! - **Local bounds checks**: `read_ok(ptr, size)` depends only on `object_id`, `offset`, and object metadata
//! - **Compatibility** with existing `BitVec(64)` pointer sort mapping
//!
//! ## SMT State
//!
//! The memory model maintains three SMT arrays:
//! - `mem : (Array (_ BitVec 64) (_ BitVec 8))` — byte-addressed payload
//! - `object_size : (Array (_ BitVec 32) (_ BitVec 32))` — size in bytes per object
//! - `object_valid : (Array (_ BitVec 32) Bool)` — allocated and not freed
//!
//! ## Example
//!
//! ```rust
//! use ay_bindings::{Expr, Sort};
//! use ay_bindings::memory::MemoryModel;
//!
//! // Create a memory model
//! let mem = MemoryModel::new();
//!
//! // Allocate an object of size 8
//! let (ptr, mem2) = mem.allocate(Expr::bitvec_const(8u32, 32));
//!
//! // Check if pointer is valid for 4-byte read
//! let valid = mem2.read_ok(ptr.clone(), Expr::bitvec_const(4u32, 32));
//!
//! // Read 4 bytes from pointer
//! let value = mem2.read_bytes(&ptr, 4);
//!
//! // Write 4 bytes to pointer
//! let mem3 = mem2.write_bytes(&ptr, vec![
//!     Expr::bitvec_const(0xAAu8, 8),
//!     Expr::bitvec_const(0xBBu8, 8),
//!     Expr::bitvec_const(0xCCu8, 8),
//!     Expr::bitvec_const(0xDDu8, 8),
//! ]);
//! ```
//!
//! ## Design Reference
//!
//! See the development design notes for full specification.

use crate::expr::Expr;
use crate::sort::Sort;

/// Object ID width in bits (high 32 bits of pointer).
pub const OBJECT_ID_WIDTH: u32 = 32;

/// Offset width in bits (low 32 bits of pointer).
pub const OFFSET_WIDTH: u32 = 32;

/// Total pointer width in bits.
pub const POINTER_WIDTH: u32 = OBJECT_ID_WIDTH + OFFSET_WIDTH;

/// Memory model for AY backend verification.
///
/// Tracks three SMT arrays that model memory state:
/// - `mem`: byte-addressed memory contents
/// - `object_size`: size of each allocated object
/// - `object_valid`: whether each object is allocated and not freed
#[derive(Debug, Clone)]
pub struct MemoryModel {
    /// Byte-addressed memory: (Array BitVec64 BitVec8)
    pub mem: Expr,
    /// Object sizes: (Array BitVec32 BitVec32)
    pub object_size: Expr,
    /// Object validity: (Array BitVec32 Bool)
    pub object_valid: Expr,
    /// Next object ID to allocate (monotonically increasing).
    pub(crate) next_object_id: u32,
    /// Stack of active frame object IDs (LIFO order).
    ///
    /// Each entry is the `next_object_id` value assigned when the frame was
    /// pushed. Used to enforce LIFO pop ordering and to associate sub-allocations.
    pub(crate) stack_frames: Vec<u32>,
    /// Per-frame sub-allocation tracking.
    ///
    /// `frame_allocations[i]` contains the object IDs of all `stack_alloca`
    /// allocations belonging to `stack_frames[i]`. When the frame is popped,
    /// all sub-allocations are deallocated automatically.
    pub(crate) frame_allocations: Vec<Vec<u32>>,
}

impl Default for MemoryModel {
    fn default() -> Self {
        Self::new()
    }
}

impl MemoryModel {
    /// Create a new memory model with symbolic initial state.
    ///
    /// The memory arrays are initialized to symbolic variables, allowing
    /// the solver to reason about arbitrary initial memory states.
    #[must_use]
    pub fn new() -> Self {
        Self {
            // Memory starts as symbolic (nondet bytes)
            mem: Expr::var(
                "mem",
                Sort::array(Sort::bitvec(POINTER_WIDTH), Sort::bitvec(8)),
            ),
            // Object sizes start as symbolic
            object_size: Expr::var(
                "object_size",
                Sort::array(Sort::bitvec(OBJECT_ID_WIDTH), Sort::bitvec(OBJECT_ID_WIDTH)),
            ),
            // Object validity starts as all-false (nothing allocated)
            object_valid: Expr::const_array(Sort::bitvec(OBJECT_ID_WIDTH), Expr::false_()),
            // Object ID 0 is reserved for null
            next_object_id: 1,
            // No active stack frames
            stack_frames: Vec::new(),
            frame_allocations: Vec::new(),
        }
    }

    /// Create a memory model with named arrays for debugging.
    ///
    /// Uses the provided prefix for array variable names.
    #[must_use]
    pub fn with_prefix(prefix: &str) -> Self {
        Self {
            mem: Expr::var(
                format!("{prefix}_mem"),
                Sort::array(Sort::bitvec(POINTER_WIDTH), Sort::bitvec(8)),
            ),
            object_size: Expr::var(
                format!("{prefix}_object_size"),
                Sort::array(Sort::bitvec(OBJECT_ID_WIDTH), Sort::bitvec(OBJECT_ID_WIDTH)),
            ),
            object_valid: Expr::const_array(Sort::bitvec(OBJECT_ID_WIDTH), Expr::false_()),
            next_object_id: 1,
            stack_frames: Vec::new(),
            frame_allocations: Vec::new(),
        }
    }

    // ===== Pointer Operations =====

    /// Extract the object ID from a pointer (high 32 bits).
    ///
    /// REQUIRES: ptr.sort().is_bitvec() && ptr.sort().bitvec_width() == Some(64)
    /// ENSURES: result.sort().is_bitvec() && result.sort().bitvec_width() == Some(32)
    ///
    /// # Panics
    /// Panics if `ptr` is not a 64-bit bitvector.
    #[must_use]
    pub fn pointer_object(ptr: Expr) -> Expr {
        assert!(
            ptr.sort().is_bitvec() && ptr.sort().bitvec_width() == Some(POINTER_WIDTH),
            "pointer_object requires BitVec(64), got {:?}",
            ptr.sort()
        );
        ptr.extract(POINTER_WIDTH - 1, OFFSET_WIDTH)
    }

    /// Extract the offset from a pointer (low 32 bits).
    ///
    /// REQUIRES: ptr.sort().is_bitvec() && ptr.sort().bitvec_width() == Some(64)
    /// ENSURES: result.sort().is_bitvec() && result.sort().bitvec_width() == Some(32)
    ///
    /// # Panics
    /// Panics if `ptr` is not a 64-bit bitvector.
    #[must_use]
    pub fn pointer_offset(ptr: Expr) -> Expr {
        assert!(
            ptr.sort().is_bitvec() && ptr.sort().bitvec_width() == Some(POINTER_WIDTH),
            "pointer_offset requires BitVec(64), got {:?}",
            ptr.sort()
        );
        ptr.extract(OFFSET_WIDTH - 1, 0)
    }

    /// Construct a pointer from object ID and offset.
    ///
    /// REQUIRES: object_id.sort().is_bitvec() && object_id.sort().bitvec_width() == Some(32)
    /// REQUIRES: offset.sort().is_bitvec() && offset.sort().bitvec_width() == Some(32)
    /// ENSURES: result.sort().is_bitvec() && result.sort().bitvec_width() == Some(64)
    /// ENSURES: pointer_object(result) == object_id
    /// ENSURES: pointer_offset(result) == offset
    ///
    /// # Panics
    /// Panics if `object_id` or `offset` are not 32-bit bitvectors.
    #[must_use]
    pub fn mk_pointer(object_id: Expr, offset: Expr) -> Expr {
        assert!(
            object_id.sort().is_bitvec()
                && object_id.sort().bitvec_width() == Some(OBJECT_ID_WIDTH),
            "mk_pointer object_id requires BitVec(32), got {:?}",
            object_id.sort()
        );
        assert!(
            offset.sort().is_bitvec() && offset.sort().bitvec_width() == Some(OFFSET_WIDTH),
            "mk_pointer offset requires BitVec(32), got {:?}",
            offset.sort()
        );
        object_id.concat(offset)
    }

    /// Create a null pointer (object_id = 0, offset = 0).
    ///
    /// ENSURES: result.sort().is_bitvec() && result.sort().bitvec_width() == Some(64)
    /// ENSURES: pointer_object(result) == 0
    /// ENSURES: pointer_offset(result) == 0
    #[must_use]
    pub fn null_pointer() -> Expr {
        Expr::bitvec_const(0i64, POINTER_WIDTH)
    }

    /// Check if a pointer is null (object_id == 0).
    ///
    /// REQUIRES: ptr.sort().is_bitvec() && ptr.sort().bitvec_width() == Some(64)
    /// ENSURES: result.sort().is_bool()
    /// ENSURES: result == (pointer_object(ptr) == 0)
    #[must_use]
    pub fn is_null(ptr: Expr) -> Expr {
        let object_id = Self::pointer_object(ptr);
        object_id.eq(Expr::bitvec_const(0u32, OBJECT_ID_WIDTH))
    }

    // ===== Memory Validity =====

    /// Check if a memory access is valid (read or write).
    ///
    /// Returns a Bool expression that is true iff:
    /// - The object is valid (allocated and not freed)
    /// - The access `[offset, offset + size)` fits within object bounds
    ///
    /// # Arguments
    /// * `ptr` - Pointer to check (BitVec64)
    /// * `size` - Size of access in bytes (BitVec32)
    ///
    /// REQUIRES: ptr.sort().is_bitvec() && ptr.sort().bitvec_width() == Some(64)
    /// REQUIRES: size.sort().is_bitvec() && size.sort().bitvec_width() == Some(32)
    /// ENSURES: result.sort().is_bool()
    /// ENSURES: result implies object is valid and access is in bounds
    ///
    /// # Panics
    /// Panics if `ptr` is not BitVec(64) or `size` is not BitVec(32).
    #[must_use]
    pub fn read_ok(&self, ptr: Expr, size: Expr) -> Expr {
        assert!(
            ptr.sort().is_bitvec() && ptr.sort().bitvec_width() == Some(POINTER_WIDTH),
            "read_ok ptr requires BitVec(64), got {:?}",
            ptr.sort()
        );
        assert!(
            size.sort().is_bitvec() && size.sort().bitvec_width() == Some(OBJECT_ID_WIDTH),
            "read_ok size requires BitVec(32), got {:?}",
            size.sort()
        );

        let object_id = Self::pointer_object(ptr.clone());
        let offset = Self::pointer_offset(ptr);

        // Check: object is valid
        let valid = self.object_valid.clone().select(object_id.clone());

        // Check: offset + size <= object_size[object_id]
        // Also check for overflow: offset + size >= offset (i.e., no wrap-around)
        let obj_size = self.object_size.clone().select(object_id);
        let end_offset = offset.clone().bvadd(size);
        let in_bounds = end_offset.clone().bvule(obj_size);
        // Overflow check: end_offset >= offset (addition didn't wrap)
        let no_overflow = end_offset.bvuge(offset);

        valid.and(in_bounds).and(no_overflow)
    }

    /// Alias for `read_ok` - write validity uses the same check.
    ///
    /// REQUIRES: ptr.sort().is_bitvec() && ptr.sort().bitvec_width() == Some(64)
    /// REQUIRES: size.sort().is_bitvec() && size.sort().bitvec_width() == Some(32)
    /// ENSURES: result.sort().is_bool()
    #[must_use]
    pub fn write_ok(&self, ptr: Expr, size: Expr) -> Expr {
        self.read_ok(ptr, size)
    }

    // Memory read/write operations and allocation are in memory_ops.rs.

    // ===== Pointer Arithmetic =====

    /// Add an offset to a pointer.
    ///
    /// This performs pointer arithmetic by adding the offset to the pointer's
    /// existing offset field, keeping the object_id unchanged.
    ///
    /// # Arguments
    /// * `ptr` - Base pointer (BitVec64)
    /// * `offset` - Offset to add in bytes (BitVec32)
    ///
    /// # Returns
    /// New pointer with the same object_id but updated offset.
    ///
    /// REQUIRES: ptr.sort().is_bitvec() && ptr.sort().bitvec_width() == Some(64)
    /// REQUIRES: offset.sort().is_bitvec() && offset.sort().bitvec_width() == Some(32)
    /// ENSURES: result.sort().bitvec_width() == Some(64)
    /// ENSURES: pointer_object(result) == pointer_object(ptr)
    /// ENSURES: pointer_offset(result) == pointer_offset(ptr) + offset
    ///
    /// # Panics
    /// Panics if `ptr` is not BitVec(64) or `offset` is not BitVec(32).
    #[must_use]
    pub fn ptr_add(ptr: Expr, offset: Expr) -> Expr {
        assert!(
            ptr.sort().is_bitvec() && ptr.sort().bitvec_width() == Some(POINTER_WIDTH),
            "ptr_add ptr requires BitVec(64), got {:?}",
            ptr.sort()
        );
        assert!(
            offset.sort().is_bitvec() && offset.sort().bitvec_width() == Some(OFFSET_WIDTH),
            "ptr_add offset requires BitVec(32), got {:?}",
            offset.sort()
        );

        let object_id = Self::pointer_object(ptr.clone());
        let current_offset = Self::pointer_offset(ptr);
        let new_offset = current_offset.bvadd(offset);
        Self::mk_pointer(object_id, new_offset)
    }

    /// Subtract an offset from a pointer.
    ///
    /// # Arguments
    /// * `ptr` - Base pointer (BitVec64)
    /// * `offset` - Offset to subtract in bytes (BitVec32)
    ///
    /// # Returns
    /// New pointer with the same object_id but updated offset.
    ///
    /// REQUIRES: ptr.sort().is_bitvec() && ptr.sort().bitvec_width() == Some(64)
    /// REQUIRES: offset.sort().is_bitvec() && offset.sort().bitvec_width() == Some(32)
    /// ENSURES: result.sort().bitvec_width() == Some(64)
    /// ENSURES: pointer_object(result) == pointer_object(ptr)
    /// ENSURES: pointer_offset(result) == pointer_offset(ptr) - offset
    #[must_use]
    pub fn ptr_sub(ptr: Expr, offset: Expr) -> Expr {
        assert!(
            ptr.sort().is_bitvec() && ptr.sort().bitvec_width() == Some(POINTER_WIDTH),
            "ptr_sub ptr requires BitVec(64), got {:?}",
            ptr.sort()
        );
        assert!(
            offset.sort().is_bitvec() && offset.sort().bitvec_width() == Some(OFFSET_WIDTH),
            "ptr_sub offset requires BitVec(32), got {:?}",
            offset.sort()
        );

        let object_id = Self::pointer_object(ptr.clone());
        let current_offset = Self::pointer_offset(ptr);
        let new_offset = current_offset.bvsub(offset);
        Self::mk_pointer(object_id, new_offset)
    }
}

#[cfg(test)]
#[path = "memory_tests.rs"]
mod tests;
