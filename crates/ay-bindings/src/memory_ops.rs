// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates
//
//! Memory read/write operations and allocation for [`MemoryModel`].
//!
//! Extracted from `memory.rs` for code health (#5970).

use crate::expr::{Expr, ExprValue};
use crate::memory::{MemoryModel, OBJECT_ID_WIDTH, OFFSET_WIDTH, POINTER_WIDTH};
use num_traits::ToPrimitive;

impl MemoryModel {
    // ===== Memory Operations =====

    /// Read a single byte from memory at the given pointer.
    ///
    /// Returns a BitVec(8) expression representing the byte value.
    ///
    /// REQUIRES: ptr.sort().is_bitvec() && ptr.sort().bitvec_width() == Some(64)
    /// ENSURES: result.sort().is_bitvec() && result.sort().bitvec_width() == Some(8)
    ///
    /// # Panics
    /// Panics if `ptr` is not BitVec(64).
    #[must_use]
    pub fn read_byte(&self, ptr: Expr) -> Expr {
        assert!(
            ptr.sort().is_bitvec() && ptr.sort().bitvec_width() == Some(POINTER_WIDTH),
            "read_byte ptr requires BitVec(64), got {:?}",
            ptr.sort()
        );
        self.mem.clone().select(ptr)
    }

    /// Read multiple bytes from memory starting at the given pointer.
    ///
    /// Returns a BitVec expression of width `n * 8` bits in little-endian order.
    /// The first byte (at `ptr`) is in the least significant position.
    ///
    /// REQUIRES: ptr.sort().is_bitvec() && ptr.sort().bitvec_width() == Some(64)
    /// REQUIRES: n > 0
    /// ENSURES: result.sort().is_bitvec() && result.sort().bitvec_width() == Some(n * 8)
    ///
    /// # Panics
    /// Panics if `ptr` is not BitVec(64) or `n` is 0.
    #[must_use]
    pub fn read_bytes(&self, ptr: &Expr, n: usize) -> Expr {
        assert!(n > 0, "read_bytes requires n > 0");
        assert!(
            ptr.sort().is_bitvec() && ptr.sort().bitvec_width() == Some(POINTER_WIDTH),
            "read_bytes ptr requires BitVec(64), got {:?}",
            ptr.sort()
        );

        // Read bytes in little-endian order: byte[0] is LSB
        let mut bytes = Vec::with_capacity(n);
        for i in 0..n {
            let offset = Expr::bitvec_const(i as i64, POINTER_WIDTH);
            let addr = ptr.clone().bvadd(offset);
            bytes.push(self.read_byte(addr));
        }

        // Concatenate: most significant byte first in concat
        // For little-endian: bytes[n-1] || bytes[n-2] || ... || bytes[0]
        let mut result = bytes
            .pop()
            .expect("bytes vec should have at least one element since n > 0");
        while let Some(byte) = bytes.pop() {
            result = result.concat(byte);
        }
        result
    }

    /// Write a single byte to memory at the given pointer.
    ///
    /// Returns a new MemoryModel with the updated memory state.
    ///
    /// REQUIRES: ptr.sort().is_bitvec() && ptr.sort().bitvec_width() == Some(64)
    /// REQUIRES: value.sort().is_bitvec() && value.sort().bitvec_width() == Some(8)
    /// ENSURES: result.mem == self.mem.store(ptr, value)
    /// ENSURES: result.object_valid == self.object_valid
    /// ENSURES: result.object_size == self.object_size
    ///
    /// # Panics
    /// Panics if `ptr` is not BitVec(64) or `value` is not BitVec(8).
    #[must_use]
    pub fn write_byte(self, ptr: Expr, value: Expr) -> Self {
        assert!(
            ptr.sort().is_bitvec() && ptr.sort().bitvec_width() == Some(POINTER_WIDTH),
            "write_byte ptr requires BitVec(64), got {:?}",
            ptr.sort()
        );
        assert!(
            value.sort().is_bitvec() && value.sort().bitvec_width() == Some(8),
            "write_byte value requires BitVec(8), got {:?}",
            value.sort()
        );

        Self {
            mem: self.mem.store(ptr, value),
            ..self
        }
    }

    /// Write multiple bytes to memory starting at the given pointer.
    ///
    /// Bytes are written in little-endian order: `bytes[0]` goes to `ptr`,
    /// `bytes[1]` goes to `ptr + 1`, etc.
    ///
    /// Returns a new MemoryModel with the updated memory state.
    ///
    /// REQUIRES: ptr.sort().is_bitvec() && ptr.sort().bitvec_width() == Some(64)
    /// REQUIRES: forall i in 0..bytes.len(): `bytes[i].sort().bitvec_width() == Some(8)`
    /// ENSURES: result.object_valid == self.object_valid
    /// ENSURES: result.object_size == self.object_size
    ///
    /// # Panics
    /// Panics if `ptr` is not BitVec(64) or any byte is not BitVec(8).
    #[must_use]
    pub fn write_bytes(self, ptr: &Expr, bytes: Vec<Expr>) -> Self {
        assert!(
            ptr.sort().is_bitvec() && ptr.sort().bitvec_width() == Some(POINTER_WIDTH),
            "write_bytes ptr requires BitVec(64), got {:?}",
            ptr.sort()
        );

        let mut model = self;
        for (i, byte) in bytes.into_iter().enumerate() {
            assert!(
                byte.sort().is_bitvec() && byte.sort().bitvec_width() == Some(8),
                "write_bytes byte[{}] requires BitVec(8), got {:?}",
                i,
                byte.sort()
            );
            let offset = Expr::bitvec_const(i as i64, POINTER_WIDTH);
            let addr = ptr.clone().bvadd(offset);
            model = model.write_byte(addr, byte);
        }
        model
    }

    /// Write a value of the given bit-width to memory in little-endian order.
    ///
    /// Extracts bytes from the value and writes them to consecutive addresses.
    ///
    /// # Arguments
    /// * `ptr` - Pointer to write to (BitVec64)
    /// * `value` - Value to write (must have width divisible by 8)
    ///
    /// REQUIRES: ptr.sort().is_bitvec() && ptr.sort().bitvec_width() == Some(64)
    /// REQUIRES: value.sort().is_bitvec()
    /// REQUIRES: value.sort().bitvec_width().unwrap() % 8 == 0
    /// ENSURES: result.object_valid == self.object_valid
    /// ENSURES: result.object_size == self.object_size
    ///
    /// # Panics
    /// Panics if `ptr` is not BitVec(64) or value width is not divisible by 8.
    #[must_use]
    pub fn write_value(self, ptr: &Expr, value: &Expr) -> Self {
        assert!(
            ptr.sort().is_bitvec() && ptr.sort().bitvec_width() == Some(POINTER_WIDTH),
            "write_value ptr requires BitVec(64), got {:?}",
            ptr.sort()
        );
        let width = value
            .sort()
            .bitvec_width()
            .expect("write_value value requires BitVec sort");
        assert!(
            width.is_multiple_of(8),
            "write_value width must be divisible by 8"
        );

        let n_bytes = (width / 8) as usize;
        let mut bytes = Vec::with_capacity(n_bytes);

        // Extract bytes in little-endian order
        for i in 0..n_bytes {
            let low = (i * 8) as u32;
            let high = low + 7;
            bytes.push(value.clone().extract(high, low));
        }

        self.write_bytes(ptr, bytes)
    }

    // ===== Allocation =====

    /// Allocate a new object of the given size.
    ///
    /// Returns a tuple of:
    /// - Pointer to the new object (with offset = 0)
    /// - Updated MemoryModel with the allocation recorded
    ///
    /// # Arguments
    /// * `size` - Size of the object in bytes (BitVec32)
    ///
    /// REQUIRES: size.sort().is_bitvec() && size.sort().bitvec_width() == Some(32)
    /// REQUIRES: self.next_object_id < u32::MAX (no overflow)
    /// ENSURES: result.0.sort().bitvec_width() == Some(64) (pointer)
    /// ENSURES: pointer_offset(result.0) == 0
    /// ENSURES: `result.1.object_valid[new_object_id] == true`
    /// ENSURES: `result.1.object_size[new_object_id] == size`
    /// ENSURES: result.1.next_object_id == self.next_object_id + 1
    ///
    /// # Panics
    /// - Panics if `size` is not BitVec(32).
    /// - Panics if object ID counter overflows (>4 billion allocations).
    ///   Object ID 0 is reserved for null, so overflow would create aliasing.
    #[must_use]
    pub fn allocate(mut self, size: Expr) -> (Expr, Self) {
        assert!(
            size.sort().is_bitvec() && size.sort().bitvec_width() == Some(OBJECT_ID_WIDTH),
            "allocate size requires BitVec(32), got {:?}",
            size.sort()
        );

        let object_id = Expr::bitvec_const(self.next_object_id, OBJECT_ID_WIDTH);
        self.next_object_id = self
            .next_object_id
            .checked_add(1)
            .expect("Object ID overflow: too many allocations (>4 billion)");

        // Update object_valid[object_id] = true
        let new_valid = self.object_valid.store(object_id.clone(), Expr::true_());

        // Update object_size[object_id] = size
        let new_size = self.object_size.store(object_id.clone(), size);

        let ptr = Self::mk_pointer(object_id, Expr::bitvec_const(0u32, OFFSET_WIDTH));

        (
            ptr,
            Self {
                object_valid: new_valid,
                object_size: new_size,
                ..self
            },
        )
    }

    /// Check if a pointer can be validly deallocated.
    ///
    /// Returns a boolean expression that is true if the object is currently
    /// allocated and not yet freed. This should be asserted before calling
    /// `deallocate` to detect double-free errors.
    ///
    /// # Arguments
    /// * `ptr` - Pointer to the object (BitVec64)
    ///
    /// # Returns
    /// Boolean expression: `object_valid[object_id] == true`
    ///
    /// REQUIRES: ptr.sort().is_bitvec() && ptr.sort().bitvec_width() == Some(64)
    /// ENSURES: result.sort().is_bool()
    /// ENSURES: result == self.object_valid[pointer_object(ptr)]
    ///
    /// # Panics
    /// Panics if `ptr` is not BitVec(64).
    #[must_use]
    pub fn dealloc_ok(&self, ptr: Expr) -> Expr {
        assert!(
            ptr.sort().is_bitvec() && ptr.sort().bitvec_width() == Some(POINTER_WIDTH),
            "dealloc_ok ptr requires BitVec(64), got {:?}",
            ptr.sort()
        );

        let object_id = Self::pointer_object(ptr);
        // Object must be currently valid (allocated and not yet freed)
        self.object_valid.clone().select(object_id)
    }

    /// Deallocate an object.
    ///
    /// Marks the object as invalid. Future accesses to this object will fail
    /// the `read_ok`/`write_ok` check.
    ///
    /// Returns a new MemoryModel with the deallocation recorded.
    ///
    /// # Double-Free Detection
    ///
    /// This operation is idempotent: deallocating an already-freed object
    /// simply sets `object_valid[id] = false` again. To detect double-free
    /// errors, callers should assert `dealloc_ok(ptr)` before calling this
    /// method:
    ///
    /// ```rust,no_run
    /// use ay_bindings::{Expr, MemoryModel};
    ///
    /// # let mem: MemoryModel = unimplemented!();
    /// # let ptr: Expr = unimplemented!();
    /// let valid = mem.dealloc_ok(ptr.clone());
    /// // Assert `valid` in verification constraints.
    /// let mem2 = mem.deallocate(ptr);
    /// # drop((valid, mem2));
    /// ```
    ///
    /// See #1034 for design rationale.
    ///
    /// # Arguments
    /// * `ptr` - Pointer to the object to deallocate (BitVec64)
    ///
    /// REQUIRES: ptr.sort().is_bitvec() && ptr.sort().bitvec_width() == Some(64)
    /// ENSURES: result.object_valid[pointer_object(ptr)] == false
    /// ENSURES: result.object_size == self.object_size
    /// ENSURES: result.mem == self.mem
    ///
    /// # Panics
    /// Panics if `ptr` is not BitVec(64).
    #[must_use]
    pub fn deallocate(self, ptr: Expr) -> Self {
        let object_id = Self::pointer_object(ptr);

        // Update object_valid[object_id] = false
        let new_valid = self.object_valid.store(object_id, Expr::false_());

        Self {
            object_valid: new_valid,
            ..self
        }
    }

    // ===== Vulnerability Detection Assertions =====

    /// Assert that a pointer access is to a currently valid object.
    ///
    /// Returns a boolean expression that is true iff the pointer's object is
    /// currently allocated and not yet freed. If the solver can falsify this
    /// assertion, the access is a use-after-free.
    ///
    /// # Arguments
    /// * `ptr` - Pointer to the object being accessed (BitVec64)
    ///
    /// # Returns
    /// Boolean expression: `object_valid[pointer_object(ptr)] == true`
    ///
    /// REQUIRES: ptr.sort().is_bitvec() && ptr.sort().bitvec_width() == Some(64)
    /// ENSURES: result.sort().is_bool()
    /// ENSURES: result == self.object_valid[pointer_object(ptr)]
    ///
    /// # Panics
    /// Panics if `ptr` is not BitVec(64).
    #[must_use]
    pub fn assert_valid_access(&self, ptr: Expr) -> Expr {
        assert!(
            ptr.sort().is_bitvec() && ptr.sort().bitvec_width() == Some(POINTER_WIDTH),
            "assert_valid_access ptr requires BitVec(64), got {:?}",
            ptr.sort()
        );

        let object_id = Self::pointer_object(ptr);
        self.object_valid.clone().select(object_id)
    }

    /// Assert that freeing a pointer is currently valid.
    ///
    /// Returns a boolean expression that is true iff the pointer's object is
    /// currently allocated and not yet freed. If the solver can falsify this
    /// assertion, the free is a double-free.
    ///
    /// # Arguments
    /// * `ptr` - Pointer to the object being freed (BitVec64)
    ///
    /// # Returns
    /// Boolean expression: `object_valid[pointer_object(ptr)] == true`
    ///
    /// REQUIRES: ptr.sort().is_bitvec() && ptr.sort().bitvec_width() == Some(64)
    /// ENSURES: result.sort().is_bool()
    /// ENSURES: result == self.object_valid[pointer_object(ptr)]
    ///
    /// # Panics
    /// Panics if `ptr` is not BitVec(64).
    #[must_use]
    pub fn assert_valid_free(&self, ptr: Expr) -> Expr {
        assert!(
            ptr.sort().is_bitvec() && ptr.sort().bitvec_width() == Some(POINTER_WIDTH),
            "assert_valid_free ptr requires BitVec(64), got {:?}",
            ptr.sort()
        );

        let object_id = Self::pointer_object(ptr);
        self.object_valid.clone().select(object_id)
    }

    /// Assert that an access range is within the bounds of its object.
    ///
    /// Returns a boolean expression that is true iff the half-open range
    /// `[ptr, ptr + size)` lies within the allocated object. The overflow
    /// check `end >= offset` ensures that `offset + size` did not wrap around.
    ///
    /// # Arguments
    /// * `ptr` - Base pointer for the access (BitVec64)
    /// * `size` - Size of the access in bytes (BitVec32)
    ///
    /// # Returns
    /// Boolean expression: `end <= object_size[pointer_object(ptr)] && end >= pointer_offset(ptr)`
    ///
    /// REQUIRES: ptr.sort().is_bitvec() && ptr.sort().bitvec_width() == Some(64)
    /// REQUIRES: size.sort().is_bitvec() && size.sort().bitvec_width() == Some(32)
    /// ENSURES: result.sort().is_bool()
    /// ENSURES: result == (((pointer_offset(ptr) + size) <=u self.object_size[pointer_object(ptr)])
    ///                     && ((pointer_offset(ptr) + size) >=u pointer_offset(ptr)))
    ///
    /// # Panics
    /// Panics if `ptr` is not BitVec(64) or `size` is not BitVec(32).
    #[must_use]
    pub fn assert_in_bounds(&self, ptr: Expr, size: Expr) -> Expr {
        assert!(
            ptr.sort().is_bitvec() && ptr.sort().bitvec_width() == Some(POINTER_WIDTH),
            "assert_in_bounds ptr requires BitVec(64), got {:?}",
            ptr.sort()
        );
        assert!(
            size.sort().is_bitvec() && size.sort().bitvec_width() == Some(OFFSET_WIDTH),
            "assert_in_bounds size requires BitVec(32), got {:?}",
            size.sort()
        );

        let offset = Self::pointer_offset(ptr.clone());
        let obj_size = self.object_size.clone().select(Self::pointer_object(ptr));
        let end = offset.clone().bvadd(size);
        end.clone().bvule(obj_size).and(end.bvuge(offset))
    }

    /// Assert that a pointer is non-null.
    ///
    /// Returns a boolean expression that is true iff the pointer is not the
    /// null pointer (object_id != 0).
    ///
    /// # Arguments
    /// * `ptr` - Pointer to check (BitVec64)
    ///
    /// # Returns
    /// Boolean expression: `!is_null(ptr)`
    ///
    /// REQUIRES: ptr.sort().is_bitvec() && ptr.sort().bitvec_width() == Some(64)
    /// ENSURES: result.sort().is_bool()
    /// ENSURES: result == !is_null(ptr)
    ///
    /// # Panics
    /// Panics if `ptr` is not BitVec(64).
    #[must_use]
    pub fn assert_non_null(ptr: Expr) -> Expr {
        assert!(
            ptr.sort().is_bitvec() && ptr.sort().bitvec_width() == Some(POINTER_WIDTH),
            "assert_non_null ptr requires BitVec(64), got {:?}",
            ptr.sort()
        );

        Self::is_null(ptr).not()
    }

    // ===== Bulk Memory Operations (issue #8294) =====

    /// Try to extract a concrete u64 value from a length expression.
    ///
    /// Returns `Some(n)` if the expression is a concrete bitvector constant
    /// that fits in a u64, `None` otherwise (symbolic or too large).
    fn try_concrete_len(len: &Expr) -> Option<u64> {
        match len.value() {
            ExprValue::BitVecConst { value, .. } => value.to_u64(),
            _ => None,
        }
    }

    /// Copy `len` bytes from `src` to `dst` (non-overlapping).
    ///
    /// Models the C `memcpy` operation. For concrete small lengths (<=16 bytes),
    /// unrolls into individual byte reads and writes. For larger concrete lengths,
    /// uses 8-byte (BV64) word-level reads/writes with byte-level remainder
    /// handling to reduce the number of SMT array operations.
    ///
    /// # Arguments
    /// * `dst` - Destination pointer (BitVec64)
    /// * `src` - Source pointer (BitVec64)
    /// * `len` - Number of bytes to copy (BitVec32)
    ///
    /// # Returns
    /// New `MemoryModel` with the copy applied to memory.
    ///
    /// # Panics
    /// Panics if `dst`/`src` are not BitVec(64) or `len` is not BitVec(32).
    /// Panics if `len` is symbolic (only concrete lengths are supported).
    #[must_use]
    pub fn memcpy(self, dst: &Expr, src: &Expr, len: &Expr) -> Self {
        assert!(
            dst.sort().is_bitvec() && dst.sort().bitvec_width() == Some(POINTER_WIDTH),
            "memcpy dst requires BitVec(64), got {:?}",
            dst.sort()
        );
        assert!(
            src.sort().is_bitvec() && src.sort().bitvec_width() == Some(POINTER_WIDTH),
            "memcpy src requires BitVec(64), got {:?}",
            src.sort()
        );
        assert!(
            len.sort().is_bitvec() && len.sort().bitvec_width() == Some(OFFSET_WIDTH),
            "memcpy len requires BitVec(32), got {:?}",
            len.sort()
        );

        let n = Self::try_concrete_len(len)
            .expect("memcpy requires concrete length; symbolic lengths not yet supported");

        if n == 0 {
            return self;
        }

        // For small lengths (<=16), unroll byte-by-byte
        if n <= 16 {
            return self.memcpy_unrolled(dst, src, n as usize);
        }

        // For larger lengths, use word-level (8-byte) operations
        self.memcpy_word_level(dst, src, n as usize)
    }

    /// Byte-by-byte memcpy for small concrete lengths.
    fn memcpy_unrolled(self, dst: &Expr, src: &Expr, n: usize) -> Self {
        let mut model = self;
        for i in 0..n {
            let offset = Expr::bitvec_const(i as i64, POINTER_WIDTH);
            let src_addr = src.clone().bvadd(offset.clone());
            let dst_addr = dst.clone().bvadd(offset);
            let byte = model.read_byte(src_addr);
            model = model.write_byte(dst_addr, byte);
        }
        model
    }

    /// Word-level memcpy: 8-byte chunks + byte remainder.
    fn memcpy_word_level(self, dst: &Expr, src: &Expr, n: usize) -> Self {
        let n_words = n / 8;
        let remainder = n % 8;
        let mut model = self;

        // Copy 8-byte words
        for w in 0..n_words {
            let byte_offset = w * 8;
            let offset = Expr::bitvec_const(byte_offset as i64, POINTER_WIDTH);
            let src_addr = src.clone().bvadd(offset.clone());
            let dst_addr = dst.clone().bvadd(offset);
            // Read 8 bytes (returns BV64)
            let word = model.read_bytes(&src_addr, 8);
            // Write 8 bytes back
            model = model.write_value(&dst_addr, &word);
        }

        // Copy remaining bytes individually
        let base_offset = n_words * 8;
        for i in 0..remainder {
            let offset = Expr::bitvec_const((base_offset + i) as i64, POINTER_WIDTH);
            let src_addr = src.clone().bvadd(offset.clone());
            let dst_addr = dst.clone().bvadd(offset);
            let byte = model.read_byte(src_addr);
            model = model.write_byte(dst_addr, byte);
        }

        model
    }

    /// Copy `len` bytes from `src` to `dst`, safe for overlapping regions.
    ///
    /// Models the C `memmove` operation. Reads ALL source bytes first into
    /// a temporary buffer, then writes them to the destination. This ensures
    /// correct behavior even when source and destination regions overlap.
    ///
    /// For concrete small lengths (<=16 bytes), reads all bytes into a Vec
    /// of expressions, then writes them. For larger lengths, uses word-level
    /// reads into a temporary buffer followed by word-level writes.
    ///
    /// # Arguments
    /// * `dst` - Destination pointer (BitVec64)
    /// * `src` - Source pointer (BitVec64)
    /// * `len` - Number of bytes to copy (BitVec32)
    ///
    /// # Returns
    /// New `MemoryModel` with the copy applied to memory.
    ///
    /// # Panics
    /// Panics if `dst`/`src` are not BitVec(64) or `len` is not BitVec(32).
    /// Panics if `len` is symbolic (only concrete lengths are supported).
    #[must_use]
    pub fn memmove(self, dst: &Expr, src: &Expr, len: &Expr) -> Self {
        assert!(
            dst.sort().is_bitvec() && dst.sort().bitvec_width() == Some(POINTER_WIDTH),
            "memmove dst requires BitVec(64), got {:?}",
            dst.sort()
        );
        assert!(
            src.sort().is_bitvec() && src.sort().bitvec_width() == Some(POINTER_WIDTH),
            "memmove src requires BitVec(64), got {:?}",
            src.sort()
        );
        assert!(
            len.sort().is_bitvec() && len.sort().bitvec_width() == Some(OFFSET_WIDTH),
            "memmove len requires BitVec(32), got {:?}",
            len.sort()
        );

        let n = Self::try_concrete_len(len)
            .expect("memmove requires concrete length; symbolic lengths not yet supported");

        if n == 0 {
            return self;
        }

        // Phase 1: Read all source bytes into a temporary buffer (Vec<Expr>).
        // This captures the source state before any writes, making it safe
        // for overlapping regions.
        let mut temp_bytes = Vec::with_capacity(n as usize);
        for i in 0..n {
            let offset = Expr::bitvec_const(i as i64, POINTER_WIDTH);
            let src_addr = src.clone().bvadd(offset);
            temp_bytes.push(self.read_byte(src_addr));
        }

        // Phase 2: Write all buffered bytes to the destination.
        let mut model = self;
        for (i, byte) in temp_bytes.into_iter().enumerate() {
            let offset = Expr::bitvec_const(i as i64, POINTER_WIDTH);
            let dst_addr = dst.clone().bvadd(offset);
            model = model.write_byte(dst_addr, byte);
        }

        model
    }

    /// Fill `len` bytes at `dst` with the value `val`.
    ///
    /// Models the C `memset` operation. For concrete small lengths (<=16 bytes),
    /// unrolls into individual byte writes. For larger lengths, creates an 8-byte
    /// word by replicating `val` 8 times (via concat) and writes word-at-a-time
    /// to reduce SMT array operations.
    ///
    /// # Arguments
    /// * `dst` - Destination pointer (BitVec64)
    /// * `val` - Byte value to fill with (BitVec8)
    /// * `len` - Number of bytes to fill (BitVec32)
    ///
    /// # Returns
    /// New `MemoryModel` with the fill applied to memory.
    ///
    /// # Panics
    /// Panics if `dst` is not BitVec(64), `val` is not BitVec(8), or
    /// `len` is not BitVec(32). Panics if `len` is symbolic.
    #[must_use]
    pub fn memset(self, dst: &Expr, val: &Expr, len: &Expr) -> Self {
        assert!(
            dst.sort().is_bitvec() && dst.sort().bitvec_width() == Some(POINTER_WIDTH),
            "memset dst requires BitVec(64), got {:?}",
            dst.sort()
        );
        assert!(
            val.sort().is_bitvec() && val.sort().bitvec_width() == Some(8),
            "memset val requires BitVec(8), got {:?}",
            val.sort()
        );
        assert!(
            len.sort().is_bitvec() && len.sort().bitvec_width() == Some(OFFSET_WIDTH),
            "memset len requires BitVec(32), got {:?}",
            len.sort()
        );

        let n = Self::try_concrete_len(len)
            .expect("memset requires concrete length; symbolic lengths not yet supported");

        if n == 0 {
            return self;
        }

        // For small lengths (<=16), unroll byte-by-byte
        if n <= 16 {
            let mut model = self;
            for i in 0..n {
                let offset = Expr::bitvec_const(i as i64, POINTER_WIDTH);
                let addr = dst.clone().bvadd(offset);
                model = model.write_byte(addr, val.clone());
            }
            return model;
        }

        // For larger lengths, build 8-byte word from repeated val
        // word = val ++ val ++ val ++ val ++ val ++ val ++ val ++ val (BV64)
        let word = Self::replicate_byte_to_word(val);

        let n_words = n as usize / 8;
        let remainder = n as usize % 8;
        let mut model = self;

        // Write 8-byte words
        for w in 0..n_words {
            let offset = Expr::bitvec_const((w * 8) as i64, POINTER_WIDTH);
            let addr = dst.clone().bvadd(offset);
            model = model.write_value(&addr, &word);
        }

        // Write remaining bytes individually
        let base_offset = n_words * 8;
        for i in 0..remainder {
            let offset = Expr::bitvec_const((base_offset + i) as i64, POINTER_WIDTH);
            let addr = dst.clone().bvadd(offset);
            model = model.write_byte(addr, val.clone());
        }

        model
    }

    /// Replicate a BV8 byte value 8 times to create a BV64 word.
    ///
    /// `val ++ val ++ val ++ val ++ val ++ val ++ val ++ val`
    fn replicate_byte_to_word(val: &Expr) -> Expr {
        // Build BV64 by concatenating 8 copies of the byte.
        // concat(a, b) puts `a` in high bits and `b` in low bits.
        // For little-endian memory, all bytes are the same so order doesn't matter.
        let mut result = val.clone();
        for _ in 1..8 {
            result = result.concat(val.clone());
        }
        result
    }

    // ===== Dangling Pointer Detection (issue #8303) =====

    /// Assert that a pointer is non-null and points to a currently valid object.
    ///
    /// Returns a boolean expression that is true iff the pointer's object is
    /// currently allocated and not yet freed, and the pointer is not null.
    /// Combines use-after-free and null-deref detection in a single check.
    ///
    /// # Arguments
    /// * `ptr` - Pointer to check (BitVec64)
    ///
    /// # Returns
    /// Boolean expression: `object_valid[pointer_object(ptr)] && pointer_object(ptr) != 0`
    ///
    /// REQUIRES: ptr.sort().is_bitvec() && ptr.sort().bitvec_width() == Some(64)
    /// ENSURES: result.sort().is_bool()
    /// ENSURES: result == (self.object_valid[pointer_object(ptr)] && pointer_object(ptr) != 0)
    ///
    /// # Panics
    /// Panics if `ptr` is not BitVec(64).
    #[must_use]
    pub fn assert_no_dangling(&self, ptr: Expr) -> Expr {
        assert!(
            ptr.sort().is_bitvec() && ptr.sort().bitvec_width() == Some(POINTER_WIDTH),
            "assert_no_dangling ptr requires BitVec(64), got {:?}",
            ptr.sort()
        );

        let object_id = Self::pointer_object(ptr);
        let valid = self.object_valid.clone().select(object_id.clone());
        let non_null = object_id
            .eq(Expr::bitvec_const(0u32, OBJECT_ID_WIDTH))
            .not();

        valid.and(non_null)
    }

    /// Assert that a pointer's provenance is restricted to a set of object IDs.
    ///
    /// Returns a boolean expression that is true iff `pointer_object(ptr)` equals
    /// one of the provided `allowed_objects`. Useful for tracking which allocation
    /// a pointer derives from in binary analysis.
    ///
    /// # Arguments
    /// * `ptr` - Pointer to check (BitVec64)
    /// * `allowed_objects` - Allowed object IDs (each BitVec32)
    ///
    /// # Returns
    /// Boolean expression: `pointer_object(ptr) == allowed[0] || ... ||
    ///                     pointer_object(ptr) == allowed[n - 1]`
    /// Returns `false` if `allowed_objects` is empty.
    ///
    /// REQUIRES: ptr.sort().is_bitvec() && ptr.sort().bitvec_width() == Some(64)
    /// REQUIRES: forall i: allowed_objects\[i\].sort().bitvec_width() == Some(32)
    /// ENSURES: result.sort().is_bool()
    ///
    /// # Panics
    /// Panics if `ptr` is not BitVec(64) or any allowed object is not BitVec(32).
    #[must_use]
    pub fn assert_pointer_provenance(&self, ptr: Expr, allowed_objects: &[Expr]) -> Expr {
        assert!(
            ptr.sort().is_bitvec() && ptr.sort().bitvec_width() == Some(POINTER_WIDTH),
            "assert_pointer_provenance ptr requires BitVec(64), got {:?}",
            ptr.sort()
        );

        if allowed_objects.is_empty() {
            return Expr::false_();
        }

        let object_id = Self::pointer_object(ptr);
        let mut disjuncts = Vec::with_capacity(allowed_objects.len());

        for (i, allowed) in allowed_objects.iter().enumerate() {
            assert!(
                allowed.sort().is_bitvec()
                    && allowed.sort().bitvec_width() == Some(OBJECT_ID_WIDTH),
                "assert_pointer_provenance allowed_objects[{}] requires BitVec(32), got {:?}",
                i,
                allowed.sort()
            );
            disjuncts.push(object_id.clone().eq(allowed.clone()));
        }

        Expr::or_many(disjuncts)
    }

    // ===== Typed Memory Access (issue #8303) =====

    /// Read a 16-bit value from memory in little-endian order.
    ///
    /// Returns a BitVec(16) expression formed from the two bytes starting at
    /// `ptr`, with the byte at `ptr` as the least significant byte.
    ///
    /// # Arguments
    /// * `ptr` - Pointer to read from (BitVec64)
    ///
    /// REQUIRES: ptr.sort().is_bitvec() && ptr.sort().bitvec_width() == Some(64)
    /// ENSURES: result.sort().is_bitvec() && result.sort().bitvec_width() == Some(16)
    ///
    /// # Panics
    /// Panics if `ptr` is not BitVec(64).
    #[must_use]
    pub fn read_u16(&self, ptr: Expr) -> Expr {
        assert!(
            ptr.sort().is_bitvec() && ptr.sort().bitvec_width() == Some(POINTER_WIDTH),
            "read_u16 ptr requires BitVec(64), got {:?}",
            ptr.sort()
        );
        self.read_bytes(&ptr, 2)
    }

    /// Read a 32-bit value from memory in little-endian order.
    ///
    /// Returns a BitVec(32) expression formed from the four bytes starting at
    /// `ptr`, with the byte at `ptr` as the least significant byte.
    ///
    /// # Arguments
    /// * `ptr` - Pointer to read from (BitVec64)
    ///
    /// REQUIRES: ptr.sort().is_bitvec() && ptr.sort().bitvec_width() == Some(64)
    /// ENSURES: result.sort().is_bitvec() && result.sort().bitvec_width() == Some(32)
    ///
    /// # Panics
    /// Panics if `ptr` is not BitVec(64).
    #[must_use]
    pub fn read_u32(&self, ptr: Expr) -> Expr {
        assert!(
            ptr.sort().is_bitvec() && ptr.sort().bitvec_width() == Some(POINTER_WIDTH),
            "read_u32 ptr requires BitVec(64), got {:?}",
            ptr.sort()
        );
        self.read_bytes(&ptr, 4)
    }

    /// Read a 64-bit value from memory in little-endian order.
    ///
    /// Returns a BitVec(64) expression formed from the eight bytes starting at
    /// `ptr`, with the byte at `ptr` as the least significant byte.
    ///
    /// # Arguments
    /// * `ptr` - Pointer to read from (BitVec64)
    ///
    /// REQUIRES: ptr.sort().is_bitvec() && ptr.sort().bitvec_width() == Some(64)
    /// ENSURES: result.sort().is_bitvec() && result.sort().bitvec_width() == Some(64)
    ///
    /// # Panics
    /// Panics if `ptr` is not BitVec(64).
    #[must_use]
    pub fn read_u64(&self, ptr: Expr) -> Expr {
        assert!(
            ptr.sort().is_bitvec() && ptr.sort().bitvec_width() == Some(POINTER_WIDTH),
            "read_u64 ptr requires BitVec(64), got {:?}",
            ptr.sort()
        );
        self.read_bytes(&ptr, 8)
    }

    /// Write a 16-bit value to memory in little-endian order.
    ///
    /// Writes the low byte of `val` to `ptr` and the high byte to `ptr + 1`.
    ///
    /// # Arguments
    /// * `ptr` - Pointer to write to (BitVec64)
    /// * `val` - Value to write (BitVec16)
    ///
    /// REQUIRES: ptr.sort().is_bitvec() && ptr.sort().bitvec_width() == Some(64)
    /// REQUIRES: val.sort().is_bitvec() && val.sort().bitvec_width() == Some(16)
    /// ENSURES: result.object_valid == self.object_valid
    /// ENSURES: result.object_size == self.object_size
    ///
    /// # Panics
    /// Panics if `ptr` is not BitVec(64) or `val` is not BitVec(16).
    #[must_use]
    pub fn write_u16(self, ptr: Expr, val: Expr) -> Self {
        assert!(
            ptr.sort().is_bitvec() && ptr.sort().bitvec_width() == Some(POINTER_WIDTH),
            "write_u16 ptr requires BitVec(64), got {:?}",
            ptr.sort()
        );
        assert!(
            val.sort().is_bitvec() && val.sort().bitvec_width() == Some(16),
            "write_u16 val requires BitVec(16), got {:?}",
            val.sort()
        );
        self.write_value(&ptr, &val)
    }

    /// Write a 32-bit value to memory in little-endian order.
    ///
    /// Writes four bytes from `val` starting at `ptr` in little-endian order.
    ///
    /// # Arguments
    /// * `ptr` - Pointer to write to (BitVec64)
    /// * `val` - Value to write (BitVec32)
    ///
    /// REQUIRES: ptr.sort().is_bitvec() && ptr.sort().bitvec_width() == Some(64)
    /// REQUIRES: val.sort().is_bitvec() && val.sort().bitvec_width() == Some(32)
    /// ENSURES: result.object_valid == self.object_valid
    /// ENSURES: result.object_size == self.object_size
    ///
    /// # Panics
    /// Panics if `ptr` is not BitVec(64) or `val` is not BitVec(32).
    #[must_use]
    pub fn write_u32(self, ptr: Expr, val: Expr) -> Self {
        assert!(
            ptr.sort().is_bitvec() && ptr.sort().bitvec_width() == Some(POINTER_WIDTH),
            "write_u32 ptr requires BitVec(64), got {:?}",
            ptr.sort()
        );
        assert!(
            val.sort().is_bitvec() && val.sort().bitvec_width() == Some(32),
            "write_u32 val requires BitVec(32), got {:?}",
            val.sort()
        );
        self.write_value(&ptr, &val)
    }

    /// Write a 64-bit value to memory in little-endian order.
    ///
    /// Writes eight bytes from `val` starting at `ptr` in little-endian order.
    ///
    /// # Arguments
    /// * `ptr` - Pointer to write to (BitVec64)
    /// * `val` - Value to write (BitVec64)
    ///
    /// REQUIRES: ptr.sort().is_bitvec() && ptr.sort().bitvec_width() == Some(64)
    /// REQUIRES: val.sort().is_bitvec() && val.sort().bitvec_width() == Some(64)
    /// ENSURES: result.object_valid == self.object_valid
    /// ENSURES: result.object_size == self.object_size
    ///
    /// # Panics
    /// Panics if `ptr` is not BitVec(64) or `val` is not BitVec(64).
    #[must_use]
    pub fn write_u64(self, ptr: Expr, val: Expr) -> Self {
        assert!(
            ptr.sort().is_bitvec() && ptr.sort().bitvec_width() == Some(POINTER_WIDTH),
            "write_u64 ptr requires BitVec(64), got {:?}",
            ptr.sort()
        );
        assert!(
            val.sort().is_bitvec() && val.sort().bitvec_width() == Some(64),
            "write_u64 val requires BitVec(64), got {:?}",
            val.sort()
        );
        self.write_value(&ptr, &val)
    }

    // ===== Memory Region Comparison (issue #8303) =====

    /// Assert that two memory regions are disjoint (non-overlapping).
    ///
    /// Returns a boolean expression that is true iff the two half-open regions
    /// `[ptr1, ptr1 + size1)` and `[ptr2, ptr2 + size2)` do not overlap.
    /// Regions in different objects are always disjoint; regions in the same
    /// object are disjoint iff one ends before the other begins.
    ///
    /// # Arguments
    /// * `ptr1` - Base pointer of the first region (BitVec64)
    /// * `size1` - Size of the first region in bytes (BitVec32)
    /// * `ptr2` - Base pointer of the second region (BitVec64)
    /// * `size2` - Size of the second region in bytes (BitVec32)
    ///
    /// # Returns
    /// Boolean expression: `pointer_object(ptr1) != pointer_object(ptr2) ||
    ///   (offset1 + size1 <=u offset2 || offset2 + size2 <=u offset1)`
    ///
    /// REQUIRES: ptr1/ptr2 are BitVec(64), size1/size2 are BitVec(32)
    /// ENSURES: result.sort().is_bool()
    ///
    /// # Panics
    /// Panics if any argument has the wrong sort.
    #[must_use]
    pub fn regions_disjoint(&self, ptr1: Expr, size1: Expr, ptr2: Expr, size2: Expr) -> Expr {
        assert!(
            ptr1.sort().is_bitvec() && ptr1.sort().bitvec_width() == Some(POINTER_WIDTH),
            "regions_disjoint ptr1 requires BitVec(64), got {:?}",
            ptr1.sort()
        );
        assert!(
            size1.sort().is_bitvec() && size1.sort().bitvec_width() == Some(OFFSET_WIDTH),
            "regions_disjoint size1 requires BitVec(32), got {:?}",
            size1.sort()
        );
        assert!(
            ptr2.sort().is_bitvec() && ptr2.sort().bitvec_width() == Some(POINTER_WIDTH),
            "regions_disjoint ptr2 requires BitVec(64), got {:?}",
            ptr2.sort()
        );
        assert!(
            size2.sort().is_bitvec() && size2.sort().bitvec_width() == Some(OFFSET_WIDTH),
            "regions_disjoint size2 requires BitVec(32), got {:?}",
            size2.sort()
        );

        let object1 = Self::pointer_object(ptr1.clone());
        let object2 = Self::pointer_object(ptr2.clone());
        let different_objects = object1.eq(object2).not();

        let offset1 = Self::pointer_offset(ptr1);
        let offset2 = Self::pointer_offset(ptr2);

        // Same object: regions are disjoint if one ends before the other starts
        let region1_before_region2 = offset1.clone().bvadd(size1).bvule(offset2.clone());
        let region2_before_region1 = offset2.bvadd(size2).bvule(offset1);
        let same_obj_disjoint = region1_before_region2.or(region2_before_region1);

        different_objects.or(same_obj_disjoint)
    }

    /// Compare `len` bytes starting at `a` and `b`.
    ///
    /// Models the C `memcmp` operation (equality-only variant). Returns a BV32
    /// expression that is 0 if all bytes are equal, and 1 (nonzero) otherwise.
    ///
    /// For concrete small lengths (<=16 bytes), unrolls into byte-by-byte
    /// comparisons combined with AND. Returns `ite(all_equal, 0, 1)`.
    ///
    /// # Arguments
    /// * `a` - First pointer (BitVec64)
    /// * `b` - Second pointer (BitVec64)
    /// * `len` - Number of bytes to compare (BitVec32)
    ///
    /// # Returns
    /// BitVec32 expression: 0 if equal, 1 if not.
    ///
    /// # Panics
    /// Panics if `a`/`b` are not BitVec(64) or `len` is not BitVec(32).
    /// Panics if `len` is symbolic.
    #[must_use]
    pub fn memcmp(&self, a: &Expr, b: &Expr, len: &Expr) -> Expr {
        assert!(
            a.sort().is_bitvec() && a.sort().bitvec_width() == Some(POINTER_WIDTH),
            "memcmp a requires BitVec(64), got {:?}",
            a.sort()
        );
        assert!(
            b.sort().is_bitvec() && b.sort().bitvec_width() == Some(POINTER_WIDTH),
            "memcmp b requires BitVec(64), got {:?}",
            b.sort()
        );
        assert!(
            len.sort().is_bitvec() && len.sort().bitvec_width() == Some(OFFSET_WIDTH),
            "memcmp len requires BitVec(32), got {:?}",
            len.sort()
        );

        let n = Self::try_concrete_len(len)
            .expect("memcmp requires concrete length; symbolic lengths not yet supported");

        let zero = Expr::bitvec_const(0i64, OFFSET_WIDTH);
        let one = Expr::bitvec_const(1i64, OFFSET_WIDTH);

        if n == 0 {
            // Zero-length comparison: always equal
            return zero;
        }

        // Build conjunction of per-byte equalities
        let mut equalities = Vec::with_capacity(n as usize);
        for i in 0..n {
            let offset = Expr::bitvec_const(i as i64, POINTER_WIDTH);
            let a_addr = a.clone().bvadd(offset.clone());
            let b_addr = b.clone().bvadd(offset);
            let a_byte = self.read_byte(a_addr);
            let b_byte = self.read_byte(b_addr);
            equalities.push(a_byte.eq(b_byte));
        }

        let all_equal = if equalities.len() == 1 {
            equalities
                .into_iter()
                .next()
                .expect("invariant: equalities.len() == 1")
        } else {
            Expr::and_many(equalities)
        };

        // ite(all_equal, 0, 1)
        Expr::ite(all_equal, zero, one)
    }
}
