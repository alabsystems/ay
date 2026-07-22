// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! JIT-compiled conflict analysis literal processing.
//!
//! Replaces the inner loop of 1UIP conflict analysis with a single native
//! function call. The inner loop processes each literal in a reason clause:
//! check if already seen, compare decision level with current level, increment
//! counter or add to learned clause buffer.
//!
//! ## Data Layout
//!
//! VarData is 16 bytes (`#[repr(C)]`):
//! - `level: u32`     (offset 0)
//! - `trail_pos: u32` (offset 4)
//! - `reason: u32`    (offset 8)
//! - `flags: u8`      (offset 12, bit 0 = seen)
//! - `_pad: [u8; 3]`  (offset 13)
//!
//! Literal encoding: `var_idx = lit >> 1`, `polarity = lit & 1`.
//!
//! ## Compiled Function ABI
//!
//! ```text
//! extern "C" fn(
//!     lits_ptr: *const u32,                 // x0: array of encoded literals
//!     lits_len: u32,                        // w1: number of literals
//!     var_data_ptr: *mut u8,                // x2: VarData array base (byte ptr)
//!     current_level: u32,                   // w3: current decision level
//!     skip_lit: u32,                        // w4: literal to skip (u32::MAX = none)
//!     out_ptr: *mut ConflictProcessorOutput // x5: output struct pointer
//!     vals_ptr: *const i8,                  // x6: vals[] for ghost literal guard (#8434)
//! )
//! ```

use crate::executable::ExecutableMemory;
use crate::JitError;

/// Dynamically-sized output buffer for JIT conflict literal processing.
///
/// Replaces the former fixed-size `[u32; 512]` arrays with dynamically-
/// allocated buffers sized to the number of variables. This eliminates
/// the stale-seen-flag bug (#8383) where overflow past the fixed buffer
/// caused seen flags to be set but not recorded in `seen_vars`, corrupting
/// subsequent conflict analyses.
///
/// ## Memory layout (contiguous, `#[repr(C)]`-compatible)
///
/// The raw buffer layout matches what the JIT native code writes to:
/// ```text
/// offset 0:                         counter (u32)
/// offset 4:                         learned_count (u32)
/// offset 8:                         resolvent_size (u32)
/// offset 12:                        learned_buf[0..capacity] (u32 * capacity)
/// offset 12 + capacity*4:           seen_count (u32)
/// offset 12 + capacity*4 + 4:       seen_vars[0..capacity] (u32 * capacity)
/// total: 16 + capacity * 8 bytes
/// ```
///
/// The JIT code generation receives `capacity` and computes offsets
/// accordingly. With capacity >= num_vars, overflow is impossible.
pub struct ConflictProcessorOutput {
    /// Raw contiguous buffer backing the output fields.
    buf: Vec<u32>,
    /// Number of u32 slots for each of learned_buf and seen_vars.
    capacity: usize,
}

// Field offsets within `buf` (in u32 units).
const COUNTER_IDX: usize = 0;
const LEARNED_COUNT_IDX: usize = 1;
const RESOLVENT_SIZE_IDX: usize = 2;
const LEARNED_BUF_START_IDX: usize = 3;

impl ConflictProcessorOutput {
    /// Create a zeroed output buffer with the given capacity.
    ///
    /// `capacity` should be >= num_vars to guarantee no overflow.
    /// Layout: 3 header u32s + capacity learned + 1 seen_count + capacity seen
    /// = 4 + 2*capacity u32s.
    pub fn new(capacity: usize) -> Self {
        let capacity = capacity.max(64); // minimum reasonable size
        let total_u32s = 3 + capacity + 1 + capacity; // header + learned + seen_count + seen
        Self {
            buf: vec![0u32; total_u32s],
            capacity,
        }
    }

    /// Resize the buffer to a new capacity (e.g., after adding variables).
    /// Resets all counters.
    pub fn resize(&mut self, new_capacity: usize) {
        let new_capacity = new_capacity.max(64);
        if new_capacity != self.capacity {
            let total_u32s = 3 + new_capacity + 1 + new_capacity;
            self.buf.resize(total_u32s, 0);
            self.buf.fill(0);
            self.capacity = new_capacity;
        } else {
            self.reset();
        }
    }

    /// Buffer capacity (number of slots in each of learned_buf / seen_vars).
    #[inline]
    pub fn capacity(&self) -> usize {
        self.capacity
    }

    /// Pointer to the raw buffer, for passing to JIT native code.
    #[inline]
    pub fn as_mut_ptr(&mut self) -> *mut u32 {
        self.buf.as_mut_ptr()
    }

    /// Reset counters for reuse (buffer content is overwritten by index).
    pub fn reset(&mut self) {
        self.buf[COUNTER_IDX] = 0;
        self.buf[LEARNED_COUNT_IDX] = 0;
        self.buf[RESOLVENT_SIZE_IDX] = 0;
        let sc_idx = LEARNED_BUF_START_IDX + self.capacity;
        self.buf[sc_idx] = 0;
    }

    // -- Accessors for the scalar fields --

    #[inline]
    pub fn counter(&self) -> u32 {
        self.buf[COUNTER_IDX]
    }

    #[inline]
    pub fn learned_count(&self) -> u32 {
        self.buf[LEARNED_COUNT_IDX]
    }

    #[inline]
    pub fn resolvent_size(&self) -> u32 {
        self.buf[RESOLVENT_SIZE_IDX]
    }

    #[inline]
    pub fn seen_count(&self) -> u32 {
        self.buf[LEARNED_BUF_START_IDX + self.capacity]
    }

    // -- Array accessors --

    #[inline]
    pub fn learned_lit(&self, i: usize) -> u32 {
        debug_assert!(i < self.capacity);
        self.buf[LEARNED_BUF_START_IDX + i]
    }

    #[inline]
    pub fn seen_var(&self, i: usize) -> u32 {
        debug_assert!(i < self.capacity);
        self.buf[LEARNED_BUF_START_IDX + self.capacity + 1 + i]
    }

    // -- Offset helpers (u32-index based) --

    #[inline]
    fn seen_count_idx(&self) -> usize {
        LEARNED_BUF_START_IDX + self.capacity // right after learned_buf
    }

    #[inline]
    fn seen_vars_start_idx(&self) -> usize {
        self.seen_count_idx() + 1
    }

    /// Byte offset of `seen_count` from buffer start (for JIT code gen).
    #[inline]
    pub fn seen_count_byte_offset(&self) -> u32 {
        (self.seen_count_idx() * 4) as u32
    }

    /// Byte offset of `seen_vars[0]` from buffer start (for JIT code gen).
    #[inline]
    pub fn seen_vars_byte_offset(&self) -> u32 {
        (self.seen_vars_start_idx() * 4) as u32
    }

    // -- Mutable accessors (for interpreter) --

    #[inline]
    pub fn counter_mut(&mut self) -> &mut u32 {
        &mut self.buf[COUNTER_IDX]
    }

    #[inline]
    pub fn learned_count_mut(&mut self) -> &mut u32 {
        &mut self.buf[LEARNED_COUNT_IDX]
    }

    #[inline]
    pub fn resolvent_size_mut(&mut self) -> &mut u32 {
        &mut self.buf[RESOLVENT_SIZE_IDX]
    }

    #[inline]
    pub fn seen_count_mut(&mut self) -> &mut u32 {
        let idx = LEARNED_BUF_START_IDX + self.capacity;
        &mut self.buf[idx]
    }

    #[inline]
    pub fn set_learned_lit(&mut self, i: usize, val: u32) {
        debug_assert!(i < self.capacity);
        self.buf[LEARNED_BUF_START_IDX + i] = val;
    }

    #[inline]
    pub fn set_seen_var(&mut self, i: usize, val: u32) {
        debug_assert!(i < self.capacity);
        let start = LEARNED_BUF_START_IDX + self.capacity + 1;
        self.buf[start + i] = val;
    }
}

/// Type alias for the compiled conflict processor function.
///
/// Parameters (register mapping on aarch64):
///   x0 = lits_ptr, w1 = lits_len, x2 = var_data_ptr,
///   w3 = current_level, w4 = skip_lit, x5 = out_ptr (raw u32 buffer),
///   x6 = vals_ptr (i8 array for ghost literal guard, #8434)
type ConflictProcessFn = unsafe extern "C" fn(
    *const u32, // lits_ptr
    u32,        // lits_len
    *mut u8,    // var_data_ptr (byte pointer for address arithmetic)
    u32,        // current_level
    u32,        // skip_lit (u32::MAX = no skip)
    *mut u32,   // out_ptr (raw buffer, layout depends on capacity)
    *const i8,  // vals_ptr (for ghost literal check: skip if vals[lit] >= 0)
);

/// JIT-compiled conflict analysis literal processor.
///
/// Holds compiled native code that implements the inner loop of conflict
/// analysis: for each literal in a reason clause, check seen/level and
/// update counters. The native code writes to a dynamically-sized buffer
/// whose offsets are baked in at JIT compile time based on the capacity.
pub struct CompiledConflictProcessor {
    func: ConflictProcessFn,
    /// The capacity baked into the compiled code. Must match the output buffer.
    capacity: usize,
    /// Executable memory must stay alive while `func` is callable.
    _executable: ExecutableMemory,
}

impl CompiledConflictProcessor {
    /// The capacity this processor was compiled for.
    #[inline]
    pub fn capacity(&self) -> usize {
        self.capacity
    }

    /// Total mmap'd executable memory allocated for this processor.
    ///
    /// Used by the code cache manager to enforce memory budgets (#8394).
    pub fn allocated_bytes(&self) -> usize {
        self._executable.allocated_bytes()
    }

    /// Process literals from a reason clause using the JIT-compiled function.
    ///
    /// # Arguments
    ///
    /// * `lits` - Encoded literals from the reason clause
    /// * `var_data_ptr` - Pointer to the VarData array (as bytes)
    /// * `current_level` - Current decision level
    /// * `skip_lit` - Literal to skip (the UIP literal `p`), or `u32::MAX`
    /// * `output` - Output buffer to receive results
    /// * `vals_ptr` - Pointer to the vals[] array (i8, indexed by lit.index()).
    ///   Used for ghost literal guard (#8434): after chrono-BT, some clause
    ///   literals may be unassigned (vals\[lit\] == 0) or satisfied (vals\[lit\] > 0).
    ///   These must be skipped to prevent inflating the counter.
    ///
    /// # Safety
    ///
    /// The caller must ensure:
    /// - `var_data_ptr` points to a valid VarData array with entries for all
    ///   variables referenced by `lits`
    /// - `vals_ptr` points to a valid i8 array with entries for all literal
    ///   indices referenced by `lits` (size >= 2 * num_vars)
    /// - `output.capacity() >= self.capacity` (buffers are large enough)
    /// - `output` is valid and writable
    /// - No concurrent modification of VarData entries
    pub unsafe fn process_literals(
        &self,
        lits: &[u32],
        var_data_ptr: *mut u8,
        current_level: u32,
        skip_lit: u32,
        output: &mut ConflictProcessorOutput,
        vals_ptr: *const i8,
    ) {
        debug_assert!(
            output.capacity() >= self.capacity,
            "BUG: output buffer capacity {} < compiled capacity {}",
            output.capacity(),
            self.capacity,
        );
        output.reset();
        if lits.is_empty() {
            return;
        }
        // SAFETY: Caller guarantees all pointers are valid and properly sized.
        // The output buffer is at least `capacity` slots for each array.
        unsafe {
            (self.func)(
                lits.as_ptr(),
                lits.len() as u32,
                var_data_ptr,
                current_level,
                skip_lit,
                output.as_mut_ptr(),
                vals_ptr,
            );
        }
    }
}

/// Compile the conflict analysis literal processor into native code.
///
/// `capacity` determines the size of the learned_buf and seen_vars arrays
/// in the output buffer. It should be >= num_vars to guarantee no overflow.
/// The compiled code has these offsets baked in, so the output buffer passed
/// to `process_literals` must have matching capacity.
///
/// # Errors
///
/// Returns `JitError::NoNativeIsa` on unsupported platforms.
pub fn compile_conflict_processor(capacity: usize) -> Result<CompiledConflictProcessor, JitError> {
    let capacity = capacity.max(64);

    #[cfg(target_arch = "aarch64")]
    {
        let code = emit_conflict_processor_aarch64(capacity);
        let executable = ExecutableMemory::new(&code)?;
        let fn_ptr = executable.as_ptr();
        // SAFETY: The code was generated by our assembler with the correct ABI.
        // The executable memory is owned by `_executable` and stays alive.
        let func: ConflictProcessFn =
            unsafe { std::mem::transmute::<*const u8, ConflictProcessFn>(fn_ptr) };
        Ok(CompiledConflictProcessor {
            func,
            capacity,
            _executable: executable,
        })
    }

    #[cfg(not(target_arch = "aarch64"))]
    {
        let _ = capacity;
        Err(JitError::NoNativeIsa)
    }
}

/// Emit aarch64 machine code for the conflict processor function.
///
/// `capacity` determines the buffer sizes baked into the generated code.
/// The seen_count field is at byte offset `12 + capacity * 4` from the
/// output buffer base, and seen_vars starts at `12 + capacity * 4 + 4`.
/// No bounds checks are emitted because capacity >= num_vars guarantees
/// no overflow (#8383).
///
/// Register allocation:
///   x0  = lits_ptr (input)
///   w1  = lits_len (input)
///   x2  = var_data_ptr (input)
///   w3  = current_level (input)
///   w4  = skip_lit (input)
///   x5  = out_ptr (input, raw u32 buffer)
///   x6  = vals_ptr (input, i8 array for ghost literal guard #8434)
///   w7  = counter (current-level unseen count)
///   w8  = learned_count
///   w9  = resolvent_size
///   x10 = scratch (var_data entry address)
///   w11 = current lit
///   w12 = var_idx (lit >> 1)
///   w13 = var_level
///   w14 = flags byte
///   x15 = scratch
///   x16 = scratch
///   w17 = seen_count (newly-seen var indices written to output)
///   w19 = loop index i (callee-saved, saved/restored in prologue/epilogue)
#[cfg(target_arch = "aarch64")]
fn emit_conflict_processor_aarch64(capacity: usize) -> Vec<u8> {
    use crate::aarch64::*;

    // Byte offsets of fields in the output buffer.
    // Layout: [counter:u32, learned_count:u32, resolvent_size:u32,
    //          learned_buf[capacity]:u32, seen_count:u32, seen_vars[capacity]:u32]
    let learned_buf_byte_offset: u32 = 12; // 3 * 4
    let seen_count_byte_offset: u32 = (3 + capacity) as u32 * 4;
    let seen_vars_byte_offset: u32 = seen_count_byte_offset + 4;

    let mut asm = Assembler::new();

    // Function prologue: save fp/lr, then save callee-saved x19/x20.
    asm.prologue();
    // STP x19, x20, [sp, #-16]!  -- save callee-saved registers
    // Encoding: 0xa9bf53f3 = STP x19, x20, [sp, #-16]!
    emit_raw(&mut asm, 0xa9bf53f3);

    // Initialize accumulators to 0.
    // w19 = i = 0 (callee-saved, x6 is now vals_ptr parameter)
    asm.movz_w(Reg::x(19), 0);
    // w7 = counter = 0
    asm.movz_w(Reg::x(7), 0);
    // w8 = learned_count = 0
    asm.movz_w(Reg::x(8), 0);
    // w9 = resolvent_size = 0
    asm.movz_w(Reg::x(9), 0);
    // w17 = seen_count = 0
    asm.movz_w(Reg::x(17), 0);

    // Loop header label.
    let loop_top = asm.label();
    let loop_end = asm.label();

    // Check: if i >= lits_len, exit loop.
    asm.bind(loop_top);
    emit_cmp_w_reg(&mut asm, Reg::x(19), Reg::x(1));
    asm.b_cond(Cond::Ge, loop_end);

    // Load lit = lits_ptr[i]: LDR W11, [X0, X19, LSL #2]
    emit_ldr_w_reg_lsl2(&mut asm, Reg::x(11), Reg::x(0), Reg::x(19));

    // Compare lit == skip_lit: CMP W11, W4
    emit_cmp_w_reg(&mut asm, Reg::x(11), Reg::x(4));
    let skip_to_next = asm.label();
    asm.b_cond(Cond::Eq, skip_to_next);

    // Ghost literal guard (#8434): skip unassigned/satisfied literals.
    // Load vals[lit] as signed byte: LDRSB W16, [X6, W11, UXTW]
    // X6 = vals_ptr (i8 array), W11 = lit (u32 index).
    // If vals[lit] >= 0, the literal is unassigned (0) or satisfied (>0) — skip it.
    //
    // LDRSB Wt, [Xn, Wm, UXTW] encoding:
    //   size=00, opc=11 (sign-extend byte to 32-bit), V=0
    //   option=010 (UXTW: zero-extend Wm to 64-bit), S=0 (no shift)
    //   = 0x38e04800 | (Rm<<16) | (Rn<<5) | Rt
    // Bits: 00 111 000 11 1 Rm 010 0 10 Rn Rt
    emit_raw(
        &mut asm,
        0x38e04800
            | (u32::from(Reg::x(11).0) << 16)
            | (u32::from(Reg::x(6).0) << 5)
            | u32::from(Reg::x(16).0),
    );
    // If val >= 0 (non-negative), literal is a ghost — skip it.
    // CMP W16, #0; B.GE skip_to_next
    asm.cmp_w_imm(Reg::x(16), 0);
    asm.b_cond(Cond::Ge, skip_to_next);

    // var_idx = lit >> 1
    asm.lsr_w_imm(Reg::x(12), Reg::x(11), 1);

    // Compute var_data_addr = var_data_ptr + var_idx * 16.
    emit_uxtw(&mut asm, Reg::x(15), Reg::x(12));
    emit_lsl_x_imm(&mut asm, Reg::x(15), Reg::x(15), 4);
    asm.add_x_reg(Reg::x(10), Reg::x(2), Reg::x(15));

    // Load flags byte from var_data_addr + 12.
    asm.ldrb_w_uimm(Reg::x(14), Reg::x(10), 12);

    // Test seen bit: flags & 1. Skip if already seen.
    emit_and_w_imm1(&mut asm, Reg::x(16), Reg::x(14));
    asm.cbnz_w(Reg::x(16), skip_to_next);

    // Mark seen: flags |= 1.
    asm.add_w_imm(Reg::x(14), Reg::x(14), 1);
    asm.strb_w_uimm(Reg::x(14), Reg::x(10), 12);

    // Record newly-seen var_idx in seen_vars buffer for bookkeeping.
    // No bounds check needed: capacity >= num_vars (#8383).
    // seen_vars[seen_count] = out_ptr + seen_vars_byte_offset + seen_count * 4.
    emit_uxtw(&mut asm, Reg::x(15), Reg::x(17));
    emit_lsl_x_imm(&mut asm, Reg::x(15), Reg::x(15), 2);
    // Add seen_vars_byte_offset. May exceed 12-bit immediate (4095), so
    // use MOVZ+ADD sequence for large offsets.
    emit_add_x_u32(&mut asm, Reg::x(15), Reg::x(15), seen_vars_byte_offset);
    asm.add_x_reg(Reg::x(15), Reg::x(5), Reg::x(15));
    // STR W12, [X15, #0] -- store var_idx
    asm.str_w_uimm(Reg::x(12), Reg::x(15), 0);
    // seen_count++
    asm.add_w_imm(Reg::x(17), Reg::x(17), 1);

    // Load var_level from var_data_addr + 0 (u32).
    asm.ldr_w_uimm(Reg::x(13), Reg::x(10), 0);

    // Branch: if var_level == current_level -> counter++
    //         else if var_level > 0 -> add to learned_buf, learned_count++
    //         if var_level > 0 -> resolvent_size++
    let not_current_level = asm.label();
    let done_lit = asm.label();

    emit_cmp_w_reg(&mut asm, Reg::x(13), Reg::x(3));
    asm.b_cond(Cond::Ne, not_current_level);

    // var_level == current_level: counter++, resolvent_size++
    asm.add_w_imm(Reg::x(7), Reg::x(7), 1);
    asm.add_w_imm(Reg::x(9), Reg::x(9), 1);
    asm.b(done_lit);

    asm.bind(not_current_level);
    asm.cbz_w(Reg::x(13), done_lit);

    // var_level > 0 and != current_level: add lit to learned_buf.
    // No bounds check needed: capacity >= num_vars (#8383).
    // learned_buf[learned_count] = out_ptr + 12 + learned_count * 4.
    emit_uxtw(&mut asm, Reg::x(15), Reg::x(8));
    emit_lsl_x_imm(&mut asm, Reg::x(15), Reg::x(15), 2);
    asm.add_x_imm(Reg::x(15), Reg::x(15), learned_buf_byte_offset);
    asm.add_x_reg(Reg::x(15), Reg::x(5), Reg::x(15));
    asm.str_w_uimm(Reg::x(11), Reg::x(15), 0);
    // learned_count++
    asm.add_w_imm(Reg::x(8), Reg::x(8), 1);
    // resolvent_size++
    asm.add_w_imm(Reg::x(9), Reg::x(9), 1);

    asm.bind(done_lit);

    asm.bind(skip_to_next);
    // i++
    asm.add_w_imm(Reg::x(19), Reg::x(19), 1);
    asm.b(loop_top);

    asm.bind(loop_end);

    // Write scalar results to out_ptr.
    // counter at offset 0
    asm.str_w_uimm(Reg::x(7), Reg::x(5), 0);
    // learned_count at offset 4
    asm.str_w_uimm(Reg::x(8), Reg::x(5), 4);
    // resolvent_size at offset 8
    asm.str_w_uimm(Reg::x(9), Reg::x(5), 8);
    // seen_count at dynamic offset (may be large).
    // Use register-based store: compute address, then STR.
    emit_movz_x_u32(&mut asm, Reg::x(15), seen_count_byte_offset);
    asm.add_x_reg(Reg::x(15), Reg::x(5), Reg::x(15));
    asm.str_w_uimm(Reg::x(17), Reg::x(15), 0);

    // Epilogue: restore callee-saved x19/x20, then fp/lr, return.
    // LDP x19, x20, [sp], #16
    emit_raw(&mut asm, 0xa8c153f3);
    asm.epilogue();

    asm.finalize()
}

/// Emit ADD Xd, Xn, #imm where imm may exceed 12-bit immediate range.
/// For small values (<4096), emits a single ADD immediate.
/// For larger values, loads the constant into x16 then emits ADD Xd, Xn, X16.
#[cfg(target_arch = "aarch64")]
fn emit_add_x_u32(
    asm: &mut crate::aarch64::Assembler,
    rd: crate::aarch64::Reg,
    rn: crate::aarch64::Reg,
    imm: u32,
) {
    if imm < 4096 {
        asm.add_x_imm(rd, rn, imm);
    } else {
        emit_movz_x_u32(asm, crate::aarch64::Reg::x(16), imm);
        asm.add_x_reg(rd, rn, crate::aarch64::Reg::x(16));
    }
}

/// Emit MOVZ Xd, #imm (up to 32-bit value) using MOVZ + optional MOVK.
#[cfg(target_arch = "aarch64")]
fn emit_movz_x_u32(asm: &mut crate::aarch64::Assembler, rd: crate::aarch64::Reg, imm: u32) {
    let lo16 = imm & 0xFFFF;
    let hi16 = (imm >> 16) & 0xFFFF;
    // MOVZ Xd, #lo16, LSL #0
    // Encoding: 0xd2800000 | (hw<<21) | (imm16<<5) | Rd
    let movz = 0xd2800000u32 | (lo16 << 5) | u32::from(rd.0);
    emit_raw(asm, movz);
    if hi16 != 0 {
        // MOVK Xd, #hi16, LSL #16
        // Encoding: 0xf2a00000 | (imm16<<5) | Rd
        let movk = 0xf2a00000u32 | (hi16 << 5) | u32::from(rd.0);
        emit_raw(asm, movk);
    }
}

/// Emit CMP Wn, Wm (SUBS WZR, Wn, Wm) as a raw instruction.
/// Encoding: 0x6b00001f | (Rm << 16) | (Rn << 5)
#[cfg(target_arch = "aarch64")]
pub(crate) fn emit_cmp_w_reg(
    asm: &mut crate::aarch64::Assembler,
    rn: crate::aarch64::Reg,
    rm: crate::aarch64::Reg,
) {
    let instr: u32 = 0x6b00001f | (u32::from(rm.0) << 16) | (u32::from(rn.0) << 5);
    // SAFETY: Valid aarch64 SUBS encoding with Rd=WZR.
    emit_raw(asm, instr);
}

/// Emit LDR Wt, [Xn, Xm, LSL #2] — 32-bit register-offset load, scaled.
/// Encoding: size=10 V=0 opc=01 option=011 S=1 = 0xb8607800
#[cfg(target_arch = "aarch64")]
pub(crate) fn emit_ldr_w_reg_lsl2(
    asm: &mut crate::aarch64::Assembler,
    rt: crate::aarch64::Reg,
    rn: crate::aarch64::Reg,
    rm: crate::aarch64::Reg,
) {
    let instr: u32 =
        0xb8607800 | (u32::from(rm.0) << 16) | (u32::from(rn.0) << 5) | u32::from(rt.0);
    emit_raw(asm, instr);
}

/// Emit UXTW Xd, Wn — zero-extend 32-bit to 64-bit.
/// Alias for UBFM Xd, Xn, #0, #31.
/// Encoding: 0xd3407c00 | (Rn << 5) | Rd
#[cfg(target_arch = "aarch64")]
pub(crate) fn emit_uxtw(
    asm: &mut crate::aarch64::Assembler,
    rd: crate::aarch64::Reg,
    rn: crate::aarch64::Reg,
) {
    let instr: u32 = 0xd3407c00 | (u32::from(rn.0) << 5) | u32::from(rd.0);
    emit_raw(asm, instr);
}

/// Emit LSL Xd, Xn, #shift (64-bit).
/// Alias for UBFM Xd, Xn, #(64-shift), #(63-shift).
/// Encoding: sf=1 opc=10 N=1 immr=(64-shift) imms=(63-shift)
/// = 0xd3400000 | (immr << 16) | (imms << 10) | (Rn << 5) | Rd
#[cfg(target_arch = "aarch64")]
pub(crate) fn emit_lsl_x_imm(
    asm: &mut crate::aarch64::Assembler,
    rd: crate::aarch64::Reg,
    rn: crate::aarch64::Reg,
    shift: u32,
) {
    debug_assert!(shift > 0 && shift < 64);
    let immr = 64 - shift;
    let imms = 63 - shift;
    let instr: u32 =
        0xd3400000 | (immr << 16) | (imms << 10) | (u32::from(rn.0) << 5) | u32::from(rd.0);
    emit_raw(asm, instr);
}

/// Emit AND Wd, Wn, #1 — bitwise AND with immediate 1.
/// Logical immediate encoding for #1 (32-bit): N=0, immr=0, imms=0.
/// AND (immediate): 0x12000000 | (immr << 16) | (imms << 10) | (Rn << 5) | Rd
#[cfg(target_arch = "aarch64")]
pub(crate) fn emit_and_w_imm1(
    asm: &mut crate::aarch64::Assembler,
    rd: crate::aarch64::Reg,
    rn: crate::aarch64::Reg,
) {
    let instr: u32 = 0x12000000 | (u32::from(rn.0) << 5) | u32::from(rd.0);
    emit_raw(asm, instr);
}

/// Emit a raw 32-bit instruction word.
///
/// The Assembler's `emit` method is private, so we access it through finalize
/// trickery: we build a one-instruction assembler and extract the bytes.
/// Actually, the assembler has a public `pos()` but emit is private.
/// We'll add a thin wrapper via the code buffer approach.
///
/// Workaround: Use inline assembly byte generation since the Assembler
/// doesn't expose a raw emit. We accumulate raw instructions in a helper
/// Vec and append them in finalize.
///
/// Actually, looking at the Assembler more carefully, its `emit` method is
/// indeed private. The cleanest approach is to add a `pub(crate) fn emit_raw`
/// to the Assembler. Let me do that.
#[cfg(target_arch = "aarch64")]
fn emit_raw(asm: &mut crate::aarch64::Assembler, instr: u32) {
    asm.emit_raw(instr);
}

// ---- Interpreter fallback ----

/// Process literals using the interpreter (for non-aarch64 platforms and testing).
///
/// Implements the same logic as the JIT-compiled version:
/// for each literal, check seen flag, compare decision level, update counters.
/// Ghost literals (unassigned or satisfied after chrono-BT) are skipped via
/// the vals_ptr guard (#8434).
///
/// The output buffer must have capacity >= the number of variables referenced
/// by `lits`. No bounds checking is performed since the buffer is pre-sized
/// to num_vars (#8383).
///
/// # Safety
///
/// - `var_data_ptr` must point to a valid VarData array with entries for all
///   variables referenced by `lits`. Each VarData entry is 16 bytes with
///   `level` at offset 0 and `flags` at offset 12.
/// - `vals_ptr` must point to a valid i8 array indexed by literal value
///   (size >= 2 * num_vars). vals\[lit\] < 0 means falsified, >= 0 means
///   unassigned or satisfied (ghost).
/// - The VarData array behind `var_data_ptr` must be writable (this function
///   sets seen bits in the flags byte) and must not be accessed concurrently
///   for the duration of the call.
pub unsafe fn process_literals_interpreter(
    lits: &[u32],
    var_data_ptr: *mut u8,
    current_level: u32,
    skip_lit: u32,
    output: &mut ConflictProcessorOutput,
    vals_ptr: *const i8,
) {
    output.reset();
    for &lit in lits {
        if lit == skip_lit {
            continue;
        }

        // Ghost literal guard (#8434): after chrono-BT find_conflict_level
        // backtrack, some conflict/reason clause literals may be unassigned.
        // Their var_data.level retains a stale value. Skip them to prevent
        // inflating counter and causing trail exhaustion in backward scan.
        // SAFETY: Caller guarantees vals_ptr covers all literal indices.
        let val = unsafe { *vals_ptr.add(lit as usize) };
        if val >= 0 {
            continue;
        }

        let var_idx = (lit >> 1) as usize;
        // SAFETY: Caller guarantees var_data_ptr covers all variables.
        let entry_base = unsafe { var_data_ptr.add(var_idx * 16) };

        // Load flags byte (offset 12).
        // SAFETY: entry_base points at this variable's 16-byte VarData entry
        // (in bounds per the caller's var_data_ptr guarantee), so offset 12 —
        // the flags byte — is within the same entry. Byte reads need no
        // alignment.
        let flags = unsafe { *entry_base.add(12) };
        // Check seen bit (bit 0).
        if flags & 1 != 0 {
            continue;
        }

        // Mark seen: set bit 0.
        // SAFETY: Same in-bounds flags byte as the read above; the caller
        // guarantees the VarData array is writable and not accessed
        // concurrently during this call.
        unsafe { *entry_base.add(12) = flags | 1 };

        // Record newly-seen var_idx in seen_vars buffer.
        // Buffer is pre-sized to num_vars, so overflow is impossible (#8383).
        {
            let sc = output.seen_count() as usize;
            output.set_seen_var(sc, var_idx as u32);
            *output.seen_count_mut() = (sc + 1) as u32;
        }

        // Load var_level (u32 at offset 0).
        // SAFETY: read_unaligned because entry_base is *const u8 (alignment 1);
        // casting to *const u32 without alignment guarantee would be UB.
        let var_level = unsafe { entry_base.cast::<u32>().read_unaligned() };

        if var_level == current_level {
            *output.counter_mut() += 1;
            *output.resolvent_size_mut() += 1;
        } else if var_level > 0 {
            let lc = output.learned_count() as usize;
            output.set_learned_lit(lc, lit);
            *output.learned_count_mut() = (lc + 1) as u32;
            *output.resolvent_size_mut() += 1;
        }
        // var_level == 0: skip (level-0 variables are not counted).
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Simulated VarData for testing. 16 bytes, matching the real layout.
    #[repr(C)]
    #[derive(Clone, Copy)]
    struct TestVarData {
        level: u32,
        trail_pos: u32,
        reason: u32,
        flags: u8,
        _pad: [u8; 3],
    }

    impl TestVarData {
        fn new(level: u32) -> Self {
            Self {
                level,
                trail_pos: u32::MAX,
                reason: u32::MAX,
                flags: 0,
                _pad: [0; 3],
            }
        }
    }

    const _: () = assert!(size_of::<TestVarData>() == 16);

    // Verify ConflictProcessorOutput dynamic layout offsets.
    #[test]
    fn test_output_layout_offsets() {
        let out = ConflictProcessorOutput::new(1024);
        // counter at byte 0, learned_count at byte 4, resolvent_size at byte 8,
        // learned_buf starts at byte 12, seen_count at 12 + 1024*4 = 4108,
        // seen_vars starts at 4112.
        assert_eq!(out.seen_count_byte_offset(), 12 + 1024 * 4);
        assert_eq!(out.seen_vars_byte_offset(), 12 + 1024 * 4 + 4);
    }

    /// Helper to run both interpreter and (on aarch64) JIT, verifying they
    /// produce identical results. The capacity is set to var_data.len() to
    /// guarantee no overflow.
    ///
    /// `vals` is the assignment array: vals[lit] = -1 (falsified), 0 (unassigned),
    /// 1 (satisfied). All literals not explicitly set are assumed falsified.
    fn run_and_compare_with_vals(
        lits: &[u32],
        var_data: &mut [TestVarData],
        current_level: u32,
        skip_lit: u32,
        vals: &[i8],
    ) -> ConflictProcessorOutput {
        let capacity = var_data.len();
        // Save original var_data for the JIT run.
        let var_data_backup: Vec<TestVarData> = var_data.to_vec();

        // Run interpreter.
        let mut interp_out = ConflictProcessorOutput::new(capacity);
        unsafe {
            process_literals_interpreter(
                lits,
                var_data.as_mut_ptr().cast::<u8>(),
                current_level,
                skip_lit,
                &mut interp_out,
                vals.as_ptr(),
            );
        }
        let interp_flags: Vec<u8> = var_data.iter().map(|v| v.flags).collect();

        // On aarch64, also run JIT and compare.
        #[cfg(target_arch = "aarch64")]
        {
            // Restore var_data for JIT run.
            var_data.copy_from_slice(&var_data_backup);

            let processor = compile_conflict_processor(capacity)
                .expect("JIT compilation should succeed on aarch64");
            let mut jit_out = ConflictProcessorOutput::new(capacity);
            unsafe {
                processor.process_literals(
                    lits,
                    var_data.as_mut_ptr().cast::<u8>(),
                    current_level,
                    skip_lit,
                    &mut jit_out,
                    vals.as_ptr(),
                );
            }

            // Compare outputs.
            assert_eq!(
                interp_out.counter(),
                jit_out.counter(),
                "counter mismatch: interp={} jit={}",
                interp_out.counter(),
                jit_out.counter(),
            );
            assert_eq!(
                interp_out.learned_count(),
                jit_out.learned_count(),
                "learned_count mismatch: interp={} jit={}",
                interp_out.learned_count(),
                jit_out.learned_count(),
            );
            assert_eq!(
                interp_out.resolvent_size(),
                jit_out.resolvent_size(),
                "resolvent_size mismatch: interp={} jit={}",
                interp_out.resolvent_size(),
                jit_out.resolvent_size(),
            );

            // Compare learned literals (order should be identical).
            for i in 0..interp_out.learned_count() as usize {
                assert_eq!(
                    interp_out.learned_lit(i),
                    jit_out.learned_lit(i),
                    "learned_buf[{i}] mismatch: interp={} jit={}",
                    interp_out.learned_lit(i),
                    jit_out.learned_lit(i),
                );
            }

            // Compare seen_vars (newly-seen variable indices).
            assert_eq!(
                interp_out.seen_count(),
                jit_out.seen_count(),
                "seen_count mismatch: interp={} jit={}",
                interp_out.seen_count(),
                jit_out.seen_count(),
            );
            for i in 0..interp_out.seen_count() as usize {
                assert_eq!(
                    interp_out.seen_var(i),
                    jit_out.seen_var(i),
                    "seen_vars[{i}] mismatch: interp={} jit={}",
                    interp_out.seen_var(i),
                    jit_out.seen_var(i),
                );
            }

            // Compare seen flags.
            let jit_flags: Vec<u8> = var_data.iter().map(|v| v.flags).collect();
            assert_eq!(
                interp_flags, jit_flags,
                "seen flag mismatch after processing"
            );
        }

        #[cfg(not(target_arch = "aarch64"))]
        let _ = (var_data_backup, interp_flags);

        interp_out
    }

    /// Convenience wrapper: all literals are falsified (val = -1).
    fn run_and_compare(
        lits: &[u32],
        var_data: &mut [TestVarData],
        current_level: u32,
        skip_lit: u32,
    ) -> ConflictProcessorOutput {
        // Create vals array with all literals falsified.
        // Each var has two literals (positive and negative), so vals has 2*num_vars entries.
        let num_vals = var_data.len() * 2;
        let vals = vec![-1i8; num_vals];
        run_and_compare_with_vals(lits, var_data, current_level, skip_lit, &vals)
    }

    #[test]
    fn test_conflict_processor_empty_lits() {
        let mut var_data = vec![TestVarData::new(0); 4];
        let result = run_and_compare(&[], &mut var_data, 3, u32::MAX);
        assert_eq!(result.counter(), 0);
        assert_eq!(result.learned_count(), 0);
        assert_eq!(result.resolvent_size(), 0);
    }

    #[test]
    fn test_conflict_processor_single_current_level() {
        let mut var_data = vec![TestVarData::new(0); 4];
        var_data[0].level = 3;

        let lits = vec![0u32];
        let result = run_and_compare(&lits, &mut var_data, 3, u32::MAX);

        assert_eq!(result.counter(), 1);
        assert_eq!(result.learned_count(), 0);
        assert_eq!(result.resolvent_size(), 1);
        assert_eq!(var_data[0].flags & 1, 1);
    }

    #[test]
    fn test_conflict_processor_single_lower_level() {
        let mut var_data = vec![TestVarData::new(0); 4];
        var_data[1].level = 2;

        let lits = vec![2u32];
        let result = run_and_compare(&lits, &mut var_data, 3, u32::MAX);

        assert_eq!(result.counter(), 0);
        assert_eq!(result.learned_count(), 1);
        assert_eq!(result.resolvent_size(), 1);
        assert_eq!(result.learned_lit(0), 2);
    }

    #[test]
    fn test_conflict_processor_level_zero_ignored() {
        let mut var_data = vec![TestVarData::new(0); 4];
        var_data[2].level = 0;

        let lits = vec![5u32];
        let result = run_and_compare(&lits, &mut var_data, 3, u32::MAX);

        assert_eq!(result.counter(), 0);
        assert_eq!(result.learned_count(), 0);
        assert_eq!(result.resolvent_size(), 0);
        assert_eq!(var_data[2].flags & 1, 1);
    }

    #[test]
    fn test_conflict_processor_skip_lit() {
        let mut var_data = vec![TestVarData::new(0); 4];
        var_data[0].level = 3;

        let lits = vec![0u32];
        let result = run_and_compare(&lits, &mut var_data, 3, 0);

        assert_eq!(result.counter(), 0);
        assert_eq!(result.learned_count(), 0);
        assert_eq!(result.resolvent_size(), 0);
        assert_eq!(var_data[0].flags & 1, 0);
    }

    #[test]
    fn test_conflict_processor_already_seen() {
        let mut var_data = vec![TestVarData::new(0); 4];
        var_data[0].level = 3;
        var_data[0].flags = 1;

        let lits = vec![0u32];
        let result = run_and_compare(&lits, &mut var_data, 3, u32::MAX);

        assert_eq!(result.counter(), 0);
        assert_eq!(result.learned_count(), 0);
        assert_eq!(result.resolvent_size(), 0);
    }

    #[test]
    fn test_conflict_processor_mixed_levels() {
        let mut var_data = vec![TestVarData::new(0); 8];
        var_data[0].level = 5;
        var_data[1].level = 3;
        var_data[2].level = 5;
        var_data[3].level = 0;
        var_data[4].level = 1;
        var_data[5].level = 5;

        let lits = vec![0u32, 3, 4, 6, 9, 10];
        let result = run_and_compare(&lits, &mut var_data, 5, 10);

        assert_eq!(result.counter(), 2);
        assert_eq!(result.learned_count(), 2);
        assert_eq!(result.resolvent_size(), 4);
        assert_eq!(result.learned_lit(0), 3);
        assert_eq!(result.learned_lit(1), 9);
    }

    #[test]
    fn test_conflict_processor_duplicate_variable() {
        let mut var_data = vec![TestVarData::new(0); 4];
        var_data[0].level = 3;

        let lits = vec![0u32, 1u32];
        let result = run_and_compare(&lits, &mut var_data, 3, u32::MAX);

        assert_eq!(result.counter(), 1);
        assert_eq!(result.learned_count(), 0);
        assert_eq!(result.resolvent_size(), 1);
    }

    #[test]
    fn test_conflict_processor_many_literals() {
        let num_vars = 100;
        let mut var_data = vec![TestVarData::new(0); num_vars];
        let current_level = 10;

        for (i, vd) in var_data.iter_mut().enumerate() {
            vd.level = match i % 4 {
                0 => current_level,
                1 => 5,
                2 => 0,
                3 => current_level,
                _ => unreachable!(),
            };
        }

        let lits: Vec<u32> = (0..num_vars as u32).map(|v| v * 2).collect();
        let result = run_and_compare(&lits, &mut var_data, current_level, u32::MAX);

        let expected_counter = (0..num_vars).filter(|i| i % 4 == 0 || i % 4 == 3).count() as u32;
        let expected_learned = (0..num_vars).filter(|i| i % 4 == 1).count() as u32;
        let expected_resolvent = expected_counter + expected_learned;

        assert_eq!(result.counter(), expected_counter);
        assert_eq!(result.learned_count(), expected_learned);
        assert_eq!(result.resolvent_size(), expected_resolvent);
    }

    #[test]
    fn test_conflict_processor_large_no_overflow() {
        // Regression test (#8383): with dynamic buffers sized to num_vars,
        // ALL variables are tracked in seen_vars — no overflow, no stale flags.
        // Previously with MAX_SEEN=512, only 512 vars were recorded and the
        // rest had stale seen flags.
        let num_vars = 2048;
        let mut var_data = vec![TestVarData::new(0); num_vars];
        let current_level = 5;

        for v in var_data.iter_mut() {
            v.level = current_level;
        }

        let lits: Vec<u32> = (0..num_vars as u32).map(|v| v * 2).collect();
        let result = run_and_compare(&lits, &mut var_data, current_level, u32::MAX);

        // ALL variables must be tracked (no capping).
        assert_eq!(
            result.seen_count() as usize,
            num_vars,
            "seen_count should equal num_vars={}, got {}",
            num_vars,
            result.seen_count(),
        );
        assert_eq!(result.counter(), num_vars as u32);
    }

    #[test]
    fn test_conflict_processor_large_learned_no_overflow() {
        // Regression test (#8383): all learned literals are recorded with
        // dynamic buffers.
        let num_vars = 2048;
        let mut var_data = vec![TestVarData::new(0); num_vars];
        let current_level = 10;

        for v in var_data.iter_mut() {
            v.level = 3;
        }

        let lits: Vec<u32> = (0..num_vars as u32).map(|v| v * 2).collect();
        let result = run_and_compare(&lits, &mut var_data, current_level, u32::MAX);

        assert_eq!(
            result.learned_count() as usize,
            num_vars,
            "learned_count should equal num_vars={}, got {}",
            num_vars,
            result.learned_count(),
        );
        assert_eq!(result.resolvent_size(), num_vars as u32);
    }

    #[test]
    fn test_conflict_processor_ghost_literal_skipped() {
        // Regression test (#8434): after chrono-BT find_conflict_level backtrack,
        // some conflict/reason clause literals may be unassigned (ghost literals).
        // These must be skipped to prevent inflating the counter.
        let mut var_data = vec![TestVarData::new(0); 8];
        let current_level = 5;

        // var 0 at current level, falsified -> should be counted
        var_data[0].level = 5;
        // var 1 at current level, but UNASSIGNED (ghost) -> should be skipped
        var_data[1].level = 5;
        // var 2 at lower level, falsified -> should be added to learned
        var_data[2].level = 3;
        // var 3 at current level, SATISFIED (ghost) -> should be skipped
        var_data[3].level = 5;

        // lits: var0+, var1+, var2+, var3+  (positive literals = var*2)
        let lits = vec![0u32, 2, 4, 6];

        // vals array: indexed by lit value.
        // lit 0 (var0+) = -1 (falsified)
        // lit 2 (var1+) =  0 (unassigned -- ghost)
        // lit 4 (var2+) = -1 (falsified)
        // lit 6 (var3+) =  1 (satisfied -- ghost)
        let mut vals = vec![-1i8; 16]; // all falsified by default
        vals[2] = 0; // var1+ unassigned
        vals[6] = 1; // var3+ satisfied

        let result =
            run_and_compare_with_vals(&lits, &mut var_data, current_level, u32::MAX, &vals);

        // Only var0 (counter) and var2 (learned) should be processed.
        // var1 and var3 are ghost literals and must be skipped.
        assert_eq!(result.counter(), 1, "only var0 should be at current level");
        assert_eq!(result.learned_count(), 1, "only var2 should be learned");
        assert_eq!(result.resolvent_size(), 2, "counter + learned");
        assert_eq!(result.seen_count(), 2, "only var0 and var2 should be seen");
        // Ghost literals should NOT have seen flag set.
        assert_eq!(var_data[1].flags & 1, 0, "var1 (ghost) should not be seen");
        assert_eq!(var_data[3].flags & 1, 0, "var3 (ghost) should not be seen");
    }

    #[test]
    fn test_conflict_processor_all_ghost_literals() {
        // Edge case: every literal is a ghost (unassigned). Nothing processed.
        let mut var_data = vec![TestVarData::new(0); 4];
        var_data[0].level = 3;
        var_data[1].level = 3;

        let lits = vec![0u32, 2];
        let vals = vec![0i8; 8]; // all unassigned

        let result = run_and_compare_with_vals(&lits, &mut var_data, 3, u32::MAX, &vals);

        assert_eq!(result.counter(), 0);
        assert_eq!(result.learned_count(), 0);
        assert_eq!(result.resolvent_size(), 0);
        assert_eq!(result.seen_count(), 0);
    }
}
