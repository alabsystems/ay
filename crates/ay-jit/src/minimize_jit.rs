// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! JIT-compiled conflict clause minimization classifier.
//!
//! During conflict analysis, the solver minimizes learned clauses by checking
//! if each literal is redundant (Sorensson & Biere 2009). The hot path
//! involves early-abort checks per literal: level counts, trail positions,
//! and cached minimize flags. This module compiles the batch classification
//! into a single native function call.
//!
//! ## STATUS (2026-07-14 triage)
//!
//! Zero callers. An aarch64 kernel for recursive conflict-clause
//! minimization whose speedup was never measured. Revive criterion:
//! aarch64 profiling shows minimization is a hot fraction of conflict
//! analysis; prune if it stays under 2-3% of runtime.
//! See the development design notes
//!
//! ## Classification
//!
//! For each literal in the learned clause, the classifier produces:
//! - `CLASSIFY_SKIP` (0): redundant by level 0, or cached removable/keep/poison
//! - `CLASSIFY_ABORT` (1): early-abort (decision var, single lit on level,
//!   trail position abort, or at current decision level)
//! - `CLASSIFY_CHECK` (2): needs full recursive redundancy check
//!
//! ## Data Layout
//!
//! VarData is 16 bytes (`#[repr(C)]`):
//! - `level: u32`     (offset 0)
//! - `trail_pos: u32` (offset 4)
//! - `reason: u32`    (offset 8)
//! - `flags: u8`      (offset 12, bit 0 = seen)
//!
//! MinimizeFlags per variable (u8):
//! - `MIN_POISON = 0x01`
//! - `MIN_REMOVABLE = 0x02`
//! - `MIN_VISITED = 0x04`
//! - `MIN_KEEP = 0x08`
//!
//! ## Function ABI
//!
//! ```text
//! extern "C" fn(
//!     lits_ptr: *const u32,             // x0: learned clause literals
//!     lits_len: u32,                    // w1: number of literals
//!     var_data_ptr: *const u8,          // x2: VarData array base (byte ptr)
//!     min_flags_ptr: *const u8,         // x3: minimize_flags array
//!     level_seen_count_ptr: *const u32, // x4: per-level seen count
//!     level_seen_trail_ptr: *const u64, // x5: per-level min trail (usize)
//!     out_classify_ptr: *mut u8,        // x6 (arg 6)
//!     decision_level: u32,              // w7 (arg 7)
//! ) -> u32  // count of CHECK literals
//! ```

use crate::executable::ExecutableMemory;
use crate::JitError;

/// Classification: skip (level 0 or cached result).
pub const CLASSIFY_SKIP: u8 = 0;
/// Classification: early-abort (non-removable without recursive check).
pub const CLASSIFY_ABORT: u8 = 1;
/// Classification: needs recursive redundancy check.
pub const CLASSIFY_CHECK: u8 = 2;

/// Minimize flag constants (must match ay-sat's MIN_* values).
const MIN_POISON: u8 = 0x01;
const MIN_REMOVABLE: u8 = 0x02;
const _MIN_VISITED: u8 = 0x04;
const MIN_KEEP: u8 = 0x08;

/// Sentinel for no reason (decision variable).
const NO_REASON: u32 = u32::MAX;

/// Type alias for the compiled minimize classifier function.
type MinimizeClassifyFn = unsafe extern "C" fn(
    *const u32, // lits_ptr
    u32,        // lits_len
    *const u8,  // var_data_ptr
    *const u8,  // min_flags_ptr
    *const u32, // level_seen_count_ptr
    *const u64, // level_seen_trail_ptr
    *mut u8,    // out_classify_ptr
    u32,        // decision_level
) -> u32;

/// JIT-compiled minimize classifier.
pub struct CompiledMinimizeClassifier {
    func: MinimizeClassifyFn,
    /// Executable memory must stay alive while `func` is callable.
    _executable: ExecutableMemory,
}

impl CompiledMinimizeClassifier {
    /// Classify learned clause literals for minimization.
    ///
    /// # Arguments
    ///
    /// * `lits` - Encoded literals (var * 2 + polarity)
    /// * `var_data_ptr` - VarData array base as bytes
    /// * `min_flags_ptr` - Per-variable minimize flags
    /// * `level_seen_count_ptr` - Per-level seen count from analysis
    /// * `level_seen_trail_ptr` - Per-level min trail position (usize)
    /// * `out_classify` - Output classification array (one byte per literal)
    /// * `decision_level` - Current decision level
    ///
    /// # Returns
    ///
    /// Number of literals classified as CHECK (need recursive check).
    ///
    /// # Safety
    ///
    /// Caller must ensure all pointers are valid and arrays are large enough.
    pub unsafe fn classify(
        &self,
        lits: &[u32],
        var_data_ptr: *const u8,
        min_flags_ptr: *const u8,
        level_seen_count_ptr: *const u32,
        level_seen_trail_ptr: *const u64,
        out_classify: &mut [u8],
        decision_level: u32,
    ) -> u32 {
        if lits.is_empty() {
            return 0;
        }
        debug_assert!(out_classify.len() >= lits.len());
        // SAFETY: Caller guarantees all pointers are valid.
        unsafe {
            (self.func)(
                lits.as_ptr(),
                lits.len() as u32,
                var_data_ptr,
                min_flags_ptr,
                level_seen_count_ptr,
                level_seen_trail_ptr,
                out_classify.as_mut_ptr(),
                decision_level,
            )
        }
    }
}

/// Compile the minimize classifier into native code.
///
/// # Errors
///
/// Returns `JitError::NoNativeIsa` on unsupported platforms.
pub fn compile_minimize_classifier() -> Result<CompiledMinimizeClassifier, JitError> {
    #[cfg(target_arch = "aarch64")]
    {
        let code = emit_minimize_classifier_aarch64();
        let executable = ExecutableMemory::new(&code)?;
        let fn_ptr = executable.as_ptr();
        // SAFETY: fn_ptr points to the start of our compiled function in
        // executable memory. The function was generated by emit_minimize_classifier_aarch64()
        // with extern "C" ABI matching MinimizeClassifyFn:
        //   fn(*const u32, u32, *const u8, *const u8, *const u32, *const u64,
        //      *mut u8, u32) -> u32
        // The ExecutableMemory is owned by CompiledMinimizeClassifier._executable
        // and remains alive for the struct's lifetime, keeping fn_ptr valid.
        let func: MinimizeClassifyFn =
            unsafe { std::mem::transmute::<*const u8, MinimizeClassifyFn>(fn_ptr) };
        Ok(CompiledMinimizeClassifier {
            func,
            _executable: executable,
        })
    }

    #[cfg(not(target_arch = "aarch64"))]
    {
        Err(JitError::NoNativeIsa)
    }
}

/// Interpreter fallback for the minimize classifier.
///
/// Implements the same logic as the JIT-compiled version. Used on non-aarch64
/// platforms and for testing correctness.
///
/// # Safety
///
/// `var_data_ptr` must point to a valid VarData array. `min_flags_ptr` must
/// cover all variable indices in `lits`. `level_seen_count_ptr` and
/// `level_seen_trail_ptr` must cover all decision levels.
pub unsafe fn classify_minimize_interpreter(
    lits: &[u32],
    var_data_ptr: *const u8,
    min_flags_ptr: *const u8,
    level_seen_count_ptr: *const u32,
    level_seen_trail_ptr: *const u64,
    out_classify: &mut [u8],
    decision_level: u32,
) -> u32 {
    let mut check_count: u32 = 0;

    for (i, &lit) in lits.iter().enumerate() {
        let var_idx = (lit >> 1) as usize;

        // SAFETY: Caller guarantees var_data_ptr covers all variables.
        let entry_base = unsafe { var_data_ptr.add(var_idx * 16) };

        // Load level (u32 at offset 0).
        // SAFETY: read_unaligned because entry_base is *const u8 (alignment 1).
        let var_level = unsafe { entry_base.cast::<u32>().read_unaligned() };

        // Level 0: always redundant -> SKIP.
        if var_level == 0 {
            out_classify[i] = CLASSIFY_SKIP;
            continue;
        }

        // Load minimize flags.
        // SAFETY: Caller guarantees min_flags_ptr covers all variable indices
        // in `lits`, and var_idx was derived from a literal in `lits`.
        let mf = unsafe { *min_flags_ptr.add(var_idx) };

        // Cached removable or keep -> SKIP (redundant).
        if mf & (MIN_REMOVABLE | MIN_KEEP) != 0 {
            out_classify[i] = CLASSIFY_SKIP;
            continue;
        }

        // Cached poison -> ABORT (known non-removable).
        if mf & MIN_POISON != 0 {
            out_classify[i] = CLASSIFY_ABORT;
            continue;
        }

        // Current decision level -> ABORT (only path is through 1UIP itself).
        if var_level == decision_level {
            out_classify[i] = CLASSIFY_ABORT;
            continue;
        }

        // Load reason (u32 at offset 8).
        // SAFETY: read_unaligned for reason field at offset 8.
        let reason = unsafe { entry_base.add(8).cast::<u32>().read_unaligned() };

        // Decision variable -> ABORT.
        if reason == NO_REASON {
            out_classify[i] = CLASSIFY_ABORT;
            continue;
        }

        // Early-abort: level seen count < 2 (Knuth's single-literal abort).
        // SAFETY: Caller guarantees level_seen_count_ptr covers all decision
        // levels; var_level is the recorded level of a variable in `lits`.
        let level_seen_count = unsafe { *level_seen_count_ptr.add(var_level as usize) };
        if level_seen_count < 2 {
            out_classify[i] = CLASSIFY_ABORT;
            continue;
        }

        // Early-abort: trail position <= min trail for level.
        // SAFETY: read_unaligned for trail_pos field at offset 4.
        let trail_pos = unsafe { entry_base.add(4).cast::<u32>().read_unaligned() };
        // SAFETY: Caller guarantees level_seen_trail_ptr covers all decision
        // levels; var_level is the recorded level of a variable in `lits`.
        let level_trail = unsafe { *level_seen_trail_ptr.add(var_level as usize) };
        if u64::from(trail_pos) <= level_trail {
            out_classify[i] = CLASSIFY_ABORT;
            continue;
        }

        // Needs recursive check.
        out_classify[i] = CLASSIFY_CHECK;
        check_count += 1;
    }

    check_count
}

/// Emit aarch64 machine code for the minimize classifier.
///
/// Register allocation:
///   x0  = lits_ptr (input)
///   w1  = lits_len (input)
///   x2  = var_data_ptr (input)
///   x3  = min_flags_ptr (input)
///   x4  = level_seen_count_ptr (input)
///   x5  = level_seen_trail_ptr (input)
///   x6  = out_classify_ptr (input, arg 6)
///   w7  = decision_level (input, arg 7)
///   w8  = loop index i
///   w9  = check_count (return value)
///   x10 = scratch (var_data entry address)
///   w11 = current lit
///   w12 = var_idx (lit >> 1)
///   w13 = var_level
///   w14 = scratch (flags, reason, etc.)
///   x15 = scratch
///   x16 = scratch
///   w17 = scratch
#[cfg(target_arch = "aarch64")]
fn emit_minimize_classifier_aarch64() -> Vec<u8> {
    use crate::aarch64::*;
    use crate::conflict_jit::{emit_and_w_imm1, emit_cmp_w_reg, emit_lsl_x_imm, emit_uxtw};

    let mut asm = Assembler::new();

    // Prologue: save fp/lr only. No callee-saved registers needed.
    // On aarch64 AAPCS, all 8 integer arguments are in x0-x7:
    //   x6 = out_classify_ptr, w7 = decision_level
    // No stack loading required.
    asm.prologue();

    // w8 = i = 0
    asm.movz_w(Reg::x(8), 0);
    // w9 = check_count = 0
    asm.movz_w(Reg::x(9), 0);

    let loop_top = asm.label();
    let loop_end = asm.label();

    asm.bind(loop_top);
    emit_cmp_w_reg(&mut asm, Reg::x(8), Reg::x(1));
    asm.b_cond(Cond::Ge, loop_end);

    // Load lit.
    crate::conflict_jit::emit_ldr_w_reg_lsl2(&mut asm, Reg::x(11), Reg::x(0), Reg::x(8));

    // var_idx = lit >> 1.
    asm.lsr_w_imm(Reg::x(12), Reg::x(11), 1);

    // Compute var_data_addr.
    emit_uxtw(&mut asm, Reg::x(15), Reg::x(12));
    emit_lsl_x_imm(&mut asm, Reg::x(15), Reg::x(15), 4);
    asm.add_x_reg(Reg::x(10), Reg::x(2), Reg::x(15));

    // Load var_level.
    asm.ldr_w_uimm(Reg::x(13), Reg::x(10), 0);

    // Level 0 -> SKIP.
    let not_level0 = asm.label();
    asm.cbnz_w(Reg::x(13), not_level0);
    // Write SKIP (0) to out_classify[i].
    // STRB WZR, [X6, X8]
    emit_strb_reg(&mut asm, Reg(31), Reg(6), Reg(8));
    let next_iter = asm.label();
    asm.b(next_iter);

    asm.bind(not_level0);

    // Load minimize_flags[var_idx].
    // LDRB W14, [X3, X12]
    emit_ldrb_reg(&mut asm, Reg(14), Reg(3), Reg(12));

    // Check cached removable or keep: (flags & (0x02 | 0x08)) != 0 -> SKIP.
    // AND w16, w14, #0x0A
    // For logical immediate 0x0A (32-bit): encode as N=0, immr=29, imms=30
    // Actually computing logical immediates is complex. Use TST alternative:
    // w16 = w14 & 0x0A. Simpler: use AND with a constant loaded.
    // Even simpler: check removable (bit 1) and keep (bit 3) separately
    // or use a 2-instruction sequence.
    // Load immediate 0x0A into w16, then AND w16, w14, w16.
    asm.movz_w(Reg::x(16), 0x0A); // MIN_REMOVABLE | MIN_KEEP
                                  // AND W17, W14, W16: encoding = 0x0a100000 | (Rm<<16) | (Rn<<5) | Rd
    emit_and_w_reg(&mut asm, Reg(17), Reg(14), Reg(16));
    let not_cached_skip = asm.label();
    asm.cbz_w(Reg::x(17), not_cached_skip);
    // Write SKIP.
    emit_strb_reg(&mut asm, Reg(31), Reg(6), Reg(8));
    asm.b(next_iter);

    asm.bind(not_cached_skip);

    // Check poison (bit 0): flags & 0x01 != 0 -> ABORT.
    emit_and_w_imm1(&mut asm, Reg::x(16), Reg::x(14));
    let not_poison = asm.label();
    asm.cbz_w(Reg::x(16), not_poison);
    // Write ABORT (1).
    asm.movz_w(Reg::x(16), u16::from(CLASSIFY_ABORT));
    emit_strb_reg(&mut asm, Reg(16), Reg(6), Reg(8));
    asm.b(next_iter);

    asm.bind(not_poison);

    // Check current decision level: level == decision_level -> ABORT.
    emit_cmp_w_reg(&mut asm, Reg::x(13), Reg::x(7));
    let not_current_level = asm.label();
    asm.b_cond(Cond::Ne, not_current_level);
    asm.movz_w(Reg::x(16), u16::from(CLASSIFY_ABORT));
    emit_strb_reg(&mut asm, Reg(16), Reg(6), Reg(8));
    asm.b(next_iter);

    asm.bind(not_current_level);

    // Load reason (u32 at offset 8).
    asm.ldr_w_uimm(Reg::x(14), Reg::x(10), 8);

    // Check decision variable (reason == NO_REASON = u32::MAX) -> ABORT.
    // CMP w14, #-1 won't work. Use CMN w14, #1 (equivalent to CMP w14, -1).
    // CMN Wn, #1: encoding 0x3100_0400 | (Rn<<5) | 0x1f
    // Actually CMN is ADDS WZR, Wn, #imm.
    // CMN W14, #1: 0x31000400 | (14<<5) | 31 = 0x3100_05df
    asm.emit_raw(0x3100_05df); // cmn w14, #1
    let not_decision = asm.label();
    asm.b_cond(Cond::Ne, not_decision);
    asm.movz_w(Reg::x(16), u16::from(CLASSIFY_ABORT));
    emit_strb_reg(&mut asm, Reg(16), Reg(6), Reg(8));
    asm.b(next_iter);

    asm.bind(not_decision);

    // Early-abort: level_seen_count[var_level] < 2 -> ABORT.
    // LDR W17, [X4, X13, LSL #2] — level_seen_count[var_level].
    // X13 holds var_level as a 32-bit value; need to extend for address calc.
    emit_uxtw(&mut asm, Reg::x(15), Reg::x(13));
    // LDR W17, [X4, X15, LSL #2]
    crate::conflict_jit::emit_ldr_w_reg_lsl2(&mut asm, Reg::x(17), Reg::x(4), Reg::x(15));
    asm.cmp_w_imm(Reg::x(17), 2);
    let not_single_lit = asm.label();
    asm.b_cond(Cond::Ge, not_single_lit);
    asm.movz_w(Reg::x(16), u16::from(CLASSIFY_ABORT));
    emit_strb_reg(&mut asm, Reg(16), Reg(6), Reg(8));
    asm.b(next_iter);

    asm.bind(not_single_lit);

    // Early-abort: trail_pos <= level_seen_trail[var_level] -> ABORT.
    // Load trail_pos (u32 at offset 4).
    asm.ldr_w_uimm(Reg::x(14), Reg::x(10), 4);
    // Load level_seen_trail[var_level] (u64).
    // LDR X16, [X5, X15, LSL #3]
    emit_ldr_x_reg_lsl3(&mut asm, Reg(16), Reg(5), Reg(15));
    // Zero-extend trail_pos to u64 for comparison.
    emit_uxtw(&mut asm, Reg::x(17), Reg::x(14));
    // CMP X17, X16 (trail_pos_u64 vs level_trail_u64).
    emit_cmp_x_reg(&mut asm, Reg(17), Reg(16));
    let not_trail_abort = asm.label();
    asm.b_cond(Cond::Gt, not_trail_abort); // Gt = unsigned greater than
                                           // trail_pos <= level_trail -> ABORT.
    asm.movz_w(Reg::x(16), u16::from(CLASSIFY_ABORT));
    emit_strb_reg(&mut asm, Reg(16), Reg(6), Reg(8));
    asm.b(next_iter);

    asm.bind(not_trail_abort);

    // Needs recursive check -> write CHECK (2).
    asm.movz_w(Reg::x(16), u16::from(CLASSIFY_CHECK));
    emit_strb_reg(&mut asm, Reg(16), Reg(6), Reg(8));
    asm.add_w_imm(Reg::x(9), Reg::x(9), 1); // check_count++

    asm.bind(next_iter);
    asm.add_w_imm(Reg::x(8), Reg::x(8), 1); // i++
    asm.b(loop_top);

    asm.bind(loop_end);

    // Return check_count in w0.
    // MOV w0, w9
    asm.emit_raw(0x2a09_03e0); // orr w0, wzr, w9

    // Epilogue: restore fp/lr and return.
    asm.epilogue();

    asm.finalize()
}

/// Emit STRB Wt, [Xn, Xm] — byte store with register offset.
/// Encoding: 0x38206800 | (Rm<<16) | (Rn<<5) | Rt
#[cfg(target_arch = "aarch64")]
fn emit_strb_reg(
    asm: &mut crate::aarch64::Assembler,
    rt: crate::aarch64::Reg,
    rn: crate::aarch64::Reg,
    rm: crate::aarch64::Reg,
) {
    let instr: u32 =
        0x3820_6800 | (u32::from(rm.0) << 16) | (u32::from(rn.0) << 5) | u32::from(rt.0);
    asm.emit_raw(instr);
}

/// Emit LDRB Wt, [Xn, Xm] — byte load with register offset.
/// Encoding: 0x38606800 | (Rm<<16) | (Rn<<5) | Rt
#[cfg(target_arch = "aarch64")]
fn emit_ldrb_reg(
    asm: &mut crate::aarch64::Assembler,
    rt: crate::aarch64::Reg,
    rn: crate::aarch64::Reg,
    rm: crate::aarch64::Reg,
) {
    let instr: u32 =
        0x3860_6800 | (u32::from(rm.0) << 16) | (u32::from(rn.0) << 5) | u32::from(rt.0);
    asm.emit_raw(instr);
}

/// Emit AND Wd, Wn, Wm — register AND.
/// Encoding: 0x0a000000 | (Rm<<16) | (Rn<<5) | Rd
#[cfg(target_arch = "aarch64")]
fn emit_and_w_reg(
    asm: &mut crate::aarch64::Assembler,
    rd: crate::aarch64::Reg,
    rn: crate::aarch64::Reg,
    rm: crate::aarch64::Reg,
) {
    let instr: u32 =
        0x0a00_0000 | (u32::from(rm.0) << 16) | (u32::from(rn.0) << 5) | u32::from(rd.0);
    asm.emit_raw(instr);
}

/// Emit LDR Xt, [Xn, Xm, LSL #3] — 64-bit register-offset load, scaled.
/// Encoding: size=11 V=0 opc=01 option=011 S=1 = 0xf8607800
#[cfg(target_arch = "aarch64")]
fn emit_ldr_x_reg_lsl3(
    asm: &mut crate::aarch64::Assembler,
    rt: crate::aarch64::Reg,
    rn: crate::aarch64::Reg,
    rm: crate::aarch64::Reg,
) {
    let instr: u32 =
        0xf860_7800 | (u32::from(rm.0) << 16) | (u32::from(rn.0) << 5) | u32::from(rt.0);
    asm.emit_raw(instr);
}

/// Emit CMP Xn, Xm (SUBS XZR, Xn, Xm) — 64-bit register compare.
/// Encoding: 0xeb00001f | (Rm<<16) | (Rn<<5)
#[cfg(target_arch = "aarch64")]
fn emit_cmp_x_reg(
    asm: &mut crate::aarch64::Assembler,
    rn: crate::aarch64::Reg,
    rm: crate::aarch64::Reg,
) {
    let instr: u32 = 0xeb00_001f | (u32::from(rm.0) << 16) | (u32::from(rn.0) << 5);
    asm.emit_raw(instr);
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
        fn new(level: u32, trail_pos: u32, reason: u32) -> Self {
            Self {
                level,
                trail_pos,
                reason,
                flags: 0,
                _pad: [0; 3],
            }
        }
    }

    const _: () = assert!(size_of::<TestVarData>() == 16);

    /// Run interpreter and (on aarch64) JIT, verifying identical results.
    fn run_and_compare(
        lits: &[u32],
        var_data: &[TestVarData],
        min_flags: &[u8],
        level_seen_count: &[u32],
        level_seen_trail: &[u64],
        decision_level: u32,
    ) -> Vec<u8> {
        let mut interp_out = vec![0u8; lits.len()];
        let interp_count = unsafe {
            classify_minimize_interpreter(
                lits,
                var_data.as_ptr().cast::<u8>(),
                min_flags.as_ptr(),
                level_seen_count.as_ptr(),
                level_seen_trail.as_ptr(),
                &mut interp_out,
                decision_level,
            )
        };

        #[cfg(target_arch = "aarch64")]
        {
            let classifier =
                compile_minimize_classifier().expect("JIT compilation should succeed on aarch64");
            let mut jit_out = vec![0u8; lits.len()];
            let jit_count = unsafe {
                classifier.classify(
                    lits,
                    var_data.as_ptr().cast::<u8>(),
                    min_flags.as_ptr(),
                    level_seen_count.as_ptr(),
                    level_seen_trail.as_ptr(),
                    &mut jit_out,
                    decision_level,
                )
            };

            assert_eq!(
                interp_count, jit_count,
                "check_count mismatch: interp={interp_count} jit={jit_count}"
            );
            assert_eq!(
                interp_out, jit_out,
                "classification mismatch: interp={interp_out:?} jit={jit_out:?}"
            );
        }

        let _ = interp_count;
        interp_out
    }

    #[test]
    fn test_minimize_classify_empty() {
        let result = run_and_compare(&[], &[], &[], &[], &[], 5);
        assert!(result.is_empty());
    }

    #[test]
    fn test_minimize_classify_level0_skip() {
        // Variable 0 at level 0 -> SKIP.
        let var_data = vec![TestVarData::new(0, 0, 42)];
        let min_flags = vec![0u8];
        let level_seen_count = vec![0u32; 10];
        let level_seen_trail = vec![u64::MAX; 10];
        let lits = vec![0u32]; // var 0, positive

        let result = run_and_compare(
            &lits,
            &var_data,
            &min_flags,
            &level_seen_count,
            &level_seen_trail,
            5,
        );
        assert_eq!(result, vec![CLASSIFY_SKIP]);
    }

    #[test]
    fn test_minimize_classify_cached_removable() {
        // Variable 1 at level 3, has MIN_REMOVABLE set -> SKIP.
        let var_data = vec![TestVarData::new(0, 0, 0), TestVarData::new(3, 5, 100)];
        let min_flags = vec![0u8, MIN_REMOVABLE];
        let level_seen_count = vec![0u32; 10];
        let level_seen_trail = vec![u64::MAX; 10];
        let lits = vec![2u32]; // var 1, positive

        let result = run_and_compare(
            &lits,
            &var_data,
            &min_flags,
            &level_seen_count,
            &level_seen_trail,
            5,
        );
        assert_eq!(result, vec![CLASSIFY_SKIP]);
    }

    #[test]
    fn test_minimize_classify_cached_keep() {
        // Variable 1 at level 3, has MIN_KEEP set -> SKIP.
        let var_data = vec![TestVarData::new(0, 0, 0), TestVarData::new(3, 5, 100)];
        let min_flags = vec![0u8, MIN_KEEP];
        let level_seen_count = vec![0u32; 10];
        let level_seen_trail = vec![u64::MAX; 10];
        let lits = vec![2u32]; // var 1, positive

        let result = run_and_compare(
            &lits,
            &var_data,
            &min_flags,
            &level_seen_count,
            &level_seen_trail,
            5,
        );
        assert_eq!(result, vec![CLASSIFY_SKIP]);
    }

    #[test]
    fn test_minimize_classify_poison_abort() {
        // Variable 1 at level 3, has MIN_POISON set -> ABORT.
        let var_data = vec![TestVarData::new(0, 0, 0), TestVarData::new(3, 5, 100)];
        let min_flags = vec![0u8, MIN_POISON];
        let level_seen_count = vec![5u32; 10]; // enough seen
        let level_seen_trail = vec![0u64; 10];
        let lits = vec![2u32]; // var 1, positive

        let result = run_and_compare(
            &lits,
            &var_data,
            &min_flags,
            &level_seen_count,
            &level_seen_trail,
            5,
        );
        assert_eq!(result, vec![CLASSIFY_ABORT]);
    }

    #[test]
    fn test_minimize_classify_current_level_abort() {
        // Variable 1 at decision level 5 -> ABORT.
        let var_data = vec![TestVarData::new(0, 0, 0), TestVarData::new(5, 10, 100)];
        let min_flags = vec![0u8; 2];
        let level_seen_count = vec![5u32; 10];
        let level_seen_trail = vec![0u64; 10];
        let lits = vec![2u32]; // var 1, positive

        let result = run_and_compare(
            &lits,
            &var_data,
            &min_flags,
            &level_seen_count,
            &level_seen_trail,
            5,
        );
        assert_eq!(result, vec![CLASSIFY_ABORT]);
    }

    #[test]
    fn test_minimize_classify_decision_var_abort() {
        // Variable 1 at level 3, reason = NO_REASON (decision) -> ABORT.
        let var_data = vec![TestVarData::new(0, 0, 0), TestVarData::new(3, 5, NO_REASON)];
        let min_flags = vec![0u8; 2];
        let level_seen_count = vec![5u32; 10];
        let level_seen_trail = vec![0u64; 10];
        let lits = vec![2u32]; // var 1, positive

        let result = run_and_compare(
            &lits,
            &var_data,
            &min_flags,
            &level_seen_count,
            &level_seen_trail,
            5,
        );
        assert_eq!(result, vec![CLASSIFY_ABORT]);
    }

    #[test]
    fn test_minimize_classify_single_lit_abort() {
        // Variable 1 at level 3, but level_seen_count[3] = 1 -> ABORT.
        let var_data = vec![TestVarData::new(0, 0, 0), TestVarData::new(3, 5, 100)];
        let min_flags = vec![0u8; 2];
        let mut level_seen_count = vec![5u32; 10];
        level_seen_count[3] = 1; // single literal on level 3
        let level_seen_trail = vec![0u64; 10];
        let lits = vec![2u32]; // var 1, positive

        let result = run_and_compare(
            &lits,
            &var_data,
            &min_flags,
            &level_seen_count,
            &level_seen_trail,
            5,
        );
        assert_eq!(result, vec![CLASSIFY_ABORT]);
    }

    #[test]
    fn test_minimize_classify_trail_pos_abort() {
        // Variable 1 at level 3, trail_pos=5, but level_seen_trail[3]=5 -> ABORT.
        // (trail_pos <= level_trail means abort)
        let var_data = vec![TestVarData::new(0, 0, 0), TestVarData::new(3, 5, 100)];
        let min_flags = vec![0u8; 2];
        let level_seen_count = vec![5u32; 10];
        let mut level_seen_trail = vec![0u64; 10];
        level_seen_trail[3] = 5; // trail_pos(5) <= 5 -> abort
        let lits = vec![2u32]; // var 1, positive

        let result = run_and_compare(
            &lits,
            &var_data,
            &min_flags,
            &level_seen_count,
            &level_seen_trail,
            5,
        );
        assert_eq!(result, vec![CLASSIFY_ABORT]);
    }

    #[test]
    fn test_minimize_classify_check() {
        // Variable 1 at level 3, trail_pos=10, reason=100, no flags,
        // level_seen_count[3]=5, level_seen_trail[3]=2 -> CHECK.
        let var_data = vec![TestVarData::new(0, 0, 0), TestVarData::new(3, 10, 100)];
        let min_flags = vec![0u8; 2];
        let level_seen_count = vec![5u32; 10];
        let mut level_seen_trail = vec![0u64; 10];
        level_seen_trail[3] = 2;
        let lits = vec![2u32]; // var 1, positive

        let result = run_and_compare(
            &lits,
            &var_data,
            &min_flags,
            &level_seen_count,
            &level_seen_trail,
            5,
        );
        assert_eq!(result, vec![CLASSIFY_CHECK]);
    }

    #[test]
    fn test_minimize_classify_mixed() {
        // Multiple literals with different classifications.
        let var_data = vec![
            TestVarData::new(0, 0, 42),        // var 0: level 0 -> SKIP
            TestVarData::new(3, 10, 100),      // var 1: level 3, needs check -> CHECK
            TestVarData::new(5, 20, 200),      // var 2: level 5 (current) -> ABORT
            TestVarData::new(2, 3, NO_REASON), // var 3: decision var -> ABORT
            TestVarData::new(3, 8, 150),       // var 4: level 3, trail_pos ok -> CHECK
        ];
        let min_flags = vec![0u8; 5];
        let mut level_seen_count = vec![5u32; 10];
        level_seen_count[0] = 0;
        let mut level_seen_trail = vec![0u64; 10];
        level_seen_trail[3] = 2; // trail positions 10, 8 are both > 2

        // lits: var0+, var1-, var2+, var3+, var4-
        let lits = vec![0u32, 3, 4, 6, 9];

        let result = run_and_compare(
            &lits,
            &var_data,
            &min_flags,
            &level_seen_count,
            &level_seen_trail,
            5,
        );
        assert_eq!(
            result,
            vec![
                CLASSIFY_SKIP,
                CLASSIFY_CHECK,
                CLASSIFY_ABORT,
                CLASSIFY_ABORT,
                CLASSIFY_CHECK
            ]
        );
    }

    #[test]
    fn test_minimize_classify_check_count() {
        // Verify the return value (check_count).
        let var_data = [
            TestVarData::new(0, 0, 42),   // SKIP
            TestVarData::new(3, 10, 100), // CHECK
            TestVarData::new(3, 12, 200), // CHECK
            TestVarData::new(3, 14, 300), // CHECK
        ];
        let min_flags = [0u8; 4];
        let level_seen_count = [5u32; 10];
        let mut level_seen_trail = [0u64; 10];
        level_seen_trail[3] = 2;

        let lits = vec![0u32, 2, 4, 6];

        let mut out = vec![0u8; 4];
        let count = unsafe {
            classify_minimize_interpreter(
                &lits,
                var_data.as_ptr().cast::<u8>(),
                min_flags.as_ptr(),
                level_seen_count.as_ptr(),
                level_seen_trail.as_ptr(),
                &mut out,
                5,
            )
        };
        assert_eq!(count, 3); // 3 CHECK results

        #[cfg(target_arch = "aarch64")]
        {
            let classifier = compile_minimize_classifier().unwrap();
            let mut jit_out = vec![0u8; 4];
            let jit_count = unsafe {
                classifier.classify(
                    &lits,
                    var_data.as_ptr().cast::<u8>(),
                    min_flags.as_ptr(),
                    level_seen_count.as_ptr(),
                    level_seen_trail.as_ptr(),
                    &mut jit_out,
                    5,
                )
            };
            assert_eq!(jit_count, 3);
        }
    }

    #[test]
    fn test_minimize_classify_many_literals() {
        // Stress test with 100 variables.
        let num_vars = 100;
        let decision_level = 10u32;
        let mut var_data = Vec::with_capacity(num_vars);
        let mut min_flags = vec![0u8; num_vars];

        for (i, flag) in min_flags.iter_mut().enumerate().take(num_vars) {
            let (level, trail_pos, reason) = match i % 6 {
                0 => (0u32, i as u32, 42),                 // level 0 -> SKIP
                1 => (3, 10 + i as u32, 100),              // normal -> CHECK
                2 => (decision_level, 20 + i as u32, 200), // current level -> ABORT
                3 => (4, 5 + i as u32, NO_REASON),         // decision -> ABORT
                4 => {
                    *flag = MIN_REMOVABLE;
                    (3, 10 + i as u32, 100) // removable -> SKIP
                }
                5 => {
                    *flag = MIN_POISON;
                    (3, 10 + i as u32, 100) // poison -> ABORT
                }
                _ => unreachable!(),
            };
            var_data.push(TestVarData::new(level, trail_pos, reason));
        }

        let level_seen_count = vec![5u32; (decision_level as usize) + 1];
        let mut level_seen_trail = vec![0u64; (decision_level as usize) + 1];
        level_seen_trail[3] = 2;
        level_seen_trail[4] = 2;

        let lits: Vec<u32> = (0..num_vars as u32).map(|v| v * 2).collect();

        let result = run_and_compare(
            &lits,
            &var_data,
            &min_flags,
            &level_seen_count,
            &level_seen_trail,
            decision_level,
        );

        // Verify expected pattern.
        for (i, &class) in result.iter().enumerate() {
            let expected = match i % 6 {
                0 => CLASSIFY_SKIP,  // level 0
                1 => CLASSIFY_CHECK, // normal
                2 => CLASSIFY_ABORT, // current level
                3 => CLASSIFY_ABORT, // decision var
                4 => CLASSIFY_SKIP,  // removable
                5 => CLASSIFY_ABORT, // poison
                _ => unreachable!(),
            };
            assert_eq!(
                class, expected,
                "mismatch at index {i}: got {class}, expected {expected}"
            );
        }
    }

    #[test]
    fn test_minimize_classify_trail_pos_boundary() {
        // Test exact boundary: trail_pos == level_trail -> ABORT,
        // trail_pos == level_trail + 1 -> CHECK.
        let var_data = vec![
            TestVarData::new(3, 5, 100), // var 0: trail_pos=5
            TestVarData::new(3, 6, 100), // var 1: trail_pos=6
        ];
        let min_flags = vec![0u8; 2];
        let level_seen_count = vec![5u32; 10];
        let mut level_seen_trail = vec![0u64; 10];
        level_seen_trail[3] = 5; // boundary at 5

        let lits = vec![0u32, 2]; // var 0, var 1

        let result = run_and_compare(
            &lits,
            &var_data,
            &min_flags,
            &level_seen_count,
            &level_seen_trail,
            10,
        );
        assert_eq!(result[0], CLASSIFY_ABORT); // trail_pos(5) <= 5
        assert_eq!(result[1], CLASSIFY_CHECK); // trail_pos(6) > 5
    }
}
