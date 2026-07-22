// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Native machine code generation for theory bound propagation.
//!
//! Compiles per-variable atom bound checks into aarch64/x86_64 machine code.
//! Each compiled function takes the variable's current bounds (lb_numer,
//! lb_denom, ub_numer, ub_denom) plus strictness flags as register arguments,
//! and returns a u64 bitmap encoding (implied_true, implied_false) per atom.
//!
//! This eliminates from the hot path:
//! - Loop control overhead (iterator, is_small branches)
//! - Result Vec allocation
//! - Branch mispredictions from atom type dispatch
//!
//! Atom bound values (numerator, denominator) are baked as immediates.
//! Cross-multiply comparison uses 64-bit MUL when operands fit in 32 bits,
//! or 128-bit (MUL+SMULH) otherwise.
//!
//! ## Calling convention
//!
//! ```text
//! extern "C" fn(
//!     lb_numer: i64,   // x0/rdi: lower bound numerator
//!     lb_denom: i64,   // x1/rsi: lower bound denominator (0 = no lb)
//!     ub_numer: i64,   // x2/rdx: upper bound numerator
//!     ub_denom: i64,   // x3/rcx: upper bound denominator (0 = no ub)
//!     lb_strict: i64,  // x4/r8:  1 if lb is strict, 0 otherwise
//!     ub_strict: i64,  // x5/r9:  1 if ub is strict, 0 otherwise
//! ) -> u64             // bitmap: 2 bits per atom (bit 2*i = implied_true, bit 2*i+1 = implied_false)
//! ```
//!
//! ## Bitmap encoding
//!
//! For atom index `i`:
//! - Bit `2*i`:   set if atom is implied TRUE
//! - Bit `2*i+1`: set if atom is implied FALSE
//!
//! Maximum 32 atoms per variable (64-bit bitmap, 2 bits each).

use crate::executable::ExecutableMemory;
use crate::theory_prop::{PropagationResult, SmallBound, VarPropagator};
// `BoundAtom` is only referenced by the native code-emitters, which are gated
// to the two native ISAs; on wasm32 it would otherwise be an unused import.
#[cfg(any(target_arch = "aarch64", target_arch = "x86_64"))]
use crate::theory_prop::BoundAtom;
#[cfg(test)]
use crate::JitError;

/// Maximum number of atoms per variable for native compilation.
/// Limited by the 64-bit return bitmap (2 bits per atom).
const MAX_NATIVE_ATOMS: usize = 32;

/// Type alias for the compiled bound check function.
///
/// Parameters (in register order):
///   lb_numer:  i64 -- lower bound numerator
///   lb_denom:  i64 -- lower bound denominator (0 = unbounded)
///   ub_numer:  i64 -- upper bound numerator
///   ub_denom:  i64 -- upper bound denominator (0 = unbounded)
///   lb_strict: i64 -- 1 if lower bound is strict, 0 otherwise
///   ub_strict: i64 -- 1 if upper bound is strict, 0 otherwise
///
/// Returns: u64 bitmap with 2 bits per atom.
type TheoryPropFn = unsafe extern "C" fn(i64, i64, i64, i64, i64, i64) -> u64;

/// A natively compiled per-variable bound propagation function.
///
/// When available, this replaces the interpreted `VarPropagator::check_bounds()`
/// loop with a single function call that returns a bitmap of implied atoms.
///
/// The backing executable memory is shared (`Arc`): all variables of one
/// compilation batch live in a single mapping (Fix A1 — one mmap + one
/// icache flush per batch instead of one per variable), and clones of the
/// propagator (structural-snapshot persistence) share the same code region.
#[derive(Clone)]
pub struct NativeVarPropagator {
    /// The compiled function.
    func: TheoryPropFn,
    /// Total number of atoms (upper + lower) compiled.
    num_atoms: usize,
    /// Atom indices in order — maps bitmap position to caller's atom_index.
    /// `atom_indices[i]` is the `atom_index` for the atom at bitmap position `i`.
    atom_indices: Vec<u32>,
    /// Backing executable memory, shared across the compilation batch.
    _executable: std::sync::Arc<ExecutableMemory>,
}

// SAFETY: The compiled function pointer points into immutable executable memory.
// The function is pure: it takes integer values and returns a bitmap, with no
// side effects. The ExecutableMemory backing is process-global (mmap'd).
unsafe impl Send for NativeVarPropagator {}
unsafe impl Sync for NativeVarPropagator {}

impl NativeVarPropagator {
    /// Invoke the native function and decode the bitmap into propagation results.
    ///
    /// # Arguments
    ///
    /// * `lb` - Current lower bound (None = unbounded).
    /// * `ub` - Current upper bound (None = unbounded).
    /// * `results` - Output buffer for propagation results (cleared first).
    pub fn check_bounds(
        &self,
        lb: Option<SmallBound>,
        ub: Option<SmallBound>,
        results: &mut Vec<PropagationResult>,
    ) {
        results.clear();

        let (lb_numer, lb_denom, lb_strict) = match lb {
            Some(b) => (b.numer, b.denom, if b.strict { 1i64 } else { 0i64 }),
            None => (0i64, 0i64, 0i64), // denom=0 signals unbounded
        };
        let (ub_numer, ub_denom, ub_strict) = match ub {
            Some(b) => (b.numer, b.denom, if b.strict { 1i64 } else { 0i64 }),
            None => (0i64, 0i64, 0i64),
        };

        // SAFETY: func is a valid function pointer in executable memory with the
        // correct ABI. All arguments are plain integers.
        let bitmap =
            unsafe { (self.func)(lb_numer, lb_denom, ub_numer, ub_denom, lb_strict, ub_strict) };

        // Decode bitmap into results.
        for i in 0..self.num_atoms {
            let bits = (bitmap >> (2 * i)) & 3;
            if bits & 1 != 0 {
                results.push(PropagationResult {
                    atom_index: self.atom_indices[i],
                    implied_value: true,
                });
            }
            if bits & 2 != 0 {
                results.push(PropagationResult {
                    atom_index: self.atom_indices[i],
                    implied_value: false,
                });
            }
        }
    }

    /// Number of atoms compiled in this function.
    pub fn num_atoms(&self) -> usize {
        self.num_atoms
    }
}

/// Emit native code bytes for a `VarPropagator`, if it is eligible.
///
/// Returns `None` if:
/// - Too many atoms (> 32, exceeding bitmap capacity)
/// - Any atom is non-small (must use interpreted fallback)
/// - Platform not supported
///
/// Returns `Some((code, atom_indices))` on success; `atom_indices` maps
/// bitmap positions to the caller's atom indices.
fn emit_native_propagator_code(prop: &VarPropagator) -> Option<(Vec<u8>, Vec<u32>)> {
    let total = prop.upper_atoms.len() + prop.lower_atoms.len();
    if total == 0 || total > MAX_NATIVE_ATOMS {
        return None;
    }

    // All atoms must be small for the native path.
    let all_small =
        prop.upper_atoms.iter().all(|a| a.is_small) && prop.lower_atoms.iter().all(|a| a.is_small);
    if !all_small {
        return None;
    }

    #[cfg(not(any(target_arch = "aarch64", target_arch = "x86_64")))]
    {
        None
    }

    #[cfg(any(target_arch = "aarch64", target_arch = "x86_64"))]
    {
        // Collect atoms in order: upper atoms first, then lower atoms.
        // This matches the bitmap bit assignment.
        let mut atoms_in_order: Vec<&BoundAtom> = Vec::with_capacity(total);
        let mut atom_indices: Vec<u32> = Vec::with_capacity(total);
        let mut is_upper: Vec<bool> = Vec::with_capacity(total);

        for atom in &prop.upper_atoms {
            atoms_in_order.push(atom);
            atom_indices.push(atom.atom_index);
            is_upper.push(true);
        }
        for atom in &prop.lower_atoms {
            atoms_in_order.push(atom);
            atom_indices.push(atom.atom_index);
            is_upper.push(false);
        }

        let code = emit_theory_prop_function(&atoms_in_order, &is_upper);
        Some((code, atom_indices))
    }
}

/// Function entry alignment within a batched executable mapping.
#[cfg(any(target_arch = "aarch64", target_arch = "x86_64"))]
const NATIVE_FN_ALIGN: usize = 16;

/// Pad `blob` with NOP bytes so the next function entry is 16-byte aligned.
#[cfg(any(target_arch = "aarch64", target_arch = "x86_64"))]
fn pad_to_fn_align(blob: &mut Vec<u8>) {
    #[cfg(target_arch = "aarch64")]
    {
        // aarch64 NOP = 0xD503201F (little-endian bytes). Code length is
        // always a multiple of 4, so 4-byte NOPs reach 16-byte alignment.
        while !blob.len().is_multiple_of(NATIVE_FN_ALIGN) {
            blob.extend_from_slice(&0xD503_201Fu32.to_le_bytes());
        }
    }
    #[cfg(target_arch = "x86_64")]
    {
        // x86_64 single-byte NOP = 0x90.
        while blob.len() % NATIVE_FN_ALIGN != 0 {
            blob.push(0x90);
        }
    }
}

/// Attempt to compile a single VarPropagator into native machine code,
/// backed by its own executable mapping.
///
/// Used by differential tests; production batches all variables into one
/// mapping via [`compile_native_propagators`].
#[cfg(test)]
pub(crate) fn compile_native_propagator(
    prop: &VarPropagator,
) -> Result<Option<NativeVarPropagator>, JitError> {
    let Some((code, atom_indices)) = emit_native_propagator_code(prop) else {
        return Ok(None);
    };
    let num_atoms = atom_indices.len();
    let executable = std::sync::Arc::new(ExecutableMemory::new(&code)?);
    let fn_ptr = executable.as_ptr();

    // SAFETY: fn_ptr points to the start of our compiled function in
    // executable memory. The function has extern "C" ABI with signature
    // fn(i64, i64, i64, i64, i64, i64) -> u64. The ExecutableMemory is
    // kept alive by the Arc for the propagator's lifetime.
    let func: TheoryPropFn = unsafe { std::mem::transmute::<*const u8, TheoryPropFn>(fn_ptr) };

    Ok(Some(NativeVarPropagator {
        func,
        num_atoms,
        atom_indices,
        _executable: executable,
    }))
}

// ---------------------------------------------------------------------------
// aarch64 code generation
// ---------------------------------------------------------------------------

/// Minimal aarch64 assembler for theory propagation functions.
///
/// Instruction subset: 64-bit arithmetic, MUL/SMULH for i128 cross-multiply,
/// conditional set (CSET), ORR for bitmap accumulation.
#[cfg(target_arch = "aarch64")]
struct TheoryAsm {
    code: Vec<u32>,
    labels: Vec<Option<u32>>,
    fixups: Vec<TheoryFixup>,
}

#[cfg(target_arch = "aarch64")]
struct TheoryFixup {
    offset: u32,
    label: TheoryLabel,
    kind: TheoryFixupKind,
}

#[cfg(target_arch = "aarch64")]
#[derive(Clone, Copy)]
struct TheoryLabel(u32);

#[cfg(target_arch = "aarch64")]
#[derive(Clone, Copy)]
enum TheoryFixupKind {
    /// B.cond / CBZ: imm19 in bits [23:5].
    Imm19,
    /// B: imm26 in bits [25:0].
    Imm26,
}

#[cfg(target_arch = "aarch64")]
impl TheoryAsm {
    fn new() -> Self {
        Self {
            code: Vec::with_capacity(256),
            labels: Vec::new(),
            fixups: Vec::new(),
        }
    }

    fn emit(&mut self, instr: u32) {
        self.code.push(instr);
    }

    fn label(&mut self) -> TheoryLabel {
        let id = self.labels.len() as u32;
        self.labels.push(None);
        TheoryLabel(id)
    }

    fn bind(&mut self, label: TheoryLabel) {
        let offset = self.code.len() as u32;
        debug_assert!(
            self.labels[label.0 as usize].is_none(),
            "label already bound"
        );
        self.labels[label.0 as usize] = Some(offset);
    }

    fn emit_branch(&mut self, base: u32, label: TheoryLabel, kind: TheoryFixupKind) {
        self.fixups.push(TheoryFixup {
            offset: self.code.len() as u32,
            label,
            kind,
        });
        self.code.push(base);
    }

    /// STP x29, x30, [sp, #-16]! ; MOV x29, sp
    fn prologue(&mut self) {
        self.emit(0xa9bf7bfd);
        self.emit(0x910003fd);
    }

    /// LDP x29, x30, [sp], #16 ; RET
    fn epilogue(&mut self) {
        self.emit(0xa8c17bfd);
        self.emit(0xd65f03c0);
    }

    /// MOV Xd, Xm (alias for ORR Xd, XZR, Xm)
    fn mov_x(&mut self, rd: u8, rm: u8) {
        self.emit(0xaa0003e0 | (u32::from(rm) << 16) | u32::from(rd));
    }

    /// MOVZ Xd, #imm16 (shift=0)
    fn movz_x(&mut self, rd: u8, imm16: u16) {
        self.emit(0xd2800000 | (u32::from(imm16) << 5) | u32::from(rd));
    }

    /// MOVZ Xd, #imm16, LSL #16
    fn movz_x_lsl16(&mut self, rd: u8, imm16: u16) {
        self.emit(0xd2a00000 | (u32::from(imm16) << 5) | u32::from(rd));
    }

    /// MOVZ Xd, #imm16, LSL #32
    fn movz_x_lsl32(&mut self, rd: u8, imm16: u16) {
        self.emit(0xd2c00000 | (u32::from(imm16) << 5) | u32::from(rd));
    }

    /// MOVZ Xd, #imm16, LSL #48
    fn movz_x_lsl48(&mut self, rd: u8, imm16: u16) {
        self.emit(0xd2e00000 | (u32::from(imm16) << 5) | u32::from(rd));
    }

    /// MOVK Xd, #imm16 (shift=0)
    #[allow(dead_code)] // ISA completeness: aarch64 instruction variant for future use
    fn movk_x(&mut self, rd: u8, imm16: u16) {
        self.emit(0xf2800000 | (u32::from(imm16) << 5) | u32::from(rd));
    }

    /// MOVK Xd, #imm16, LSL #16
    fn movk_x_lsl16(&mut self, rd: u8, imm16: u16) {
        self.emit(0xf2a00000 | (u32::from(imm16) << 5) | u32::from(rd));
    }

    /// MOVK Xd, #imm16, LSL #32
    fn movk_x_lsl32(&mut self, rd: u8, imm16: u16) {
        self.emit(0xf2c00000 | (u32::from(imm16) << 5) | u32::from(rd));
    }

    /// MOVK Xd, #imm16, LSL #48
    fn movk_x_lsl48(&mut self, rd: u8, imm16: u16) {
        self.emit(0xf2e00000 | (u32::from(imm16) << 5) | u32::from(rd));
    }

    /// MOVN Xd, #imm16 (shift=0)
    fn movn_x(&mut self, rd: u8, imm16: u16) {
        self.emit(0x92800000 | (u32::from(imm16) << 5) | u32::from(rd));
    }

    /// Load a 64-bit immediate into Xd.
    fn mov_imm64(&mut self, rd: u8, value: i64) {
        let v = value as u64;

        // Small positive
        if (0..=0xFFFF).contains(&value) {
            self.movz_x(rd, v as u16);
            return;
        }

        // Small negative
        if (-0x10000..0).contains(&value) {
            self.movn_x(rd, (!v) as u16);
            return;
        }

        // General case: MOVZ + MOVK
        let h0 = v as u16;
        let h1 = (v >> 16) as u16;
        let h2 = (v >> 32) as u16;
        let h3 = (v >> 48) as u16;

        // Start with the lowest non-zero halfword via MOVZ
        if h0 != 0 || (h1 == 0 && h2 == 0 && h3 == 0) {
            self.movz_x(rd, h0);
        } else if h1 != 0 {
            self.movz_x_lsl16(rd, h1);
        } else if h2 != 0 {
            self.movz_x_lsl32(rd, h2);
        } else {
            self.movz_x_lsl48(rd, h3);
        }

        // Fill remaining non-zero halfwords via MOVK
        if h0 != 0 || (h1 == 0 && h2 == 0 && h3 == 0) {
            if h1 != 0 {
                self.movk_x_lsl16(rd, h1);
            }
            if h2 != 0 {
                self.movk_x_lsl32(rd, h2);
            }
            if h3 != 0 {
                self.movk_x_lsl48(rd, h3);
            }
        } else if h1 != 0 {
            if h2 != 0 {
                self.movk_x_lsl32(rd, h2);
            }
            if h3 != 0 {
                self.movk_x_lsl48(rd, h3);
            }
        } else if h2 != 0 {
            if h3 != 0 {
                self.movk_x_lsl48(rd, h3);
            }
        }
    }

    /// MUL Xd, Xn, Xm (64-bit multiply, low 64 bits of result)
    fn mul_x(&mut self, rd: u8, rn: u8, rm: u8) {
        // MUL is MADD with Ra=XZR (register 31)
        self.emit(0x9b007c00 | (u32::from(rm) << 16) | (u32::from(rn) << 5) | u32::from(rd));
    }

    /// SMULH Xd, Xn, Xm (signed 64x64->128, high 64 bits)
    fn smulh_x(&mut self, rd: u8, rn: u8, rm: u8) {
        self.emit(0x9b407c00 | (u32::from(rm) << 16) | (u32::from(rn) << 5) | u32::from(rd));
    }

    /// SUBS Xd, Xn, Xm (sets flags)
    fn subs_x(&mut self, rd: u8, rn: u8, rm: u8) {
        self.emit(0xeb000000 | (u32::from(rm) << 16) | (u32::from(rn) << 5) | u32::from(rd));
    }

    /// CMP Xn, Xm (alias SUBS XZR, Xn, Xm)
    fn cmp_x(&mut self, rn: u8, rm: u8) {
        self.subs_x(31, rn, rm);
    }

    /// CMP Xn, #0 (alias SUBS XZR, Xn, #0)
    fn cmp_x_zero(&mut self, rn: u8) {
        // SUBS XZR, Xn, #0
        self.emit(0xf100001f | (u32::from(rn) << 5));
    }

    /// ORR Xd, Xn, Xm
    fn orr_x(&mut self, rd: u8, rn: u8, rm: u8) {
        self.emit(0xaa000000 | (u32::from(rm) << 16) | (u32::from(rn) << 5) | u32::from(rd));
    }

    /// B.cond label
    fn b_cond(&mut self, cond: u8, label: TheoryLabel) {
        self.emit_branch(0x54000000 | u32::from(cond), label, TheoryFixupKind::Imm19);
    }

    /// B label (unconditional)
    fn b(&mut self, label: TheoryLabel) {
        self.emit_branch(0x14000000, label, TheoryFixupKind::Imm26);
    }

    /// CBZ Xn, label
    fn cbz_x(&mut self, rn: u8, label: TheoryLabel) {
        self.emit_branch(0xb4000000 | u32::from(rn), label, TheoryFixupKind::Imm19);
    }

    /// CBNZ Xn, label
    #[allow(dead_code)] // ISA completeness: aarch64 instruction variant for future use
    fn cbnz_x(&mut self, rn: u8, label: TheoryLabel) {
        self.emit_branch(0xb5000000 | u32::from(rn), label, TheoryFixupKind::Imm19);
    }

    fn finalize(mut self) -> Vec<u8> {
        for fixup in &self.fixups {
            // INVARIANT: every theory-prop label returned by `new_label()`
            // must be bound via `bind()` before `finalize()`. This is an
            // assembler-internal invariant, not a user-input error.
            let target = self.labels[fixup.label.0 as usize]
                .expect("invariant: all emitted theory-prop labels must be bound before finalize");
            let delta = target as i32 - fixup.offset as i32;

            match fixup.kind {
                TheoryFixupKind::Imm19 => {
                    assert!(
                        (-(1 << 18)..(1 << 18)).contains(&delta),
                        "branch offset out of imm19 range: {delta}"
                    );
                    let imm19 = (delta as u32) & 0x7ffff;
                    self.code[fixup.offset as usize] |= imm19 << 5;
                }
                TheoryFixupKind::Imm26 => {
                    assert!(
                        (-(1 << 25)..(1 << 25)).contains(&delta),
                        "branch offset out of imm26 range: {delta}"
                    );
                    let imm26 = (delta as u32) & 0x3ffffff;
                    self.code[fixup.offset as usize] |= imm26;
                }
            }
        }

        let mut bytes = Vec::with_capacity(self.code.len() * 4);
        for &instr in &self.code {
            bytes.extend_from_slice(&instr.to_le_bytes());
        }
        bytes
    }
}

// Condition codes — ISA completeness: all standard AArch64 condition codes defined
// for the assembler. Not all are used in current theory propagation codegen.
#[cfg(target_arch = "aarch64")]
#[allow(dead_code)] // ISA completeness
const COND_EQ: u8 = 0b0000;
#[cfg(target_arch = "aarch64")]
const COND_NE: u8 = 0b0001;
#[cfg(target_arch = "aarch64")]
const COND_LO: u8 = 0b0011; // unsigned lower (carry clear) — for low-word of i128
#[cfg(target_arch = "aarch64")]
const COND_HI: u8 = 0b1000; // unsigned higher — for low-word of i128
#[cfg(target_arch = "aarch64")]
#[allow(dead_code)] // ISA completeness
const COND_LS: u8 = 0b1001; // unsigned lower or same
#[cfg(target_arch = "aarch64")]
#[allow(dead_code)] // ISA completeness
const COND_HS: u8 = 0b0010; // unsigned higher or same (carry set)
#[cfg(target_arch = "aarch64")]
const COND_LT: u8 = 0b1011; // signed less than — for high-word of i128
#[cfg(target_arch = "aarch64")]
const COND_GT: u8 = 0b1100; // signed greater than — for high-word of i128
#[cfg(target_arch = "aarch64")]
#[allow(dead_code)] // ISA completeness
const COND_LE: u8 = 0b1101;
#[cfg(target_arch = "aarch64")]
#[allow(dead_code)] // ISA completeness
const COND_GE: u8 = 0b1010;

// Register assignments for the compiled function:
//
// Arguments (caller-provided):
//   x0 = lb_numer
//   x1 = lb_denom (0 = no lower bound)
//   x2 = ub_numer
//   x3 = ub_denom (0 = no upper bound)
//   x4 = lb_strict (1 = strict, 0 = non-strict)
//   x5 = ub_strict (1 = strict, 0 = non-strict)
//
// Scratch registers:
//   x6 = atom_numer (loaded per atom)
//   x7 = atom_denom (loaded per atom)
//   x8 = cross-multiply LHS low
//   x9 = cross-multiply LHS high (for i128)
//   x10 = cross-multiply RHS low
//   x11 = cross-multiply RHS high (for i128)
//   x12 = scratch for comparison
//   x13 = bit mask for current atom
//   x14 = result bitmap (accumulated)
//   x15 = scratch
//
// Return:
//   x0 = bitmap (moved from x14 in epilogue)

#[cfg(target_arch = "aarch64")]
const LB_NUMER: u8 = 0;
#[cfg(target_arch = "aarch64")]
const LB_DENOM: u8 = 1;
#[cfg(target_arch = "aarch64")]
const UB_NUMER: u8 = 2;
#[cfg(target_arch = "aarch64")]
const UB_DENOM: u8 = 3;
#[cfg(target_arch = "aarch64")]
const LB_STRICT: u8 = 4;
#[cfg(target_arch = "aarch64")]
const UB_STRICT: u8 = 5;
#[cfg(target_arch = "aarch64")]
const ATOM_NUMER: u8 = 6;
#[cfg(target_arch = "aarch64")]
const ATOM_DENOM: u8 = 7;
#[cfg(target_arch = "aarch64")]
const LHS_LO: u8 = 8;
#[cfg(target_arch = "aarch64")]
const LHS_HI: u8 = 9;
#[cfg(target_arch = "aarch64")]
const RHS_LO: u8 = 10;
#[cfg(target_arch = "aarch64")]
const RHS_HI: u8 = 11;
#[cfg(target_arch = "aarch64")]
#[allow(dead_code)] // Register allocation: reserved scratch registers for future codegen
const SCRATCH: u8 = 12;
#[cfg(target_arch = "aarch64")]
const BITMASK: u8 = 13;
#[cfg(target_arch = "aarch64")]
const RESULT: u8 = 14;
#[cfg(target_arch = "aarch64")]
#[allow(dead_code)] // Register allocation: reserved scratch register for future codegen
const SCRATCH2: u8 = 15;

/// Emit a complete theory propagation function for a variable's atoms.
///
/// The function checks each atom against the current bounds and accumulates
/// a bitmap of implied truth values.
#[cfg(target_arch = "aarch64")]
fn emit_theory_prop_function(atoms: &[&BoundAtom], is_upper: &[bool]) -> Vec<u8> {
    let mut asm = TheoryAsm::new();

    asm.prologue();

    // Initialize result bitmap to 0.
    asm.movz_x(RESULT, 0);

    for (i, (atom, &upper)) in atoms.iter().zip(is_upper.iter()).enumerate() {
        let bit_true = (2 * i) as u32; // implied_true bit position
        let bit_false = (2 * i + 1) as u32; // implied_false bit position

        if upper {
            // Upper atom (x <= k or x < k):
            // - Implied TRUE if ub satisfies: check ub vs atom bound
            // - Implied FALSE if lb contradicts: check lb vs atom bound
            emit_upper_atom_check(&mut asm, atom, bit_true, bit_false);
        } else {
            // Lower atom (x >= k or x > k):
            // - Implied TRUE if lb satisfies: check lb vs atom bound
            // - Implied FALSE if ub contradicts: check ub vs atom bound
            emit_lower_atom_check(&mut asm, atom, bit_true, bit_false);
        }
    }

    // Move result to x0 for return.
    asm.mov_x(0, RESULT);
    asm.epilogue();

    asm.finalize()
}

/// Emit code for checking an upper atom (x <= k or x < k).
///
/// Implied TRUE when:
///   - Non-strict (x <= k): ub <= k
///   - Strict (x < k): ub < k, or (ub == k and ub.strict)
///
/// Implied FALSE when:
///   - Strict (x < k): lb >= k
///   - Non-strict (x <= k): lb > k, or (lb == k and lb.strict)
#[cfg(target_arch = "aarch64")]
fn emit_upper_atom_check(asm: &mut TheoryAsm, atom: &BoundAtom, bit_true: u32, bit_false: u32) {
    // --- Check implied TRUE (requires ub) ---
    let skip_true = asm.label();
    // If ub_denom == 0, no upper bound => skip true check.
    asm.cbz_x(UB_DENOM, skip_true);

    // Load atom bound value as immediates.
    asm.mov_imm64(ATOM_NUMER, atom.bound_numer);
    asm.mov_imm64(ATOM_DENOM, atom.bound_denom);

    // Cross-multiply: lhs = ub_numer * atom_denom, rhs = atom_numer * ub_denom
    // Compare as i128: (lhs_hi, lhs_lo) vs (rhs_hi, rhs_lo)
    emit_i128_cross_multiply(asm, UB_NUMER, ATOM_DENOM, ATOM_NUMER, UB_DENOM);

    // Now LHS_HI:LHS_LO = ub_numer * atom_denom
    //     RHS_HI:RHS_LO = atom_numer * ub_denom

    if atom.strict {
        // Strict atom (x < k): implied true when lhs < rhs, or (lhs == rhs and ub_strict)
        let not_true = asm.label();
        let set_true = asm.label();

        // Compare high words first
        asm.cmp_x(LHS_HI, RHS_HI);
        asm.b_cond(COND_LT, set_true); // lhs_hi < rhs_hi => lhs < rhs
        asm.b_cond(COND_GT, not_true); // lhs_hi > rhs_hi => lhs > rhs

        // High words equal, compare low words (unsigned — low half of signed i128)
        asm.cmp_x(LHS_LO, RHS_LO);
        asm.b_cond(COND_LO, set_true); // unsigned lower for low word
        asm.b_cond(COND_HI, not_true); // unsigned higher for low word

        // lhs == rhs: check ub_strict
        asm.cmp_x_zero(UB_STRICT);
        asm.b_cond(COND_NE, set_true);
        asm.b(not_true);

        asm.bind(set_true);
        emit_set_bit(asm, RESULT, bit_true);

        asm.bind(not_true);
    } else {
        // Non-strict atom (x <= k): implied true when lhs <= rhs
        let not_true = asm.label();
        let set_true = asm.label();

        asm.cmp_x(LHS_HI, RHS_HI);
        asm.b_cond(COND_LT, set_true);
        asm.b_cond(COND_GT, not_true);

        // High equal, compare low (unsigned — low half of signed i128)
        asm.cmp_x(LHS_LO, RHS_LO);
        asm.b_cond(COND_LO, set_true); // unsigned lower for low word
        asm.b_cond(COND_HI, not_true); // unsigned higher for low word

        // Equal => lhs <= rhs is true
        asm.bind(set_true);
        emit_set_bit(asm, RESULT, bit_true);

        asm.bind(not_true);
    }

    asm.bind(skip_true);

    // --- Check implied FALSE (requires lb) ---
    let skip_false = asm.label();
    asm.cbz_x(LB_DENOM, skip_false);

    // Reload atom bound (may have been clobbered by the true check path,
    // but since we use the same registers, we reload to be safe).
    asm.mov_imm64(ATOM_NUMER, atom.bound_numer);
    asm.mov_imm64(ATOM_DENOM, atom.bound_denom);

    // Cross-multiply: lhs = lb_numer * atom_denom, rhs = atom_numer * lb_denom
    emit_i128_cross_multiply(asm, LB_NUMER, ATOM_DENOM, ATOM_NUMER, LB_DENOM);

    if atom.strict {
        // Strict (x < k): implied false when lhs >= rhs (lb >= k)
        let not_false = asm.label();
        let set_false = asm.label();

        asm.cmp_x(LHS_HI, RHS_HI);
        asm.b_cond(COND_GT, set_false);
        asm.b_cond(COND_LT, not_false);

        asm.cmp_x(LHS_LO, RHS_LO);
        asm.b_cond(COND_LO, not_false); // unsigned lower for low word

        // lhs >= rhs (equal case also satisfies >=)
        asm.bind(set_false);
        emit_set_bit(asm, RESULT, bit_false);

        asm.bind(not_false);
    } else {
        // Non-strict (x <= k): implied false when lhs > rhs, or (lhs == rhs and lb_strict)
        let not_false = asm.label();
        let set_false = asm.label();

        asm.cmp_x(LHS_HI, RHS_HI);
        asm.b_cond(COND_GT, set_false);
        asm.b_cond(COND_LT, not_false);

        asm.cmp_x(LHS_LO, RHS_LO);
        asm.b_cond(COND_HI, set_false); // unsigned higher for low word
        asm.b_cond(COND_LO, not_false); // unsigned lower for low word

        // Equal: check lb_strict
        asm.cmp_x_zero(LB_STRICT);
        asm.b_cond(COND_NE, set_false);
        asm.b(not_false);

        asm.bind(set_false);
        emit_set_bit(asm, RESULT, bit_false);

        asm.bind(not_false);
    }

    asm.bind(skip_false);
}

/// Emit code for checking a lower atom (x >= k or x > k).
///
/// Implied TRUE when:
///   - Non-strict (x >= k): lb >= k
///   - Strict (x > k): lb > k, or (lb == k and lb.strict)
///
/// Implied FALSE when:
///   - Strict (x > k): ub <= k
///   - Non-strict (x >= k): ub < k, or (ub == k and ub.strict)
#[cfg(target_arch = "aarch64")]
fn emit_lower_atom_check(asm: &mut TheoryAsm, atom: &BoundAtom, bit_true: u32, bit_false: u32) {
    // --- Check implied TRUE (requires lb) ---
    let skip_true = asm.label();
    asm.cbz_x(LB_DENOM, skip_true);

    asm.mov_imm64(ATOM_NUMER, atom.bound_numer);
    asm.mov_imm64(ATOM_DENOM, atom.bound_denom);

    // Cross-multiply: lhs = lb_numer * atom_denom, rhs = atom_numer * lb_denom
    emit_i128_cross_multiply(asm, LB_NUMER, ATOM_DENOM, ATOM_NUMER, LB_DENOM);

    if atom.strict {
        // Strict (x > k): implied true when lhs > rhs, or (lhs == rhs and lb_strict)
        let not_true = asm.label();
        let set_true = asm.label();

        asm.cmp_x(LHS_HI, RHS_HI);
        asm.b_cond(COND_GT, set_true);
        asm.b_cond(COND_LT, not_true);

        asm.cmp_x(LHS_LO, RHS_LO);
        asm.b_cond(COND_HI, set_true); // unsigned higher for low word
        asm.b_cond(COND_LO, not_true); // unsigned lower for low word

        // Equal: check lb_strict
        asm.cmp_x_zero(LB_STRICT);
        asm.b_cond(COND_NE, set_true);
        asm.b(not_true);

        asm.bind(set_true);
        emit_set_bit(asm, RESULT, bit_true);

        asm.bind(not_true);
    } else {
        // Non-strict (x >= k): implied true when lhs >= rhs
        let not_true = asm.label();
        let set_true = asm.label();

        asm.cmp_x(LHS_HI, RHS_HI);
        asm.b_cond(COND_GT, set_true);
        asm.b_cond(COND_LT, not_true);

        asm.cmp_x(LHS_LO, RHS_LO);
        asm.b_cond(COND_LO, not_true); // unsigned lower for low word

        // lhs >= rhs
        asm.bind(set_true);
        emit_set_bit(asm, RESULT, bit_true);

        asm.bind(not_true);
    }

    asm.bind(skip_true);

    // --- Check implied FALSE (requires ub) ---
    let skip_false = asm.label();
    asm.cbz_x(UB_DENOM, skip_false);

    asm.mov_imm64(ATOM_NUMER, atom.bound_numer);
    asm.mov_imm64(ATOM_DENOM, atom.bound_denom);

    // Cross-multiply: lhs = ub_numer * atom_denom, rhs = atom_numer * ub_denom
    emit_i128_cross_multiply(asm, UB_NUMER, ATOM_DENOM, ATOM_NUMER, UB_DENOM);

    if atom.strict {
        // Strict (x > k): implied false when lhs <= rhs (ub <= k)
        let not_false = asm.label();
        let set_false = asm.label();

        asm.cmp_x(LHS_HI, RHS_HI);
        asm.b_cond(COND_LT, set_false);
        asm.b_cond(COND_GT, not_false);

        asm.cmp_x(LHS_LO, RHS_LO);
        asm.b_cond(COND_HI, not_false); // unsigned higher for low word

        // lhs <= rhs
        asm.bind(set_false);
        emit_set_bit(asm, RESULT, bit_false);

        asm.bind(not_false);
    } else {
        // Non-strict (x >= k): implied false when lhs < rhs, or (lhs == rhs and ub_strict)
        let not_false = asm.label();
        let set_false = asm.label();

        asm.cmp_x(LHS_HI, RHS_HI);
        asm.b_cond(COND_LT, set_false);
        asm.b_cond(COND_GT, not_false);

        asm.cmp_x(LHS_LO, RHS_LO);
        asm.b_cond(COND_LO, set_false); // unsigned lower for low word
        asm.b_cond(COND_HI, not_false); // unsigned higher for low word

        // Equal: check ub_strict
        asm.cmp_x_zero(UB_STRICT);
        asm.b_cond(COND_NE, set_false);
        asm.b(not_false);

        asm.bind(set_false);
        emit_set_bit(asm, RESULT, bit_false);

        asm.bind(not_false);
    }

    asm.bind(skip_false);
}

/// Emit i128 cross-multiply: compute (a * b) and (c * d) as i128 values.
///
/// After execution:
///   LHS_HI:LHS_LO = a * b (signed 128-bit)
///   RHS_HI:RHS_LO = c * d (signed 128-bit)
///
/// Uses MUL for low 64 bits and SMULH for high 64 bits.
#[cfg(target_arch = "aarch64")]
fn emit_i128_cross_multiply(
    asm: &mut TheoryAsm,
    a: u8, // register holding first factor of LHS
    b: u8, // register holding second factor of LHS
    c: u8, // register holding first factor of RHS
    d: u8, // register holding second factor of RHS
) {
    // LHS = a * b
    asm.mul_x(LHS_LO, a, b); // LHS_LO = (a * b) low 64 bits
    asm.smulh_x(LHS_HI, a, b); // LHS_HI = (a * b) high 64 bits

    // RHS = c * d
    asm.mul_x(RHS_LO, c, d); // RHS_LO = (c * d) low 64 bits
    asm.smulh_x(RHS_HI, c, d); // RHS_HI = (c * d) high 64 bits
}

/// Emit code to set bit `bit_pos` in register `result_reg`.
///
/// Uses BITMASK (x13) as scratch to hold the bit mask, then ORRs into result.
#[cfg(target_arch = "aarch64")]
fn emit_set_bit(asm: &mut TheoryAsm, result_reg: u8, bit_pos: u32) {
    if bit_pos == 0 {
        // For bit 0, we can use MOVZ + ORR
        asm.movz_x(BITMASK, 1);
    } else if bit_pos < 16 {
        asm.movz_x(BITMASK, 1u16 << bit_pos);
    } else if bit_pos < 32 {
        asm.movz_x_lsl16(BITMASK, 1u16 << (bit_pos - 16));
    } else if bit_pos < 48 {
        asm.movz_x_lsl32(BITMASK, 1u16 << (bit_pos - 32));
    } else {
        asm.movz_x_lsl48(BITMASK, 1u16 << (bit_pos - 48));
    }
    asm.orr_x(result_reg, result_reg, BITMASK);
}

// ---------------------------------------------------------------------------
// x86_64 code generation
// ---------------------------------------------------------------------------

/// Minimal x86_64 assembler for theory propagation functions.
///
/// x86_64 uses variable-length instructions and a FLAGS register for comparisons.
/// The System V AMD64 ABI passes arguments in rdi, rsi, rdx, rcx, r8, r9 and
/// returns in rax.
#[cfg(target_arch = "x86_64")]
struct TheoryAsmX64 {
    code: Vec<u8>,
    labels: Vec<Option<u32>>,
    /// Fixup for rel32 displacement (4 bytes at the offset).
    fixups: Vec<X64Fixup>,
}

#[cfg(target_arch = "x86_64")]
struct X64Fixup {
    /// Byte offset where the rel32 displacement starts.
    offset: u32,
    label: X64Label,
}

#[cfg(target_arch = "x86_64")]
#[derive(Clone, Copy)]
struct X64Label(u32);

#[cfg(target_arch = "x86_64")]
impl TheoryAsmX64 {
    fn new() -> Self {
        Self {
            code: Vec::with_capacity(1024),
            labels: Vec::new(),
            fixups: Vec::new(),
        }
    }

    fn emit_byte(&mut self, b: u8) {
        self.code.push(b);
    }

    fn emit_bytes(&mut self, bytes: &[u8]) {
        self.code.extend_from_slice(bytes);
    }

    fn emit_i32_le(&mut self, v: i32) {
        self.code.extend_from_slice(&v.to_le_bytes());
    }

    fn emit_u32_le(&mut self, v: u32) {
        self.code.extend_from_slice(&v.to_le_bytes());
    }

    fn label(&mut self) -> X64Label {
        let id = self.labels.len() as u32;
        self.labels.push(None);
        X64Label(id)
    }

    fn bind(&mut self, label: X64Label) {
        let offset = self.code.len() as u32;
        debug_assert!(
            self.labels[label.0 as usize].is_none(),
            "label already bound"
        );
        self.labels[label.0 as usize] = Some(offset);
    }

    fn emit_fixup(&mut self, label: X64Label) {
        self.fixups.push(X64Fixup {
            offset: self.code.len() as u32,
            label,
        });
        self.emit_i32_le(0); // placeholder
    }

    /// REX prefix. W=1 for 64-bit operand size.
    fn rex(w: bool, r: u8, rm: u8) -> u8 {
        let mut rex = 0x40u8;
        if w {
            rex |= 0x08;
        }
        if r >= 8 {
            rex |= 0x04; // R
        }
        if rm >= 8 {
            rex |= 0x01; // B
        }
        rex
    }

    /// ModRM byte: mod=11 (register-register).
    fn modrm_rr(r: u8, rm: u8) -> u8 {
        0xC0 | ((r & 7) << 3) | (rm & 7)
    }

    // --- Prologue / Epilogue ---
    // We use RBX, R12-R15 as callee-saved storage for arguments.
    // System V AMD64 calling convention:
    //   Args: rdi(0), rsi(1), rdx(2), rcx(3), r8(4), r9(5)
    //   Return: rax(0)
    //   Callee-saved: rbx(3), rbp(5), r12(12)-r15(15)

    /// Push callee-saved registers and move args to callee-saved regs.
    ///
    /// After prologue:
    ///   rbx  = lb_numer  (from rdi)
    ///   rbp  = lb_denom  (from rsi)
    ///   r12  = ub_numer  (from rdx)
    ///   r13  = ub_denom  (from rcx)
    ///   r14  = lb_strict (from r8)
    ///   r15  = ub_strict (from r9)
    fn prologue(&mut self) {
        // push rbx
        self.emit_byte(0x53);
        // push rbp
        self.emit_byte(0x55);
        // push r12
        self.emit_bytes(&[0x41, 0x54]);
        // push r13
        self.emit_bytes(&[0x41, 0x55]);
        // push r14
        self.emit_bytes(&[0x41, 0x56]);
        // push r15
        self.emit_bytes(&[0x41, 0x57]);

        // Move args into callee-saved registers.
        // MOV rbx, rdi (lb_numer)
        self.mov_r64(X64_RBX, X64_RDI);
        // MOV rbp, rsi (lb_denom)
        self.mov_r64(X64_RBP, X64_RSI);
        // MOV r12, rdx (ub_numer)
        self.mov_r64(X64_R12, X64_RDX);
        // MOV r13, rcx (ub_denom)
        self.mov_r64(X64_R13, X64_RCX);
        // MOV r14, r8  (lb_strict)
        self.mov_r64(X64_R14, X64_R8);
        // MOV r15, r9  (ub_strict)
        self.mov_r64(X64_R15, X64_R9);
    }

    /// Pop callee-saved registers and return.
    fn epilogue(&mut self) {
        // pop r15
        self.emit_bytes(&[0x41, 0x5F]);
        // pop r14
        self.emit_bytes(&[0x41, 0x5E]);
        // pop r13
        self.emit_bytes(&[0x41, 0x5D]);
        // pop r12
        self.emit_bytes(&[0x41, 0x5C]);
        // pop rbp
        self.emit_byte(0x5D);
        // pop rbx
        self.emit_byte(0x5B);
        // ret
        self.emit_byte(0xC3);
    }

    /// MOV r64, r64
    fn mov_r64(&mut self, dst: u8, src: u8) {
        self.emit_byte(Self::rex(true, src, dst));
        self.emit_byte(0x89);
        self.emit_byte(Self::modrm_rr(src, dst));
    }

    /// MOV r64, imm64 (REX.W + B8+rd + imm64)
    fn mov_imm64(&mut self, rd: u8, value: i64) {
        let v = value as u64;

        // XOR r32, r32 for zero
        if v == 0 {
            self.xor_r64(rd, rd);
            return;
        }

        // MOV r32, imm32 for small positive values (zero-extends to 64 bits)
        if (0..=0xFFFF_FFFF).contains(&value) {
            if rd >= 8 {
                self.emit_byte(0x41); // REX.B
            }
            self.emit_byte(0xB8 + (rd & 7));
            self.emit_u32_le(v as u32);
            return;
        }

        // MOV r64, imm64 (10-byte encoding)
        self.emit_byte(Self::rex(true, 0, rd));
        self.emit_byte(0xB8 + (rd & 7));
        self.emit_bytes(&v.to_le_bytes());
    }

    /// XOR r64, r64 (zero register, but uses 32-bit XOR which zero-extends)
    fn xor_r64(&mut self, dst: u8, src: u8) {
        // Use 32-bit XOR for smaller encoding (implicitly zero-extends upper 32).
        // Opcode 0x31 XOR r/m32, r32 writes to the rm field: dst goes in rm,
        // src in reg. (The previous encoding had the operands swapped and
        // wrote the result to `src` whenever dst != src; all callers were
        // self-zeroing so no miscompile shipped.)
        let needs_rex = dst >= 8 || src >= 8;
        if needs_rex {
            self.emit_byte(Self::rex(false, src, dst));
        }
        self.emit_byte(0x31);
        self.emit_byte(Self::modrm_rr(src, dst));
    }

    /// IMUL r64 — signed 128-bit multiply: RDX:RAX = RAX * r64.
    fn imul_r64_widening(&mut self, src: u8) {
        self.emit_byte(Self::rex(true, 0, src));
        self.emit_byte(0xF7);
        self.emit_byte(Self::modrm_rr(5, src)); // /5 = IMUL
    }

    /// CMP r64, r64 — compare two 64-bit registers.
    fn cmp_r64(&mut self, a: u8, b: u8) {
        self.emit_byte(Self::rex(true, b, a));
        self.emit_byte(0x39);
        self.emit_byte(Self::modrm_rr(b, a));
    }

    /// TEST r64, r64 — test register against itself (sets ZF if zero).
    fn test_r64(&mut self, a: u8, b: u8) {
        self.emit_byte(Self::rex(true, b, a));
        self.emit_byte(0x85);
        self.emit_byte(Self::modrm_rr(b, a));
    }

    /// OR r64, r64
    fn or_r64(&mut self, dst: u8, src: u8) {
        self.emit_byte(Self::rex(true, src, dst));
        self.emit_byte(0x09);
        self.emit_byte(Self::modrm_rr(src, dst));
    }

    /// Jcc rel32 — conditional jump.
    fn jcc(&mut self, cc: u8, label: X64Label) {
        self.emit_byte(0x0F);
        self.emit_byte(0x80 + cc);
        self.emit_fixup(label);
    }

    /// JMP rel32 — unconditional jump.
    fn jmp(&mut self, label: X64Label) {
        self.emit_byte(0xE9);
        self.emit_fixup(label);
    }

    /// JE label (ZF=1)
    fn je(&mut self, label: X64Label) {
        self.jcc(0x04, label);
    }

    /// JNE label (ZF=0)
    fn jne(&mut self, label: X64Label) {
        self.jcc(0x05, label);
    }

    /// JL label — signed less than (SF != OF)
    fn jl(&mut self, label: X64Label) {
        self.jcc(0x0C, label);
    }

    /// JG label — signed greater than (ZF=0 && SF=OF)
    fn jg(&mut self, label: X64Label) {
        self.jcc(0x0F, label);
    }

    /// JB label — unsigned below (CF=1)
    fn jb(&mut self, label: X64Label) {
        self.jcc(0x02, label);
    }

    /// JA label — unsigned above (CF=0 && ZF=0)
    fn ja(&mut self, label: X64Label) {
        self.jcc(0x07, label);
    }

    fn finalize(mut self) -> Vec<u8> {
        for fixup in &self.fixups {
            // INVARIANT: every theory-prop x86_64 label returned by
            // `new_label()` must be bound via `bind()` before `finalize()`.
            // Assembler-internal invariant, not a user-input error.
            let target = self.labels[fixup.label.0 as usize].expect(
                "invariant: all emitted theory-prop x86_64 labels must be bound before finalize",
            );
            let next_ip = fixup.offset + 4;
            let delta = target as i32 - next_ip as i32;
            self.code[fixup.offset as usize..fixup.offset as usize + 4]
                .copy_from_slice(&delta.to_le_bytes());
        }
        self.code
    }
}

// x86_64 register numbers.
#[cfg(target_arch = "x86_64")]
const X64_RAX: u8 = 0;
#[cfg(target_arch = "x86_64")]
const X64_RCX: u8 = 1;
#[cfg(target_arch = "x86_64")]
const X64_RDX: u8 = 2;
#[cfg(target_arch = "x86_64")]
const X64_RBX: u8 = 3;
#[cfg(target_arch = "x86_64")]
const X64_RBP: u8 = 5;
#[cfg(target_arch = "x86_64")]
const X64_RSI: u8 = 6;
#[cfg(target_arch = "x86_64")]
const X64_RDI: u8 = 7;
#[cfg(target_arch = "x86_64")]
const X64_R8: u8 = 8;
#[cfg(target_arch = "x86_64")]
const X64_R9: u8 = 9;
#[cfg(target_arch = "x86_64")]
const X64_R10: u8 = 10;
#[cfg(target_arch = "x86_64")]
const X64_R11: u8 = 11;
#[cfg(target_arch = "x86_64")]
const X64_R12: u8 = 12;
#[cfg(target_arch = "x86_64")]
const X64_R13: u8 = 13;
#[cfg(target_arch = "x86_64")]
const X64_R14: u8 = 14;
#[cfg(target_arch = "x86_64")]
const X64_R15: u8 = 15;

// x86_64 register assignments for compiled theory prop function:
//
// After prologue (callee-saved):
//   rbx  = lb_numer
//   rbp  = lb_denom  (0 = no lower bound)
//   r12  = ub_numer
//   r13  = ub_denom  (0 = no upper bound)
//   r14  = lb_strict (1 = strict, 0 = non-strict)
//   r15  = ub_strict (1 = strict, 0 = non-strict)
//
// Scratch (caller-saved):
//   rax  = multiply scratch / return value
//   rcx  = atom_numer (loaded per atom)
//   rdx  = multiply high / atom_denom (loaded per atom)
//   rsi  = scratch for cross-multiply
//   rdi  = scratch for cross-multiply
//   r8   = lhs_hi (cross-multiply result high)
//   r9   = lhs_lo (cross-multiply result low)
//   r10  = rhs_hi
//   r11  = rhs_lo
//   [rax, rdx used by IMUL widening]
//
// Result register: rax (moved from accumulator before return)

/// Callee-saved register assignments after prologue.
#[cfg(target_arch = "x86_64")]
const X_LB_NUMER: u8 = X64_RBX;
#[cfg(target_arch = "x86_64")]
const X_LB_DENOM: u8 = X64_RBP;
#[cfg(target_arch = "x86_64")]
const X_UB_NUMER: u8 = X64_R12;
#[cfg(target_arch = "x86_64")]
const X_UB_DENOM: u8 = X64_R13;
#[cfg(target_arch = "x86_64")]
const X_LB_STRICT: u8 = X64_R14;
#[cfg(target_arch = "x86_64")]
const X_UB_STRICT: u8 = X64_R15;

/// Scratch register assignments.
///
/// IMPORTANT: IMUL r64 (one-operand form) clobbers RAX and RDX. The result
/// bitmap must NOT be in either of these registers during cross-multiply.
/// We use RDI as the result accumulator (free after prologue saves args)
/// and move to RAX only in the epilogue.
#[cfg(target_arch = "x86_64")]
const X_ATOM_NUMER: u8 = X64_RCX;
#[cfg(target_arch = "x86_64")]
const X_ATOM_DENOM: u8 = X64_RSI;
#[cfg(target_arch = "x86_64")]
const X_LHS_HI: u8 = X64_R8;
#[cfg(target_arch = "x86_64")]
const X_LHS_LO: u8 = X64_R9;
#[cfg(target_arch = "x86_64")]
const X_RHS_HI: u8 = X64_R10;
#[cfg(target_arch = "x86_64")]
const X_RHS_LO: u8 = X64_R11;
#[cfg(target_arch = "x86_64")]
const X_BITMASK: u8 = X64_RAX; // scratch for bitmask (ok: not during IMUL)
#[cfg(target_arch = "x86_64")]
const X_RESULT: u8 = X64_RDI; // Accumulates bitmap, moved to rax before ret

/// Emit a complete theory propagation function for x86_64.
#[cfg(target_arch = "x86_64")]
fn emit_theory_prop_function(atoms: &[&BoundAtom], is_upper: &[bool]) -> Vec<u8> {
    let mut asm = TheoryAsmX64::new();

    asm.prologue();

    // Initialize result bitmap to 0. X_RESULT is rdi (free after prologue).
    asm.xor_r64(X_RESULT, X_RESULT);

    for (i, (atom, &upper)) in atoms.iter().zip(is_upper.iter()).enumerate() {
        let bit_true = (2 * i) as u32;
        let bit_false = (2 * i + 1) as u32;

        if upper {
            emit_upper_atom_check_x64(&mut asm, atom, bit_true, bit_false);
        } else {
            emit_lower_atom_check_x64(&mut asm, atom, bit_true, bit_false);
        }
    }

    // Move result from rdi (X_RESULT) to rax for return.
    asm.mov_r64(X64_RAX, X_RESULT);
    asm.epilogue();

    asm.finalize()
}

/// Emit code for checking an upper atom (x <= k or x < k) on x86_64.
#[cfg(target_arch = "x86_64")]
fn emit_upper_atom_check_x64(
    asm: &mut TheoryAsmX64,
    atom: &BoundAtom,
    bit_true: u32,
    bit_false: u32,
) {
    // --- Check implied TRUE (requires ub) ---
    let skip_true = asm.label();
    // If ub_denom == 0, no upper bound => skip true check.
    asm.test_r64(X_UB_DENOM, X_UB_DENOM);
    asm.je(skip_true);

    // Load atom bound value as immediates.
    asm.mov_imm64(X_ATOM_NUMER, atom.bound_numer);
    asm.mov_imm64(X_ATOM_DENOM, atom.bound_denom);

    // Cross-multiply: lhs = ub_numer * atom_denom, rhs = atom_numer * ub_denom
    emit_i128_cross_multiply_x64(asm, X_UB_NUMER, X_ATOM_DENOM, X_ATOM_NUMER, X_UB_DENOM);

    if atom.strict {
        // Strict atom (x < k): implied true when lhs < rhs, or (lhs == rhs and ub_strict)
        let not_true = asm.label();
        let set_true = asm.label();

        // Compare high words first (signed)
        asm.cmp_r64(X_LHS_HI, X_RHS_HI);
        asm.jl(set_true);
        asm.jg(not_true);

        // High words equal, compare low words (unsigned — these are the low halves
        // of a signed 128-bit product, treated as unsigned magnitude)
        asm.cmp_r64(X_LHS_LO, X_RHS_LO);
        asm.jb(set_true);
        asm.ja(not_true);

        // lhs == rhs: check ub_strict
        asm.test_r64(X_UB_STRICT, X_UB_STRICT);
        asm.jne(set_true);
        asm.jmp(not_true);

        asm.bind(set_true);
        emit_set_bit_x64(asm, X_RESULT, bit_true);

        asm.bind(not_true);
    } else {
        // Non-strict atom (x <= k): implied true when lhs <= rhs
        let not_true = asm.label();
        let set_true = asm.label();

        asm.cmp_r64(X_LHS_HI, X_RHS_HI);
        asm.jl(set_true);
        asm.jg(not_true);

        asm.cmp_r64(X_LHS_LO, X_RHS_LO);
        asm.jb(set_true);
        asm.ja(not_true);

        // Equal => lhs <= rhs is true
        asm.bind(set_true);
        emit_set_bit_x64(asm, X_RESULT, bit_true);

        asm.bind(not_true);
    }

    asm.bind(skip_true);

    // --- Check implied FALSE (requires lb) ---
    let skip_false = asm.label();
    asm.test_r64(X_LB_DENOM, X_LB_DENOM);
    asm.je(skip_false);

    // Reload atom bound.
    asm.mov_imm64(X_ATOM_NUMER, atom.bound_numer);
    asm.mov_imm64(X_ATOM_DENOM, atom.bound_denom);

    // Cross-multiply: lhs = lb_numer * atom_denom, rhs = atom_numer * lb_denom
    emit_i128_cross_multiply_x64(asm, X_LB_NUMER, X_ATOM_DENOM, X_ATOM_NUMER, X_LB_DENOM);

    if atom.strict {
        // Strict (x < k): implied false when lhs >= rhs (lb >= k)
        let not_false = asm.label();
        let set_false = asm.label();

        asm.cmp_r64(X_LHS_HI, X_RHS_HI);
        asm.jg(set_false);
        asm.jl(not_false);

        asm.cmp_r64(X_LHS_LO, X_RHS_LO);
        asm.jb(not_false);

        // lhs >= rhs (equal case also satisfies >=)
        asm.bind(set_false);
        emit_set_bit_x64(asm, X_RESULT, bit_false);

        asm.bind(not_false);
    } else {
        // Non-strict (x <= k): implied false when lhs > rhs, or (lhs == rhs and lb_strict)
        let not_false = asm.label();
        let set_false = asm.label();

        asm.cmp_r64(X_LHS_HI, X_RHS_HI);
        asm.jg(set_false);
        asm.jl(not_false);

        asm.cmp_r64(X_LHS_LO, X_RHS_LO);
        asm.ja(set_false);
        asm.jb(not_false);

        // Equal: check lb_strict
        asm.test_r64(X_LB_STRICT, X_LB_STRICT);
        asm.jne(set_false);
        asm.jmp(not_false);

        asm.bind(set_false);
        emit_set_bit_x64(asm, X_RESULT, bit_false);

        asm.bind(not_false);
    }

    asm.bind(skip_false);
}

/// Emit code for checking a lower atom (x >= k or x > k) on x86_64.
#[cfg(target_arch = "x86_64")]
fn emit_lower_atom_check_x64(
    asm: &mut TheoryAsmX64,
    atom: &BoundAtom,
    bit_true: u32,
    bit_false: u32,
) {
    // --- Check implied TRUE (requires lb) ---
    let skip_true = asm.label();
    asm.test_r64(X_LB_DENOM, X_LB_DENOM);
    asm.je(skip_true);

    asm.mov_imm64(X_ATOM_NUMER, atom.bound_numer);
    asm.mov_imm64(X_ATOM_DENOM, atom.bound_denom);

    // Cross-multiply: lhs = lb_numer * atom_denom, rhs = atom_numer * lb_denom
    emit_i128_cross_multiply_x64(asm, X_LB_NUMER, X_ATOM_DENOM, X_ATOM_NUMER, X_LB_DENOM);

    if atom.strict {
        // Strict (x > k): implied true when lhs > rhs, or (lhs == rhs and lb_strict)
        let not_true = asm.label();
        let set_true = asm.label();

        asm.cmp_r64(X_LHS_HI, X_RHS_HI);
        asm.jg(set_true);
        asm.jl(not_true);

        asm.cmp_r64(X_LHS_LO, X_RHS_LO);
        asm.ja(set_true);
        asm.jb(not_true);

        // Equal: check lb_strict
        asm.test_r64(X_LB_STRICT, X_LB_STRICT);
        asm.jne(set_true);
        asm.jmp(not_true);

        asm.bind(set_true);
        emit_set_bit_x64(asm, X_RESULT, bit_true);

        asm.bind(not_true);
    } else {
        // Non-strict (x >= k): implied true when lhs >= rhs
        let not_true = asm.label();
        let set_true = asm.label();

        asm.cmp_r64(X_LHS_HI, X_RHS_HI);
        asm.jg(set_true);
        asm.jl(not_true);

        asm.cmp_r64(X_LHS_LO, X_RHS_LO);
        asm.jb(not_true);

        // lhs >= rhs
        asm.bind(set_true);
        emit_set_bit_x64(asm, X_RESULT, bit_true);

        asm.bind(not_true);
    }

    asm.bind(skip_true);

    // --- Check implied FALSE (requires ub) ---
    let skip_false = asm.label();
    asm.test_r64(X_UB_DENOM, X_UB_DENOM);
    asm.je(skip_false);

    asm.mov_imm64(X_ATOM_NUMER, atom.bound_numer);
    asm.mov_imm64(X_ATOM_DENOM, atom.bound_denom);

    // Cross-multiply: lhs = ub_numer * atom_denom, rhs = atom_numer * ub_denom
    emit_i128_cross_multiply_x64(asm, X_UB_NUMER, X_ATOM_DENOM, X_ATOM_NUMER, X_UB_DENOM);

    if atom.strict {
        // Strict (x > k): implied false when lhs <= rhs (ub <= k)
        let not_false = asm.label();
        let set_false = asm.label();

        asm.cmp_r64(X_LHS_HI, X_RHS_HI);
        asm.jl(set_false);
        asm.jg(not_false);

        asm.cmp_r64(X_LHS_LO, X_RHS_LO);
        asm.ja(not_false);

        // lhs <= rhs
        asm.bind(set_false);
        emit_set_bit_x64(asm, X_RESULT, bit_false);

        asm.bind(not_false);
    } else {
        // Non-strict (x >= k): implied false when lhs < rhs, or (lhs == rhs and ub_strict)
        let not_false = asm.label();
        let set_false = asm.label();

        asm.cmp_r64(X_LHS_HI, X_RHS_HI);
        asm.jl(set_false);
        asm.jg(not_false);

        asm.cmp_r64(X_LHS_LO, X_RHS_LO);
        asm.jb(set_false);
        asm.ja(not_false);

        // Equal: check ub_strict
        asm.test_r64(X_UB_STRICT, X_UB_STRICT);
        asm.jne(set_false);
        asm.jmp(not_false);

        asm.bind(set_false);
        emit_set_bit_x64(asm, X_RESULT, bit_false);

        asm.bind(not_false);
    }

    asm.bind(skip_false);
}

/// Emit i128 cross-multiply on x86_64: compute (a * b) and (c * d) as i128.
///
/// Uses IMUL r64 (one-operand form) which produces RDX:RAX = RAX * src.
///
/// After execution:
///   X_LHS_HI:X_LHS_LO = a * b (signed 128-bit)
///   X_RHS_HI:X_RHS_LO = c * d (signed 128-bit)
///
/// Clobbers: rax, rdx (used by IMUL).
/// The registers `a` and `b` must not be rax or rdx (they are callee-saved
/// so this is guaranteed by our register assignment).
#[cfg(target_arch = "x86_64")]
fn emit_i128_cross_multiply_x64(
    asm: &mut TheoryAsmX64,
    a: u8, // register holding first factor of LHS
    b: u8, // register holding second factor of LHS
    c: u8, // register holding first factor of RHS
    d: u8, // register holding second factor of RHS
) {
    // LHS = a * b: MOV rax, a; IMUL b => RDX:RAX
    asm.mov_r64(X64_RAX, a);
    asm.imul_r64_widening(b);
    // Save result: LHS_LO = RAX, LHS_HI = RDX
    asm.mov_r64(X_LHS_LO, X64_RAX);
    asm.mov_r64(X_LHS_HI, X64_RDX);

    // RHS = c * d: MOV rax, c; IMUL d => RDX:RAX
    asm.mov_r64(X64_RAX, c);
    asm.imul_r64_widening(d);
    // Save result: RHS_LO = RAX, RHS_HI = RDX
    asm.mov_r64(X_RHS_LO, X64_RAX);
    asm.mov_r64(X_RHS_HI, X64_RDX);
}

/// Emit code to set bit `bit_pos` in register `result_reg` on x86_64.
///
/// Uses X_BITMASK (rdi) as scratch to hold the bit mask, then ORs into result.
#[cfg(target_arch = "x86_64")]
fn emit_set_bit_x64(asm: &mut TheoryAsmX64, result_reg: u8, bit_pos: u32) {
    // Load 1 << bit_pos into X_BITMASK, then OR into result.
    let mask = 1u64 << bit_pos;
    asm.mov_imm64(X_BITMASK, mask as i64);
    asm.or_r64(result_reg, X_BITMASK);
}

// ---------------------------------------------------------------------------
// Integration with TheoryPropJit
// ---------------------------------------------------------------------------

/// Upgrade a `TheoryPropJit` by compiling native functions for eligible variables.
///
/// For each variable with a compiled VarPropagator, attempts to compile a native
/// machine code version. Variables that cannot be compiled (too many atoms, non-small
/// atoms) retain their interpreted path.
///
/// All eligible variables are batched into a **single** executable mapping
/// (Fix A1): code for every variable is emitted into one buffer (16-byte
/// aligned entries), then one mmap + one icache flush publishes the whole
/// batch. Previously each variable allocated its own page-rounded mapping
/// (~160 mmaps and ≥2.5MB for a DRAGON-class atom index); the per-instance
/// recompile storm of mmap/memmove/icache calls was measured at ~59% of
/// theory time in the lazy DPLL(T) loop (lia-hot-loop-plan.md §0.3).
///
/// Returns the number of variables successfully compiled to native code.
pub fn compile_native_propagators(
    jit: &crate::theory_prop::TheoryPropJit,
) -> (Vec<Option<NativeVarPropagator>>, u32) {
    let props = jit.propagators();
    let mut native_props: Vec<Option<NativeVarPropagator>> = Vec::with_capacity(props.len());
    native_props.resize_with(props.len(), || None);

    #[cfg(not(any(target_arch = "aarch64", target_arch = "x86_64")))]
    {
        (native_props, 0)
    }

    #[cfg(any(target_arch = "aarch64", target_arch = "x86_64"))]
    {
        // Pass 1: emit code for every eligible variable into one buffer.
        struct PendingFn {
            slot: usize,
            offset: usize,
            atom_indices: Vec<u32>,
        }

        let mut blob: Vec<u8> = Vec::new();
        let mut pending: Vec<PendingFn> = Vec::new();

        for (slot, prop_opt) in props.iter().enumerate() {
            let Some(prop) = prop_opt else { continue };
            let Some((code, atom_indices)) = emit_native_propagator_code(prop) else {
                continue;
            };
            pad_to_fn_align(&mut blob);
            pending.push(PendingFn {
                slot,
                offset: blob.len(),
                atom_indices,
            });
            blob.extend_from_slice(&code);
        }

        if pending.is_empty() {
            return (native_props, 0);
        }

        // Pass 2: publish the whole batch with a single executable mapping.
        let Ok(executable) = ExecutableMemory::new(&blob) else {
            // Native compilation is an optimization; fall back to interpreted.
            return (native_props, 0);
        };
        let executable = std::sync::Arc::new(executable);
        let base = executable.as_ptr();

        let mut native_count = 0u32;
        for entry in pending {
            // SAFETY: entry.offset < blob.len() <= allocation size; the
            // offset is 16-byte aligned and marks the entry point of a
            // complete function emitted by emit_theory_prop_function with
            // extern "C" ABI fn(i64, i64, i64, i64, i64, i64) -> u64. The
            // ExecutableMemory is kept alive by the shared Arc for the
            // lifetime of every NativeVarPropagator in the batch.
            let func: TheoryPropFn =
                unsafe { std::mem::transmute::<*const u8, TheoryPropFn>(base.add(entry.offset)) };
            let num_atoms = entry.atom_indices.len();
            native_props[entry.slot] = Some(NativeVarPropagator {
                func,
                num_atoms,
                atom_indices: entry.atom_indices,
                _executable: std::sync::Arc::clone(&executable),
            });
            native_count += 1;
        }

        (native_props, native_count)
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

// Every test in this module executes JIT-emitted native code, which requires
// `ExecutableMemory` — implemented only on Linux/macOS (Windows fails closed
// with NoNativeIsa by design; see executable.rs). Gate the module so the
// suite skips instead of failing 27 tests on unsupported OSes.
#[cfg(all(test, any(target_os = "linux", target_os = "macos")))]
mod tests {
    use super::*;
    use crate::theory_prop::{BoundAtom, SmallBound, VarPropagator};

    fn make_atom(index: u32, numer: i64, denom: i64, is_upper: bool, strict: bool) -> BoundAtom {
        BoundAtom {
            atom_index: index,
            bound_numer: numer,
            bound_denom: denom,
            is_upper,
            strict,
            is_small: true,
        }
    }

    fn make_bound(numer: i64, denom: i64, strict: bool) -> SmallBound {
        SmallBound {
            numer,
            denom,
            strict,
        }
    }

    /// Compare native results against interpreted results for the same inputs.
    #[cfg(any(target_arch = "aarch64", target_arch = "x86_64"))]
    fn assert_native_matches_interpreted(
        atoms: Vec<BoundAtom>,
        lb: Option<SmallBound>,
        ub: Option<SmallBound>,
    ) {
        let prop = VarPropagator::new(0, atoms);

        // Interpreted results
        let mut interp_results = Vec::new();
        prop.check_bounds(lb, ub, &mut interp_results);

        // Native compilation
        let native = compile_native_propagator(&prop)
            .expect("compile should not error")
            .expect("should produce native propagator");

        let mut native_results = Vec::new();
        native.check_bounds(lb, ub, &mut native_results);

        // Sort both result sets for comparison (order may differ).
        let mut interp_set: Vec<(u32, bool)> = interp_results
            .iter()
            .map(|r| (r.atom_index, r.implied_value))
            .collect();
        interp_set.sort_unstable();

        let mut native_set: Vec<(u32, bool)> = native_results
            .iter()
            .map(|r| (r.atom_index, r.implied_value))
            .collect();
        native_set.sort_unstable();

        assert_eq!(
            interp_set, native_set,
            "Native results differ from interpreted.\n  Interpreted: {interp_set:?}\n  Native: {native_set:?}\n  lb={lb:?}, ub={ub:?}",
        );
    }

    // --- Basic tests ---

    #[cfg(any(target_arch = "aarch64", target_arch = "x86_64"))]
    #[test]
    fn test_native_upper_nonstrict_implied_true() {
        // Atom: x <= 10. ub = 5. Should be implied true.
        let atoms = vec![make_atom(0, 10, 1, true, false)];
        assert_native_matches_interpreted(atoms, None, Some(make_bound(5, 1, false)));
    }

    #[cfg(any(target_arch = "aarch64", target_arch = "x86_64"))]
    #[test]
    fn test_native_upper_nonstrict_implied_false() {
        // Atom: x <= 5. lb = 7. Should be implied false.
        let atoms = vec![make_atom(0, 5, 1, true, false)];
        assert_native_matches_interpreted(atoms, Some(make_bound(7, 1, false)), None);
    }

    #[cfg(any(target_arch = "aarch64", target_arch = "x86_64"))]
    #[test]
    fn test_native_upper_strict_implied_true() {
        // Atom: x < 5. ub = 3. Should be implied true.
        let atoms = vec![make_atom(0, 5, 1, true, true)];
        assert_native_matches_interpreted(atoms, None, Some(make_bound(3, 1, false)));
    }

    #[cfg(any(target_arch = "aarch64", target_arch = "x86_64"))]
    #[test]
    fn test_native_upper_strict_implied_true_equal_strict_ub() {
        // Atom: x < 5. ub = 5 (strict). Implied true.
        let atoms = vec![make_atom(0, 5, 1, true, true)];
        assert_native_matches_interpreted(atoms, None, Some(make_bound(5, 1, true)));
    }

    #[cfg(any(target_arch = "aarch64", target_arch = "x86_64"))]
    #[test]
    fn test_native_upper_strict_not_implied_equal_nonstrict_ub() {
        // Atom: x < 5. ub = 5 (non-strict). Not implied.
        let atoms = vec![make_atom(0, 5, 1, true, true)];
        assert_native_matches_interpreted(atoms, None, Some(make_bound(5, 1, false)));
    }

    #[cfg(any(target_arch = "aarch64", target_arch = "x86_64"))]
    #[test]
    fn test_native_lower_nonstrict_implied_true() {
        // Atom: x >= 3. lb = 7. Should be implied true.
        let atoms = vec![make_atom(0, 3, 1, false, false)];
        assert_native_matches_interpreted(atoms, Some(make_bound(7, 1, false)), None);
    }

    #[cfg(any(target_arch = "aarch64", target_arch = "x86_64"))]
    #[test]
    fn test_native_lower_strict_implied_true() {
        // Atom: x > 5. lb = 7. Should be implied true.
        let atoms = vec![make_atom(0, 5, 1, false, true)];
        assert_native_matches_interpreted(atoms, Some(make_bound(7, 1, false)), None);
    }

    #[cfg(any(target_arch = "aarch64", target_arch = "x86_64"))]
    #[test]
    fn test_native_lower_nonstrict_implied_false() {
        // Atom: x >= 5. ub = 3. Should be implied false.
        let atoms = vec![make_atom(0, 5, 1, false, false)];
        assert_native_matches_interpreted(atoms, None, Some(make_bound(3, 1, false)));
    }

    // --- Multiple atoms ---

    #[cfg(any(target_arch = "aarch64", target_arch = "x86_64"))]
    #[test]
    fn test_native_multiple_atoms() {
        // Mix of upper and lower atoms with both strict and non-strict.
        let atoms = vec![
            make_atom(0, 10, 1, true, false), // x <= 10
            make_atom(1, 5, 1, true, false),  // x <= 5
            make_atom(2, 3, 1, false, false), // x >= 3
            make_atom(3, 7, 1, false, false), // x >= 7
        ];
        // lb=4, ub=8: x<=10 true, x<=5 unknown, x>=3 true, x>=7 unknown
        assert_native_matches_interpreted(
            atoms,
            Some(make_bound(4, 1, false)),
            Some(make_bound(8, 1, false)),
        );
    }

    #[cfg(any(target_arch = "aarch64", target_arch = "x86_64"))]
    #[test]
    fn test_native_multiple_atoms_implied_false() {
        let atoms = vec![
            make_atom(0, 5, 1, true, false),  // x <= 5
            make_atom(1, 3, 1, false, false), // x >= 3
        ];
        // lb=7: x <= 5 is false, x >= 3 is true
        assert_native_matches_interpreted(atoms, Some(make_bound(7, 1, false)), None);
    }

    // --- Rational bounds ---

    #[cfg(any(target_arch = "aarch64", target_arch = "x86_64"))]
    #[test]
    fn test_native_rational_bounds() {
        // Atom: x <= 3/2. ub = 1/1. 1*2 <= 3*1 => true.
        let atoms = vec![make_atom(0, 3, 2, true, false)];
        assert_native_matches_interpreted(atoms, None, Some(make_bound(1, 1, false)));
    }

    #[cfg(any(target_arch = "aarch64", target_arch = "x86_64"))]
    #[test]
    fn test_native_rational_bounds_not_implied() {
        // Atom: x <= 1/3. ub = 1/2. 1*3 > 1*2 => unknown.
        let atoms = vec![make_atom(0, 1, 3, true, false)];
        assert_native_matches_interpreted(atoms, None, Some(make_bound(1, 2, false)));
    }

    // --- Negative bounds ---

    #[cfg(any(target_arch = "aarch64", target_arch = "x86_64"))]
    #[test]
    fn test_native_negative_bounds() {
        // Atom: x <= -3. ub = -5. -5 <= -3 => true.
        let atoms = vec![make_atom(0, -3, 1, true, false)];
        assert_native_matches_interpreted(atoms, None, Some(make_bound(-5, 1, false)));
    }

    // --- Strictness edge cases ---

    #[cfg(any(target_arch = "aarch64", target_arch = "x86_64"))]
    #[test]
    fn test_native_strict_at_zero() {
        // x > 0. lb = 0 (non-strict). Should NOT be implied.
        let atoms_a = vec![make_atom(0, 0, 1, false, true)];
        assert_native_matches_interpreted(atoms_a, Some(make_bound(0, 1, false)), None);

        // x > 0. lb = 0 (strict). Should be implied true.
        let atoms_b = vec![make_atom(0, 0, 1, false, true)];
        assert_native_matches_interpreted(atoms_b, Some(make_bound(0, 1, true)), None);
    }

    // --- Both bounds present ---

    #[cfg(any(target_arch = "aarch64", target_arch = "x86_64"))]
    #[test]
    fn test_native_both_bounds() {
        // Upper and lower atoms with both bounds.
        let atoms = vec![
            make_atom(0, 10, 1, true, false), // x <= 10
            make_atom(1, 5, 1, true, true),   // x < 5
            make_atom(2, 3, 1, false, false), // x >= 3
            make_atom(3, 8, 1, false, true),  // x > 8
        ];
        // lb=4, ub=6
        assert_native_matches_interpreted(
            atoms,
            Some(make_bound(4, 1, false)),
            Some(make_bound(6, 1, false)),
        );
    }

    // --- No bounds ---

    #[cfg(any(target_arch = "aarch64", target_arch = "x86_64"))]
    #[test]
    fn test_native_no_bounds() {
        let atoms = vec![
            make_atom(0, 5, 1, true, false),
            make_atom(1, 3, 1, false, false),
        ];
        assert_native_matches_interpreted(atoms, None, None);
    }

    // --- Large i64 values ---

    #[cfg(any(target_arch = "aarch64", target_arch = "x86_64"))]
    #[test]
    fn test_native_large_values() {
        let atoms = vec![make_atom(0, i64::MAX / 2, 1, true, false)];
        assert_native_matches_interpreted(
            atoms,
            None,
            Some(make_bound(i64::MAX / 2 - 1, 1, false)),
        );
    }

    // --- Compile failure cases ---

    #[test]
    fn test_compile_empty_returns_none() {
        let prop = VarPropagator::new(0, vec![]);
        let result = compile_native_propagator(&prop).expect("should not error");
        assert!(result.is_none());
    }

    #[test]
    fn test_compile_non_small_returns_none() {
        let atoms = vec![BoundAtom {
            atom_index: 0,
            bound_numer: 0,
            bound_denom: 1,
            is_upper: true,
            strict: false,
            is_small: false,
        }];
        let prop = VarPropagator::new(0, atoms);
        let result = compile_native_propagator(&prop).expect("should not error");
        assert!(result.is_none());
    }

    // --- Equivalence stress test ---

    /// Verify that TheoryPropJit::compile() actually produces native machine code
    /// propagators on supported platforms and that propagate_var() dispatches
    /// through the native path (not just the interpreted i128 fallback).
    #[cfg(any(target_arch = "aarch64", target_arch = "x86_64"))]
    #[test]
    fn test_native_compilation_wired_into_jit_pipeline() {
        use crate::theory_prop::TheoryPropJit;

        let mut jit = TheoryPropJit::new();
        // Eager native emission: this test exercises the native pipeline
        // directly (production defers behind the hotness threshold).
        jit.set_native_compile_threshold(0);

        let var0_atoms = vec![
            make_atom(0, 10, 1, true, false), // x <= 10
            make_atom(1, 5, 1, false, false), // x >= 5
        ];
        let var1_atoms = vec![
            make_atom(0, 3, 1, true, true),   // x < 3
            make_atom(1, -2, 1, false, true), // x > -2
        ];

        jit.compile(vec![(0, var0_atoms), (1, var1_atoms)]);

        // On aarch64/x86_64, all small-int atoms should produce native propagators.
        assert_eq!(
            jit.native_compiled_vars(),
            2,
            "Both variables should have native machine code propagators"
        );
        assert_eq!(jit.compiled_vars(), 2);
        assert_eq!(jit.total_atoms(), 4);
        assert_eq!(jit.small_atoms(), 4);

        // Verify that propagate_var dispatches through native and produces
        // correct results (native is tried first in propagate_var).
        let mut results = Vec::new();

        // var0: lb=6, ub=8 => x<=10 implied true, x>=5 implied true
        jit.propagate_var(
            0,
            Some(make_bound(6, 1, false)),
            Some(make_bound(8, 1, false)),
            &mut results,
        );
        let res: Vec<(u32, bool)> = results
            .iter()
            .map(|r| (r.atom_index, r.implied_value))
            .collect();
        assert!(
            res.contains(&(0, true)),
            "x<=10 should be implied true by ub=8"
        );
        assert!(
            res.contains(&(1, true)),
            "x>=5 should be implied true by lb=6"
        );

        // var1: lb=0, ub=2 => x<3 implied true (ub=2 < 3), x>-2 implied true (lb=0 > -2)
        jit.propagate_var(
            1,
            Some(make_bound(0, 1, false)),
            Some(make_bound(2, 1, false)),
            &mut results,
        );
        let res: Vec<(u32, bool)> = results
            .iter()
            .map(|r| (r.atom_index, r.implied_value))
            .collect();
        assert!(
            res.contains(&(0, true)),
            "x<3 should be implied true by ub=2"
        );
        assert!(
            res.contains(&(1, true)),
            "x>-2 should be implied true by lb=0"
        );
    }

    /// Verify that compile_native_propagators returns the expected count and
    /// that the returned NativeVarPropagator objects function correctly.
    #[cfg(any(target_arch = "aarch64", target_arch = "x86_64"))]
    #[test]
    fn test_compile_native_propagators_direct() {
        use crate::theory_prop::TheoryPropJit;

        let mut jit = TheoryPropJit::new();
        // Eager native emission for direct pipeline testing.
        jit.set_native_compile_threshold(0);

        // Mix of variables: some with small atoms, some empty.
        let var0_atoms = vec![
            make_atom(0, 100, 3, true, false), // x <= 100/3
            make_atom(1, -7, 2, false, true),  // x > -7/2
        ];
        // var1: no atoms (gap in variable IDs)
        let var5_atoms = vec![
            make_atom(0, 0, 1, true, false), // x <= 0
        ];

        jit.compile(vec![(0, var0_atoms), (5, var5_atoms)]);

        // Both variables with atoms should get native propagators.
        assert_eq!(jit.native_compiled_vars(), 2);

        // Test var0 propagation with rational bounds.
        let mut results = Vec::new();
        jit.propagate_var(
            0,
            Some(make_bound(-3, 1, false)), // lb = -3
            Some(make_bound(30, 1, false)), // ub = 30
            &mut results,
        );
        // ub=30 vs atom x<=100/3: 30*3=90 <= 100*1=100 => implied true
        let res: Vec<(u32, bool)> = results
            .iter()
            .map(|r| (r.atom_index, r.implied_value))
            .collect();
        assert!(
            res.contains(&(0, true)),
            "x<=100/3 should be implied true by ub=30"
        );
        // lb=-3 vs atom x>-7/2: -3*2=-6 > -7*1=-7 => implied true
        assert!(
            res.contains(&(1, true)),
            "x>-7/2 should be implied true by lb=-3"
        );

        // Test var5 propagation.
        jit.propagate_var(
            5,
            None,
            Some(make_bound(-1, 1, false)), // ub = -1
            &mut results,
        );
        // ub=-1 <= 0 => x<=0 implied true
        let res: Vec<(u32, bool)> = results
            .iter()
            .map(|r| (r.atom_index, r.implied_value))
            .collect();
        assert!(
            res.contains(&(0, true)),
            "x<=0 should be implied true by ub=-1"
        );
    }

    /// Differential test for the batched single-mapping compilation path:
    /// many variables compiled into ONE executable mapping must each produce
    /// results identical to their interpreted VarPropagator across a sweep
    /// of bound configurations.
    #[cfg(any(target_arch = "aarch64", target_arch = "x86_64"))]
    #[test]
    fn test_batched_native_matches_interpreted_per_var() {
        use crate::theory_prop::TheoryPropJit;

        // 24 variables with varied atom mixes (bounds, strictness, rationals),
        // plus deliberate gaps in the variable id space.
        let mut entries: Vec<(u32, Vec<BoundAtom>)> = Vec::new();
        for v in 0..24u32 {
            let var_id = v * 3; // gaps at non-multiples of 3
            let k = i64::from(v) - 12;
            let atoms = vec![
                make_atom(0, k, 1, true, v % 2 == 0),      // x <=/< k
                make_atom(1, k - 5, 1, false, v % 3 == 0), // x >=/> k-5
                make_atom(2, 2 * k + 1, 2, true, false),   // x <= (2k+1)/2
                make_atom(3, -k, 3, false, true),          // x > -k/3
            ];
            entries.push((var_id, atoms));
        }

        let mut jit = TheoryPropJit::new();
        jit.set_native_compile_threshold(0);
        jit.compile(entries.clone());
        assert_eq!(
            jit.native_compiled_vars(),
            24,
            "all 24 variables should be natively compiled into the batch"
        );

        let bounds: &[Option<SmallBound>] = &[
            None,
            Some(make_bound(-20, 1, false)),
            Some(make_bound(-3, 1, true)),
            Some(make_bound(0, 1, false)),
            Some(make_bound(7, 2, false)),
            Some(make_bound(15, 1, true)),
        ];

        let mut native_results = Vec::new();
        let mut interp_results = Vec::new();
        for (var_id, atoms) in &entries {
            let interp = VarPropagator::new(*var_id, atoms.clone());
            for &lb in bounds {
                for &ub in bounds {
                    jit.propagate_var(*var_id, lb, ub, &mut native_results);
                    interp.check_bounds(lb, ub, &mut interp_results);

                    let mut native_set: Vec<(u32, bool)> = native_results
                        .iter()
                        .map(|r| (r.atom_index, r.implied_value))
                        .collect();
                    native_set.sort_unstable();
                    let mut interp_set: Vec<(u32, bool)> = interp_results
                        .iter()
                        .map(|r| (r.atom_index, r.implied_value))
                        .collect();
                    interp_set.sort_unstable();

                    assert_eq!(
                        native_set, interp_set,
                        "batched native disagrees with interpreted for var {var_id}, lb={lb:?}, ub={ub:?}"
                    );
                }
            }
        }
    }

    #[cfg(any(target_arch = "aarch64", target_arch = "x86_64"))]
    #[test]
    fn test_native_equivalence_sweep() {
        // Test many combinations of atom types, bound values, and strictness.
        let test_values: &[i64] = &[-100, -10, -1, 0, 1, 5, 10, 100];
        let strictness = &[false, true];

        for &atom_numer in test_values {
            for &is_upper in &[true, false] {
                for &atom_strict in strictness {
                    let atoms = vec![make_atom(0, atom_numer, 1, is_upper, atom_strict)];

                    for &bound_numer in test_values {
                        for &bound_strict in strictness {
                            let bound = Some(make_bound(bound_numer, 1, bound_strict));

                            if is_upper {
                                // Test with ub
                                assert_native_matches_interpreted(atoms.clone(), None, bound);
                                // Test with lb
                                assert_native_matches_interpreted(atoms.clone(), bound, None);
                            } else {
                                // Test with lb
                                assert_native_matches_interpreted(atoms.clone(), bound, None);
                                // Test with ub
                                assert_native_matches_interpreted(atoms.clone(), None, bound);
                            }
                        }
                    }
                }
            }
        }
    }

    /// Regression test for P1 soundness bug: signed vs unsigned condition codes
    /// in i128 low-word comparison on aarch64.
    ///
    /// When the high words of two i128 cross-multiply products are equal and the
    /// low words straddle the i64 sign boundary (one >= 2^63, the other < 2^63),
    /// using signed conditions (COND_LT/COND_GT) instead of unsigned conditions
    /// (COND_LO/COND_HI) produces incorrect comparison results. The low word of
    /// a signed i128 is always an unsigned magnitude.
    ///
    /// This test constructs bound values whose cross-multiply products have equal
    /// high words but low words on opposite sides of the 2^63 boundary.
    #[cfg(any(target_arch = "aarch64", target_arch = "x86_64"))]
    #[test]
    fn test_native_i128_sign_boundary_low_word() {
        // Construction that makes high words equal but low words straddle 2^63:
        //
        //   atom = 0x180000000 / 0x100000000 (= 1.5)
        //   bound = 0x17FFFFFFF / 0x100000000 (~= 1.4999999998)
        //
        //   Cross products with multiplier a = 0x100000000:
        //     lhs = 0x17FFFFFFF * 0x100000000 = (high=1, low=0x7FFFFFFF00000000)
        //     rhs = 0x180000000 * 0x100000000 = (high=1, low=0x8000000000000000)
        //
        //   High words equal (both 1). Low words straddle 2^63:
        //     unsigned: 0x7FFFFFFF00000000 < 0x8000000000000000 (correct: lhs < rhs)
        //     signed:   0x7FFFFFFF00000000 > 0x8000000000000000 (wrong: 0x8000... is i64::MIN)

        // Atom: x <= 6442450944/4294967296 (= 1.5)
        let atom_n: i64 = 0x180000000;
        let atom_d: i64 = 0x100000000;
        let atoms_upper = vec![make_atom(0, atom_n, atom_d, true, false)];

        // ub = 6442450943/4294967296 (= 1.5 - epsilon)
        // The ub < atom, so x <= 1.5 should be implied TRUE
        let ub_n: i64 = 0x17FFFFFFF;
        let ub_d: i64 = 0x100000000;

        assert_native_matches_interpreted(atoms_upper, None, Some(make_bound(ub_n, ub_d, false)));

        // Atom: x >= 6442450944/4294967296 (= 1.5)
        let atoms_lower = vec![make_atom(0, atom_n, atom_d, false, false)];

        // lb = 6442450943/4294967296 (= 1.5 - epsilon)
        // lb < atom bound, so x >= 1.5 should NOT be implied true
        assert_native_matches_interpreted(
            atoms_lower.clone(),
            Some(make_bound(ub_n, ub_d, false)),
            None,
        );

        // lb = atom value exactly: x >= 1.5 should be implied true
        assert_native_matches_interpreted(
            atoms_lower,
            Some(make_bound(atom_n, atom_d, false)),
            None,
        );

        // Also test strict variants
        let atoms_upper_strict = vec![make_atom(0, atom_n, atom_d, true, true)];
        assert_native_matches_interpreted(
            atoms_upper_strict,
            None,
            Some(make_bound(ub_n, ub_d, false)),
        );

        let atoms_lower_strict = vec![make_atom(0, atom_n, atom_d, false, true)];
        assert_native_matches_interpreted(
            atoms_lower_strict,
            Some(make_bound(ub_n, ub_d, false)),
            None,
        );

        // Test the reverse direction: low word 0x8000... vs 0x7FFF...
        // Atom: x <= ub_n/ub_d (the smaller value)
        let atoms_reverse = vec![make_atom(0, ub_n, ub_d, true, false)];
        // ub = atom_n/atom_d (the larger value, 1.5)
        // ub > atom bound, so x <= (1.5-eps) is NOT implied true
        assert_native_matches_interpreted(
            atoms_reverse.clone(),
            None,
            Some(make_bound(atom_n, atom_d, false)),
        );

        // But lb = atom_n/atom_d (1.5 > 1.5-eps), so x <= (1.5-eps) IS implied false
        assert_native_matches_interpreted(
            atoms_reverse,
            Some(make_bound(atom_n, atom_d, false)),
            None,
        );
    }

    /// Proptest: verify that JIT native i128 comparison matches Rust native
    /// comparison for random i64 pairs used in cross-multiply.
    ///
    /// Generates random atom numerator/denominator and bound numerator/denominator,
    /// compiles a native propagator, and verifies the result matches the interpreted
    /// path. Covers both upper and lower atoms, strict and non-strict.
    #[cfg(any(target_arch = "aarch64", target_arch = "x86_64"))]
    mod proptest_native {
        use super::*;
        use proptest::prelude::*;

        proptest! {
            #[test]
            fn test_native_upper_nonstrict_random(
                atom_numer in prop::num::i64::ANY,
                atom_denom in 1i64..=i64::MAX,
                bound_numer in prop::num::i64::ANY,
                bound_denom in 1i64..=i64::MAX,
                bound_strict in proptest::bool::ANY,
            ) {
                let atoms = vec![make_atom(0, atom_numer, atom_denom, true, false)];
                let bound = Some(make_bound(bound_numer, bound_denom, bound_strict));

                // Test with ub
                assert_native_matches_interpreted(atoms.clone(), None, bound);
                // Test with lb
                assert_native_matches_interpreted(atoms, bound, None);
            }

            #[test]
            fn test_native_upper_strict_random(
                atom_numer in prop::num::i64::ANY,
                atom_denom in 1i64..=i64::MAX,
                bound_numer in prop::num::i64::ANY,
                bound_denom in 1i64..=i64::MAX,
                bound_strict in proptest::bool::ANY,
            ) {
                let atoms = vec![make_atom(0, atom_numer, atom_denom, true, true)];
                let bound = Some(make_bound(bound_numer, bound_denom, bound_strict));

                assert_native_matches_interpreted(atoms.clone(), None, bound);
                assert_native_matches_interpreted(atoms, bound, None);
            }

            #[test]
            fn test_native_lower_nonstrict_random(
                atom_numer in prop::num::i64::ANY,
                atom_denom in 1i64..=i64::MAX,
                bound_numer in prop::num::i64::ANY,
                bound_denom in 1i64..=i64::MAX,
                bound_strict in proptest::bool::ANY,
            ) {
                let atoms = vec![make_atom(0, atom_numer, atom_denom, false, false)];
                let bound = Some(make_bound(bound_numer, bound_denom, bound_strict));

                assert_native_matches_interpreted(atoms.clone(), bound, None);
                assert_native_matches_interpreted(atoms, None, bound);
            }

            #[test]
            fn test_native_lower_strict_random(
                atom_numer in prop::num::i64::ANY,
                atom_denom in 1i64..=i64::MAX,
                bound_numer in prop::num::i64::ANY,
                bound_denom in 1i64..=i64::MAX,
                bound_strict in proptest::bool::ANY,
            ) {
                let atoms = vec![make_atom(0, atom_numer, atom_denom, false, true)];
                let bound = Some(make_bound(bound_numer, bound_denom, bound_strict));

                assert_native_matches_interpreted(atoms.clone(), bound, None);
                assert_native_matches_interpreted(atoms, None, bound);
            }

            #[test]
            fn test_native_both_bounds_random(
                atom_numer in prop::num::i64::ANY,
                atom_denom in 1i64..=i64::MAX,
                is_upper in proptest::bool::ANY,
                strict in proptest::bool::ANY,
                lb_numer in prop::num::i64::ANY,
                lb_denom in 1i64..=i64::MAX,
                lb_strict in proptest::bool::ANY,
                ub_numer in prop::num::i64::ANY,
                ub_denom in 1i64..=i64::MAX,
                ub_strict in proptest::bool::ANY,
            ) {
                let atoms = vec![make_atom(0, atom_numer, atom_denom, is_upper, strict)];
                let lb = Some(make_bound(lb_numer, lb_denom, lb_strict));
                let ub = Some(make_bound(ub_numer, ub_denom, ub_strict));

                assert_native_matches_interpreted(atoms, lb, ub);
            }
        }
    }
}
