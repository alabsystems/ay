// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Minimal aarch64 assembler for SAT clause propagation functions.
//!
//! Supports only the instruction subset needed for BCP: load/store (byte,
//! word, doubleword), compare/branch, integer arithmetic, and the standard
//! function call convention. No floating-point, SIMD, or atomics.
//!
//! All instructions are 4 bytes (one u32 word). Branch targets use a
//! label + fixup system for forward references, resolved in `finalize()`.

/// General-purpose register (0-30) or zero register / stack pointer (31).
#[derive(Clone, Copy, PartialEq, Eq)]
pub(crate) struct Reg(pub u8);

// ISA completeness: Reg::x() is part of the register API even if not all
// callers use it directly (some construct Reg(n) instead).
impl Reg {
    pub const fn x(n: u8) -> Self {
        debug_assert!(n <= 30, "use XZR or SP for register 31");
        Self(n)
    }
}

// Fixed register assignments for propagation functions.
//
// Register-based calling convention (#8260): propagation state arrives
// directly in registers from the caller, eliminating the struct-pointer
// indirection. On aarch64, the C ABI delivers the 6 pointer/scalar
// arguments in x0-x5:
//
//   x0 = conflict_ptr  (where to write conflict clause_id)
//   x1 = vals           (literal assignment values)
//   x2 = trail          (trail array for enqueuing propagations)
//   x3 = trail_len_ptr  (pointer to current trail length)
//   x4 = guards         (clause guard bytes)
//   x5 = reasons        (reason clause_id per variable)
//
// This eliminates:
//   - 5 LDR instructions in the callee prologue (loading from struct)
//   - 7-9 STR instructions in the caller (building the struct)
//   - Net savings: ~15 instructions per JIT function call

/// Conflict pointer (first arg, x0). JIT writes clause_id here on conflict.
pub(crate) const CONFLICT_PTR: Reg = Reg(0);
/// vals pointer (second arg, x1).
pub(crate) const VALS: Reg = Reg(1);
/// trail pointer (third arg, x2).
pub(crate) const TRAIL: Reg = Reg(2);
/// trail_len pointer (fourth arg, x3).
pub(crate) const TRAIL_LEN_PTR: Reg = Reg(3);
/// guards pointer (fifth arg, x4).
pub(crate) const GUARDS: Reg = Reg(4);
/// reasons pointer (sixth arg, x5).
pub(crate) const REASONS: Reg = Reg(5);
/// Current trail_len value (updated on enqueue).
pub(crate) const TRAIL_LEN: Reg = Reg(6);
/// Constant 1 (pre-loaded for EOR and enqueue).
pub(crate) const CONST_ONE: Reg = Reg(15);

// Scratch registers for clause bodies (T3-T7 used dynamically via Reg(T0.0 + i)).
pub(crate) const T0: Reg = Reg(7);
pub(crate) const T1: Reg = Reg(8);
pub(crate) const T2: Reg = Reg(9);
// ISA completeness: T3-T7 are available scratch registers for clauses with
// many watched literals. Used dynamically via Reg(T0.0 + i) indexing.
#[allow(dead_code)]
pub(crate) const T3: Reg = Reg(10);
#[allow(dead_code)]
pub(crate) const T4: Reg = Reg(11);
#[allow(dead_code)]
pub(crate) const T5: Reg = Reg(12);
#[allow(dead_code)]
pub(crate) const T6: Reg = Reg(13);
#[allow(dead_code)]
pub(crate) const T7: Reg = Reg(14);
// T8/T9 for additional scratch when needed.
pub(crate) const T8: Reg = Reg(16);
pub(crate) const T9: Reg = Reg(17);

// ISA completeness: standard aarch64 register aliases for ABI conformance.
#[allow(dead_code)]
pub(crate) const XZR: Reg = Reg(31);
#[allow(dead_code)]
pub(crate) const SP: Reg = Reg(31);
#[allow(dead_code)]
pub(crate) const FP: Reg = Reg(29);
#[allow(dead_code)]
pub(crate) const LR: Reg = Reg(30);

/// Condition codes for B.cond and CSEL.
/// ISA completeness: all standard AArch64 signed comparison conditions.
#[derive(Clone, Copy)]
#[repr(u8)]
#[allow(dead_code)] // ISA completeness: not all conditions used in current codegen
pub(crate) enum Cond {
    Eq = 0b0000,
    Ne = 0b0001,
    Gt = 0b1100,
    Ge = 0b1010,
    Lt = 0b1011,
    Le = 0b1101,
}

/// A branch target label. Created with `new_label()`, bound with `bind()`.
#[derive(Clone, Copy)]
pub(crate) struct Label(u32);

/// Pending branch fixup for forward references.
struct Fixup {
    /// Index into `code` (in u32 words) where the branch instruction lives.
    offset: u32,
    /// Target label.
    label: Label,
    /// Encoding format.
    kind: FixupKind,
}

#[derive(Clone, Copy)]
enum FixupKind {
    /// B.cond / CBZ / CBNZ: imm19 in bits [23:5], signed offset in 4-byte units.
    Imm19,
    /// B: imm26 in bits [25:0], signed offset in 4-byte units.
    Imm26,
}

/// Minimal aarch64 assembler. Accumulates instructions and resolves
/// branch labels on `finalize()`.
pub(crate) struct Assembler {
    code: Vec<u32>,
    labels: Vec<Option<u32>>,
    fixups: Vec<Fixup>,
}

impl Assembler {
    pub fn new() -> Self {
        Self {
            code: Vec::with_capacity(256),
            labels: Vec::new(),
            fixups: Vec::new(),
        }
    }

    /// Create a new unbound label.
    pub fn label(&mut self) -> Label {
        let id = self.labels.len() as u32;
        self.labels.push(None);
        Label(id)
    }

    /// Bind a label to the current code position.
    pub fn bind(&mut self, label: Label) {
        let offset = self.code.len() as u32;
        debug_assert!(
            self.labels[label.0 as usize].is_none(),
            "label already bound"
        );
        self.labels[label.0 as usize] = Some(offset);
    }

    /// Current code offset in u32 words.
    #[allow(dead_code)] // ISA completeness
    pub fn pos(&self) -> u32 {
        self.code.len() as u32
    }

    fn emit(&mut self, instr: u32) {
        self.code.push(instr);
    }

    /// Emit a raw 32-bit instruction word. Used by modules that need
    /// addressing modes not covered by the typed helpers (e.g., conflict_jit).
    pub(crate) fn emit_raw(&mut self, instr: u32) {
        self.code.push(instr);
    }

    fn emit_branch(&mut self, base: u32, label: Label, kind: FixupKind) {
        self.fixups.push(Fixup {
            offset: self.code.len() as u32,
            label,
            kind,
        });
        self.code.push(base);
    }

    // ---- Function prologue/epilogue ----

    /// STP x29, x30, [sp, #-16]!
    pub fn prologue(&mut self) {
        self.emit(0xa9bf7bfd);
        // MOV x29, sp
        self.emit(0x910003fd);
    }

    /// LDP x29, x30, [sp], #16; RET
    pub fn epilogue(&mut self) {
        self.emit(0xa8c17bfd);
        self.emit(0xd65f03c0);
    }

    /// RET — bare return for leaf functions (no frame restore).
    pub fn emit_ret(&mut self) {
        self.emit(0xd65f03c0);
    }

    // ---- Load/Store (unsigned immediate offset) ----

    /// LDR Xt, [Xn, #imm] — 64-bit load, imm must be 8-byte aligned.
    #[allow(dead_code)] // ISA completeness
    pub fn ldr_x_uimm(&mut self, rt: Reg, rn: Reg, byte_offset: u32) {
        debug_assert!(byte_offset.is_multiple_of(8) && byte_offset / 8 < 4096);
        let imm12 = byte_offset / 8;
        self.emit(0xf9400000 | (imm12 << 10) | (u32::from(rn.0) << 5) | u32::from(rt.0));
    }

    /// LDR Wt, [Xn, #imm] — 32-bit load, imm must be 4-byte aligned.
    pub fn ldr_w_uimm(&mut self, rt: Reg, rn: Reg, byte_offset: u32) {
        debug_assert!(byte_offset.is_multiple_of(4) && byte_offset / 4 < 4096);
        let imm12 = byte_offset / 4;
        self.emit(0xb9400000 | (imm12 << 10) | (u32::from(rn.0) << 5) | u32::from(rt.0));
    }

    /// LDRSB Wt, [Xn, #imm] — sign-extending byte load to 32-bit.
    pub fn ldrsb_w_uimm(&mut self, rt: Reg, rn: Reg, byte_offset: u32) {
        debug_assert!(byte_offset < 4096);
        self.emit(0x39c00000 | (byte_offset << 10) | (u32::from(rn.0) << 5) | u32::from(rt.0));
    }

    /// LDRSB Wt, [Xn, Xm] — sign-extending byte load, register offset.
    pub fn ldrsb_w_reg(&mut self, rt: Reg, rn: Reg, rm: Reg) {
        // option=011 (LSL), S=0
        self.emit(0x38e06800 | (u32::from(rm.0) << 16) | (u32::from(rn.0) << 5) | u32::from(rt.0));
    }

    /// LDRB Wt, [Xn, #imm] — unsigned byte load.
    pub fn ldrb_w_uimm(&mut self, rt: Reg, rn: Reg, byte_offset: u32) {
        debug_assert!(byte_offset < 4096);
        self.emit(0x39400000 | (byte_offset << 10) | (u32::from(rn.0) << 5) | u32::from(rt.0));
    }

    /// STRB Wt, [Xn, #imm] — byte store with unsigned immediate offset.
    pub fn strb_w_uimm(&mut self, rt: Reg, rn: Reg, byte_offset: u32) {
        debug_assert!(byte_offset < 4096);
        self.emit(0x39000000 | (byte_offset << 10) | (u32::from(rn.0) << 5) | u32::from(rt.0));
    }

    /// STRB Wt, [Xn, Xm] — byte store with register offset.
    pub fn strb_w_reg(&mut self, rt: Reg, rn: Reg, rm: Reg) {
        // option=011 (LSL), S=0
        self.emit(0x38206800 | (u32::from(rm.0) << 16) | (u32::from(rn.0) << 5) | u32::from(rt.0));
    }

    /// STR Wt, [Xn, #imm] — 32-bit store, imm must be 4-byte aligned.
    pub fn str_w_uimm(&mut self, rt: Reg, rn: Reg, byte_offset: u32) {
        debug_assert!(byte_offset.is_multiple_of(4) && byte_offset / 4 < 4096);
        let imm12 = byte_offset / 4;
        self.emit(0xb9000000 | (imm12 << 10) | (u32::from(rn.0) << 5) | u32::from(rt.0));
    }

    /// STR Wt, [Xn, Xm, LSL #2] — 32-bit store with register offset, scaled.
    pub fn str_w_reg_lsl2(&mut self, rt: Reg, rn: Reg, rm: Reg) {
        // option=011 (LSL), S=1 (scale by 4)
        self.emit(0xb8207800 | (u32::from(rm.0) << 16) | (u32::from(rn.0) << 5) | u32::from(rt.0));
    }

    // ---- Move / Immediate ----

    /// MOVZ Wd, #imm16 — move 16-bit immediate to Wd, zero upper bits.
    pub fn movz_w(&mut self, rd: Reg, imm16: u16) {
        self.emit(0x52800000 | (u32::from(imm16) << 5) | u32::from(rd.0));
    }

    /// MOVZ Wd, #imm16, LSL #16 — move 16-bit immediate to upper half-word.
    pub fn movz_w_lsl16(&mut self, rd: Reg, imm16: u16) {
        self.emit(0x52a00000 | (u32::from(imm16) << 5) | u32::from(rd.0));
    }

    /// MOVK Wd, #imm16 — move 16-bit immediate, keep other bits.
    #[allow(dead_code)] // ISA completeness
    pub fn movk_w(&mut self, rd: Reg, imm16: u16) {
        self.emit(0x72800000 | (u32::from(imm16) << 5) | u32::from(rd.0));
    }

    /// MOVK Wd, #imm16, LSL #16 — move 16-bit to upper half, keep lower.
    #[allow(dead_code)] // ISA completeness
    pub fn movk_w_lsl16(&mut self, rd: Reg, imm16: u16) {
        self.emit(0x72a00000 | (u32::from(imm16) << 5) | u32::from(rd.0));
    }

    /// Load a 32-bit immediate into Wd. Uses MOVZ for 16-bit values,
    /// MOVZ+MOVK for larger values.
    pub fn mov_imm32(&mut self, rd: Reg, value: u32) {
        let lo = value as u16;
        let hi = (value >> 16) as u16;
        if hi == 0 {
            self.movz_w(rd, lo);
        } else if lo == 0 {
            self.movz_w_lsl16(rd, hi);
        } else {
            self.movz_w(rd, lo);
            self.movk_w_lsl16(rd, hi);
        }
    }

    /// MOV Wd, Wm (alias for ORR Wd, WZR, Wm).
    #[allow(dead_code)] // ISA completeness
    pub fn mov_w(&mut self, rd: Reg, rm: Reg) {
        self.emit(0x2a0003e0 | (u32::from(rm.0) << 16) | u32::from(rd.0));
    }

    /// MOV Xd, Xm (alias for ORR Xd, XZR, Xm).
    #[allow(dead_code)] // ISA completeness
    pub fn mov_x(&mut self, rd: Reg, rm: Reg) {
        self.emit(0xaa0003e0 | (u32::from(rm.0) << 16) | u32::from(rd.0));
    }

    // ---- Arithmetic ----

    /// ADD Wd, Wn, #imm12.
    pub fn add_w_imm(&mut self, rd: Reg, rn: Reg, imm12: u32) {
        debug_assert!(imm12 < 4096);
        self.emit(0x11000000 | (imm12 << 10) | (u32::from(rn.0) << 5) | u32::from(rd.0));
    }

    /// ADD Xd, Xn, #imm12.
    #[allow(dead_code)] // ISA completeness
    pub fn add_x_imm(&mut self, rd: Reg, rn: Reg, imm12: u32) {
        debug_assert!(imm12 < 4096);
        self.emit(0x91000000 | (imm12 << 10) | (u32::from(rn.0) << 5) | u32::from(rd.0));
    }

    /// ADD Xd, Xn, Xm.
    #[allow(dead_code)] // ISA completeness
    pub fn add_x_reg(&mut self, rd: Reg, rn: Reg, rm: Reg) {
        self.emit(0x8b000000 | (u32::from(rm.0) << 16) | (u32::from(rn.0) << 5) | u32::from(rd.0));
    }

    /// SUB Wd, Wn, Wm.
    #[allow(dead_code)] // ISA completeness
    pub fn sub_w_reg(&mut self, rd: Reg, rn: Reg, rm: Reg) {
        self.emit(0x4b000000 | (u32::from(rm.0) << 16) | (u32::from(rn.0) << 5) | u32::from(rd.0));
    }

    /// LSR Wd, Wn, #shift (UBFM Wd, Wn, #shift, #31).
    pub fn lsr_w_imm(&mut self, rd: Reg, rn: Reg, shift: u32) {
        debug_assert!(shift > 0 && shift < 32);
        let immr = shift;
        let imms = 31;
        self.emit(
            0x53000000 | (immr << 16) | (imms << 10) | (u32::from(rn.0) << 5) | u32::from(rd.0),
        );
    }

    /// EOR Wd, Wn, Wm.
    pub fn eor_w_reg(&mut self, rd: Reg, rn: Reg, rm: Reg) {
        self.emit(0x4a000000 | (u32::from(rm.0) << 16) | (u32::from(rn.0) << 5) | u32::from(rd.0));
    }

    // ---- Compare ----

    /// CMP Wn, #imm12 (SUBS WZR, Wn, #imm12).
    pub fn cmp_w_imm(&mut self, rn: Reg, imm12: u32) {
        debug_assert!(imm12 < 4096);
        self.emit(0x7100001f | (imm12 << 10) | (u32::from(rn.0) << 5));
    }

    // ---- Conditional select ----

    /// CSEL Wd, Wn, Wm, cond — if cond then Wd=Wn else Wd=Wm.
    pub fn csel_w(&mut self, rd: Reg, rn: Reg, rm: Reg, cond: Cond) {
        self.emit(
            0x1a800000
                | (u32::from(rm.0) << 16)
                | ((cond as u32) << 12)
                | (u32::from(rn.0) << 5)
                | u32::from(rd.0),
        );
    }

    // ---- Branches ----

    /// B label — unconditional branch.
    pub fn b(&mut self, label: Label) {
        self.emit_branch(0x14000000, label, FixupKind::Imm26);
    }

    /// B.cond label — conditional branch.
    pub fn b_cond(&mut self, cond: Cond, label: Label) {
        self.emit_branch(0x54000000 | cond as u32, label, FixupKind::Imm19);
    }

    /// CBZ Wn, label — branch if Wn == 0.
    pub fn cbz_w(&mut self, rt: Reg, label: Label) {
        self.emit_branch(0x34000000 | u32::from(rt.0), label, FixupKind::Imm19);
    }

    /// CBNZ Wn, label — branch if Wn != 0.
    #[allow(dead_code)] // ISA completeness
    pub fn cbnz_w(&mut self, rt: Reg, label: Label) {
        self.emit_branch(0x35000000 | u32::from(rt.0), label, FixupKind::Imm19);
    }

    // ---- Finalization ----

    /// Resolve all branch fixups and return the code as u32 instruction words.
    /// Used by template generation to get raw instruction words for diffing.
    pub fn finalize_u32(mut self) -> Vec<u32> {
        for fixup in &self.fixups {
            // INVARIANT: Every `Label` returned by `new_label()` must be
            // bound exactly once via `bind()` before `finalize*()` is called.
            // A missing bind is an assembler-internal bug in the caller, not a
            // user-input error — the assembler API does not allow any input
            // that could reach here with an unbound label.
            let target = self.labels[fixup.label.0 as usize]
                .expect("invariant: all emitted branch labels must be bound before finalize_u32");
            let delta = target as i32 - fixup.offset as i32;

            match fixup.kind {
                FixupKind::Imm19 => {
                    assert!(
                        (-(1 << 18)..(1 << 18)).contains(&delta),
                        "branch offset out of imm19 range: {delta}"
                    );
                    let imm19 = (delta as u32) & 0x7ffff;
                    self.code[fixup.offset as usize] |= imm19 << 5;
                }
                FixupKind::Imm26 => {
                    assert!(
                        (-(1 << 25)..(1 << 25)).contains(&delta),
                        "branch offset out of imm26 range: {delta}"
                    );
                    let imm26 = (delta as u32) & 0x3ffffff;
                    self.code[fixup.offset as usize] |= imm26;
                }
            }
        }
        self.code
    }

    /// Resolve all branch fixups and return the code as a byte vector.
    ///
    /// Panics only on assembler-internal invariant violations: every label
    /// returned by `new_label()` must be bound via `bind()` before calling
    /// `finalize()`, and every branch offset must fit in its immediate field.
    /// These are programmer-invariant failures, not user-input failures — no
    /// external input can reach these paths.
    pub fn finalize(mut self) -> Vec<u8> {
        for fixup in &self.fixups {
            // INVARIANT: see doc comment on this function.
            let target = self.labels[fixup.label.0 as usize]
                .expect("invariant: all emitted branch labels must be bound before finalize");
            let delta = target as i32 - fixup.offset as i32; // in u32 words

            match fixup.kind {
                FixupKind::Imm19 => {
                    assert!(
                        (-(1 << 18)..(1 << 18)).contains(&delta),
                        "branch offset out of imm19 range: {delta}"
                    );
                    let imm19 = (delta as u32) & 0x7ffff;
                    self.code[fixup.offset as usize] |= imm19 << 5;
                }
                FixupKind::Imm26 => {
                    assert!(
                        (-(1 << 25)..(1 << 25)).contains(&delta),
                        "branch offset out of imm26 range: {delta}"
                    );
                    let imm26 = (delta as u32) & 0x3ffffff;
                    self.code[fixup.offset as usize] |= imm26;
                }
            }
        }

        // Convert u32 instructions to little-endian bytes.
        let mut bytes = Vec::with_capacity(self.code.len() * 4);
        for &instr in &self.code {
            bytes.extend_from_slice(&instr.to_le_bytes());
        }
        bytes
    }

    // ---- Prefetch (#8264) ----

    /// PRFM PLDL1KEEP, [Xn, #imm] — prefetch for load, L1 cache, temporal.
    /// Byte offset is rounded down to 8-byte alignment as required by the
    /// encoding (imm12 is scaled by 8). Rt field = 0b00000 selects PLDL1KEEP.
    pub fn prfm_pldl1keep_uimm(&mut self, rn: Reg, byte_offset: u32) {
        let aligned = byte_offset & !7;
        let imm12 = aligned / 8;
        debug_assert!(imm12 < 4096, "prefetch offset too large: {byte_offset}");
        // PRFM (immediate): 11_111_0_01_10_imm12_Rn_Rt where Rt=0 (PLDL1KEEP)
        self.emit(0xf9800000 | (imm12 << 10) | (u32::from(rn.0) << 5));
    }

    /// PRFM PLDL1KEEP, [Xn, Xm] — prefetch with register offset.
    /// option=011 (LSL), S=0. Rt field = 0b00000 selects PLDL1KEEP.
    pub fn prfm_pldl1keep_reg(&mut self, rn: Reg, rm: Reg) {
        // PRFM (register): 11_111_0_00_10_1_Rm_option_S_10_Rn_Rt
        self.emit(0xf8a06800 | (u32::from(rm.0) << 16) | (u32::from(rn.0) << 5));
    }

    // ---- High-level helpers for propagation codegen ----

    /// Prefetch vals[lit_encoded] into L1 data cache (#8264).
    /// Uses immediate offset for small literals, register offset for large.
    pub fn prefetch_val(&mut self, lit_encoded: u32) {
        if lit_encoded < 32768 {
            self.prfm_pldl1keep_uimm(VALS, lit_encoded);
        } else {
            self.mov_imm32(T8, lit_encoded);
            self.prfm_pldl1keep_reg(VALS, T8);
        }
    }

    /// Load a sign-extended byte from vals[lit_encoded] into `dst`.
    /// Uses immediate or register offset depending on the literal value.
    pub fn load_val(&mut self, dst: Reg, lit_encoded: u32) {
        if lit_encoded < 4096 {
            self.ldrsb_w_uimm(dst, VALS, lit_encoded);
        } else {
            self.mov_imm32(T8, lit_encoded);
            self.ldrsb_w_reg(dst, VALS, T8);
        }
    }

    /// Load a guard byte from guards[clause_id] into `dst`.
    pub fn load_guard(&mut self, dst: Reg, clause_id: u32) {
        if clause_id < 4096 {
            self.ldrb_w_uimm(dst, GUARDS, clause_id);
        } else {
            self.mov_imm32(T8, clause_id);
            // LDRB Wt, [Xn, Xm] — same as LDRSB but opc=01 instead of 11
            // Actually we need unsigned byte load with register offset.
            // Encoding: 0x38606800 | (Rm<<16) | (Rn<<5) | Rt
            // size=00, V=0, opc=01, option=011, S=0
            self.emit(
                0x38606800
                    | (u32::from(T8.0) << 16)
                    | (u32::from(GUARDS.0) << 5)
                    | u32::from(dst.0),
            );
        }
    }

    /// Emit enqueue of a compile-time literal with a given clause_id as reason.
    /// Updates trail, trail_len (w6), reasons, and vals.
    pub fn emit_enqueue_const(&mut self, lit_encoded: u32, clause_id: u32) {
        let var = lit_encoded >> 1;
        let neg_lit = lit_encoded ^ 1;

        // trail[trail_len] = lit_encoded
        self.mov_imm32(T0, lit_encoded);
        self.str_w_reg_lsl2(T0, TRAIL, TRAIL_LEN);

        // trail_len++
        self.add_w_imm(TRAIL_LEN, TRAIL_LEN, 1);
        self.str_w_uimm(TRAIL_LEN, TRAIL_LEN_PTR, 0);

        // reasons[var] = clause_id
        self.mov_imm32(T0, clause_id);
        self.mov_imm32(T1, var);
        self.str_w_reg_lsl2(T0, REASONS, T1);

        // vals[lit_encoded] = 1
        if lit_encoded < 4096 {
            self.strb_w_uimm(CONST_ONE, VALS, lit_encoded);
        } else {
            self.mov_imm32(T0, lit_encoded);
            self.strb_w_reg(CONST_ONE, VALS, T0);
        }

        // vals[lit_encoded ^ 1] = 0xFF (-1 as i8)
        self.mov_imm32(T0, 0xFF);
        if neg_lit < 4096 {
            self.strb_w_uimm(T0, VALS, neg_lit);
        } else {
            self.mov_imm32(T1, neg_lit);
            self.strb_w_reg(T0, VALS, T1);
        }
    }

    /// Emit enqueue of a runtime literal (in register `lit_reg`) with
    /// a compile-time clause_id. Uses T0-T2 as scratch.
    pub fn emit_enqueue_runtime(&mut self, lit_reg: Reg, clause_id: u32) {
        // trail[trail_len] = lit_reg
        self.str_w_reg_lsl2(lit_reg, TRAIL, TRAIL_LEN);

        // trail_len++
        self.add_w_imm(TRAIL_LEN, TRAIL_LEN, 1);
        self.str_w_uimm(TRAIL_LEN, TRAIL_LEN_PTR, 0);

        // reasons[var(lit)] = clause_id; var = lit >> 1
        self.lsr_w_imm(T0, lit_reg, 1);
        self.mov_imm32(T1, clause_id);
        self.str_w_reg_lsl2(T1, REASONS, T0);

        // vals[lit] = 1 (lit_reg value as byte offset via register)
        self.strb_w_reg(CONST_ONE, VALS, lit_reg);

        // vals[lit ^ 1] = 0xFF (-1)
        self.eor_w_reg(T0, lit_reg, CONST_ONE); // T0 = lit ^ 1
        self.mov_imm32(T1, 0xFF);
        self.strb_w_reg(T1, VALS, T0);
    }

    /// Emit conflict: store clause_id to *conflict_ptr, return 1.
    ///
    /// Register-based calling convention (#8260): CONFLICT_PTR (x0) holds
    /// the conflict pointer directly — no need to load it from a struct.
    /// This saves 1 LDR instruction per conflict path.
    pub fn emit_conflict(&mut self, clause_id: u32) {
        // CONFLICT_PTR (x0) already holds the conflict pointer (passed as arg).
        self.mov_imm32(T0, clause_id);
        self.str_w_uimm(T0, CONFLICT_PTR, 0);
        // return 1 — note: CONFLICT_PTR is x0, so we must set x0=1 AFTER
        // the store (which reads x0 as the base address).
        self.movz_w(Reg(0), 1);
        self.epilogue();
    }
}
