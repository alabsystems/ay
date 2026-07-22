// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! JIT compilation of CHC expression evaluation to native code.
//!
//! The implication cache (`SmallModel::evaluate`) walks recursive `ChcExpr`
//! trees doing HashMap lookups at every variable node. This module compiles
//! frequently-evaluated expressions into native functions that:
//!
//! 1. Read variable values from a flat `&[i64]` array (index known at compile time)
//! 2. Evaluate arithmetic and boolean operations via native instructions
//! 3. Return the result as an `i64` (booleans: 0=false, 1=true, -1=indeterminate)
//!
//! ## Architecture
//!
//! Expressions are first flattened into a linear opcode sequence, then compiled
//! to native code using a self-contained 64-bit assembler (aarch64 or x86_64).
//! The assembler is separate from the SAT BCP assembler because expression
//! evaluation needs 64-bit arithmetic (i64 values) while BCP uses 8/32-bit ops.
//!
//! ## Integration
//!
//! The `CompiledExprEval` is cached alongside the expression in the implication
//! cache. When an expression is evaluated more than N times, it is JIT-compiled,
//! and subsequent evaluations call the native function directly.

use std::collections::BTreeMap;

use crate::executable::ExecutableMemory;
use crate::JitError;

// ---------------------------------------------------------------------------
// Variable mapping: name -> flat array index
// ---------------------------------------------------------------------------

/// Maps variable names to flat array indices for the compiled evaluator.
///
/// At compile time, each unique variable in the expression is assigned an index
/// (0..n_vars). At evaluation time, the caller fills a flat `&[i64]` array with
/// variable values at these indices. This replaces HashMap lookups with direct
/// array indexing.
#[derive(Debug, Clone)]
pub struct VarMapping {
    /// Variable name to index mapping.
    name_to_index: BTreeMap<String, u32>,
    /// Number of integer variables.
    pub(crate) num_int_vars: u32,
    /// Number of boolean variables (stored after int vars in the flat array).
    pub(crate) num_bool_vars: u32,
}

impl Default for VarMapping {
    fn default() -> Self {
        Self::new()
    }
}

impl VarMapping {
    /// Create a new empty variable mapping.
    pub fn new() -> Self {
        Self {
            name_to_index: BTreeMap::new(),
            num_int_vars: 0,
            num_bool_vars: 0,
        }
    }

    /// Get or assign an index for an integer variable.
    pub fn get_or_insert_int(&mut self, name: &str) -> u32 {
        if let Some(&idx) = self.name_to_index.get(name) {
            return idx;
        }
        let idx = self.num_int_vars + self.num_bool_vars;
        self.name_to_index.insert(name.to_string(), idx);
        self.num_int_vars += 1;
        idx
    }

    /// Get or assign an index for a boolean variable.
    pub fn get_or_insert_bool(&mut self, name: &str) -> u32 {
        if let Some(&idx) = self.name_to_index.get(name) {
            return idx;
        }
        let idx = self.num_int_vars + self.num_bool_vars;
        self.name_to_index.insert(name.to_string(), idx);
        self.num_bool_vars += 1;
        idx
    }

    /// Look up an index by name.
    pub fn get(&self, name: &str) -> Option<u32> {
        self.name_to_index.get(name).copied()
    }

    /// Total number of variables (int + bool).
    pub fn total_vars(&self) -> u32 {
        self.num_int_vars + self.num_bool_vars
    }

    /// Iterate over (name, index) pairs.
    pub fn iter(&self) -> impl Iterator<Item = (&str, &u32)> {
        self.name_to_index.iter().map(|(k, v)| (k.as_str(), v))
    }
}

// ---------------------------------------------------------------------------
// Flattened opcode sequence
// ---------------------------------------------------------------------------

/// Opcodes for a flattened expression evaluation sequence.
///
/// The expression tree is linearized into a post-order sequence of operations.
/// Each opcode either pushes a value onto a virtual stack or consumes values
/// from it. The final stack value is the expression result.
#[derive(Debug, Clone)]
pub enum ExprOpcode {
    /// Push boolean constant (0 or 1).
    PushBool(bool),
    /// Push integer constant.
    PushInt(i64),
    /// Push variable value from flat array at given index.
    LoadIntVar(u32),
    /// Push boolean variable value from flat array at given index.
    LoadBoolVar(u32),

    // Arithmetic (operate on top stack values)
    /// Pop two, push sum.
    Add,
    /// Pop two (a then b), push a - b.
    Sub,
    /// Pop two, push product.
    Mul,
    /// Pop one, push negation.
    Neg,
    /// Pop two (a then b), push Euclidean div.
    Div,
    /// Pop two (a then b), push Euclidean mod.
    Mod,

    // Comparisons (pop two ints, push bool)
    CmpEq,
    CmpNe,
    CmpLt,
    CmpLe,
    CmpGt,
    CmpGe,

    // Boolean
    /// Pop one bool, push NOT.
    Not,
    /// N-ary AND with short-circuit. Operand count follows.
    And(u16),
    /// N-ary OR with short-circuit. Operand count follows.
    Or(u16),
    /// Pop two bools (a then b), push a => b.
    Implies,

    /// Pop cond, then_val, else_val; push result.
    Ite,
}

// ---------------------------------------------------------------------------
// Compiled expression evaluator
// ---------------------------------------------------------------------------

/// Type alias for the compiled evaluation function.
/// Signature: `extern "C" fn(vars: *const i64) -> i64`
///
/// - `vars`: flat array of i64 values indexed by VarMapping
/// - Returns: for boolean exprs 0=false, 1=true; for int exprs the i64 value
type EvalFn = unsafe extern "C" fn(*const i64) -> i64;

/// A JIT-compiled expression evaluator.
///
/// Holds the compiled native function, the variable mapping needed to fill
/// the input array, and the backing executable memory.
pub struct CompiledExprEval {
    /// The compiled native function.
    func: EvalFn,
    /// Variable name to flat array index mapping.
    pub(crate) var_mapping: VarMapping,
    /// Whether this expression returns a boolean (vs integer).
    pub(crate) is_boolean: bool,
    /// Backing executable memory (must outlive func).
    _executable: ExecutableMemory,
}

// SAFETY: The compiled function pointer points into immutable executable memory.
// The function is pure (reads only from the vars array, no side effects).
unsafe impl Send for CompiledExprEval {}
unsafe impl Sync for CompiledExprEval {}

impl CompiledExprEval {
    /// Evaluate the compiled expression with the given variable values.
    ///
    /// `vars` must have length >= `var_mapping.total_vars()`. Each entry
    /// corresponds to the variable at that index in the mapping. Boolean
    /// variables use 0 (false) or 1 (true).
    ///
    /// Returns the raw i64 result. For boolean expressions, 0=false, 1=true.
    ///
    /// # Safety
    ///
    /// The `vars` slice must be at least `var_mapping.total_vars()` elements.
    #[inline]
    pub unsafe fn evaluate_raw(&self, vars: &[i64]) -> i64 {
        debug_assert!(
            vars.len() >= self.var_mapping.total_vars() as usize,
            "vars array too small: {} < {}",
            vars.len(),
            self.var_mapping.total_vars()
        );
        // SAFETY: Caller guarantees vars has sufficient length. The compiled
        // function reads from vars at compile-time-known indices that are
        // bounded by total_vars(). The function pointer is valid because
        // _executable is alive.
        unsafe { (self.func)(vars.as_ptr()) }
    }

    /// Evaluate and return `Option<bool>` for boolean expressions.
    ///
    /// # Safety
    ///
    /// Same requirements as `evaluate_raw`.
    #[inline]
    pub unsafe fn evaluate_bool(&self, vars: &[i64]) -> Option<bool> {
        debug_assert!(self.is_boolean, "not a boolean expression");
        let result = unsafe { self.evaluate_raw(vars) };
        match result {
            0 => Some(false),
            1 => Some(true),
            _ => None, // -1 or any other value = indeterminate
        }
    }

    /// Evaluate the compiled expression with bounds-checked variable array.
    ///
    /// Returns `None` if `vars` is too short.
    /// This is the safe equivalent of `evaluate_raw`.
    pub fn evaluate_checked(&self, vars: &[i64]) -> Option<i64> {
        if vars.len() < self.var_mapping.total_vars() as usize {
            return None;
        }
        // SAFETY: We just verified vars.len() >= total_vars(). The compiled
        // function reads at compile-time-known indices bounded by total_vars().
        Some(unsafe { (self.func)(vars.as_ptr()) })
    }

    /// Evaluate a boolean expression with bounds-checked variable array.
    ///
    /// Returns `None` if `vars` is too short or the result is indeterminate.
    /// This is the safe equivalent of `evaluate_bool`.
    pub fn evaluate_bool_checked(&self, vars: &[i64]) -> Option<bool> {
        if !self.is_boolean {
            return None;
        }
        match self.evaluate_checked(vars)? {
            0 => Some(false),
            1 => Some(true),
            _ => None,
        }
    }

    /// Access the variable mapping.
    pub fn var_mapping(&self) -> &VarMapping {
        &self.var_mapping
    }
}

// ---------------------------------------------------------------------------
// Minimal aarch64 assembler for 64-bit expression evaluation
// ---------------------------------------------------------------------------

#[cfg(target_arch = "aarch64")]
#[allow(unreachable_pub, dead_code)]
mod asm64 {
    /// General-purpose register.
    #[derive(Clone, Copy, PartialEq, Eq)]
    pub(crate) struct Reg(pub u8);

    impl Reg {
        pub const fn x(n: u8) -> Self {
            Self(n)
        }
    }

    // Register assignments for expression evaluation:
    // x0 = vars pointer (argument, preserved)
    // x1-x6 = scratch for intermediate values
    // x7-x17 = more scratch
    // x19-x28 = callee-saved (used for deep expressions)
    // x29 = FP, x30 = LR, x31 = SP/XZR

    pub(crate) const VARS: Reg = Reg(0);
    pub(crate) const XZR: Reg = Reg(31);
    pub(crate) const SP: Reg = Reg(31);
    pub(crate) const FP: Reg = Reg(29);
    pub(crate) const LR: Reg = Reg(30);

    // Scratch registers for expression values (x1-x17, skip x18 = platform)
    pub(crate) const SCRATCH: [Reg; 17] = [
        Reg(1),
        Reg(2),
        Reg(3),
        Reg(4),
        Reg(5),
        Reg(6),
        Reg(7),
        Reg(8),
        Reg(9),
        Reg(10),
        Reg(11),
        Reg(12),
        Reg(13),
        Reg(14),
        Reg(15),
        Reg(16),
        Reg(17),
    ];

    /// Condition codes for B.cond and CSEL.
    #[derive(Clone, Copy)]
    #[repr(u8)]
    pub(crate) enum Cond {
        Eq = 0b0000,
        Ne = 0b0001,
        // Signed comparisons
        Gt = 0b1100,
        Ge = 0b1010,
        Lt = 0b1011,
        Le = 0b1101,
    }

    /// Branch label for forward/backward references.
    #[derive(Clone, Copy)]
    pub(crate) struct Label(u32);

    struct Fixup {
        offset: u32,
        label: Label,
        kind: FixupKind,
    }

    #[derive(Clone, Copy)]
    enum FixupKind {
        Imm19,
        Imm26,
    }

    /// Minimal 64-bit aarch64 assembler for expression evaluation.
    pub(crate) struct Asm64 {
        code: Vec<u32>,
        labels: Vec<Option<u32>>,
        fixups: Vec<Fixup>,
    }

    impl Asm64 {
        pub fn new() -> Self {
            Self {
                code: Vec::with_capacity(256),
                labels: Vec::new(),
                fixups: Vec::new(),
            }
        }

        pub fn label(&mut self) -> Label {
            let id = self.labels.len() as u32;
            self.labels.push(None);
            Label(id)
        }

        pub fn bind(&mut self, label: Label) {
            debug_assert!(
                self.labels[label.0 as usize].is_none(),
                "label already bound"
            );
            self.labels[label.0 as usize] = Some(self.code.len() as u32);
        }

        fn emit(&mut self, instr: u32) {
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

        // -- Prologue / Epilogue --

        /// STP x29, x30, [sp, #-16]! ; MOV x29, sp
        pub fn prologue(&mut self) {
            self.emit(0xa9bf7bfd); // stp x29, x30, [sp, #-16]!
            self.emit(0x910003fd); // mov x29, sp
        }

        /// LDP x29, x30, [sp], #16 ; RET
        pub fn epilogue(&mut self) {
            self.emit(0xa8c17bfd); // ldp x29, x30, [sp], #16
            self.emit(0xd65f03c0); // ret
        }

        // -- Load / Store (64-bit) --

        /// LDR Xt, [Xn, #imm] — 64-bit load, imm must be 8-byte aligned, < 32768.
        pub fn ldr_x_uimm(&mut self, rt: Reg, rn: Reg, byte_offset: u32) {
            debug_assert!(byte_offset.is_multiple_of(8) && byte_offset / 8 < 4096);
            let imm12 = byte_offset / 8;
            self.emit(0xf9400000 | (imm12 << 10) | (u32::from(rn.0) << 5) | u32::from(rt.0));
        }

        /// LDR Xt, [Xn, Xm, LSL #3] — 64-bit load with register offset scaled by 8.
        pub fn ldr_x_reg_lsl3(&mut self, rt: Reg, rn: Reg, rm: Reg) {
            // size=11, V=0, opc=01, option=011, S=1
            self.emit(
                0xf8607800 | (u32::from(rm.0) << 16) | (u32::from(rn.0) << 5) | u32::from(rt.0),
            );
        }

        /// STR Xt, [Xn, #imm] — 64-bit store.
        pub fn str_x_uimm(&mut self, rt: Reg, rn: Reg, byte_offset: u32) {
            debug_assert!(byte_offset.is_multiple_of(8) && byte_offset / 8 < 4096);
            let imm12 = byte_offset / 8;
            self.emit(0xf9000000 | (imm12 << 10) | (u32::from(rn.0) << 5) | u32::from(rt.0));
        }

        // -- Move / Immediate --

        /// MOVZ Xd, #imm16 (64-bit, shift=0)
        pub fn movz_x(&mut self, rd: Reg, imm16: u16) {
            self.emit(0xd2800000 | (u32::from(imm16) << 5) | u32::from(rd.0));
        }

        /// MOVZ Xd, #imm16, LSL #16
        pub fn movz_x_lsl16(&mut self, rd: Reg, imm16: u16) {
            self.emit(0xd2a00000 | (u32::from(imm16) << 5) | u32::from(rd.0));
        }

        /// MOVZ Xd, #imm16, LSL #32
        pub fn movz_x_lsl32(&mut self, rd: Reg, imm16: u16) {
            self.emit(0xd2c00000 | (u32::from(imm16) << 5) | u32::from(rd.0));
        }

        /// MOVZ Xd, #imm16, LSL #48
        pub fn movz_x_lsl48(&mut self, rd: Reg, imm16: u16) {
            self.emit(0xd2e00000 | (u32::from(imm16) << 5) | u32::from(rd.0));
        }

        /// MOVK Xd, #imm16 (keep, shift=0)
        pub fn movk_x(&mut self, rd: Reg, imm16: u16) {
            self.emit(0xf2800000 | (u32::from(imm16) << 5) | u32::from(rd.0));
        }

        /// MOVK Xd, #imm16, LSL #16
        pub fn movk_x_lsl16(&mut self, rd: Reg, imm16: u16) {
            self.emit(0xf2a00000 | (u32::from(imm16) << 5) | u32::from(rd.0));
        }

        /// MOVK Xd, #imm16, LSL #32
        pub fn movk_x_lsl32(&mut self, rd: Reg, imm16: u16) {
            self.emit(0xf2c00000 | (u32::from(imm16) << 5) | u32::from(rd.0));
        }

        /// MOVK Xd, #imm16, LSL #48
        pub fn movk_x_lsl48(&mut self, rd: Reg, imm16: u16) {
            self.emit(0xf2e00000 | (u32::from(imm16) << 5) | u32::from(rd.0));
        }

        /// Load a 64-bit immediate into Xd.
        pub fn mov_imm64(&mut self, rd: Reg, value: i64) {
            let v = value as u64;
            let h0 = v as u16;
            let h1 = (v >> 16) as u16;
            let h2 = (v >> 32) as u16;
            let h3 = (v >> 48) as u16;

            // Check for MOVN optimization for negative values near -1
            if (0..=0xFFFF).contains(&value) {
                self.movz_x(rd, h0);
            } else if value >= 0 && h0 == 0 && h2 == 0 && h3 == 0 {
                self.movz_x_lsl16(rd, h1);
            } else {
                // General case: MOVZ + MOVK sequence
                // Find first non-zero halfword for MOVZ
                if h0 != 0 || (h1 == 0 && h2 == 0 && h3 == 0) {
                    self.movz_x(rd, h0);
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
                    self.movz_x_lsl16(rd, h1);
                    if h2 != 0 {
                        self.movk_x_lsl32(rd, h2);
                    }
                    if h3 != 0 {
                        self.movk_x_lsl48(rd, h3);
                    }
                } else if h2 != 0 {
                    self.movz_x_lsl32(rd, h2);
                    if h3 != 0 {
                        self.movk_x_lsl48(rd, h3);
                    }
                } else {
                    self.movz_x_lsl48(rd, h3);
                }
            }
        }

        /// MOV Xd, Xm (alias for ORR Xd, XZR, Xm)
        pub fn mov_x(&mut self, rd: Reg, rm: Reg) {
            self.emit(0xaa0003e0 | (u32::from(rm.0) << 16) | u32::from(rd.0));
        }

        // -- 64-bit Arithmetic --

        /// ADD Xd, Xn, Xm
        pub fn add_x(&mut self, rd: Reg, rn: Reg, rm: Reg) {
            self.emit(
                0x8b000000 | (u32::from(rm.0) << 16) | (u32::from(rn.0) << 5) | u32::from(rd.0),
            );
        }

        /// ADD Xd, Xn, #imm12
        pub fn add_x_imm(&mut self, rd: Reg, rn: Reg, imm12: u32) {
            debug_assert!(imm12 < 4096);
            self.emit(0x91000000 | (imm12 << 10) | (u32::from(rn.0) << 5) | u32::from(rd.0));
        }

        /// SUB Xd, Xn, Xm
        pub fn sub_x(&mut self, rd: Reg, rn: Reg, rm: Reg) {
            self.emit(
                0xcb000000 | (u32::from(rm.0) << 16) | (u32::from(rn.0) << 5) | u32::from(rd.0),
            );
        }

        /// SUB Xd, Xn, #imm12
        pub fn sub_x_imm(&mut self, rd: Reg, rn: Reg, imm12: u32) {
            debug_assert!(imm12 < 4096);
            self.emit(0xd1000000 | (imm12 << 10) | (u32::from(rn.0) << 5) | u32::from(rd.0));
        }

        /// MUL Xd, Xn, Xm (alias: MADD Xd, Xn, Xm, XZR)
        pub fn mul_x(&mut self, rd: Reg, rn: Reg, rm: Reg) {
            self.emit(
                0x9b007c00 | (u32::from(rm.0) << 16) | (u32::from(rn.0) << 5) | u32::from(rd.0),
            );
        }

        /// SDIV Xd, Xn, Xm (signed 64-bit divide)
        pub fn sdiv_x(&mut self, rd: Reg, rn: Reg, rm: Reg) {
            self.emit(
                0x9ac00c00 | (u32::from(rm.0) << 16) | (u32::from(rn.0) << 5) | u32::from(rd.0),
            );
        }

        /// MSUB Xd, Xn, Xm, Xa — Xd = Xa - Xn * Xm
        pub fn msub_x(&mut self, rd: Reg, rn: Reg, rm: Reg, ra: Reg) {
            self.emit(
                0x9b008000
                    | (u32::from(rm.0) << 16)
                    | (u32::from(ra.0) << 10)
                    | (u32::from(rn.0) << 5)
                    | u32::from(rd.0),
            );
        }

        /// NEG Xd, Xm (alias: SUB Xd, XZR, Xm)
        pub fn neg_x(&mut self, rd: Reg, rm: Reg) {
            self.sub_x(rd, XZR, rm);
        }

        // -- Compare --

        /// CMP Xn, Xm (SUBS XZR, Xn, Xm, 64-bit)
        pub fn cmp_x(&mut self, rn: Reg, rm: Reg) {
            self.emit(0xeb00001f | (u32::from(rm.0) << 16) | (u32::from(rn.0) << 5));
        }

        /// CMP Xn, #imm12
        pub fn cmp_x_imm(&mut self, rn: Reg, imm12: u32) {
            debug_assert!(imm12 < 4096);
            self.emit(0xf100001f | (imm12 << 10) | (u32::from(rn.0) << 5));
        }

        // -- Conditional select --

        /// CSEL Xd, Xn, Xm, cond (64-bit)
        pub fn csel_x(&mut self, rd: Reg, rn: Reg, rm: Reg, cond: Cond) {
            self.emit(
                0x9a800000
                    | (u32::from(rm.0) << 16)
                    | ((cond as u32) << 12)
                    | (u32::from(rn.0) << 5)
                    | u32::from(rd.0),
            );
        }

        /// CSET Xd, cond — set Xd to 1 if cond, else 0.
        /// Encoded as CSINC Xd, XZR, XZR, invert(cond).
        pub fn cset_x(&mut self, rd: Reg, cond: Cond) {
            let inv_cond = (cond as u8) ^ 1;
            self.emit(0x9a9f07e0 | (u32::from(inv_cond) << 12) | u32::from(rd.0));
        }

        // -- Bitwise --

        /// EOR Xd, Xn, Xm (64-bit XOR)
        pub fn eor_x(&mut self, rd: Reg, rn: Reg, rm: Reg) {
            self.emit(
                0xca000000 | (u32::from(rm.0) << 16) | (u32::from(rn.0) << 5) | u32::from(rd.0),
            );
        }

        /// AND Xd, Xn, Xm (64-bit AND)
        pub fn and_x(&mut self, rd: Reg, rn: Reg, rm: Reg) {
            self.emit(
                0x8a000000 | (u32::from(rm.0) << 16) | (u32::from(rn.0) << 5) | u32::from(rd.0),
            );
        }

        /// ORR Xd, Xn, Xm (64-bit OR)
        pub fn orr_x(&mut self, rd: Reg, rn: Reg, rm: Reg) {
            self.emit(
                0xaa000000 | (u32::from(rm.0) << 16) | (u32::from(rn.0) << 5) | u32::from(rd.0),
            );
        }

        // -- Branches --

        /// B label (unconditional)
        pub fn b(&mut self, label: Label) {
            self.emit_branch(0x14000000, label, FixupKind::Imm26);
        }

        /// B.cond label
        pub fn b_cond(&mut self, cond: Cond, label: Label) {
            self.emit_branch(0x54000000 | cond as u32, label, FixupKind::Imm19);
        }

        /// CBZ Xt, label (64-bit)
        pub fn cbz_x(&mut self, rt: Reg, label: Label) {
            self.emit_branch(0xb4000000 | u32::from(rt.0), label, FixupKind::Imm19);
        }

        /// CBNZ Xt, label (64-bit)
        pub fn cbnz_x(&mut self, rt: Reg, label: Label) {
            self.emit_branch(0xb5000000 | u32::from(rt.0), label, FixupKind::Imm19);
        }

        // -- Stack (callee-saved register save/restore; pushes and pops must
        //    stay balanced — see the #18 epilogue frame-record corruption) --

        /// STP Xt1, Xt2, [sp, #-16]! (pre-index)
        pub fn push_pair(&mut self, rt1: Reg, rt2: Reg) {
            // opc=10, V=0, L=0, pre-index, imm7 = -16/8 = -2 (7-bit signed)
            let imm7 = ((-2i32) as u32) & 0x7f;
            self.emit(
                0xa9800000
                    | (imm7 << 15)
                    | (u32::from(rt2.0) << 10)
                    | (u32::from(SP.0) << 5)
                    | u32::from(rt1.0),
            );
        }

        /// LDP Xt1, Xt2, [sp], #16 (post-index)
        pub fn pop_pair(&mut self, rt1: Reg, rt2: Reg) {
            let imm7 = 2u32; // 16/8 = 2
            self.emit(
                0xa8c00000
                    | (imm7 << 15)
                    | (u32::from(rt2.0) << 10)
                    | (u32::from(SP.0) << 5)
                    | u32::from(rt1.0),
            );
        }

        // -- Finalize --

        pub fn finalize(mut self) -> Vec<u8> {
            for fixup in &self.fixups {
                // INVARIANT: every expr-eval aarch64 label returned by
                // `new_label()` must be bound via `bind()` before
                // `finalize()`. Assembler-internal invariant, not
                // a user-input error.
                let target = self.labels[fixup.label.0 as usize].expect(
                    "invariant: all emitted expr-eval aarch64 labels must be bound before finalize",
                );
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

            let mut bytes = Vec::with_capacity(self.code.len() * 4);
            for &instr in &self.code {
                bytes.extend_from_slice(&instr.to_le_bytes());
            }
            bytes
        }
    }
}

// ---------------------------------------------------------------------------
// Minimal x86_64 assembler for 64-bit expression evaluation
// ---------------------------------------------------------------------------

#[cfg(target_arch = "x86_64")]
mod asm64_x86 {
    #[derive(Clone, Copy, PartialEq, Eq)]
    pub(crate) struct Reg(pub u8);

    impl Reg {
        const fn is_ext(self) -> bool {
            self.0 >= 8
        }
        const fn lo3(self) -> u8 {
            self.0 & 7
        }
    }

    pub(crate) const RAX: Reg = Reg(0);
    pub(crate) const RCX: Reg = Reg(1);
    pub(crate) const RDX: Reg = Reg(2);
    pub(crate) const RBX: Reg = Reg(3);
    pub(crate) const RDI: Reg = Reg(7);
    pub(crate) const R8: Reg = Reg(8);
    pub(crate) const R9: Reg = Reg(9);
    pub(crate) const R10: Reg = Reg(10);
    pub(crate) const R11: Reg = Reg(11);
    pub(crate) const R12: Reg = Reg(12);
    pub(crate) const R13: Reg = Reg(13);
    pub(crate) const R14: Reg = Reg(14);
    pub(crate) const R15: Reg = Reg(15);

    pub(crate) const VARS: Reg = RDI;

    pub(crate) const SCRATCH: [Reg; 10] = [R8, R9, R10, R11, RCX, Reg(6), RBX, R12, R13, R14];

    pub(crate) const CALLEE_SAVED_START: usize = 6;

    #[derive(Clone, Copy)]
    #[repr(u8)]
    pub(crate) enum Cond {
        Eq = 0x4,
        Ne = 0x5,
        Lt = 0xC,
        Ge = 0xD,
        Le = 0xE,
        Gt = 0xF,
    }

    #[derive(Clone, Copy)]
    pub(crate) struct Label(u32);

    struct Fixup {
        offset: u32,
        label: Label,
    }

    pub(crate) struct Asm64X86 {
        code: Vec<u8>,
        labels: Vec<Option<u32>>,
        fixups: Vec<Fixup>,
    }

    impl Asm64X86 {
        pub(crate) fn new() -> Self {
            Self {
                code: Vec::with_capacity(1024),
                labels: Vec::new(),
                fixups: Vec::new(),
            }
        }
        pub(crate) fn label(&mut self) -> Label {
            let id = self.labels.len() as u32;
            self.labels.push(None);
            Label(id)
        }
        pub(crate) fn bind(&mut self, label: Label) {
            debug_assert!(
                self.labels[label.0 as usize].is_none(),
                "label already bound"
            );
            self.labels[label.0 as usize] = Some(self.code.len() as u32);
        }
        fn emit(&mut self, bytes: &[u8]) {
            self.code.extend_from_slice(bytes);
        }
        fn emit_u8(&mut self, b: u8) {
            self.code.push(b);
        }
        fn emit_i32(&mut self, v: i32) {
            self.code.extend_from_slice(&v.to_le_bytes());
        }
        fn emit_jcc(&mut self, cond: Cond, label: Label) {
            self.emit(&[0x0F, 0x80 | cond as u8]);
            self.fixups.push(Fixup {
                offset: self.code.len() as u32,
                label,
            });
            self.emit_i32(0);
        }
        fn emit_jmp(&mut self, label: Label) {
            self.emit_u8(0xE9);
            self.fixups.push(Fixup {
                offset: self.code.len() as u32,
                label,
            });
            self.emit_i32(0);
        }
        fn rex_w(r_ext: bool, b_ext: bool) -> u8 {
            0x48 | if r_ext { 4 } else { 0 } | if b_ext { 1 } else { 0 }
        }
        fn modrm_rr(reg: Reg, rm: Reg) -> u8 {
            0xC0 | (reg.lo3() << 3) | rm.lo3()
        }
        pub(crate) fn prologue(&mut self) {
            self.emit_u8(0x55);
            self.emit(&[0x48, 0x89, 0xE5]);
        }
        pub(crate) fn epilogue(&mut self) {
            self.emit(&[0x48, 0x89, 0xEC]);
            self.emit_u8(0x5D);
            self.emit_u8(0xC3);
        }
        pub(crate) fn push_r64(&mut self, r: Reg) {
            if r.is_ext() {
                self.emit_u8(0x41);
            }
            self.emit_u8(0x50 + r.lo3());
        }
        pub(crate) fn pop_r64(&mut self, r: Reg) {
            if r.is_ext() {
                self.emit_u8(0x41);
            }
            self.emit_u8(0x58 + r.lo3());
        }
        pub(crate) fn mov_rr(&mut self, dst: Reg, src: Reg) {
            if dst == src {
                return;
            }
            self.emit_u8(Self::rex_w(src.is_ext(), dst.is_ext()));
            self.emit(&[0x89, Self::modrm_rr(src, dst)]);
        }
        pub(crate) fn mov_imm64(&mut self, dst: Reg, imm: i64) {
            if imm == 0 {
                self.xor_rr32(dst, dst);
                return;
            }
            if imm > 0 && imm <= 0x7FFFFFFF {
                if dst.is_ext() {
                    self.emit_u8(0x41);
                }
                self.emit_u8(0xB8 + dst.lo3());
                self.emit_i32(imm as i32);
                return;
            }
            if (-0x80000000..0).contains(&imm) {
                self.emit_u8(Self::rex_w(false, dst.is_ext()));
                self.emit(&[0xC7, 0xC0 | dst.lo3()]);
                self.emit_i32(imm as i32);
                return;
            }
            self.emit_u8(Self::rex_w(false, dst.is_ext()));
            self.emit_u8(0xB8 + dst.lo3());
            self.code.extend_from_slice(&imm.to_le_bytes());
        }
        pub(crate) fn load_qword(&mut self, dst: Reg, base: Reg, disp: i32) {
            self.emit_u8(Self::rex_w(dst.is_ext(), base.is_ext()));
            if base.lo3() == 4 {
                self.emit(&[0x8B, 0x80 | (dst.lo3() << 3) | 4, 0x24]);
            } else if base.lo3() == 5 && disp == 0 {
                self.emit(&[0x8B, 0x40 | (dst.lo3() << 3) | base.lo3(), 0x00]);
                return;
            } else {
                self.emit(&[0x8B, 0x80 | (dst.lo3() << 3) | base.lo3()]);
            }
            self.emit_i32(disp);
        }
        pub(crate) fn add_rr(&mut self, dst: Reg, src: Reg) {
            self.emit_u8(Self::rex_w(src.is_ext(), dst.is_ext()));
            self.emit(&[0x01, Self::modrm_rr(src, dst)]);
        }
        pub(crate) fn sub_rr(&mut self, dst: Reg, src: Reg) {
            self.emit_u8(Self::rex_w(src.is_ext(), dst.is_ext()));
            self.emit(&[0x29, Self::modrm_rr(src, dst)]);
        }
        pub(crate) fn imul_rr(&mut self, dst: Reg, src: Reg) {
            self.emit_u8(Self::rex_w(dst.is_ext(), src.is_ext()));
            self.emit(&[0x0F, 0xAF, Self::modrm_rr(dst, src)]);
        }
        pub(crate) fn neg_r64(&mut self, r: Reg) {
            self.emit_u8(Self::rex_w(false, r.is_ext()));
            self.emit(&[0xF7, 0xD8 | r.lo3()]);
        }
        pub(crate) fn add_imm32(&mut self, dst: Reg, imm: i32) {
            self.emit_u8(Self::rex_w(false, dst.is_ext()));
            if dst == RAX {
                self.emit_u8(0x05);
                self.emit_i32(imm);
            } else if (-128..=127).contains(&imm) {
                self.emit(&[0x83, 0xC0 | dst.lo3()]);
                self.emit_u8(imm as u8);
            } else {
                self.emit(&[0x81, 0xC0 | dst.lo3()]);
                self.emit_i32(imm);
            }
        }
        pub(crate) fn sub_imm32(&mut self, dst: Reg, imm: i32) {
            self.emit_u8(Self::rex_w(false, dst.is_ext()));
            if (-128..=127).contains(&imm) {
                self.emit(&[0x83, 0xE8 | dst.lo3()]);
                self.emit_u8(imm as u8);
            } else {
                self.emit(&[0x81, 0xE8 | dst.lo3()]);
                self.emit_i32(imm);
            }
        }
        pub(crate) fn cqo(&mut self) {
            self.emit(&[0x48, 0x99]);
        }
        pub(crate) fn idiv_r64(&mut self, divisor: Reg) {
            self.emit_u8(Self::rex_w(false, divisor.is_ext()));
            self.emit(&[0xF7, 0xF8 | divisor.lo3()]);
        }
        pub(crate) fn cmp_rr(&mut self, a: Reg, b: Reg) {
            self.emit_u8(Self::rex_w(b.is_ext(), a.is_ext()));
            self.emit(&[0x39, Self::modrm_rr(b, a)]);
        }
        pub(crate) fn cmp_imm32(&mut self, r: Reg, imm: i32) {
            self.emit_u8(Self::rex_w(false, r.is_ext()));
            if (-128..=127).contains(&imm) {
                self.emit(&[0x83, 0xF8 | r.lo3()]);
                self.emit_u8(imm as u8);
            } else {
                self.emit(&[0x81, 0xF8 | r.lo3()]);
                self.emit_i32(imm);
            }
        }
        pub(crate) fn test_rr(&mut self, a: Reg, b: Reg) {
            self.emit_u8(Self::rex_w(a.is_ext(), b.is_ext()));
            self.emit(&[0x85, Self::modrm_rr(a, b)]);
        }
        pub(crate) fn setcc(&mut self, dst: Reg, cond: Cond) {
            if dst.is_ext() {
                self.emit_u8(0x41);
            } else if dst.0 >= 4 {
                self.emit_u8(0x40);
            }
            self.emit(&[0x0F, 0x90 | cond as u8, 0xC0 | dst.lo3()]);
            self.emit_u8(Self::rex_w(dst.is_ext(), dst.is_ext()));
            self.emit(&[0x0F, 0xB6, Self::modrm_rr(dst, dst)]);
        }
        pub(crate) fn cmovcc(&mut self, dst: Reg, src: Reg, cond: Cond) {
            self.emit_u8(Self::rex_w(dst.is_ext(), src.is_ext()));
            self.emit(&[0x0F, 0x40 | cond as u8, Self::modrm_rr(dst, src)]);
        }
        fn xor_rr32(&mut self, dst: Reg, src: Reg) {
            if dst.is_ext() || src.is_ext() {
                self.emit_u8(
                    0x40 | if src.is_ext() { 4 } else { 0 } | if dst.is_ext() { 1 } else { 0 },
                );
            }
            self.emit(&[0x31, Self::modrm_rr(src, dst)]);
        }
        pub(crate) fn jmp(&mut self, label: Label) {
            self.emit_jmp(label);
        }
        pub(crate) fn jcc(&mut self, cond: Cond, label: Label) {
            self.emit_jcc(cond, label);
        }
        pub(crate) fn finalize(mut self) -> Vec<u8> {
            for fixup in &self.fixups {
                // INVARIANT: every expr-eval x86_64 label returned by
                // `new_label()` must be bound via `bind()` before
                // `finalize()`. Assembler-internal invariant, not
                // a user-input error.
                let target = self.labels[fixup.label.0 as usize].expect(
                    "invariant: all emitted expr-eval x86_64 labels must be bound before finalize",
                );
                let delta = target as i32 - (fixup.offset as i32 + 4);
                let bytes = delta.to_le_bytes();
                let off = fixup.offset as usize;
                self.code[off..off + 4].copy_from_slice(&bytes);
            }
            self.code
        }
    }
}

// ---------------------------------------------------------------------------
// Flatten: ChcExpr -> ExprOpcode sequence
// ---------------------------------------------------------------------------

/// Check if an expression is JIT-compilable (only int/bool arithmetic, no arrays/BV/predicates).
pub fn is_jit_compilable(expr: &dyn ExprLike) -> bool {
    expr.is_jit_compilable()
}

/// Trait abstracting over ChcExpr for the JIT compiler.
///
/// This avoids a direct dependency on ay-chc types in the ay-jit crate.
/// The ay-chc crate implements this trait for ChcExpr.
pub trait ExprLike {
    /// Check if this expression can be JIT-compiled.
    fn is_jit_compilable(&self) -> bool;

    /// Flatten this expression into an opcode sequence, populating the var mapping.
    fn flatten_into(&self, opcodes: &mut Vec<ExprOpcode>, var_mapping: &mut VarMapping) -> bool;

    /// Whether this expression returns a boolean value.
    fn is_boolean(&self) -> bool;
}

/// Flatten an expression into opcodes and build the variable mapping.
///
/// Returns None if the expression contains unsupported operations.
pub fn flatten(expr: &dyn ExprLike, var_mapping: &mut VarMapping) -> Option<Vec<ExprOpcode>> {
    let mut opcodes = Vec::new();
    if expr.flatten_into(&mut opcodes, var_mapping) {
        Some(opcodes)
    } else {
        None
    }
}

// ---------------------------------------------------------------------------
// Interpret: ExprOpcode sequence -> result (no native code, all platforms)
// ---------------------------------------------------------------------------

/// Interpret an opcode sequence using a Rust stack.
///
/// This is the platform-independent fallback for expression evaluation. It
/// matches the semantics of the native aarch64 code generator exactly,
/// operating on the same opcode representation and variable mapping.
///
/// Returns the raw i64 result. For boolean expressions, 0=false, 1=true.
/// Returns `None` if the opcode sequence is malformed (stack underflow).
pub fn interpret(opcodes: &[ExprOpcode], vars: &[i64]) -> Option<i64> {
    let mut stack: Vec<i64> = Vec::with_capacity(16);

    for op in opcodes {
        match op {
            ExprOpcode::PushBool(b) => {
                stack.push(i64::from(*b));
            }
            ExprOpcode::PushInt(n) => {
                stack.push(*n);
            }
            ExprOpcode::LoadIntVar(idx) | ExprOpcode::LoadBoolVar(idx) => {
                stack.push(*vars.get(*idx as usize).unwrap_or(&0));
            }
            ExprOpcode::Add => {
                let b = stack.pop()?;
                let a = stack.last_mut()?;
                *a = a.wrapping_add(b);
            }
            ExprOpcode::Sub => {
                let b = stack.pop()?;
                let a = stack.last_mut()?;
                *a = a.wrapping_sub(b);
            }
            ExprOpcode::Mul => {
                let b = stack.pop()?;
                let a = stack.last_mut()?;
                *a = a.wrapping_mul(b);
            }
            ExprOpcode::Neg => {
                let a = stack.last_mut()?;
                *a = a.wrapping_neg();
            }
            ExprOpcode::Div => {
                // SMT-LIB: div(a, 0) = 0, Euclidean division otherwise.
                // b == -1 is special-cased: div_euclid(a, -1) = -a, and
                // wrapping_neg keeps i64::MIN / -1 total (Rust div_euclid
                // panics on that overflow). This matches the aarch64 native
                // path, where SDIV defines MIN / -1 = MIN without trapping.
                let b = stack.pop()?;
                let a = stack.last_mut()?;
                if b == 0 {
                    *a = 0;
                } else if b == -1 {
                    *a = a.wrapping_neg();
                } else {
                    *a = a.div_euclid(b);
                }
            }
            ExprOpcode::Mod => {
                // SMT-LIB: mod(a, 0) = a, Euclidean remainder otherwise.
                // b == -1 is special-cased: mod(a, -1) = 0 for all a, and it
                // keeps i64::MIN % -1 total (Rust rem_euclid panics on that
                // overflow). Matches the aarch64 native path.
                let b = stack.pop()?;
                let a = stack.last_mut()?;
                if b == -1 {
                    *a = 0;
                } else if b != 0 {
                    *a = a.rem_euclid(b);
                }
                // If b == 0, result is a (unchanged)
            }
            ExprOpcode::CmpEq => {
                let b = stack.pop()?;
                let a = stack.last_mut()?;
                *a = i64::from(*a == b);
            }
            ExprOpcode::CmpNe => {
                let b = stack.pop()?;
                let a = stack.last_mut()?;
                *a = i64::from(*a != b);
            }
            ExprOpcode::CmpLt => {
                let b = stack.pop()?;
                let a = stack.last_mut()?;
                *a = i64::from(*a < b);
            }
            ExprOpcode::CmpLe => {
                let b = stack.pop()?;
                let a = stack.last_mut()?;
                *a = i64::from(*a <= b);
            }
            ExprOpcode::CmpGt => {
                let b = stack.pop()?;
                let a = stack.last_mut()?;
                *a = i64::from(*a > b);
            }
            ExprOpcode::CmpGe => {
                let b = stack.pop()?;
                let a = stack.last_mut()?;
                *a = i64::from(*a >= b);
            }
            ExprOpcode::Not => {
                let a = stack.last_mut()?;
                *a = i64::from(*a == 0);
            }
            ExprOpcode::And(count) => {
                let n = *count as usize;
                if n == 0 {
                    stack.push(1); // empty AND = true
                } else {
                    let mut result = true;
                    for _ in 0..n {
                        let v = stack.pop()?;
                        if v == 0 {
                            result = false;
                        }
                    }
                    stack.push(i64::from(result));
                }
            }
            ExprOpcode::Or(count) => {
                let n = *count as usize;
                if n == 0 {
                    stack.push(0); // empty OR = false
                } else {
                    let mut result = false;
                    for _ in 0..n {
                        let v = stack.pop()?;
                        if v != 0 {
                            result = true;
                        }
                    }
                    stack.push(i64::from(result));
                }
            }
            ExprOpcode::Implies => {
                let b = stack.pop()?;
                let a = stack.pop()?;
                // a => b == !a || b
                stack.push(if a == 0 { 1 } else { b });
            }
            ExprOpcode::Ite => {
                // Stack order: cond pushed first, then then_val, then else_val
                let else_val = stack.pop()?;
                let then_val = stack.pop()?;
                let cond = stack.pop()?;
                stack.push(if cond != 0 { then_val } else { else_val });
            }
        }
    }

    stack.pop()
}

/// A portable expression evaluator using interpretation.
///
/// Unlike `CompiledExprEval`, this works on all platforms. It evaluates
/// expressions by interpreting the opcode sequence rather than executing
/// native machine code. Used as a fallback when JIT compilation is
/// unavailable or as a reference implementation for testing.
pub struct InterpretedExprEval {
    /// The opcode sequence to evaluate.
    opcodes: Vec<ExprOpcode>,
    /// Variable name to flat array index mapping.
    pub(crate) var_mapping: VarMapping,
    /// Whether this expression returns a boolean (vs integer).
    pub(crate) is_boolean: bool,
}

impl InterpretedExprEval {
    /// Create a new interpreted evaluator from opcodes and variable mapping.
    pub fn new(opcodes: Vec<ExprOpcode>, var_mapping: VarMapping, is_boolean: bool) -> Self {
        Self {
            opcodes,
            var_mapping,
            is_boolean,
        }
    }

    /// Evaluate the expression with the given variable values.
    ///
    /// `vars` must have length >= `var_mapping.total_vars()`. Returns `None`
    /// if the opcode sequence is malformed.
    pub fn evaluate_raw(&self, vars: &[i64]) -> Option<i64> {
        interpret(&self.opcodes, vars)
    }

    /// Evaluate and return `Option<bool>` for boolean expressions.
    pub fn evaluate_bool(&self, vars: &[i64]) -> Option<bool> {
        match self.evaluate_raw(vars)? {
            0 => Some(false),
            1 => Some(true),
            _ => None,
        }
    }

    /// Evaluate with bounds-checked variable array.
    pub fn evaluate_checked(&self, vars: &[i64]) -> Option<i64> {
        if vars.len() < self.var_mapping.total_vars() as usize {
            return None;
        }
        self.evaluate_raw(vars)
    }

    /// Evaluate a boolean expression with bounds-checked variable array.
    pub fn evaluate_bool_checked(&self, vars: &[i64]) -> Option<bool> {
        if !self.is_boolean {
            return None;
        }
        match self.evaluate_checked(vars)? {
            0 => Some(false),
            1 => Some(true),
            _ => None,
        }
    }

    /// Access the variable mapping.
    pub fn var_mapping(&self) -> &VarMapping {
        &self.var_mapping
    }
}

/// Compile an expression into a portable interpreted evaluator.
///
/// Returns `None` if the expression is not JIT-compilable.
/// This always succeeds on any platform (no native code needed).
pub fn compile_interpreted(expr: &dyn ExprLike) -> Option<InterpretedExprEval> {
    if !expr.is_jit_compilable() {
        return None;
    }
    let mut var_mapping = VarMapping::new();
    let opcodes = flatten(expr, &mut var_mapping)?;
    let is_boolean = expr.is_boolean();
    Some(InterpretedExprEval::new(opcodes, var_mapping, is_boolean))
}

// ---------------------------------------------------------------------------
// Compile: ExprOpcode sequence -> native code
// ---------------------------------------------------------------------------

/// Maximum operand-stack depth supported by the native expression evaluator.
///
/// The code generators keep every live operand in its own scratch register
/// (the value at operand-stack position `i` lives in `SCRATCH[i]`), so the
/// peak number of simultaneously-live operands is bounded by the scratch
/// register file. Deeper expressions must fail closed to the interpreter.
#[cfg(target_arch = "aarch64")]
pub const NATIVE_EVAL_MAX_OPERAND_DEPTH: usize = 17; // == asm64::SCRATCH.len()
/// Maximum operand-stack depth supported by the native expression evaluator.
#[cfg(target_arch = "x86_64")]
pub const NATIVE_EVAL_MAX_OPERAND_DEPTH: usize = 10; // == asm64_x86::SCRATCH.len()

#[cfg(target_arch = "aarch64")]
const _: () = assert!(NATIVE_EVAL_MAX_OPERAND_DEPTH == asm64::SCRATCH.len());
#[cfg(target_arch = "x86_64")]
const _: () = assert!(NATIVE_EVAL_MAX_OPERAND_DEPTH == asm64_x86::SCRATCH.len());

/// Exact peak operand-stack depth of an opcode sequence.
///
/// Returns `None` for malformed sequences (operand-stack underflow), which
/// must never be compiled. This mirrors the code generators' register-stack
/// discipline exactly: every value-producing opcode pushes one operand;
/// consumers pop their operands and write the result in place of the deepest
/// one.
///
/// ## Why this gate is load-bearing (#18 crash class)
///
/// The aarch64 generator previously had a register-"spill" fallback that
/// emitted an unmatched `stp` when it ran out of scratch registers. The
/// orphaned 16-byte stack slot was then popped by the epilogue's
/// `ldp x29, x30, [sp], #16; ret`, so the function returned into a data value
/// (the deterministic `pc == lr == fp == <model value>` instruction aborts on
/// reve/010-horn and rust-horn/bmc-2). The fallback is gone; every compile
/// path MUST validate the peak depth with this function before emitting code.
pub fn peak_operand_stack_depth(opcodes: &[ExprOpcode]) -> Option<usize> {
    let mut depth = 0usize;
    let mut peak = 0usize;
    for op in opcodes {
        match op {
            ExprOpcode::PushBool(_)
            | ExprOpcode::PushInt(_)
            | ExprOpcode::LoadIntVar(_)
            | ExprOpcode::LoadBoolVar(_) => depth += 1,
            ExprOpcode::Add
            | ExprOpcode::Sub
            | ExprOpcode::Mul
            | ExprOpcode::Div
            | ExprOpcode::Mod
            | ExprOpcode::CmpEq
            | ExprOpcode::CmpNe
            | ExprOpcode::CmpLt
            | ExprOpcode::CmpLe
            | ExprOpcode::CmpGt
            | ExprOpcode::CmpGe
            | ExprOpcode::Implies => {
                if depth < 2 {
                    return None;
                }
                depth -= 1;
            }
            ExprOpcode::Neg | ExprOpcode::Not => {
                if depth < 1 {
                    return None;
                }
            }
            ExprOpcode::And(n) | ExprOpcode::Or(n) => {
                let n = *n as usize;
                if n == 0 {
                    depth += 1; // empty AND/OR pushes a constant result
                } else {
                    if depth < n {
                        return None;
                    }
                    depth -= n - 1;
                }
            }
            ExprOpcode::Ite => {
                if depth < 3 {
                    return None;
                }
                depth -= 2;
            }
        }
        peak = peak.max(depth);
    }
    Some(peak)
}

/// Compile an opcode sequence into a native expression evaluator.
///
/// # Errors
///
/// Returns `JitError` if:
/// - Platform is not aarch64 or x86_64
/// - The opcode sequence is malformed or its peak operand-stack depth exceeds
///   the scratch register file (`NATIVE_EVAL_MAX_OPERAND_DEPTH`)
/// - mmap fails
pub fn compile(
    opcodes: &[ExprOpcode],
    var_mapping: VarMapping,
    is_boolean: bool,
) -> Result<CompiledExprEval, JitError> {
    #[cfg(not(any(target_arch = "aarch64", target_arch = "x86_64")))]
    {
        let _ = (opcodes, var_mapping, is_boolean);
        return Err(JitError::NoNativeIsa);
    }

    #[cfg(any(target_arch = "aarch64", target_arch = "x86_64"))]
    {
        // Fail closed before emitting any code (#18): the generators have no
        // spill path, so an over-deep or malformed sequence must never reach
        // them. See `peak_operand_stack_depth` for the crash-class history.
        let peak = peak_operand_stack_depth(opcodes).ok_or_else(|| {
            JitError::BackendError(
                "malformed expression opcode sequence (operand-stack underflow)".to_string(),
            )
        })?;
        if peak > NATIVE_EVAL_MAX_OPERAND_DEPTH {
            return Err(JitError::BackendError(format!(
                "expression peak operand depth {peak} exceeds \
                 {NATIVE_EVAL_MAX_OPERAND_DEPTH} native scratch registers"
            )));
        }
    }

    #[cfg(target_arch = "aarch64")]
    {
        compile_aarch64(opcodes, var_mapping, is_boolean)
    }

    #[cfg(target_arch = "x86_64")]
    {
        compile_x86_64(opcodes, var_mapping, is_boolean)
    }
}

#[cfg(target_arch = "aarch64")]
fn compile_aarch64(
    opcodes: &[ExprOpcode],
    var_mapping: VarMapping,
    is_boolean: bool,
) -> Result<CompiledExprEval, JitError> {
    use asm64::*;

    let mut asm = Asm64::new();

    // Check if callee-saved registers x19/x20 are needed (Div/Mod use them).
    let needs_callee_saved = opcodes
        .iter()
        .any(|op| matches!(op, ExprOpcode::Div | ExprOpcode::Mod));

    // Prologue: save FP/LR, set up frame
    asm.prologue();

    // Save callee-saved registers if needed by Div/Mod.
    if needs_callee_saved {
        asm.push_pair(Reg::x(19), Reg::x(20));
    }

    // x0 = vars pointer (preserved throughout)
    // We use a virtual stack of registers for expression evaluation.
    //
    // Register discipline: the operand at stack position `i` always lives in
    // SCRATCH[i]. Popped positions are reused by later pushes, so only the
    // PEAK depth is bounded (validated by `compile()` against
    // NATIVE_EVAL_MAX_OPERAND_DEPTH before this function runs). There is no
    // spill path: a previous "spill" fallback emitted an unmatched stp that
    // corrupted the epilogue's frame-record pop and made `ret` branch into a
    // data value (#18 pc==lr==fp instruction aborts).

    let mut reg_stack: Vec<Reg> = Vec::new();

    // Helper: allocate the register for a new operand-stack position.
    //
    // Registers are assigned by operand-stack position and reused after pops,
    // so allocation cannot run out once `compile()` has validated the peak
    // depth against NATIVE_EVAL_MAX_OPERAND_DEPTH. There is NO spill path: the
    // previous aarch64 backend emitted an unbalanced `push_pair` here (SP -= 16
    // with no matching pop) once it exhausted the scratch file, so the epilogue
    // (`ldp x29,x30,[sp],#16; ret`) restored a garbage {fp,lr} pair from the
    // wrong stack slot and returned to a wild address — a memory-safety bug
    // that crashed the worker with pc==lr==fp==a tiny value (#18 crash class).
    let alloc_reg = |stack: &mut Vec<Reg>| -> Reg {
        assert!(
            stack.len() < SCRATCH.len(),
            "expr-eval operand stack exceeded the scratch register file despite \
             the pre-compile peak-depth check (#18 contract violation)"
        );
        let r = SCRATCH[stack.len()];
        stack.push(r);
        r
    };

    for op in opcodes {
        match op {
            ExprOpcode::PushBool(b) => {
                let dst = alloc_reg(&mut reg_stack);
                asm.mov_imm64(dst, if *b { 1 } else { 0 });
            }

            ExprOpcode::PushInt(n) => {
                let dst = alloc_reg(&mut reg_stack);
                asm.mov_imm64(dst, *n);
            }

            ExprOpcode::LoadIntVar(idx) | ExprOpcode::LoadBoolVar(idx) => {
                let dst = alloc_reg(&mut reg_stack);
                let byte_offset = *idx * 8;
                if byte_offset < 32768 && byte_offset % 8 == 0 {
                    asm.ldr_x_uimm(dst, VARS, byte_offset);
                } else {
                    // Large offset: compute address in scratch
                    asm.mov_imm64(dst, i64::from(byte_offset));
                    asm.ldr_x_reg_lsl3(dst, VARS, dst);
                }
            }

            ExprOpcode::Add => {
                let b = reg_stack.pop().expect("stack underflow");
                let a = reg_stack.last().copied().expect("stack underflow");
                asm.add_x(a, a, b);
            }

            ExprOpcode::Sub => {
                let b = reg_stack.pop().expect("stack underflow");
                let a = reg_stack.last().copied().expect("stack underflow");
                asm.sub_x(a, a, b);
            }

            ExprOpcode::Mul => {
                let b = reg_stack.pop().expect("stack underflow");
                let a = reg_stack.last().copied().expect("stack underflow");
                asm.mul_x(a, a, b);
            }

            ExprOpcode::Neg => {
                let a = reg_stack.last().copied().expect("stack underflow");
                asm.neg_x(a, a);
            }

            ExprOpcode::Div => {
                // Euclidean division: q = a div_euclid b
                // SMT-LIB: div(a, 0) = 0
                // Uses x19/x20 as temps (callee-saved scratch).
                let b = reg_stack.pop().expect("stack underflow");
                let a = reg_stack.last().copied().expect("stack underflow");
                let tmp_a = Reg::x(19); // save original a
                let tmp_b = Reg::x(20); // save original b

                let done = asm.label();
                let nonzero = asm.label();

                // div(a, 0) = 0
                asm.cbnz_x(b, nonzero);
                asm.mov_imm64(a, 0);
                asm.b(done);

                asm.bind(nonzero);
                // Save originals
                asm.mov_x(tmp_a, a);
                asm.mov_x(tmp_b, b);
                // q = sdiv(a, b)
                asm.sdiv_x(a, tmp_a, tmp_b);
                // r = a_orig - q * b
                // Use b as scratch for r (b is popped, safe to overwrite)
                asm.msub_x(b, a, tmp_b, tmp_a);

                // Euclidean correction: if r < 0, adjust q
                let no_adjust = asm.label();
                asm.cmp_x_imm(b, 0);
                asm.b_cond(Cond::Ge, no_adjust);
                // r < 0: if b_orig > 0 then q -= 1 else q += 1
                let b_neg = asm.label();
                asm.cmp_x_imm(tmp_b, 0);
                asm.b_cond(Cond::Lt, b_neg);
                asm.sub_x_imm(a, a, 1); // q -= 1
                asm.b(done);
                asm.bind(b_neg);
                asm.add_x_imm(a, a, 1); // q += 1

                asm.bind(no_adjust);
                asm.bind(done);
            }

            ExprOpcode::Mod => {
                // Euclidean modulus: r = a mod b (always non-negative)
                // SMT-LIB: mod(a, 0) = a
                // Uses x19/x20 as temps.
                let b = reg_stack.pop().expect("stack underflow");
                let a = reg_stack.last().copied().expect("stack underflow");
                let tmp_a = Reg::x(19);
                let tmp_b = Reg::x(20);

                let done = asm.label();
                let nonzero = asm.label();

                // mod(a, 0) = a
                asm.cbnz_x(b, nonzero);
                asm.b(done);

                asm.bind(nonzero);
                // Save originals
                asm.mov_x(tmp_a, a);
                asm.mov_x(tmp_b, b);
                // q = sdiv(a, b)
                asm.sdiv_x(b, tmp_a, tmp_b); // reuse b for quotient
                                             // r = a_orig - q * b_orig
                asm.msub_x(a, b, tmp_b, tmp_a);

                // Euclidean: if r < 0, r += abs(b)
                let no_adjust = asm.label();
                asm.cmp_x_imm(a, 0);
                asm.b_cond(Cond::Ge, no_adjust);
                // r < 0: if b_orig > 0 then r += b else r -= b
                let b_neg = asm.label();
                asm.cmp_x_imm(tmp_b, 0);
                asm.b_cond(Cond::Lt, b_neg);
                asm.add_x(a, a, tmp_b); // r += b
                asm.b(done);
                asm.bind(b_neg);
                asm.sub_x(a, a, tmp_b); // r -= b (since b is negative, this adds |b|)

                asm.bind(no_adjust);
                asm.bind(done);
            }

            ExprOpcode::CmpEq => {
                let b = reg_stack.pop().expect("stack underflow");
                let a = reg_stack.last().copied().expect("stack underflow");
                asm.cmp_x(a, b);
                asm.cset_x(a, Cond::Eq);
            }

            ExprOpcode::CmpNe => {
                let b = reg_stack.pop().expect("stack underflow");
                let a = reg_stack.last().copied().expect("stack underflow");
                asm.cmp_x(a, b);
                asm.cset_x(a, Cond::Ne);
            }

            ExprOpcode::CmpLt => {
                let b = reg_stack.pop().expect("stack underflow");
                let a = reg_stack.last().copied().expect("stack underflow");
                asm.cmp_x(a, b);
                asm.cset_x(a, Cond::Lt);
            }

            ExprOpcode::CmpLe => {
                let b = reg_stack.pop().expect("stack underflow");
                let a = reg_stack.last().copied().expect("stack underflow");
                asm.cmp_x(a, b);
                asm.cset_x(a, Cond::Le);
            }

            ExprOpcode::CmpGt => {
                let b = reg_stack.pop().expect("stack underflow");
                let a = reg_stack.last().copied().expect("stack underflow");
                asm.cmp_x(a, b);
                asm.cset_x(a, Cond::Gt);
            }

            ExprOpcode::CmpGe => {
                let b = reg_stack.pop().expect("stack underflow");
                let a = reg_stack.last().copied().expect("stack underflow");
                asm.cmp_x(a, b);
                asm.cset_x(a, Cond::Ge);
            }

            ExprOpcode::Not => {
                let a = reg_stack.last().copied().expect("stack underflow");
                // Bool NOT: CMP a, 0; CSET a, EQ → if a==0 set 1, if a==1 set 0.
                asm.cmp_x_imm(a, 0);
                asm.cset_x(a, Cond::Eq);
            }

            ExprOpcode::And(count) => {
                // Short-circuit AND: if any operand is 0 (false), result is 0.
                // Operands are already on the stack (pushed left to right).
                // We need to pop `count` values and AND them with short-circuit.
                let n = *count as usize;
                if n == 0 {
                    let dst = alloc_reg(&mut reg_stack);
                    asm.mov_imm64(dst, 1); // empty AND = true
                } else {
                    // Pop n-1 values into the first, short-circuiting
                    let end_false = asm.label();
                    let end_label = asm.label();

                    for _ in 1..n {
                        let top = reg_stack.pop().expect("stack underflow");
                        asm.cbz_x(top, end_false);
                    }
                    // Last value remains on stack
                    let result = *reg_stack.last().expect("stack underflow");
                    asm.cbz_x(result, end_false);
                    asm.mov_imm64(result, 1);
                    asm.b(end_label);

                    asm.bind(end_false);
                    let result = *reg_stack.last().expect("stack underflow");
                    asm.mov_imm64(result, 0);

                    asm.bind(end_label);
                }
            }

            ExprOpcode::Or(count) => {
                let n = *count as usize;
                if n == 0 {
                    let dst = alloc_reg(&mut reg_stack);
                    asm.mov_imm64(dst, 0); // empty OR = false
                } else {
                    let end_true = asm.label();
                    let end_label = asm.label();

                    for _ in 1..n {
                        let top = reg_stack.pop().expect("stack underflow");
                        asm.cbnz_x(top, end_true);
                    }
                    let result = *reg_stack.last().expect("stack underflow");
                    asm.cbnz_x(result, end_true);
                    asm.mov_imm64(result, 0);
                    asm.b(end_label);

                    asm.bind(end_true);
                    let result = *reg_stack.last().expect("stack underflow");
                    asm.mov_imm64(result, 1);

                    asm.bind(end_label);
                }
            }

            ExprOpcode::Implies => {
                // a => b == !a || b
                let b = reg_stack.pop().expect("stack underflow");
                let a = reg_stack.last().copied().expect("stack underflow");

                let true_label = asm.label();
                let end_label = asm.label();

                // if !a (a==0), result is true
                asm.cbz_x(a, true_label);
                // a is true, result = b
                asm.mov_x(a, b);
                asm.b(end_label);

                asm.bind(true_label);
                asm.mov_imm64(a, 1);

                asm.bind(end_label);
            }

            ExprOpcode::Ite => {
                // Stack: ..., else_val, then_val, cond
                // Pop in reverse: cond first (last pushed), then then_val, then else_val
                // Wait, our stack order: cond is pushed first, then then_val, then else_val
                // So: else_val is on top, then then_val, then cond
                let else_val = reg_stack.pop().expect("stack underflow");
                let then_val = reg_stack.pop().expect("stack underflow");
                let cond = reg_stack.last().copied().expect("stack underflow");

                // if cond != 0: result = then_val, else result = else_val
                asm.cmp_x_imm(cond, 0);
                asm.csel_x(cond, then_val, else_val, Cond::Ne);
            }
        }
    }

    // Move result to x0 for return
    if let Some(&result_reg) = reg_stack.last() {
        if result_reg.0 != 0 {
            asm.mov_x(VARS, result_reg); // x0 = result (overwrites vars ptr, fine)
        }
    } else {
        // Empty expression: return 0
        asm.mov_imm64(VARS, 0);
    }

    // Restore callee-saved registers before return.
    if needs_callee_saved {
        asm.pop_pair(Reg::x(19), Reg::x(20));
    }

    asm.epilogue();

    let code = asm.finalize();
    let executable = ExecutableMemory::new(&code)?;
    let fn_ptr = executable.as_ptr();

    // SAFETY: fn_ptr points to the start of our compiled function in executable
    // memory. The function has extern "C" ABI with signature fn(*const i64) -> i64.
    // The ExecutableMemory is owned by CompiledExprEval and remains alive.
    let func: EvalFn = unsafe { std::mem::transmute::<*const u8, EvalFn>(fn_ptr) };

    Ok(CompiledExprEval {
        func,
        var_mapping,
        is_boolean,
        _executable: executable,
    })
}

#[cfg(target_arch = "x86_64")]
fn compile_x86_64(
    opcodes: &[ExprOpcode],
    var_mapping: VarMapping,
    is_boolean: bool,
) -> Result<CompiledExprEval, JitError> {
    use asm64_x86::*;
    let mut asm = Asm64X86::new();
    let max_scratch_needed = peak_operand_stack_depth(opcodes).ok_or_else(|| {
        JitError::BackendError(
            "malformed expression opcode sequence (operand-stack underflow)".to_string(),
        )
    })?;
    if max_scratch_needed > SCRATCH.len() {
        return Err(JitError::BackendError(format!(
            "x86_64 expression evaluator stack depth {max_scratch_needed} exceeds {} scratch registers",
            SCRATCH.len()
        )));
    }
    let needs_div_mod = opcodes
        .iter()
        .any(|op| matches!(op, ExprOpcode::Div | ExprOpcode::Mod));
    let callee_saved_used: Vec<Reg> = {
        let mut regs = Vec::new();
        for &reg in SCRATCH
            .iter()
            .take(SCRATCH.len().min(max_scratch_needed))
            .skip(CALLEE_SAVED_START)
        {
            regs.push(reg);
        }
        if needs_div_mod && !regs.contains(&R15) {
            regs.push(R15);
        }
        regs
    };
    asm.prologue();
    for &r in &callee_saved_used {
        asm.push_r64(r);
    }
    // Register discipline: the operand at stack position `i` always lives in
    // SCRATCH[i]; popped positions are reused by later pushes. Peak depth was
    // validated against SCRATCH.len() above, so allocation cannot run out.
    // (The previous monotonic allocator silently aliased SCRATCH[0] once the
    // TOTAL number of pushed values exceeded the register file — same #18
    // class as the aarch64 spill bug, minus the crash.)
    let mut reg_stack: Vec<Reg> = Vec::new();
    let alloc_reg = |stack: &mut Vec<Reg>| -> Reg {
        assert!(
            stack.len() < SCRATCH.len(),
            "expr-eval operand stack exceeded the scratch register file despite \
             the pre-compile peak-depth check (#18 contract violation)"
        );
        let r = SCRATCH[stack.len()];
        stack.push(r);
        r
    };
    for op in opcodes {
        match op {
            ExprOpcode::PushBool(b) => {
                let dst = alloc_reg(&mut reg_stack);
                asm.mov_imm64(dst, if *b { 1 } else { 0 });
            }
            ExprOpcode::PushInt(n) => {
                let dst = alloc_reg(&mut reg_stack);
                asm.mov_imm64(dst, *n);
            }
            ExprOpcode::LoadIntVar(idx) | ExprOpcode::LoadBoolVar(idx) => {
                let dst = alloc_reg(&mut reg_stack);
                asm.load_qword(dst, VARS, (*idx as i32) * 8);
            }
            ExprOpcode::Add => {
                let b = reg_stack.pop().expect("stack underflow");
                let a = *reg_stack.last().expect("stack underflow");
                asm.add_rr(a, b);
            }
            ExprOpcode::Sub => {
                let b = reg_stack.pop().expect("stack underflow");
                let a = *reg_stack.last().expect("stack underflow");
                asm.sub_rr(a, b);
            }
            ExprOpcode::Mul => {
                let b = reg_stack.pop().expect("stack underflow");
                let a = *reg_stack.last().expect("stack underflow");
                asm.imul_rr(a, b);
            }
            ExprOpcode::Neg => {
                let a = *reg_stack.last().expect("stack underflow");
                asm.neg_r64(a);
            }
            ExprOpcode::Div => {
                let b = reg_stack.pop().expect("stack underflow");
                let a = *reg_stack.last().expect("stack underflow");
                let done = asm.label();
                let nonzero = asm.label();
                let not_neg_one = asm.label();
                let no_adjust = asm.label();
                let b_neg = asm.label();
                asm.test_rr(b, b);
                asm.jcc(Cond::Ne, nonzero);
                asm.mov_imm64(a, 0);
                asm.jmp(done);
                asm.bind(nonzero);
                // div(a, -1) = -a via wrapping negation. IDIV raises #DE
                // (hardware fault, no unwinding) on i64::MIN / -1; NEG wraps
                // to i64::MIN, matching aarch64 SDIV and the interpreter.
                asm.cmp_imm32(b, -1);
                asm.jcc(Cond::Ne, not_neg_one);
                asm.neg_r64(a);
                asm.jmp(done);
                asm.bind(not_neg_one);
                asm.mov_rr(R15, b);
                asm.mov_rr(RAX, a);
                asm.cqo();
                asm.idiv_r64(R15);
                asm.mov_rr(a, RAX);
                asm.cmp_imm32(RDX, 0);
                asm.jcc(Cond::Ge, no_adjust);
                asm.cmp_imm32(R15, 0);
                asm.jcc(Cond::Lt, b_neg);
                asm.sub_imm32(a, 1);
                asm.jmp(done);
                asm.bind(b_neg);
                asm.add_imm32(a, 1);
                asm.bind(no_adjust);
                asm.bind(done);
            }
            ExprOpcode::Mod => {
                let b = reg_stack.pop().expect("stack underflow");
                let a = *reg_stack.last().expect("stack underflow");
                let done = asm.label();
                let nonzero = asm.label();
                let not_neg_one = asm.label();
                let no_adjust = asm.label();
                let b_neg = asm.label();
                asm.test_rr(b, b);
                asm.jcc(Cond::Ne, nonzero);
                asm.jmp(done);
                asm.bind(nonzero);
                // mod(a, -1) = 0 for all a. IDIV raises #DE on
                // i64::MIN / -1; matches aarch64 SDIV/MSUB and the
                // interpreter.
                asm.cmp_imm32(b, -1);
                asm.jcc(Cond::Ne, not_neg_one);
                asm.mov_imm64(a, 0);
                asm.jmp(done);
                asm.bind(not_neg_one);
                asm.mov_rr(R15, b);
                asm.mov_rr(RAX, a);
                asm.cqo();
                asm.idiv_r64(R15);
                asm.mov_rr(a, RDX);
                asm.cmp_imm32(a, 0);
                asm.jcc(Cond::Ge, no_adjust);
                asm.cmp_imm32(R15, 0);
                asm.jcc(Cond::Lt, b_neg);
                asm.add_rr(a, R15);
                asm.jmp(done);
                asm.bind(b_neg);
                asm.sub_rr(a, R15);
                asm.bind(no_adjust);
                asm.bind(done);
            }
            ExprOpcode::CmpEq => {
                let b = reg_stack.pop().expect("su");
                let a = *reg_stack.last().expect("su");
                asm.cmp_rr(a, b);
                asm.setcc(a, Cond::Eq);
            }
            ExprOpcode::CmpNe => {
                let b = reg_stack.pop().expect("su");
                let a = *reg_stack.last().expect("su");
                asm.cmp_rr(a, b);
                asm.setcc(a, Cond::Ne);
            }
            ExprOpcode::CmpLt => {
                let b = reg_stack.pop().expect("su");
                let a = *reg_stack.last().expect("su");
                asm.cmp_rr(a, b);
                asm.setcc(a, Cond::Lt);
            }
            ExprOpcode::CmpLe => {
                let b = reg_stack.pop().expect("su");
                let a = *reg_stack.last().expect("su");
                asm.cmp_rr(a, b);
                asm.setcc(a, Cond::Le);
            }
            ExprOpcode::CmpGt => {
                let b = reg_stack.pop().expect("su");
                let a = *reg_stack.last().expect("su");
                asm.cmp_rr(a, b);
                asm.setcc(a, Cond::Gt);
            }
            ExprOpcode::CmpGe => {
                let b = reg_stack.pop().expect("su");
                let a = *reg_stack.last().expect("su");
                asm.cmp_rr(a, b);
                asm.setcc(a, Cond::Ge);
            }
            ExprOpcode::Not => {
                let a = *reg_stack.last().expect("su");
                asm.cmp_imm32(a, 0);
                asm.setcc(a, Cond::Eq);
            }
            ExprOpcode::And(count) => {
                let n = *count as usize;
                if n == 0 {
                    let dst = alloc_reg(&mut reg_stack);
                    asm.mov_imm64(dst, 1);
                } else {
                    let end_false = asm.label();
                    let end_label = asm.label();
                    for _ in 1..n {
                        let top = reg_stack.pop().expect("su");
                        asm.test_rr(top, top);
                        asm.jcc(Cond::Eq, end_false);
                    }
                    let result = *reg_stack.last().expect("su");
                    asm.test_rr(result, result);
                    asm.jcc(Cond::Eq, end_false);
                    asm.mov_imm64(result, 1);
                    asm.jmp(end_label);
                    asm.bind(end_false);
                    let result = *reg_stack.last().expect("su");
                    asm.mov_imm64(result, 0);
                    asm.bind(end_label);
                }
            }
            ExprOpcode::Or(count) => {
                let n = *count as usize;
                if n == 0 {
                    let dst = alloc_reg(&mut reg_stack);
                    asm.mov_imm64(dst, 0);
                } else {
                    let end_true = asm.label();
                    let end_label = asm.label();
                    for _ in 1..n {
                        let top = reg_stack.pop().expect("su");
                        asm.test_rr(top, top);
                        asm.jcc(Cond::Ne, end_true);
                    }
                    let result = *reg_stack.last().expect("su");
                    asm.test_rr(result, result);
                    asm.jcc(Cond::Ne, end_true);
                    asm.mov_imm64(result, 0);
                    asm.jmp(end_label);
                    asm.bind(end_true);
                    let result = *reg_stack.last().expect("su");
                    asm.mov_imm64(result, 1);
                    asm.bind(end_label);
                }
            }
            ExprOpcode::Implies => {
                let b = reg_stack.pop().expect("su");
                let a = *reg_stack.last().expect("su");
                let true_label = asm.label();
                let end_label = asm.label();
                asm.test_rr(a, a);
                asm.jcc(Cond::Eq, true_label);
                asm.mov_rr(a, b);
                asm.jmp(end_label);
                asm.bind(true_label);
                asm.mov_imm64(a, 1);
                asm.bind(end_label);
            }
            ExprOpcode::Ite => {
                let else_val = reg_stack.pop().expect("su");
                let then_val = reg_stack.pop().expect("su");
                let cond = *reg_stack.last().expect("su");
                asm.test_rr(cond, cond);
                asm.mov_rr(cond, else_val);
                asm.cmovcc(cond, then_val, Cond::Ne);
            }
        }
    }
    if let Some(&result_reg) = reg_stack.last() {
        if result_reg != RAX {
            asm.mov_rr(RAX, result_reg);
        }
    } else {
        asm.mov_imm64(RAX, 0);
    }
    for &r in callee_saved_used.iter().rev() {
        asm.pop_r64(r);
    }
    asm.epilogue();
    let code = asm.finalize();
    let executable = ExecutableMemory::new(&code)?;
    let fn_ptr = executable.as_ptr();
    // SAFETY: fn_ptr points to the start of our compiled function in executable
    // memory. The function has extern "C" ABI with signature fn(*const i64) -> i64.
    let func: EvalFn = unsafe { std::mem::transmute::<*const u8, EvalFn>(fn_ptr) };
    Ok(CompiledExprEval {
        func,
        var_mapping,
        is_boolean,
        _executable: executable,
    })
}

// ---------------------------------------------------------------------------
// Compile from expression trait object
// ---------------------------------------------------------------------------

/// Compile an expression into a native evaluator.
///
/// Returns None if the expression is not JIT-compilable.
///
/// # Errors
///
/// Returns `JitError` if native compilation fails.
pub fn compile_expr(expr: &dyn ExprLike) -> Result<Option<CompiledExprEval>, JitError> {
    if !expr.is_jit_compilable() {
        return Ok(None);
    }

    let mut var_mapping = VarMapping::new();
    let opcodes = match flatten(expr, &mut var_mapping) {
        Some(ops) => ops,
        None => return Ok(None),
    };
    // Fail closed to the interpreter when the expression needs more
    // simultaneously-live operands than the scratch register file holds.
    // The native generators have no spill path by design (#18).
    #[cfg(any(target_arch = "aarch64", target_arch = "x86_64"))]
    match peak_operand_stack_depth(&opcodes) {
        Some(peak) if peak <= NATIVE_EVAL_MAX_OPERAND_DEPTH => {}
        _ => return Ok(None),
    }

    let is_boolean = expr.is_boolean();
    let compiled = compile(&opcodes, var_mapping, is_boolean)?;
    Ok(Some(compiled))
}

/// Expression evaluator: either native JIT or interpreted fallback.
///
/// On aarch64 and x86_64, `compile_expr_portable` produces a `Native` variant
/// backed by machine code. On other platforms (or if compilation fails), it
/// produces an `Interpreted` variant that evaluates opcodes in Rust. Both
/// variants expose the same evaluation interface.
pub enum ExprEvaluator {
    /// JIT-compiled native machine code.
    Native(CompiledExprEval),
    /// Interpreted opcode sequence (all platforms).
    Interpreted(InterpretedExprEval),
}

impl ExprEvaluator {
    /// Evaluate the expression with the given variable values.
    ///
    /// `vars` must have length >= `var_mapping().total_vars()`.
    pub fn evaluate_checked(&self, vars: &[i64]) -> Option<i64> {
        match self {
            Self::Native(c) => c.evaluate_checked(vars),
            Self::Interpreted(i) => i.evaluate_checked(vars),
        }
    }

    /// Evaluate a boolean expression with bounds-checked variable array.
    pub fn evaluate_bool_checked(&self, vars: &[i64]) -> Option<bool> {
        match self {
            Self::Native(c) => c.evaluate_bool_checked(vars),
            Self::Interpreted(i) => i.evaluate_bool_checked(vars),
        }
    }

    /// Access the variable mapping.
    pub fn var_mapping(&self) -> &VarMapping {
        match self {
            Self::Native(c) => c.var_mapping(),
            Self::Interpreted(i) => i.var_mapping(),
        }
    }

    /// Whether this is backed by native machine code.
    pub fn is_native(&self) -> bool {
        matches!(self, Self::Native(_))
    }
}

/// Compile an expression, trying native JIT first and falling back to
/// interpreted evaluation.
///
/// Returns `None` if the expression is not compilable. Always succeeds on
/// any platform for compilable expressions (the interpreted fallback has
/// no platform requirements).
pub fn compile_expr_portable(expr: &dyn ExprLike) -> Option<ExprEvaluator> {
    if !expr.is_jit_compilable() {
        return None;
    }

    // Try native compilation first.
    match compile_expr(expr) {
        Ok(Some(compiled)) => return Some(ExprEvaluator::Native(compiled)),
        Ok(None) => {}
        Err(_) => {}
    }

    // Fall back to interpreted evaluation.
    compile_interpreted(expr).map(ExprEvaluator::Interpreted)
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

/// Compile for a test, or SKIP the enclosing test (early return) on OSes
/// where JIT executable memory is unavailable (Windows fails closed with
/// `NoNativeIsa` by design; see executable.rs). Any other compile error
/// still panics — only the designed-unavailable case skips.
#[cfg(test)]
macro_rules! compile_or_skip {
    ($($args:tt)*) => {
        match compile($($args)*) {
            Ok(compiled) => compiled,
            Err(crate::JitError::NoNativeIsa) => return,
            Err(error) => panic!("compile failed: {error:?}"),
        }
    };
}

#[cfg(test)]
#[cfg(any(target_arch = "aarch64", target_arch = "x86_64"))]
mod tests {
    use super::*;

    #[test]
    fn test_compile_bool_constant_true() {
        let opcodes = vec![ExprOpcode::PushBool(true)];
        let var_mapping = VarMapping::new();
        let compiled = compile_or_skip!(&opcodes, var_mapping, true);
        let vars: Vec<i64> = vec![];
        // SAFETY: `vars` is sized to match `var_mapping.total_vars()` for this
        // compiled expression (both constructed adjacent above), satisfying
        // `evaluate_raw`'s contract. `compiled` owns the backing executable.
        let result = unsafe { compiled.evaluate_raw(&vars) };
        assert_eq!(result, 1);
    }

    #[test]
    fn test_compile_bool_constant_false() {
        let opcodes = vec![ExprOpcode::PushBool(false)];
        let var_mapping = VarMapping::new();
        let compiled = compile_or_skip!(&opcodes, var_mapping, true);
        let vars: Vec<i64> = vec![];
        // SAFETY: `vars` is sized to match `var_mapping.total_vars()` for this
        // compiled expression (both constructed adjacent above), satisfying
        // `evaluate_raw`'s contract. `compiled` owns the backing executable.
        let result = unsafe { compiled.evaluate_raw(&vars) };
        assert_eq!(result, 0);
    }

    #[test]
    fn test_compile_int_constant() {
        let opcodes = vec![ExprOpcode::PushInt(42)];
        let var_mapping = VarMapping::new();
        let compiled = compile_or_skip!(&opcodes, var_mapping, false);
        let vars: Vec<i64> = vec![];
        // SAFETY: `vars` is sized to match `var_mapping.total_vars()` for this
        // compiled expression (both constructed adjacent above), satisfying
        // `evaluate_raw`'s contract. `compiled` owns the backing executable.
        let result = unsafe { compiled.evaluate_raw(&vars) };
        assert_eq!(result, 42);
    }

    #[test]
    fn test_compile_int_constant_negative() {
        let opcodes = vec![ExprOpcode::PushInt(-123)];
        let var_mapping = VarMapping::new();
        let compiled = compile_or_skip!(&opcodes, var_mapping, false);
        let vars: Vec<i64> = vec![];
        // SAFETY: `vars` is sized to match `var_mapping.total_vars()` for this
        // compiled expression (both constructed adjacent above), satisfying
        // `evaluate_raw`'s contract. `compiled` owns the backing executable.
        let result = unsafe { compiled.evaluate_raw(&vars) };
        assert_eq!(result, -123);
    }

    #[test]
    fn test_compile_int_constant_large() {
        let opcodes = vec![ExprOpcode::PushInt(i64::MAX)];
        let var_mapping = VarMapping::new();
        let compiled = compile_or_skip!(&opcodes, var_mapping, false);
        let vars: Vec<i64> = vec![];
        // SAFETY: `vars` is sized to match `var_mapping.total_vars()` for this
        // compiled expression (both constructed adjacent above), satisfying
        // `evaluate_raw`'s contract. `compiled` owns the backing executable.
        let result = unsafe { compiled.evaluate_raw(&vars) };
        assert_eq!(result, i64::MAX);
    }

    #[test]
    fn test_compile_load_var() {
        let opcodes = vec![ExprOpcode::LoadIntVar(0)];
        let mut var_mapping = VarMapping::new();
        var_mapping.get_or_insert_int("x");
        let compiled = compile_or_skip!(&opcodes, var_mapping, false);
        let vars: Vec<i64> = vec![99];
        // SAFETY: `vars` is sized to match `var_mapping.total_vars()` for this
        // compiled expression (both constructed adjacent above), satisfying
        // `evaluate_raw`'s contract. `compiled` owns the backing executable.
        let result = unsafe { compiled.evaluate_raw(&vars) };
        assert_eq!(result, 99);
    }

    #[test]
    fn test_compile_add() {
        // x + y where x=10, y=20
        let opcodes = vec![
            ExprOpcode::LoadIntVar(0),
            ExprOpcode::LoadIntVar(1),
            ExprOpcode::Add,
        ];
        let mut var_mapping = VarMapping::new();
        var_mapping.get_or_insert_int("x");
        var_mapping.get_or_insert_int("y");
        let compiled = compile_or_skip!(&opcodes, var_mapping, false);
        let vars: Vec<i64> = vec![10, 20];
        // SAFETY: `vars` is sized to match `var_mapping.total_vars()` for this
        // compiled expression (both constructed adjacent above), satisfying
        // `evaluate_raw`'s contract. `compiled` owns the backing executable.
        let result = unsafe { compiled.evaluate_raw(&vars) };
        assert_eq!(result, 30);
    }

    #[test]
    fn test_compile_sub() {
        // x - y where x=50, y=30
        let opcodes = vec![
            ExprOpcode::LoadIntVar(0),
            ExprOpcode::LoadIntVar(1),
            ExprOpcode::Sub,
        ];
        let mut var_mapping = VarMapping::new();
        var_mapping.get_or_insert_int("x");
        var_mapping.get_or_insert_int("y");
        let compiled = compile_or_skip!(&opcodes, var_mapping, false);
        let vars: Vec<i64> = vec![50, 30];
        // SAFETY: `vars` is sized to match `var_mapping.total_vars()` for this
        // compiled expression (both constructed adjacent above), satisfying
        // `evaluate_raw`'s contract. `compiled` owns the backing executable.
        let result = unsafe { compiled.evaluate_raw(&vars) };
        assert_eq!(result, 20);
    }

    #[test]
    fn test_compile_mul() {
        // x * y where x=6, y=7
        let opcodes = vec![
            ExprOpcode::LoadIntVar(0),
            ExprOpcode::LoadIntVar(1),
            ExprOpcode::Mul,
        ];
        let mut var_mapping = VarMapping::new();
        var_mapping.get_or_insert_int("x");
        var_mapping.get_or_insert_int("y");
        let compiled = compile_or_skip!(&opcodes, var_mapping, false);
        let vars: Vec<i64> = vec![6, 7];
        // SAFETY: `vars` is sized to match `var_mapping.total_vars()` for this
        // compiled expression (both constructed adjacent above), satisfying
        // `evaluate_raw`'s contract. `compiled` owns the backing executable.
        let result = unsafe { compiled.evaluate_raw(&vars) };
        assert_eq!(result, 42);
    }

    #[test]
    fn test_compile_neg() {
        let opcodes = vec![ExprOpcode::PushInt(42), ExprOpcode::Neg];
        let var_mapping = VarMapping::new();
        let compiled = compile_or_skip!(&opcodes, var_mapping, false);
        let vars: Vec<i64> = vec![];
        // SAFETY: `vars` is sized to match `var_mapping.total_vars()` for this
        // compiled expression (both constructed adjacent above), satisfying
        // `evaluate_raw`'s contract. `compiled` owns the backing executable.
        let result = unsafe { compiled.evaluate_raw(&vars) };
        assert_eq!(result, -42);
    }

    #[test]
    fn test_compile_cmp_lt() {
        // x < y where x=5, y=10
        let opcodes = vec![
            ExprOpcode::LoadIntVar(0),
            ExprOpcode::LoadIntVar(1),
            ExprOpcode::CmpLt,
        ];
        let mut var_mapping = VarMapping::new();
        var_mapping.get_or_insert_int("x");
        var_mapping.get_or_insert_int("y");
        let compiled = compile_or_skip!(&opcodes, var_mapping, true);

        let vars_true: Vec<i64> = vec![5, 10];
        // SAFETY: `vars` is sized to match `var_mapping.total_vars()` for this
        // compiled expression (both constructed adjacent above), satisfying
        // `evaluate_raw`'s contract. `compiled` owns the backing executable.
        let result = unsafe { compiled.evaluate_raw(&vars_true) };
        assert_eq!(result, 1);

        let vars_false: Vec<i64> = vec![10, 5];
        // SAFETY: `vars` is sized to match `var_mapping.total_vars()` for this
        // compiled expression (both constructed adjacent above), satisfying
        // `evaluate_raw`'s contract. `compiled` owns the backing executable.
        let result = unsafe { compiled.evaluate_raw(&vars_false) };
        assert_eq!(result, 0);
    }

    #[test]
    fn test_compile_cmp_eq() {
        let opcodes = vec![
            ExprOpcode::LoadIntVar(0),
            ExprOpcode::LoadIntVar(1),
            ExprOpcode::CmpEq,
        ];
        let mut var_mapping = VarMapping::new();
        var_mapping.get_or_insert_int("x");
        var_mapping.get_or_insert_int("y");
        let compiled = compile_or_skip!(&opcodes, var_mapping, true);

        let vars_eq: Vec<i64> = vec![42, 42];
        // SAFETY: `vars` is sized to match `var_mapping.total_vars()` for this
        // compiled expression (both constructed adjacent above), satisfying
        // `evaluate_raw`'s contract. `compiled` owns the backing executable.
        assert_eq!(unsafe { compiled.evaluate_raw(&vars_eq) }, 1);

        let vars_ne: Vec<i64> = vec![42, 43];
        // SAFETY: `vars` is sized to match `var_mapping.total_vars()` for this
        // compiled expression (both constructed adjacent above), satisfying
        // `evaluate_raw`'s contract. `compiled` owns the backing executable.
        assert_eq!(unsafe { compiled.evaluate_raw(&vars_ne) }, 0);
    }

    #[test]
    fn test_compile_not() {
        let opcodes = vec![ExprOpcode::PushBool(true), ExprOpcode::Not];
        let var_mapping = VarMapping::new();
        let compiled = compile_or_skip!(&opcodes, var_mapping, true);
        let vars: Vec<i64> = vec![];
        // SAFETY: `vars` is sized to match `var_mapping.total_vars()` for this
        // compiled expression (both constructed adjacent above), satisfying
        // `evaluate_raw`'s contract. `compiled` owns the backing executable.
        assert_eq!(unsafe { compiled.evaluate_raw(&vars) }, 0);

        let opcodes2 = vec![ExprOpcode::PushBool(false), ExprOpcode::Not];
        let compiled2 = compile_or_skip!(&opcodes2, VarMapping::new(), true);
        // SAFETY: `vars` is sized to match `var_mapping.total_vars()` for this
        // compiled expression (both constructed adjacent above), satisfying
        // `evaluate_raw`'s contract. `compiled` owns the backing executable.
        assert_eq!(unsafe { compiled2.evaluate_raw(&vars) }, 1);
    }

    #[test]
    fn test_compile_and_short_circuit() {
        // AND(false, true) should short-circuit to false
        let opcodes = vec![
            ExprOpcode::PushBool(false),
            ExprOpcode::PushBool(true),
            ExprOpcode::And(2),
        ];
        let var_mapping = VarMapping::new();
        let compiled = compile_or_skip!(&opcodes, var_mapping, true);
        let vars: Vec<i64> = vec![];
        // SAFETY: `vars` is sized to match `var_mapping.total_vars()` for this
        // compiled expression (both constructed adjacent above), satisfying
        // `evaluate_raw`'s contract. `compiled` owns the backing executable.
        assert_eq!(unsafe { compiled.evaluate_raw(&vars) }, 0);
    }

    #[test]
    fn test_compile_and_both_true() {
        let opcodes = vec![
            ExprOpcode::PushBool(true),
            ExprOpcode::PushBool(true),
            ExprOpcode::And(2),
        ];
        let compiled = compile_or_skip!(&opcodes, VarMapping::new(), true);
        // SAFETY: `vars` is sized to match `var_mapping.total_vars()` for this
        // compiled expression (both constructed adjacent above), satisfying
        // `evaluate_raw`'s contract. `compiled` owns the backing executable.
        assert_eq!(unsafe { compiled.evaluate_raw(&[]) }, 1);
    }

    #[test]
    fn test_compile_or_short_circuit() {
        // OR(true, false) should short-circuit to true
        let opcodes = vec![
            ExprOpcode::PushBool(true),
            ExprOpcode::PushBool(false),
            ExprOpcode::Or(2),
        ];
        let compiled = compile_or_skip!(&opcodes, VarMapping::new(), true);
        // SAFETY: `vars` is sized to match `var_mapping.total_vars()` for this
        // compiled expression (both constructed adjacent above), satisfying
        // `evaluate_raw`'s contract. `compiled` owns the backing executable.
        assert_eq!(unsafe { compiled.evaluate_raw(&[]) }, 1);
    }

    #[test]
    fn test_compile_or_both_false() {
        let opcodes = vec![
            ExprOpcode::PushBool(false),
            ExprOpcode::PushBool(false),
            ExprOpcode::Or(2),
        ];
        let compiled = compile_or_skip!(&opcodes, VarMapping::new(), true);
        // SAFETY: `vars` is sized to match `var_mapping.total_vars()` for this
        // compiled expression (both constructed adjacent above), satisfying
        // `evaluate_raw`'s contract. `compiled` owns the backing executable.
        assert_eq!(unsafe { compiled.evaluate_raw(&[]) }, 0);
    }

    #[test]
    fn test_compile_implies() {
        // true => false = false
        let opcodes = vec![
            ExprOpcode::PushBool(true),
            ExprOpcode::PushBool(false),
            ExprOpcode::Implies,
        ];
        let compiled = compile_or_skip!(&opcodes, VarMapping::new(), true);
        // SAFETY: `vars` is sized to match `var_mapping.total_vars()` for this
        // compiled expression (both constructed adjacent above), satisfying
        // `evaluate_raw`'s contract. `compiled` owns the backing executable.
        assert_eq!(unsafe { compiled.evaluate_raw(&[]) }, 0);

        // false => false = true
        let opcodes2 = vec![
            ExprOpcode::PushBool(false),
            ExprOpcode::PushBool(false),
            ExprOpcode::Implies,
        ];
        let compiled2 = compile_or_skip!(&opcodes2, VarMapping::new(), true);
        // SAFETY: `vars` is sized to match `var_mapping.total_vars()` for this
        // compiled expression (both constructed adjacent above), satisfying
        // `evaluate_raw`'s contract. `compiled` owns the backing executable.
        assert_eq!(unsafe { compiled2.evaluate_raw(&[]) }, 1);
    }

    #[test]
    fn test_compile_ite() {
        // if true then 42 else 99
        let opcodes = vec![
            ExprOpcode::PushBool(true),
            ExprOpcode::PushInt(42),
            ExprOpcode::PushInt(99),
            ExprOpcode::Ite,
        ];
        let compiled = compile_or_skip!(&opcodes, VarMapping::new(), false);
        // SAFETY: `vars` is sized to match `var_mapping.total_vars()` for this
        // compiled expression (both constructed adjacent above), satisfying
        // `evaluate_raw`'s contract. `compiled` owns the backing executable.
        assert_eq!(unsafe { compiled.evaluate_raw(&[]) }, 42);

        // if false then 42 else 99
        let opcodes2 = vec![
            ExprOpcode::PushBool(false),
            ExprOpcode::PushInt(42),
            ExprOpcode::PushInt(99),
            ExprOpcode::Ite,
        ];
        let compiled2 = compile_or_skip!(&opcodes2, VarMapping::new(), false);
        // SAFETY: `vars` is sized to match `var_mapping.total_vars()` for this
        // compiled expression (both constructed adjacent above), satisfying
        // `evaluate_raw`'s contract. `compiled` owns the backing executable.
        assert_eq!(unsafe { compiled2.evaluate_raw(&[]) }, 99);
    }

    #[test]
    fn test_compile_nested_comparison() {
        // (x + y) <= 10 where x=3, y=5
        let opcodes = vec![
            ExprOpcode::LoadIntVar(0), // x
            ExprOpcode::LoadIntVar(1), // y
            ExprOpcode::Add,           // x + y
            ExprOpcode::PushInt(10),
            ExprOpcode::CmpLe, // (x + y) <= 10
        ];
        let mut var_mapping = VarMapping::new();
        var_mapping.get_or_insert_int("x");
        var_mapping.get_or_insert_int("y");
        let compiled = compile_or_skip!(&opcodes, var_mapping, true);

        // 3 + 5 = 8 <= 10 = true
        let vars: Vec<i64> = vec![3, 5];
        // SAFETY: `vars` is sized to match `var_mapping.total_vars()` for this
        // compiled expression (both constructed adjacent above), satisfying
        // `evaluate_raw`'s contract. `compiled` owns the backing executable.
        assert_eq!(unsafe { compiled.evaluate_raw(&vars) }, 1);

        // 6 + 7 = 13 <= 10 = false
        let vars2: Vec<i64> = vec![6, 7];
        // SAFETY: `vars` is sized to match `var_mapping.total_vars()` for this
        // compiled expression (both constructed adjacent above), satisfying
        // `evaluate_raw`'s contract. `compiled` owns the backing executable.
        assert_eq!(unsafe { compiled.evaluate_raw(&vars2) }, 0);
    }

    #[test]
    fn test_compile_complex_and() {
        // (x <= 10) AND (y > 0)
        let opcodes = vec![
            ExprOpcode::LoadIntVar(0),
            ExprOpcode::PushInt(10),
            ExprOpcode::CmpLe,
            ExprOpcode::LoadIntVar(1),
            ExprOpcode::PushInt(0),
            ExprOpcode::CmpGt,
            ExprOpcode::And(2),
        ];
        let mut var_mapping = VarMapping::new();
        var_mapping.get_or_insert_int("x");
        var_mapping.get_or_insert_int("y");
        let compiled = compile_or_skip!(&opcodes, var_mapping, true);

        // x=5 <= 10 AND y=3 > 0 -> true
        // SAFETY: `vars` is sized to match `var_mapping.total_vars()` for this
        // compiled expression (both constructed adjacent above), satisfying
        // `evaluate_raw`'s contract. `compiled` owns the backing executable.
        assert_eq!(unsafe { compiled.evaluate_raw(&[5, 3]) }, 1);

        // x=15 <= 10 = false, short-circuits to false
        // SAFETY: `vars` is sized to match `var_mapping.total_vars()` for this
        // compiled expression (both constructed adjacent above), satisfying
        // `evaluate_raw`'s contract. `compiled` owns the backing executable.
        assert_eq!(unsafe { compiled.evaluate_raw(&[15, 3]) }, 0);

        // x=5 <= 10 = true, y=-1 > 0 = false
        // SAFETY: `vars` is sized to match `var_mapping.total_vars()` for this
        // compiled expression (both constructed adjacent above), satisfying
        // `evaluate_raw`'s contract. `compiled` owns the backing executable.
        assert_eq!(unsafe { compiled.evaluate_raw(&[5, -1]) }, 0);
    }

    #[test]
    fn test_compile_div_by_zero() {
        // x / 0 should return 0 (SMT-LIB semantics)
        let opcodes = vec![
            ExprOpcode::PushInt(42),
            ExprOpcode::PushInt(0),
            ExprOpcode::Div,
        ];
        let compiled = compile_or_skip!(&opcodes, VarMapping::new(), false);
        // SAFETY: `vars` is sized to match `var_mapping.total_vars()` for this
        // compiled expression (both constructed adjacent above), satisfying
        // `evaluate_raw`'s contract. `compiled` owns the backing executable.
        assert_eq!(unsafe { compiled.evaluate_raw(&[]) }, 0);
    }

    #[test]
    fn test_compile_mod() {
        // 7 mod 3 = 1 (Euclidean)
        let opcodes = vec![
            ExprOpcode::PushInt(7),
            ExprOpcode::PushInt(3),
            ExprOpcode::Mod,
        ];
        let compiled = compile_or_skip!(&opcodes, VarMapping::new(), false);
        // SAFETY: `vars` is sized to match `var_mapping.total_vars()` for this
        // compiled expression (both constructed adjacent above), satisfying
        // `evaluate_raw`'s contract. `compiled` owns the backing executable.
        assert_eq!(unsafe { compiled.evaluate_raw(&[]) }, 1);
    }

    #[test]
    fn test_compile_mod_by_zero() {
        // x mod 0 = x (SMT-LIB semantics)
        let opcodes = vec![
            ExprOpcode::PushInt(42),
            ExprOpcode::PushInt(0),
            ExprOpcode::Mod,
        ];
        let compiled = compile_or_skip!(&opcodes, VarMapping::new(), false);
        // SAFETY: `vars` is sized to match `var_mapping.total_vars()` for this
        // compiled expression (both constructed adjacent above), satisfying
        // `evaluate_raw`'s contract. `compiled` owns the backing executable.
        assert_eq!(unsafe { compiled.evaluate_raw(&[]) }, 42);
    }

    #[test]
    fn test_compile_div_mod_min_by_neg_one_matches_interpreter() {
        // Regression: IDIV on i64::MIN / -1 raises a hardware #DE fault.
        // The emitted b == -1 guard must keep the native path total and in
        // lockstep with the interpreter's wrapping semantics.
        assert_jit_matches_interpret(
            &[
                ExprOpcode::PushInt(i64::MIN),
                ExprOpcode::PushInt(-1),
                ExprOpcode::Div,
            ],
            &[],
        );
        assert_jit_matches_interpret(
            &[
                ExprOpcode::PushInt(i64::MIN),
                ExprOpcode::PushInt(-1),
                ExprOpcode::Mod,
            ],
            &[],
        );
        assert_jit_matches_interpret(
            &[
                ExprOpcode::PushInt(7),
                ExprOpcode::PushInt(-1),
                ExprOpcode::Div,
            ],
            &[],
        );
        assert_jit_matches_interpret(
            &[
                ExprOpcode::PushInt(-7),
                ExprOpcode::PushInt(-1),
                ExprOpcode::Mod,
            ],
            &[],
        );
    }

    /// Helper: run opcodes through both JIT and interpreter, assert results match.
    fn assert_jit_matches_interpret(opcodes: &[ExprOpcode], vars: &[i64]) {
        let interp_result = interpret(opcodes, vars).expect("interpret failed");
        let compiled = compile_or_skip!(opcodes, VarMapping::new(), false);
        // SAFETY: `vars` is sized to match `var_mapping.total_vars()` for this
        // compiled expression (both constructed adjacent above), satisfying
        // `evaluate_raw`'s contract. `compiled` owns the backing executable.
        let jit_result = unsafe { compiled.evaluate_raw(vars) };
        assert_eq!(
            jit_result, interp_result,
            "JIT ({jit_result}) != interpret ({interp_result}) for opcodes {opcodes:?} with vars {vars:?}"
        );
    }

    #[test]
    #[cfg(target_arch = "x86_64")]
    fn test_x86_64_rejects_register_stack_overflow() {
        let operand_count = asm64_x86::SCRATCH.len() + 1;
        let mut opcodes = vec![ExprOpcode::PushBool(true); operand_count];
        opcodes.push(ExprOpcode::And(operand_count as u16));

        assert_eq!(interpret(&opcodes, &[]), Some(1));
        assert!(
            compile(&opcodes, VarMapping::new(), true).is_err(),
            "x86_64 native evaluator must fail closed until it has real spilling"
        );
    }

    #[test]
    fn test_jit_vs_interpret_constants() {
        assert_jit_matches_interpret(&[ExprOpcode::PushBool(true)], &[]);
        assert_jit_matches_interpret(&[ExprOpcode::PushBool(false)], &[]);
        assert_jit_matches_interpret(&[ExprOpcode::PushInt(0)], &[]);
        assert_jit_matches_interpret(&[ExprOpcode::PushInt(42)], &[]);
        assert_jit_matches_interpret(&[ExprOpcode::PushInt(-1)], &[]);
        assert_jit_matches_interpret(&[ExprOpcode::PushInt(i64::MAX)], &[]);
        assert_jit_matches_interpret(&[ExprOpcode::PushInt(i64::MIN)], &[]);
    }

    #[test]
    fn test_jit_vs_interpret_arithmetic() {
        // add
        assert_jit_matches_interpret(
            &[
                ExprOpcode::PushInt(10),
                ExprOpcode::PushInt(20),
                ExprOpcode::Add,
            ],
            &[],
        );
        // sub
        assert_jit_matches_interpret(
            &[
                ExprOpcode::PushInt(50),
                ExprOpcode::PushInt(30),
                ExprOpcode::Sub,
            ],
            &[],
        );
        // mul
        assert_jit_matches_interpret(
            &[
                ExprOpcode::PushInt(6),
                ExprOpcode::PushInt(7),
                ExprOpcode::Mul,
            ],
            &[],
        );
        // neg
        assert_jit_matches_interpret(&[ExprOpcode::PushInt(42), ExprOpcode::Neg], &[]);
        // div
        assert_jit_matches_interpret(
            &[
                ExprOpcode::PushInt(10),
                ExprOpcode::PushInt(3),
                ExprOpcode::Div,
            ],
            &[],
        );
        // div by zero
        assert_jit_matches_interpret(
            &[
                ExprOpcode::PushInt(42),
                ExprOpcode::PushInt(0),
                ExprOpcode::Div,
            ],
            &[],
        );
        // mod
        assert_jit_matches_interpret(
            &[
                ExprOpcode::PushInt(7),
                ExprOpcode::PushInt(3),
                ExprOpcode::Mod,
            ],
            &[],
        );
        // mod by zero
        assert_jit_matches_interpret(
            &[
                ExprOpcode::PushInt(42),
                ExprOpcode::PushInt(0),
                ExprOpcode::Mod,
            ],
            &[],
        );
    }

    #[test]
    fn test_jit_vs_interpret_euclidean_div_negative() {
        // Euclidean division: -7 / 2 = -4 (floor), not -3 (truncation)
        assert_jit_matches_interpret(
            &[
                ExprOpcode::PushInt(-7),
                ExprOpcode::PushInt(2),
                ExprOpcode::Div,
            ],
            &[],
        );
        // -7 / -2 = 4 (Euclidean)
        assert_jit_matches_interpret(
            &[
                ExprOpcode::PushInt(-7),
                ExprOpcode::PushInt(-2),
                ExprOpcode::Div,
            ],
            &[],
        );
        // -7 mod 2 = 1 (Euclidean, always non-negative)
        assert_jit_matches_interpret(
            &[
                ExprOpcode::PushInt(-7),
                ExprOpcode::PushInt(2),
                ExprOpcode::Mod,
            ],
            &[],
        );
        // -7 mod -2 = 1 (Euclidean)
        assert_jit_matches_interpret(
            &[
                ExprOpcode::PushInt(-7),
                ExprOpcode::PushInt(-2),
                ExprOpcode::Mod,
            ],
            &[],
        );
    }

    #[test]
    fn test_jit_vs_interpret_comparisons() {
        for &(a, b) in &[(5, 10), (10, 5), (5, 5), (-1, 0), (0, -1)] {
            let ops = &[ExprOpcode::PushInt(a), ExprOpcode::PushInt(b)];
            assert_jit_matches_interpret(&[ops[0].clone(), ops[1].clone(), ExprOpcode::CmpEq], &[]);
            assert_jit_matches_interpret(&[ops[0].clone(), ops[1].clone(), ExprOpcode::CmpNe], &[]);
            assert_jit_matches_interpret(&[ops[0].clone(), ops[1].clone(), ExprOpcode::CmpLt], &[]);
            assert_jit_matches_interpret(&[ops[0].clone(), ops[1].clone(), ExprOpcode::CmpLe], &[]);
            assert_jit_matches_interpret(&[ops[0].clone(), ops[1].clone(), ExprOpcode::CmpGt], &[]);
            assert_jit_matches_interpret(&[ops[0].clone(), ops[1].clone(), ExprOpcode::CmpGe], &[]);
        }
    }

    #[test]
    fn test_jit_vs_interpret_boolean() {
        // NOT
        assert_jit_matches_interpret(&[ExprOpcode::PushBool(true), ExprOpcode::Not], &[]);
        assert_jit_matches_interpret(&[ExprOpcode::PushBool(false), ExprOpcode::Not], &[]);

        // AND
        for &(a, b) in &[(true, true), (true, false), (false, true), (false, false)] {
            assert_jit_matches_interpret(
                &[
                    ExprOpcode::PushBool(a),
                    ExprOpcode::PushBool(b),
                    ExprOpcode::And(2),
                ],
                &[],
            );
        }

        // OR
        for &(a, b) in &[(true, true), (true, false), (false, true), (false, false)] {
            assert_jit_matches_interpret(
                &[
                    ExprOpcode::PushBool(a),
                    ExprOpcode::PushBool(b),
                    ExprOpcode::Or(2),
                ],
                &[],
            );
        }

        // IMPLIES
        for &(a, b) in &[(true, true), (true, false), (false, true), (false, false)] {
            assert_jit_matches_interpret(
                &[
                    ExprOpcode::PushBool(a),
                    ExprOpcode::PushBool(b),
                    ExprOpcode::Implies,
                ],
                &[],
            );
        }
    }

    #[test]
    fn test_jit_vs_interpret_ite() {
        assert_jit_matches_interpret(
            &[
                ExprOpcode::PushBool(true),
                ExprOpcode::PushInt(42),
                ExprOpcode::PushInt(99),
                ExprOpcode::Ite,
            ],
            &[],
        );
        assert_jit_matches_interpret(
            &[
                ExprOpcode::PushBool(false),
                ExprOpcode::PushInt(42),
                ExprOpcode::PushInt(99),
                ExprOpcode::Ite,
            ],
            &[],
        );
    }

    #[test]
    fn test_jit_vs_interpret_complex_expression() {
        // (x + y) <= 10 AND (x * 2) > 0
        let opcodes = vec![
            ExprOpcode::LoadIntVar(0),
            ExprOpcode::LoadIntVar(1),
            ExprOpcode::Add,
            ExprOpcode::PushInt(10),
            ExprOpcode::CmpLe,
            ExprOpcode::LoadIntVar(0),
            ExprOpcode::PushInt(2),
            ExprOpcode::Mul,
            ExprOpcode::PushInt(0),
            ExprOpcode::CmpGt,
            ExprOpcode::And(2),
        ];
        // Test with multiple variable assignments.
        for &(x, y) in &[(3, 5), (6, 7), (0, 0), (-1, 11), (5, 5)] {
            let vars = vec![x, y];
            let interp_result = interpret(&opcodes, &vars).expect("interpret failed");
            let mut vm = VarMapping::new();
            vm.get_or_insert_int("x");
            vm.get_or_insert_int("y");
            let compiled = compile_or_skip!(&opcodes, vm, true);
            // SAFETY: `vars` is sized to match `var_mapping.total_vars()` for this
            // compiled expression (both constructed adjacent above), satisfying
            // `evaluate_raw`'s contract. `compiled` owns the backing executable.
            let jit_result = unsafe { compiled.evaluate_raw(&vars) };
            assert_eq!(jit_result, interp_result, "x={x}, y={y}");
        }
    }

    #[test]
    fn test_jit_vs_interpret_nested_ite() {
        // if (x > 0) then (x + 1) else (x - 1)
        let opcodes = vec![
            ExprOpcode::LoadIntVar(0),
            ExprOpcode::PushInt(0),
            ExprOpcode::CmpGt,
            ExprOpcode::LoadIntVar(0),
            ExprOpcode::PushInt(1),
            ExprOpcode::Add,
            ExprOpcode::LoadIntVar(0),
            ExprOpcode::PushInt(1),
            ExprOpcode::Sub,
            ExprOpcode::Ite,
        ];
        for &x in &[5, 0, -3, 1, -1] {
            let vars = vec![x];
            let interp_result = interpret(&opcodes, &vars).expect("interpret failed");
            let mut vm = VarMapping::new();
            vm.get_or_insert_int("x");
            let compiled = compile_or_skip!(&opcodes, vm, false);
            // SAFETY: `vars` is sized to match `var_mapping.total_vars()` for this
            // compiled expression (both constructed adjacent above), satisfying
            // `evaluate_raw`'s contract. `compiled` owns the backing executable.
            let jit_result = unsafe { compiled.evaluate_raw(&vars) };
            assert_eq!(jit_result, interp_result, "x={x}");
        }
    }
}

// Tests that work on all platforms (interpreted evaluator).
#[cfg(test)]
mod interpret_tests {
    use super::*;

    #[test]
    fn test_interpret_bool_constants() {
        assert_eq!(interpret(&[ExprOpcode::PushBool(true)], &[]), Some(1));
        assert_eq!(interpret(&[ExprOpcode::PushBool(false)], &[]), Some(0));
    }

    #[test]
    fn test_interpret_int_constants() {
        assert_eq!(interpret(&[ExprOpcode::PushInt(42)], &[]), Some(42));
        assert_eq!(interpret(&[ExprOpcode::PushInt(-123)], &[]), Some(-123));
        assert_eq!(interpret(&[ExprOpcode::PushInt(0)], &[]), Some(0));
    }

    #[test]
    fn test_interpret_load_var() {
        assert_eq!(interpret(&[ExprOpcode::LoadIntVar(0)], &[99]), Some(99));
        assert_eq!(interpret(&[ExprOpcode::LoadIntVar(1)], &[10, 20]), Some(20));
        // Out-of-range index defaults to 0.
        assert_eq!(interpret(&[ExprOpcode::LoadIntVar(5)], &[1, 2]), Some(0));
    }

    #[test]
    fn test_interpret_arithmetic() {
        assert_eq!(
            interpret(
                &[
                    ExprOpcode::PushInt(10),
                    ExprOpcode::PushInt(20),
                    ExprOpcode::Add
                ],
                &[]
            ),
            Some(30)
        );
        assert_eq!(
            interpret(
                &[
                    ExprOpcode::PushInt(50),
                    ExprOpcode::PushInt(30),
                    ExprOpcode::Sub
                ],
                &[]
            ),
            Some(20)
        );
        assert_eq!(
            interpret(
                &[
                    ExprOpcode::PushInt(6),
                    ExprOpcode::PushInt(7),
                    ExprOpcode::Mul
                ],
                &[]
            ),
            Some(42)
        );
        assert_eq!(
            interpret(&[ExprOpcode::PushInt(42), ExprOpcode::Neg], &[]),
            Some(-42)
        );
    }

    #[test]
    fn test_interpret_div_euclidean() {
        // 7 / 3 = 2
        assert_eq!(
            interpret(
                &[
                    ExprOpcode::PushInt(7),
                    ExprOpcode::PushInt(3),
                    ExprOpcode::Div
                ],
                &[]
            ),
            Some(2)
        );
        // -7 / 2 = -4 (Euclidean, floors toward negative infinity)
        assert_eq!(
            interpret(
                &[
                    ExprOpcode::PushInt(-7),
                    ExprOpcode::PushInt(2),
                    ExprOpcode::Div
                ],
                &[]
            ),
            Some(-4)
        );
        // div by zero = 0
        assert_eq!(
            interpret(
                &[
                    ExprOpcode::PushInt(42),
                    ExprOpcode::PushInt(0),
                    ExprOpcode::Div
                ],
                &[]
            ),
            Some(0)
        );
    }

    #[test]
    fn test_interpret_mod_euclidean() {
        // 7 mod 3 = 1
        assert_eq!(
            interpret(
                &[
                    ExprOpcode::PushInt(7),
                    ExprOpcode::PushInt(3),
                    ExprOpcode::Mod
                ],
                &[]
            ),
            Some(1)
        );
        // -7 mod 2 = 1 (Euclidean, always non-negative)
        assert_eq!(
            interpret(
                &[
                    ExprOpcode::PushInt(-7),
                    ExprOpcode::PushInt(2),
                    ExprOpcode::Mod
                ],
                &[]
            ),
            Some(1)
        );
        // mod by zero = a
        assert_eq!(
            interpret(
                &[
                    ExprOpcode::PushInt(42),
                    ExprOpcode::PushInt(0),
                    ExprOpcode::Mod
                ],
                &[]
            ),
            Some(42)
        );
    }

    #[test]
    fn test_interpret_div_mod_min_by_neg_one_is_total() {
        // i64::MIN div -1 = 2^63 overflows the i64 carrier. The interpreter
        // must stay total (wrapping negation, matching aarch64 SDIV and the
        // guarded x86-64 IDIV path) instead of panicking on solver input.
        assert_eq!(
            interpret(
                &[
                    ExprOpcode::PushInt(i64::MIN),
                    ExprOpcode::PushInt(-1),
                    ExprOpcode::Div
                ],
                &[]
            ),
            Some(i64::MIN.wrapping_neg())
        );
        // mod(a, -1) = 0 for all a, including i64::MIN.
        assert_eq!(
            interpret(
                &[
                    ExprOpcode::PushInt(i64::MIN),
                    ExprOpcode::PushInt(-1),
                    ExprOpcode::Mod
                ],
                &[]
            ),
            Some(0)
        );
        // Non-overflow b == -1 cases keep exact Euclidean results.
        assert_eq!(
            interpret(
                &[
                    ExprOpcode::PushInt(7),
                    ExprOpcode::PushInt(-1),
                    ExprOpcode::Div
                ],
                &[]
            ),
            Some(-7)
        );
        assert_eq!(
            interpret(
                &[
                    ExprOpcode::PushInt(-7),
                    ExprOpcode::PushInt(-1),
                    ExprOpcode::Mod
                ],
                &[]
            ),
            Some(0)
        );
    }

    #[test]
    fn test_interpret_comparisons() {
        assert_eq!(
            interpret(
                &[
                    ExprOpcode::PushInt(5),
                    ExprOpcode::PushInt(5),
                    ExprOpcode::CmpEq
                ],
                &[]
            ),
            Some(1)
        );
        assert_eq!(
            interpret(
                &[
                    ExprOpcode::PushInt(5),
                    ExprOpcode::PushInt(6),
                    ExprOpcode::CmpEq
                ],
                &[]
            ),
            Some(0)
        );
        assert_eq!(
            interpret(
                &[
                    ExprOpcode::PushInt(5),
                    ExprOpcode::PushInt(10),
                    ExprOpcode::CmpLt
                ],
                &[]
            ),
            Some(1)
        );
        assert_eq!(
            interpret(
                &[
                    ExprOpcode::PushInt(10),
                    ExprOpcode::PushInt(5),
                    ExprOpcode::CmpLt
                ],
                &[]
            ),
            Some(0)
        );
        assert_eq!(
            interpret(
                &[
                    ExprOpcode::PushInt(5),
                    ExprOpcode::PushInt(5),
                    ExprOpcode::CmpLe
                ],
                &[]
            ),
            Some(1)
        );
        assert_eq!(
            interpret(
                &[
                    ExprOpcode::PushInt(5),
                    ExprOpcode::PushInt(10),
                    ExprOpcode::CmpGt
                ],
                &[]
            ),
            Some(0)
        );
        assert_eq!(
            interpret(
                &[
                    ExprOpcode::PushInt(10),
                    ExprOpcode::PushInt(5),
                    ExprOpcode::CmpGe
                ],
                &[]
            ),
            Some(1)
        );
        assert_eq!(
            interpret(
                &[
                    ExprOpcode::PushInt(5),
                    ExprOpcode::PushInt(6),
                    ExprOpcode::CmpNe
                ],
                &[]
            ),
            Some(1)
        );
    }

    #[test]
    fn test_interpret_boolean_logic() {
        // NOT
        assert_eq!(
            interpret(&[ExprOpcode::PushBool(true), ExprOpcode::Not], &[]),
            Some(0)
        );
        assert_eq!(
            interpret(&[ExprOpcode::PushBool(false), ExprOpcode::Not], &[]),
            Some(1)
        );

        // AND
        assert_eq!(
            interpret(
                &[
                    ExprOpcode::PushBool(true),
                    ExprOpcode::PushBool(true),
                    ExprOpcode::And(2)
                ],
                &[]
            ),
            Some(1)
        );
        assert_eq!(
            interpret(
                &[
                    ExprOpcode::PushBool(true),
                    ExprOpcode::PushBool(false),
                    ExprOpcode::And(2)
                ],
                &[]
            ),
            Some(0)
        );

        // OR
        assert_eq!(
            interpret(
                &[
                    ExprOpcode::PushBool(false),
                    ExprOpcode::PushBool(false),
                    ExprOpcode::Or(2)
                ],
                &[]
            ),
            Some(0)
        );
        assert_eq!(
            interpret(
                &[
                    ExprOpcode::PushBool(false),
                    ExprOpcode::PushBool(true),
                    ExprOpcode::Or(2)
                ],
                &[]
            ),
            Some(1)
        );

        // IMPLIES
        assert_eq!(
            interpret(
                &[
                    ExprOpcode::PushBool(true),
                    ExprOpcode::PushBool(false),
                    ExprOpcode::Implies
                ],
                &[]
            ),
            Some(0)
        );
        assert_eq!(
            interpret(
                &[
                    ExprOpcode::PushBool(false),
                    ExprOpcode::PushBool(false),
                    ExprOpcode::Implies
                ],
                &[]
            ),
            Some(1)
        );
    }

    #[test]
    fn test_interpret_ite() {
        assert_eq!(
            interpret(
                &[
                    ExprOpcode::PushBool(true),
                    ExprOpcode::PushInt(42),
                    ExprOpcode::PushInt(99),
                    ExprOpcode::Ite
                ],
                &[],
            ),
            Some(42)
        );
        assert_eq!(
            interpret(
                &[
                    ExprOpcode::PushBool(false),
                    ExprOpcode::PushInt(42),
                    ExprOpcode::PushInt(99),
                    ExprOpcode::Ite
                ],
                &[],
            ),
            Some(99)
        );
    }

    #[test]
    fn test_interpret_empty_opcodes() {
        assert_eq!(interpret(&[], &[]), None);
    }

    #[test]
    fn test_interpret_stack_underflow() {
        // Add with only one value on stack
        assert_eq!(
            interpret(&[ExprOpcode::PushInt(1), ExprOpcode::Add], &[]),
            None
        );
    }

    #[test]
    fn test_interpret_complex_expression() {
        // (x + y) <= 10 AND (x > 0) where x=3, y=5
        let opcodes = vec![
            ExprOpcode::LoadIntVar(0), // x
            ExprOpcode::LoadIntVar(1), // y
            ExprOpcode::Add,
            ExprOpcode::PushInt(10),
            ExprOpcode::CmpLe,
            ExprOpcode::LoadIntVar(0), // x
            ExprOpcode::PushInt(0),
            ExprOpcode::CmpGt,
            ExprOpcode::And(2),
        ];
        // 3 + 5 = 8 <= 10 = true, 3 > 0 = true, AND = true
        assert_eq!(interpret(&opcodes, &[3, 5]), Some(1));
        // 6 + 7 = 13 <= 10 = false, AND short-circuits to false
        assert_eq!(interpret(&opcodes, &[6, 7]), Some(0));
        // -1 + 5 = 4 <= 10 = true, -1 > 0 = false, AND = false
        assert_eq!(interpret(&opcodes, &[-1, 5]), Some(0));
    }

    #[test]
    fn test_interpreted_expr_eval() {
        let opcodes = vec![
            ExprOpcode::LoadIntVar(0),
            ExprOpcode::PushInt(10),
            ExprOpcode::CmpLe,
        ];
        let mut vm = VarMapping::new();
        vm.get_or_insert_int("x");
        let eval = InterpretedExprEval::new(opcodes, vm, true);

        assert_eq!(eval.evaluate_bool_checked(&[5]), Some(true));
        assert_eq!(eval.evaluate_bool_checked(&[15]), Some(false));
        assert_eq!(eval.evaluate_bool_checked(&[10]), Some(true));
        // Too-short vars
        assert_eq!(eval.evaluate_bool_checked(&[]), None);
    }

    #[test]
    fn test_and_3ary() {
        // 3-way AND: true AND true AND false = false
        let opcodes = vec![
            ExprOpcode::PushBool(true),
            ExprOpcode::PushBool(true),
            ExprOpcode::PushBool(false),
            ExprOpcode::And(3),
        ];
        assert_eq!(interpret(&opcodes, &[]), Some(0));

        // 3-way AND: true AND true AND true = true
        let opcodes2 = vec![
            ExprOpcode::PushBool(true),
            ExprOpcode::PushBool(true),
            ExprOpcode::PushBool(true),
            ExprOpcode::And(3),
        ];
        assert_eq!(interpret(&opcodes2, &[]), Some(1));
    }

    #[test]
    fn test_or_3ary() {
        // 3-way OR: false OR false OR true = true
        let opcodes = vec![
            ExprOpcode::PushBool(false),
            ExprOpcode::PushBool(false),
            ExprOpcode::PushBool(true),
            ExprOpcode::Or(3),
        ];
        assert_eq!(interpret(&opcodes, &[]), Some(1));

        // 3-way OR: false OR false OR false = false
        let opcodes2 = vec![
            ExprOpcode::PushBool(false),
            ExprOpcode::PushBool(false),
            ExprOpcode::PushBool(false),
            ExprOpcode::Or(3),
        ];
        assert_eq!(interpret(&opcodes2, &[]), Some(0));
    }

    #[test]
    fn test_empty_and_or() {
        // Empty AND = true (vacuous truth)
        assert_eq!(interpret(&[ExprOpcode::And(0)], &[]), Some(1));
        // Empty OR = false
        assert_eq!(interpret(&[ExprOpcode::Or(0)], &[]), Some(0));
    }

    // -- #18 register-pressure regression tests ----------------------------
    //
    // The aarch64 generator used a monotonic register counter with a broken
    // "spill" fallback: once the TOTAL number of pushed values exceeded the
    // scratch file it emitted an unmatched `stp` whose orphaned slot was later
    // popped as the frame record by the epilogue, so `ret` branched into a
    // data value (deterministic pc==lr==fp==<operand value> SIGBUS/SIGSEGV on
    // reve/010-horn and rust-horn/bmc-2 with native CHC helpers enabled).
    // Registers are now assigned by operand-stack position (reused after
    // pops) and over-deep sequences fail closed before codegen.

    /// Builds `x0 + x1 + ... + x{n-1}` as a left-deep chain: peak depth 2,
    /// but n total value allocations. Pre-fix this crashed the process on
    /// aarch64 once n exceeded the 17-register scratch file.
    #[cfg(any(target_arch = "aarch64", target_arch = "x86_64"))]
    fn long_add_chain(n: u32) -> (Vec<ExprOpcode>, VarMapping) {
        let mut opcodes = vec![ExprOpcode::LoadIntVar(0)];
        let mut var_mapping = VarMapping::new();
        var_mapping.get_or_insert_int("x0");
        for i in 1..n {
            var_mapping.get_or_insert_int(&format!("x{i}"));
            opcodes.push(ExprOpcode::LoadIntVar(i));
            opcodes.push(ExprOpcode::Add);
        }
        (opcodes, var_mapping)
    }

    #[test]
    #[cfg(any(target_arch = "aarch64", target_arch = "x86_64"))]
    fn test_register_pressure_long_add_chain_compiles_and_is_correct() {
        let n = (NATIVE_EVAL_MAX_OPERAND_DEPTH as u32) + 7;
        let (opcodes, var_mapping) = long_add_chain(n);
        assert_eq!(peak_operand_stack_depth(&opcodes), Some(2));
        let compiled = compile_or_skip!(&opcodes, var_mapping, false);
        let vars: Vec<i64> = (1..=i64::from(n)).collect();
        let expected: i64 = vars.iter().sum();
        assert_eq!(compiled.evaluate_checked(&vars), Some(expected));
    }

    #[test]
    #[cfg(any(target_arch = "aarch64", target_arch = "x86_64"))]
    fn test_wide_conjunction_at_depth_capacity_compiles() {
        let n = NATIVE_EVAL_MAX_OPERAND_DEPTH;
        let mut opcodes: Vec<ExprOpcode> = Vec::new();
        let mut var_mapping = VarMapping::new();
        for i in 0..n {
            var_mapping.get_or_insert_bool(&format!("b{i}"));
            opcodes.push(ExprOpcode::LoadBoolVar(i as u32));
        }
        opcodes.push(ExprOpcode::And(n as u16));
        assert_eq!(peak_operand_stack_depth(&opcodes), Some(n));
        let compiled = compile_or_skip!(&opcodes, var_mapping, true);

        let all_true = vec![1i64; n];
        assert_eq!(compiled.evaluate_bool_checked(&all_true), Some(true));
        let mut one_false = vec![1i64; n];
        one_false[n - 1] = 0;
        assert_eq!(compiled.evaluate_bool_checked(&one_false), Some(false));
    }

    #[test]
    #[cfg(any(target_arch = "aarch64", target_arch = "x86_64"))]
    fn test_beyond_depth_capacity_fails_closed() {
        let n = NATIVE_EVAL_MAX_OPERAND_DEPTH + 1;
        let mut opcodes: Vec<ExprOpcode> = Vec::new();
        let mut var_mapping = VarMapping::new();
        for i in 0..n {
            var_mapping.get_or_insert_bool(&format!("b{i}"));
            opcodes.push(ExprOpcode::LoadBoolVar(i as u32));
        }
        opcodes.push(ExprOpcode::And(n as u16));
        assert_eq!(peak_operand_stack_depth(&opcodes), Some(n));
        assert!(
            compile(&opcodes, var_mapping, true).is_err(),
            "over-deep sequences must fail closed instead of emitting spill code"
        );
    }

    #[test]
    fn test_malformed_opcode_sequence_fails_closed() {
        // Stack underflow: binary op with a single operand.
        let opcodes = vec![ExprOpcode::PushInt(1), ExprOpcode::Add];
        assert_eq!(peak_operand_stack_depth(&opcodes), None);
        assert!(compile(&opcodes, VarMapping::new(), false).is_err());
    }

    #[test]
    fn test_peak_operand_stack_depth_counts_empty_connectives() {
        // Empty AND/OR push a constant result and must count as +1.
        assert_eq!(peak_operand_stack_depth(&[ExprOpcode::And(0)]), Some(1));
        assert_eq!(peak_operand_stack_depth(&[ExprOpcode::Or(0)]), Some(1));
        // Ite consumes three operands.
        let ite = vec![
            ExprOpcode::PushBool(true),
            ExprOpcode::PushInt(1),
            ExprOpcode::PushInt(2),
            ExprOpcode::Ite,
        ];
        assert_eq!(peak_operand_stack_depth(&ite), Some(3));
        assert_eq!(
            peak_operand_stack_depth(&[ExprOpcode::PushInt(1), ExprOpcode::Ite]),
            None
        );
    }

    /// Regression: a wide-but-shallow expression must NOT be miscompiled or
    /// crash. Post-fix it compiles correctly via position-based register reuse
    /// rather than tripping a register-exhaustion bail-out.
    ///
    /// A left-associated `1 + 1 + ... + 1` chain has a max evaluation-stack
    /// *depth* of only 2, so the old depth-based guard (`estimate_max_stack_depth`)
    /// never flagged it. But the old register allocator never reused scratch
    /// registers (`next_scratch` was monotonic), so it needed one scratch
    /// register per leaf. With more leaves than scratch registers the old code
    /// reached the overflow branch, which on aarch64 emitted an unbalanced
    /// `push_pair` (SP -= 16, no matching pop) that corrupted the return address
    /// — the function returned to a wild address and crashed the running thread
    /// (pc==lr==fp==tiny value) — and on x86_64 silently aliased SCRATCH[0] and
    /// returned a wrong value. The allocator now assigns registers by
    /// operand-stack position (reusing them after pops), so this shallow chain
    /// fits in the scratch file regardless of width and compiles correctly.
    #[test]
    #[cfg(any(target_arch = "aarch64", target_arch = "x86_64"))]
    fn wide_low_depth_expr_compiles_and_is_correct() {
        // 25 leaves > aarch64 SCRATCH (17) and > x86_64 SCRATCH (10), but the
        // peak operand-stack depth is only 2 thanks to register reuse.
        let leaves = 25usize;
        let mut opcodes = vec![ExprOpcode::PushInt(1)];
        for _ in 1..leaves {
            opcodes.push(ExprOpcode::PushInt(1));
            opcodes.push(ExprOpcode::Add);
        }

        // Shallow (peak operand-stack depth 2): must not be rejected on width.
        assert_eq!(peak_operand_stack_depth(&opcodes), Some(2));

        // Must compile (no spill, no crash, no miscompile) and return the right
        // value; the interpreter agrees as the sound reference (sum of 25 ones).
        let compiled = compile_or_skip!(&opcodes, VarMapping::new(), false);
        assert_eq!(compiled.evaluate_checked(&[]), Some(leaves as i64));
        assert_eq!(interpret(&opcodes, &[]), Some(leaves as i64));
    }
}
