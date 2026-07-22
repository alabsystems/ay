// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Architecture-neutral x86_64 encoder regression tests for #8109.
//!
//! The production module is cfg-gated to `target_arch = "x86_64"`, but these
//! byte-level checks include the assembler directly so Apple/aarch64 hosts can
//! guard the risky encodings without executing native x86_64 code.

#[allow(dead_code, unreachable_pub)]
#[path = "../src/x86_64.rs"]
mod x86_64;

use x86_64::{Assembler, Cond, R10, R12, R13, R8, R9, RAX, RBP, RCX, RDI, RSP};

fn assemble(emit: impl FnOnce(&mut Assembler)) -> Vec<u8> {
    let mut asm = Assembler::new();
    emit(&mut asm);
    asm.finalize()
}

#[test]
fn byte_register_stores_emit_rex_for_low_regs_four_through_seven() {
    let direct = assemble(|asm| asm.strb_w_uimm(RDI, RAX, 0x1122_3344));
    assert_eq!(direct, [0x40, 0x88, 0xB8, 0x44, 0x33, 0x22, 0x11]);

    let indexed = assemble(|asm| asm.mov_byte_indexed_r8(RAX, RCX, RDI));
    assert_eq!(indexed, [0x40, 0x88, 0x3C, 0x08]);
}

#[test]
fn base_displacement_addressing_uses_shortest_safe_encoding() {
    let no_disp = assemble(|asm| asm.mov_r32_mem(RAX, RCX, 0));
    assert_eq!(no_disp, [0x8B, 0x01]);

    let sib_no_disp = assemble(|asm| asm.mov_r32_mem(RAX, RSP, 0));
    assert_eq!(sib_no_disp, [0x8B, 0x04, 0x24]);

    let rbp_zero_disp = assemble(|asm| asm.mov_r32_mem(RAX, RBP, 0));
    assert_eq!(rbp_zero_disp, [0x8B, 0x45, 0x00]);

    let r13_zero_disp = assemble(|asm| asm.mov_r64_mem(R8, R13, 0));
    assert_eq!(r13_zero_disp, [0x4D, 0x8B, 0x45, 0x00]);

    let disp8 = assemble(|asm| asm.mov_r32_mem(RAX, RCX, 127));
    assert_eq!(disp8, [0x8B, 0x41, 0x7F]);

    let neg_disp8 = assemble(|asm| asm.mov_r32_mem(RAX, RCX, -1));
    assert_eq!(neg_disp8, [0x8B, 0x41, 0xFF]);

    let disp32 = assemble(|asm| asm.mov_r32_mem(RAX, RCX, 128));
    assert_eq!(disp32, [0x8B, 0x81, 0x80, 0x00, 0x00, 0x00]);
}

#[test]
fn aarch64_style_word_immediates_honor_byte_offsets() {
    let load = assemble(|asm| asm.ldr_w_uimm(RAX, RCX, 4));
    assert_eq!(load, [0x8B, 0x41, 0x04]);

    let store = assemble(|asm| asm.str_w_uimm(RAX, RCX, 4));
    assert_eq!(store, [0x89, 0x41, 0x04]);
}

#[test]
fn sib_indexed_addressing_carries_rex_r_x_b_bits() {
    let code = assemble(|asm| asm.mov_mem_indexed_r32(R12, R10, R9));
    assert_eq!(code, [0x47, 0x89, 0x0C, 0x94]);
}

#[test]
fn rbp_and_r13_indexed_bases_use_disp8_zero() {
    let rbp = assemble(|asm| asm.movsx_r32_byte_indexed(RAX, RBP, RCX));
    assert_eq!(rbp, [0x0F, 0xBE, 0x44, 0x0D, 0x00]);

    let r13 = assemble(|asm| asm.movzx_r32_byte_indexed(R8, R13, R10));
    assert_eq!(r13, [0x47, 0x0F, 0xB6, 0x44, 0x15, 0x00]);
}

#[test]
fn rel32_fixups_are_relative_to_next_instruction() {
    let forward = assemble(|asm| {
        let target = asm.label();
        asm.jmp(target);
        asm.mov_r32_imm(RAX, 0x1122_3344);
        asm.bind(target);
        asm.emit_ret();
    });
    assert_eq!(
        forward,
        [0xE9, 0x05, 0x00, 0x00, 0x00, 0xB8, 0x44, 0x33, 0x22, 0x11, 0xC3]
    );

    let backward = assemble(|asm| {
        let loop_start = asm.label();
        asm.bind(loop_start);
        asm.mov_r32_imm(RAX, 1);
        asm.jcc(Cond::Ne, loop_start);
    });
    assert_eq!(
        backward,
        [0xB8, 0x01, 0x00, 0x00, 0x00, 0x0F, 0x85, 0xF5, 0xFF, 0xFF, 0xFF]
    );
}

#[test]
fn cmov_condition_codes_match_signed_condition_mapping() {
    for (cond, opcode) in [
        (Cond::Eq, 0x44),
        (Cond::Ne, 0x45),
        (Cond::Lt, 0x4C),
        (Cond::Ge, 0x4D),
        (Cond::Le, 0x4E),
        (Cond::Gt, 0x4F),
    ] {
        let code = assemble(|asm| asm.cmov_r32(RAX, RCX, cond));
        assert_eq!(code, [0x0F, opcode, 0xC1]);
    }

    let high_regs = assemble(|asm| asm.cmov_r32(R8, R9, Cond::Le));
    assert_eq!(high_regs, [0x45, 0x0F, 0x4E, 0xC1]);
}

#[test]
fn xor_r32_rex_bits_track_modrm_operands() {
    // xor eax, ecx — no REX needed for low registers.
    let low = assemble(|asm| asm.xor_r32(RAX, RCX));
    assert_eq!(low, [0x31, 0xC8]);

    // Self-zero of an extended register: xor r9d, r9d = 45 31 C9.
    let zero_ext = assemble(|asm| asm.xor_r32(R9, R9));
    assert_eq!(zero_ext, [0x45, 0x31, 0xC9]);

    // Regression (#audit-2026-07-13): REX bits were computed from swapped
    // operands, so xor_r32(R9, RCX) assembled to 44 31 C9 = xor ecx, r9d —
    // writing the result to the WRONG register. Correct encoding:
    // xor r9d, ecx = REX.B(dst=r9) + 31 /r with reg=ecx, rm=r9d.
    let dst_ext = assemble(|asm| asm.xor_r32(R9, RCX));
    assert_eq!(dst_ext, [0x41, 0x31, 0xC9]);

    // Mirror case: xor ecx, r9d = REX.R(src=r9) + 31 /r, reg=r9d, rm=ecx.
    let src_ext = assemble(|asm| asm.xor_r32(RCX, R9));
    assert_eq!(src_ext, [0x44, 0x31, 0xC9]);
}
