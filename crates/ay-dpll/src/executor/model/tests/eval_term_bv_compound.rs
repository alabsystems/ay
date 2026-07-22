// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression tests for BV compound bitwise ops (bvnand, bvnor, bvxnor),
//! bvcomp, and shift overflow edge cases.
//!
//! These tests verify that evaluate_term (model/mod.rs) handles these ops,
//! not just the BV model recovery path (bv_model.rs). Filed as part of
//! prover audit of #5115 (W20 commit 04b1f036c).

use super::*;

// ==========================================================================
// BV compound bitwise ops: bvnand, bvnor, bvxnor
// ==========================================================================

#[test]
fn test_evaluate_bv_nand_5115() {
    let mut executor = Executor::new();
    let x = executor.ctx.terms.mk_var("x", Sort::bitvec(8));
    let y = executor.ctx.terms.mk_var("y", Sort::bitvec(8));
    let nand = executor
        .ctx
        .terms
        .mk_app(Symbol::named("bvnand"), vec![x, y], Sort::bitvec(8));

    // x = 0b1010_1100 (172), y = 0b1100_1010 (202)
    let mut bv_values = HashMap::default();
    bv_values.insert(x, BigInt::from(0b1010_1100u8));
    bv_values.insert(y, BigInt::from(0b1100_1010u8));
    let mut model = empty_model();
    model.bv_model = Some(BvModel {
        values: bv_values,
        term_to_bits: HashMap::default(),
        bool_overrides: HashMap::default(),
    });

    // nand: ~(0b1010_1100 & 0b1100_1010) = ~0b1000_1000 = 0b0111_0111 = 119
    assert_eq!(
        executor.evaluate_term(&model, nand),
        EvalValue::BitVec {
            value: BigInt::from(0b0111_0111u8),
            width: 8,
        }
    );
}

#[test]
fn test_evaluate_bv_nor_5115() {
    let mut executor = Executor::new();
    let x = executor.ctx.terms.mk_var("x", Sort::bitvec(8));
    let y = executor.ctx.terms.mk_var("y", Sort::bitvec(8));
    let nor = executor
        .ctx
        .terms
        .mk_app(Symbol::named("bvnor"), vec![x, y], Sort::bitvec(8));

    let mut bv_values = HashMap::default();
    bv_values.insert(x, BigInt::from(0b1010_1100u8));
    bv_values.insert(y, BigInt::from(0b1100_1010u8));
    let mut model = empty_model();
    model.bv_model = Some(BvModel {
        values: bv_values,
        term_to_bits: HashMap::default(),
        bool_overrides: HashMap::default(),
    });

    // nor: ~(0b1010_1100 | 0b1100_1010) = ~0b1110_1110 = 0b0001_0001 = 17
    assert_eq!(
        executor.evaluate_term(&model, nor),
        EvalValue::BitVec {
            value: BigInt::from(0b0001_0001u8),
            width: 8,
        }
    );
}

#[test]
fn test_evaluate_bv_xnor_5115() {
    let mut executor = Executor::new();
    let x = executor.ctx.terms.mk_var("x", Sort::bitvec(8));
    let y = executor.ctx.terms.mk_var("y", Sort::bitvec(8));
    let xnor = executor
        .ctx
        .terms
        .mk_app(Symbol::named("bvxnor"), vec![x, y], Sort::bitvec(8));

    let mut bv_values = HashMap::default();
    bv_values.insert(x, BigInt::from(0b1010_1100u8));
    bv_values.insert(y, BigInt::from(0b1100_1010u8));
    let mut model = empty_model();
    model.bv_model = Some(BvModel {
        values: bv_values,
        term_to_bits: HashMap::default(),
        bool_overrides: HashMap::default(),
    });

    // xnor: ~(0b1010_1100 ^ 0b1100_1010) = ~0b0110_0110 = 0b1001_1001 = 153
    assert_eq!(
        executor.evaluate_term(&model, xnor),
        EvalValue::BitVec {
            value: BigInt::from(0b1001_1001u8),
            width: 8,
        }
    );
}

// ==========================================================================
// BV bvcomp
// ==========================================================================

#[test]
fn test_evaluate_bv_comp_equal_5115() {
    let mut executor = Executor::new();
    let x = executor.ctx.terms.mk_var("x", Sort::bitvec(8));
    let y = executor.ctx.terms.mk_var("y", Sort::bitvec(8));
    let comp = executor
        .ctx
        .terms
        .mk_app(Symbol::named("bvcomp"), vec![x, y], Sort::bitvec(1));

    let mut bv_values = HashMap::default();
    bv_values.insert(x, BigInt::from(42u8));
    bv_values.insert(y, BigInt::from(42u8));
    let mut model = empty_model();
    model.bv_model = Some(BvModel {
        values: bv_values,
        term_to_bits: HashMap::default(),
        bool_overrides: HashMap::default(),
    });

    // bvcomp(42, 42) = #b1
    assert_eq!(
        executor.evaluate_term(&model, comp),
        EvalValue::BitVec {
            value: BigInt::from(1u8),
            width: 1,
        }
    );
}

#[test]
fn test_evaluate_bv_comp_not_equal_5115() {
    let mut executor = Executor::new();
    let x = executor.ctx.terms.mk_var("x", Sort::bitvec(8));
    let z = executor.ctx.terms.mk_var("z", Sort::bitvec(8));
    let comp = executor
        .ctx
        .terms
        .mk_app(Symbol::named("bvcomp"), vec![x, z], Sort::bitvec(1));

    let mut bv_values = HashMap::default();
    bv_values.insert(x, BigInt::from(42u8));
    bv_values.insert(z, BigInt::from(43u8));
    let mut model = empty_model();
    model.bv_model = Some(BvModel {
        values: bv_values,
        term_to_bits: HashMap::default(),
        bool_overrides: HashMap::default(),
    });

    // bvcomp(42, 43) = #b0
    assert_eq!(
        executor.evaluate_term(&model, comp),
        EvalValue::BitVec {
            value: BigInt::from(0u8),
            width: 1,
        }
    );
}

// ==========================================================================
// BV shift overflow (shift amount >= bitwidth)
// ==========================================================================

#[test]
fn test_evaluate_bv_shift_overflow_shl_5115() {
    let mut executor = Executor::new();
    let x = executor.ctx.terms.mk_var("x", Sort::bitvec(8));
    let y = executor.ctx.terms.mk_var("y", Sort::bitvec(8));
    let shl = executor
        .ctx
        .terms
        .mk_app(Symbol::named("bvshl"), vec![x, y], Sort::bitvec(8));

    // x = 0b1100_0011, shift by 8 (== bitwidth)
    let mut bv_values = HashMap::default();
    bv_values.insert(x, BigInt::from(0b1100_0011u8));
    bv_values.insert(y, BigInt::from(8u8));
    let mut model = empty_model();
    model.bv_model = Some(BvModel {
        values: bv_values,
        term_to_bits: HashMap::default(),
        bool_overrides: HashMap::default(),
    });

    // shl by >= width: 0
    assert_eq!(
        executor.evaluate_term(&model, shl),
        EvalValue::BitVec {
            value: BigInt::from(0u8),
            width: 8,
        }
    );
}

#[test]
fn test_evaluate_bv_shift_overflow_lshr_5115() {
    let mut executor = Executor::new();
    let x = executor.ctx.terms.mk_var("x", Sort::bitvec(8));
    let y = executor.ctx.terms.mk_var("y", Sort::bitvec(8));
    let lshr = executor
        .ctx
        .terms
        .mk_app(Symbol::named("bvlshr"), vec![x, y], Sort::bitvec(8));

    let mut bv_values = HashMap::default();
    bv_values.insert(x, BigInt::from(0b1100_0011u8));
    bv_values.insert(y, BigInt::from(8u8));
    let mut model = empty_model();
    model.bv_model = Some(BvModel {
        values: bv_values,
        term_to_bits: HashMap::default(),
        bool_overrides: HashMap::default(),
    });

    // lshr by >= width: 0
    assert_eq!(
        executor.evaluate_term(&model, lshr),
        EvalValue::BitVec {
            value: BigInt::from(0u8),
            width: 8,
        }
    );
}

#[test]
fn test_evaluate_bv_shift_overflow_ashr_negative_5115() {
    let mut executor = Executor::new();
    let x = executor.ctx.terms.mk_var("x", Sort::bitvec(8));
    let y = executor.ctx.terms.mk_var("y", Sort::bitvec(8));
    let ashr = executor
        .ctx
        .terms
        .mk_app(Symbol::named("bvashr"), vec![x, y], Sort::bitvec(8));

    // x = 0b1100_0011 = 195 unsigned = -61 signed, shift by 8
    let mut bv_values = HashMap::default();
    bv_values.insert(x, BigInt::from(0b1100_0011u8));
    bv_values.insert(y, BigInt::from(8u8));
    let mut model = empty_model();
    model.bv_model = Some(BvModel {
        values: bv_values,
        term_to_bits: HashMap::default(),
        bool_overrides: HashMap::default(),
    });

    // ashr by >= width on negative value: all 1s = 0xFF = 255
    assert_eq!(
        executor.evaluate_term(&model, ashr),
        EvalValue::BitVec {
            value: BigInt::from(0xFFu8),
            width: 8,
        }
    );
}
