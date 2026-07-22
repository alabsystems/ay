// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Differential fuzz of `simplify_constants` BV constant folding against the
//! ay-dpll executor (model-checker-consumer parity wishlist 2026-07-17 item 2, P0).
//!
//! PDR const-props transition/inductiveness queries through
//! `simplify_constants` and TRUSTS syntactic `Bool(false)`/constant results
//! without SMT (see `pdr/verification/model_inductive.rs`
//! `is_trivial_contradiction`, `propagate_equalities` fast-paths). A wrong BV
//! constant fold therefore converts directly into unchecked inductiveness /
//! validity — a false-Safe route. These tests pin the fold semantics to the
//! independent ay-dpll bit-blasting pipeline:
//!
//! 1. Random well-typed ground BV terms must fold to a constant that ay-dpll
//!    proves equal to the original term (`(not (= T C))` is unsat).
//! 2. Width-mismatched (ill-typed) BV atoms — which sort-changing
//!    substitutions DO produce (see `smt/convert.rs` #6047 notes) — must NOT
//!    fold at all (fail-closed, matching the BvUDiv/BvURem width guard).

#![allow(clippy::unwrap_used, clippy::panic)]
use super::*;
use crate::pdr::model::InvariantModel;
use crate::smt::executor_adapter::check_unsat_smtlib_via_executor;
use crate::ChcOp;

/// Deterministic splitmix64 RNG — no external dependency, reproducible runs.
struct Rng(u64);

impl Rng {
    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }

    fn next_u128(&mut self) -> u128 {
        (u128::from(self.next_u64()) << 64) | u128::from(self.next_u64())
    }

    /// Uniform-ish in `0..n` (n > 0).
    fn below(&mut self, n: u64) -> u64 {
        self.next_u64() % n
    }
}

fn bv_mask(width: u32) -> u128 {
    if width >= 128 {
        u128::MAX
    } else {
        (1u128 << width) - 1
    }
}

fn rand_width(rng: &mut Rng) -> u32 {
    const WIDTHS: [u32; 14] = [1, 2, 3, 7, 8, 13, 16, 31, 32, 63, 64, 65, 127, 128];
    WIDTHS[rng.below(WIDTHS.len() as u64) as usize]
}

fn bv_leaf(rng: &mut Rng, width: u32) -> ChcExpr {
    ChcExpr::BitVec(rng.next_u128() & bv_mask(width), width)
}

/// Random well-typed ground BV term of exactly `width` bits.
fn rand_bv_term(rng: &mut Rng, width: u32, depth: u32) -> ChcExpr {
    if depth == 0 {
        return bv_leaf(rng, width);
    }
    match rng.below(7) {
        // Same-width binary ops.
        0 | 1 => {
            const OPS: [ChcOp; 8] = [
                ChcOp::BvAdd,
                ChcOp::BvSub,
                ChcOp::BvMul,
                ChcOp::BvAnd,
                ChcOp::BvOr,
                ChcOp::BvXor,
                ChcOp::BvUDiv,
                ChcOp::BvURem,
            ];
            let op = OPS[rng.below(OPS.len() as u64) as usize];
            let a = rand_bv_term(rng, width, depth - 1);
            let b = rand_bv_term(rng, width, depth - 1);
            ChcExpr::Op(op, vec![Arc::new(a), Arc::new(b)])
        }
        // Unary ops.
        2 => {
            let op = if rng.below(2) == 0 {
                ChcOp::BvNot
            } else {
                ChcOp::BvNeg
            };
            let a = rand_bv_term(rng, width, depth - 1);
            ChcExpr::Op(op, vec![Arc::new(a)])
        }
        // zero_extend / sign_extend from a narrower source.
        3 if width >= 2 => {
            let n = 1 + rng.below(u64::from(width - 1)) as u32;
            let sub = rand_bv_term(rng, width - n, depth - 1);
            let op = if rng.below(2) == 0 {
                ChcOp::BvZeroExtend(n)
            } else {
                ChcOp::BvSignExtend(n)
            };
            ChcExpr::Op(op, vec![Arc::new(sub)])
        }
        // concat of two parts summing to `width`.
        4 if width >= 2 => {
            let wa = 1 + rng.below(u64::from(width - 1)) as u32;
            let a = rand_bv_term(rng, wa, depth - 1);
            let b = rand_bv_term(rng, width - wa, depth - 1);
            ChcExpr::Op(ChcOp::BvConcat, vec![Arc::new(a), Arc::new(b)])
        }
        // extract of `width` bits out of a wider source.
        5 => {
            let extra = rng.below(9) as u32;
            let src_width = (width + extra).min(128);
            let max_lo = src_width - width;
            let lo = if max_lo == 0 {
                0
            } else {
                rng.below(u64::from(max_lo) + 1) as u32
            };
            let hi = lo + width - 1;
            let src = rand_bv_term(rng, src_width, depth - 1);
            ChcExpr::Op(ChcOp::BvExtract(hi, lo), vec![Arc::new(src)])
        }
        _ => bv_leaf(rng, width),
    }
}

fn smtlib(expr: &ChcExpr) -> String {
    InvariantModel::expr_to_smtlib(expr)
}

/// (1) Differential fuzz: every well-typed ground BV term must fold to a
/// constant, and ay-dpll (independent bit-blasting pipeline) must prove the
/// fold exact.
#[test]
fn bv_const_fold_differential_fuzz_vs_executor() {
    let mut rng = Rng(0x00AB_517E_2026_0717);
    let mut folded_terms = 0usize;

    for case in 0..140u32 {
        let width = rand_width(&mut rng);
        let depth = 1 + (rng.below(3) as u32);
        let term = rand_bv_term(&mut rng, width, depth);
        let simplified = term.simplify_constants();

        let ChcExpr::BitVec(value, w) = simplified else {
            panic!(
                "case {case}: well-typed ground BV term failed to fold to a constant:\n\
                 term = {term:?}\nsimplified = {simplified:?}"
            );
        };
        assert_eq!(
            w, width,
            "case {case}: fold changed the width: term = {term:?}"
        );
        assert_eq!(
            value,
            value & bv_mask(width),
            "case {case}: folded value not canonical for width {width}: term = {term:?}"
        );
        folded_terms += 1;

        // Differential cross-check: ay-dpll must prove term == constant.
        let smt = format!(
            "(set-logic QF_BV)\n(assert (not (= {} {})))\n(check-sat)\n",
            smtlib(&term),
            smtlib(&ChcExpr::BitVec(value, w)),
        );
        assert!(
            check_unsat_smtlib_via_executor(&smt),
            "case {case}: ay-dpll DISAGREES with simplify_constants BV fold:\n\
             term = {term:?}\nfolded to (_ bv{value} {w})\nquery:\n{smt}"
        );
    }
    assert_eq!(folded_terms, 140, "fuzz should have exercised every case");
}

/// (1b) Differential fuzz for BV comparison folds (feeding Bool fast-paths).
#[test]
fn bv_cmp_const_fold_differential_fuzz_vs_executor() {
    const CMPS: [ChcOp; 8] = [
        ChcOp::BvULt,
        ChcOp::BvULe,
        ChcOp::BvUGt,
        ChcOp::BvUGe,
        ChcOp::BvSLt,
        ChcOp::BvSLe,
        ChcOp::BvSGt,
        ChcOp::BvSGe,
    ];
    let mut rng = Rng(0x00AB_517E_0000_CAFE);

    for case in 0..60u32 {
        let width = rand_width(&mut rng);
        let op = CMPS[rng.below(CMPS.len() as u64) as usize];
        let depth_a = 1 + (rng.below(2) as u32);
        let a = rand_bv_term(&mut rng, width, depth_a);
        let depth_b = 1 + (rng.below(2) as u32);
        let b = rand_bv_term(&mut rng, width, depth_b);
        let cmp = ChcExpr::Op(op, vec![Arc::new(a), Arc::new(b)]);
        let simplified = cmp.simplify_constants();

        let ChcExpr::Bool(result) = simplified else {
            panic!(
                "case {case}: ground BV comparison failed to fold:\n\
                 cmp = {cmp:?}\nsimplified = {simplified:?}"
            );
        };

        // If folded true, the negation must be unsat; if false, the
        // comparison itself must be unsat.
        let assertion = if result {
            format!("(not {})", smtlib(&cmp))
        } else {
            smtlib(&cmp)
        };
        let smt = format!("(set-logic QF_BV)\n(assert {assertion})\n(check-sat)\n");
        assert!(
            check_unsat_smtlib_via_executor(&smt),
            "case {case}: ay-dpll DISAGREES with BV comparison fold:\n\
             cmp = {cmp:?}\nfolded to {result}\nquery:\n{smt}"
        );
    }
}

/// (2) Width-mismatched (ill-typed) BV arithmetic/bitwise atoms must NOT
/// constant-fold — masking by the left width folds to a wrong constant that
/// unchecked const-prop fast-paths then trust (the concrete defect this
/// change fixes; BvUDiv/BvURem already had the guard).
#[test]
fn bv_const_fold_width_mismatch_stays_symbolic() {
    const OPS: [ChcOp; 6] = [
        ChcOp::BvAdd,
        ChcOp::BvSub,
        ChcOp::BvMul,
        ChcOp::BvAnd,
        ChcOp::BvOr,
        ChcOp::BvXor,
    ];
    for op in OPS {
        let mismatched = ChcExpr::Op(
            op,
            vec![
                Arc::new(ChcExpr::BitVec(0x0Fu128, 8)),
                Arc::new(ChcExpr::BitVec(0x1234u128, 16)),
            ],
        );
        let simplified = mismatched.simplify_constants();
        assert!(
            matches!(simplified, ChcExpr::Op(o, _) if o == op),
            "{op:?}: width-mismatched fold must stay symbolic, got {simplified:?}"
        );
    }
}

/// (2b) Width-mismatched BV comparisons must NOT fold to a Bool constant.
/// A wrong Bool(false) here reaches `propagate_equalities` /
/// `is_trivial_contradiction` fast-paths that skip SMT entirely.
#[test]
fn bv_cmp_const_fold_width_mismatch_stays_symbolic() {
    const CMPS: [ChcOp; 8] = [
        ChcOp::BvULt,
        ChcOp::BvULe,
        ChcOp::BvUGt,
        ChcOp::BvUGe,
        ChcOp::BvSLt,
        ChcOp::BvSLe,
        ChcOp::BvSGt,
        ChcOp::BvSGe,
    ];
    for op in CMPS {
        let mismatched = ChcExpr::Op(
            op,
            vec![
                Arc::new(ChcExpr::BitVec(0x80u128, 8)),
                Arc::new(ChcExpr::BitVec(0x8000u128, 16)),
            ],
        );
        let simplified = mismatched.simplify_constants();
        assert!(
            matches!(simplified, ChcExpr::Op(o, _) if o == op),
            "{op:?}: width-mismatched comparison must stay symbolic, got {simplified:?}"
        );
    }
}

/// Same-width folding still works after the guard (no over-degradation):
/// spot-check wrap semantics on the exact byte-offset-overflow shape from
/// the model-checker-consumer wishlist (bvadd wrap at width 8).
#[test]
fn bv_const_fold_same_width_still_folds() {
    // 250 + 10 wraps to 4 at width 8.
    let add = ChcExpr::Op(
        ChcOp::BvAdd,
        vec![
            Arc::new(ChcExpr::BitVec(250, 8)),
            Arc::new(ChcExpr::BitVec(10, 8)),
        ],
    );
    assert_eq!(add.simplify_constants(), ChcExpr::BitVec(4, 8));

    // Unsigned comparison across the wrap boundary.
    let lt = ChcExpr::Op(
        ChcOp::BvULt,
        vec![
            Arc::new(ChcExpr::BitVec(4, 8)),
            Arc::new(ChcExpr::BitVec(250, 8)),
        ],
    );
    assert_eq!(lt.simplify_constants(), ChcExpr::Bool(true));

    // Signed: 0x80 (=-128) < 0x7F (=127) at width 8.
    let slt = ChcExpr::Op(
        ChcOp::BvSLt,
        vec![
            Arc::new(ChcExpr::BitVec(0x80, 8)),
            Arc::new(ChcExpr::BitVec(0x7F, 8)),
        ],
    );
    assert_eq!(slt.simplify_constants(), ChcExpr::Bool(true));
}

/// A width-mismatched atom inside a larger Bool context must not collapse the
/// context to a constant (the const-prop short-circuit route into
/// inductiveness fast-paths).
#[test]
fn bv_width_mismatch_inside_eq_stays_symbolic() {
    let mismatched_add = ChcExpr::Op(
        ChcOp::BvAdd,
        vec![
            Arc::new(ChcExpr::BitVec(1, 8)),
            Arc::new(ChcExpr::BitVec(1, 32)),
        ],
    );
    let eq = ChcExpr::eq(mismatched_add, ChcExpr::BitVec(2, 8));
    let simplified = eq.simplify_constants();
    assert!(
        !matches!(simplified, ChcExpr::Bool(_)),
        "ill-typed BV equality must not fold to a Bool constant, got {simplified:?}"
    );
}

/// Constants wider than the `u128` backing store have implicit zero bits above
/// bit 127. Extracting that region must fold to zero without a host-language
/// oversized-shift panic.
#[test]
fn bv_extract_above_u128_backing_store_folds_to_zero() {
    let extract = ChcExpr::Op(
        ChcOp::BvExtract(255, 128),
        vec![Arc::new(ChcExpr::BitVec(u128::MAX, 256))],
    );

    assert_eq!(extract.simplify_constants(), ChcExpr::BitVec(0, 128));
}

/// A wide constant's unrepresented sign bit is zero. Sign extension must keep
/// the represented low bits unchanged and must not shift a `u128` by 128 or
/// more while reading that sign bit.
#[test]
fn bv_sign_extend_above_u128_backing_store_uses_zero_sign_bit() {
    let sign_extend = ChcExpr::Op(
        ChcOp::BvSignExtend(7),
        vec![Arc::new(ChcExpr::BitVec(u128::MAX, 129))],
    );

    assert_eq!(
        sign_extend.simplify_constants(),
        ChcExpr::BitVec(u128::MAX, 136)
    );
}
