// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The native DPLL(T) loop decides a masked `bv2nat` residue.
//!
//! `bv2nat(bvand(2^k - 1, int2bv_w(x)))` is the overflow-check operand of a
//! Rust `x & 0xff` (model-checker-consumer's typed lowering). ay-core's term builder turns
//! it into `(mod x 2^k)` (`TermStore::mk_bv2nat`), but only after check_sat's
//! expression-level mod elimination ran, so the loop used to hand ay-lia an
//! opaque `mod`: LRA skips such atoms as unsupported (#8373), so ay-lia
//! branched on `x` one value at a time and gave up with `Unknown` after a
//! fixed 226 iterations (55-70 ms in release, well inside the slice), and only
//! the executor fallback decided the query. The mod pass now decomposes the
//! residue like any constant-modulus `mod`.

use super::*;
use crate::{ChcExpr, ChcOp, ChcSort, ChcVar};
use std::sync::Arc;
use std::time::Duration;

const U32_MAX: i128 = u32::MAX as i128;

fn op(op: ChcOp, args: Vec<ChcExpr>) -> ChcExpr {
    ChcExpr::Op(op, args.into_iter().map(Arc::new).collect())
}

fn int_var(name: &str) -> ChcExpr {
    ChcExpr::var(ChcVar::new(name, ChcSort::Int))
}

fn mask_term(mask: i128, mask_width: u32, x: ChcExpr, x_width: u32) -> ChcExpr {
    op(
        ChcOp::Bv2Nat,
        vec![op(
            ChcOp::BvAnd,
            vec![
                op(ChcOp::Int2Bv(mask_width), vec![ChcExpr::int(mask)]),
                op(ChcOp::Int2Bv(x_width), vec![x]),
            ],
        )],
    )
}

/// `0 <= x <= 2^32-1 ∧ bv2nat(255 & int2bv32(x)) + k > bound`.
fn masked_add(k: i128, bound: i128) -> ChcExpr {
    let x = int_var("x");
    ChcExpr::and_all(vec![
        ChcExpr::le(ChcExpr::int(0), x.clone()),
        ChcExpr::le(x.clone(), ChcExpr::int(U32_MAX)),
        ChcExpr::gt(
            ChcExpr::add(mask_term(255, 32, x, 32), ChcExpr::int(k)),
            ChcExpr::int(bound),
        ),
    ])
}

fn internal(expr: &ChcExpr) -> SmtResult {
    let mut ctx = SmtContext::new();
    ctx.check_timeout.set(Some(Duration::from_secs(5)));
    ctx.check_sat_internal(expr)
}

#[test]
fn residue_shape_matches_only_what_the_term_builder_rewrites() {
    let x = int_var("x");
    let residue = |mask: i128, mask_width: u32, x_width: u32| {
        let term = mask_term(mask, mask_width, x.clone(), x_width);
        let ChcExpr::Op(ChcOp::Bv2Nat, args) = &term else {
            unreachable!()
        };
        ChcExpr::masked_int2bv_residue(&args[0]).map(|(_, modulus)| modulus)
    };
    assert_eq!(residue(255, 32, 32), Some(256));
    assert_eq!(residue(1, 8, 8), Some(2));
    assert_eq!(residue(0x7fff_ffff, 32, 32), Some(1 << 31));
    // `mk_int2bv` reduces a constant mod 2^w, so these are the mask 255 in
    // the term builder and become `(mod x 256)` there too.
    assert_eq!(residue((1 << 32) + 255, 32, 32), Some(256));
    assert_eq!(residue(-(1 << 32) + 255, 32, 32), Some(256));
    // Not a low mask, the zero mask, the all-ones mask (also as the reduced
    // -1 and 2^32), and a width mismatch: the term builder makes no `mod`
    // of these (`mk_bvand` folds zero and all-ones away).
    assert_eq!(residue(254, 32, 32), None);
    assert_eq!(residue(0, 32, 32), None);
    assert_eq!(residue(U32_MAX, 32, 32), None);
    assert_eq!(residue(-1, 32, 32), None);
    assert_eq!(residue(1 << 32, 32, 32), None);
    assert_eq!(residue(255, 16, 32), None);
    // At width 127 a negative constant reduces to a low mask too
    // (-2^127 + 255 is 255 mod 2^127); at 128 bits it never does.
    assert_eq!(residue(i128::MIN + 255, 127, 127), Some(256));
    assert_eq!(residue(i128::MAX, 127, 127), None);
    assert_eq!(residue(i128::MIN + 255, 128, 128), None);
    assert_eq!(residue(-1, 128, 128), None);
    assert_eq!(residue(255, 128, 128), Some(256));
    // Either operand order.
    let swapped = op(
        ChcOp::BvAnd,
        vec![
            op(ChcOp::Int2Bv(32), vec![x.clone()]),
            op(ChcOp::Int2Bv(32), vec![ChcExpr::int(255)]),
        ],
    );
    assert_eq!(
        ChcExpr::masked_int2bv_residue(&swapped).map(|(_, modulus)| modulus),
        Some(256)
    );
}

/// The recognizer fires on exactly the masks ay-core's term builder turns
/// into `(mod x 2^k)` with `2^k` within i128, with the same modulus: a miss
/// leaves that `mod` opaque to the native loop, and an extra match
/// decomposes a residue ay-core would not have rewritten.
#[test]
fn residue_shape_agrees_with_the_term_builder() {
    use ay_core::{Constant, Sort, Symbol, TermData, TermStore};
    use num_bigint::BigInt;
    for width in [2u32, 8, 32, 64, 126, 127, 128] {
        let mut constants = vec![
            0,
            1,
            2,
            3,
            15,
            0xf0,
            254,
            255,
            -1,
            -2,
            -256,
            i128::MAX,
            i128::MAX - 1,
            i128::MIN,
            i128::MIN + 1,
            i128::MIN + 255,
        ];
        if width < 127 {
            let full = 1i128 << width;
            constants.extend([full - 1, full, full + 255, -full + 255, (full >> 1) - 1]);
            if width < 126 {
                constants.extend([2 * full + 15, -2 * full + 15]);
            }
        }
        for constant in constants {
            for mask_first in [true, false] {
                let mut terms = TermStore::new();
                let x = terms.mk_var("x", Sort::Int);
                let c = terms.mk_int(BigInt::from(constant));
                let mask = terms.mk_int2bv(width, c);
                let value = terms.mk_int2bv(width, x);
                let and_args = if mask_first {
                    vec![mask, value]
                } else {
                    vec![value, mask]
                };
                let and = terms.mk_bvand(and_args);
                let bv2nat = terms.mk_bv2nat(and);
                let builder = match terms.get(bv2nat) {
                    TermData::App(Symbol::Named(name), args)
                        if name == "mod" && args.len() == 2 && args[0] == x =>
                    {
                        match terms.get(args[1]) {
                            TermData::Const(Constant::Int(modulus)) => Some(modulus.clone()),
                            other => panic!("non-constant modulus {other:?}"),
                        }
                    }
                    _ => None,
                };
                // The `Mod` arm decomposes only an i128 modulus (W1-1B), so a
                // builder `mod` by 2^127 (the width-128 mask 2^127 - 1) stays
                // on the slow path on purpose, like any other `mod` that wide.
                let expected = builder.and_then(|modulus| i128::try_from(modulus).ok());

                let mask_expr = op(ChcOp::Int2Bv(width), vec![ChcExpr::int(constant)]);
                let value_expr = op(ChcOp::Int2Bv(width), vec![int_var("x")]);
                let and_expr = op(
                    ChcOp::BvAnd,
                    if mask_first {
                        vec![mask_expr, value_expr]
                    } else {
                        vec![value_expr, mask_expr]
                    },
                );
                let recognized =
                    ChcExpr::masked_int2bv_residue(&and_expr).map(|(_, modulus)| modulus);
                assert_eq!(
                    recognized, expected,
                    "width {width} constant {constant} mask_first {mask_first}"
                );
            }
        }
    }
}

#[test]
fn native_loop_refutes_the_masked_add_overflow_check() {
    let result = internal(&masked_add(7, U32_MAX));
    assert!(
        result.is_unsat(),
        "the native loop must refute (x & 0xff) + 7 > u32::MAX, got {result:?}"
    );
}

#[test]
fn native_loop_keeps_the_satisfiable_masked_add_satisfiable() {
    let expr = masked_add(7, 100);
    let SmtResult::Sat(model) = internal(&expr) else {
        panic!("(x & 0xff) + 7 > 100 is satisfiable");
    };
    // The model must satisfy the ORIGINAL bv2nat form, not only the
    // decomposition (the remainder variable is the loop's own).
    assert_eq!(
        crate::expr::evaluate_expr(&expr, &model),
        Some(SmtValue::Bool(true)),
        "model {model:?}"
    );
}

#[test]
fn residue_of_a_negative_or_overflowing_operand_is_its_euclidean_residue() {
    // int2bv32 wraps: bv2nat(255 & int2bv32(x)) = x mod 256 for every x,
    // so x = -1 gives 255 and x = 2^32 + 3 gives 3. Both directions: any
    // other residue is refuted, and the true one stays satisfiable (a wrong
    // `unsat` here would be the decomposition over-constraining `x`).
    let x = int_var("x");
    for (value, residue) in [(-1i128, 255i128), ((1 << 32) + 3, 3)] {
        let pinned = ChcExpr::eq(x.clone(), ChcExpr::int(value));
        let other = ChcExpr::and_all(vec![
            pinned.clone(),
            ChcExpr::ne(mask_term(255, 32, x.clone(), 32), ChcExpr::int(residue)),
        ]);
        let result = internal(&other);
        assert!(
            result.is_unsat(),
            "x = {value}: residue must be {residue}, got {result:?}"
        );
        let actual = ChcExpr::and_all(vec![
            pinned,
            ChcExpr::eq(mask_term(255, 32, x.clone(), 32), ChcExpr::int(residue)),
        ]);
        let SmtResult::Sat(model) = internal(&actual) else {
            panic!("x = {value} with residue {residue} is satisfiable");
        };
        assert_eq!(
            crate::expr::evaluate_expr(&actual, &model),
            Some(SmtValue::Bool(true)),
            "x = {value}: model {model:?}"
        );
    }
}

#[test]
fn the_residue_is_the_euclidean_mod_under_the_evaluator() {
    // The identity itself, independent of any solver: ay-chc's evaluator
    // gives bv2nat(m & int2bv_w(x)) = x mod 2^k for x of both signs and
    // beyond the width.
    for (width, mask) in [(32, 255), (32, 0xffff), (8, 15), (64, 1), (16, 0x7fff)] {
        let term = mask_term(mask, width, int_var("x"), width);
        let ChcExpr::Op(ChcOp::Bv2Nat, args) = &term else {
            unreachable!()
        };
        let (_, modulus) =
            ChcExpr::masked_int2bv_residue(&args[0]).expect("a low-bit mask below the width");
        assert_eq!(modulus, mask + 1);
        for value in [
            0,
            1,
            7,
            255,
            256,
            1000,
            -1,
            -256,
            -257,
            (1 << 40) + 3,
            -(1 << 40) - 5,
        ] {
            let mut model = FxHashMap::default();
            model.insert("x".to_owned(), SmtValue::Int(value));
            assert_eq!(
                crate::expr::evaluate_expr(&term, &model),
                Some(SmtValue::Int(value.rem_euclid(modulus))),
                "width {width} mask {mask:#x} x {value}"
            );
        }
    }
}

#[test]
fn a_reduced_constant_mask_is_the_same_residue_under_the_evaluator() {
    for mask in [(1i128 << 32) + 255, -(1i128 << 32) + 255] {
        let term = mask_term(mask, 32, int_var("x"), 32);
        let ChcExpr::Op(ChcOp::Bv2Nat, args) = &term else {
            unreachable!()
        };
        let (_, modulus) = ChcExpr::masked_int2bv_residue(&args[0]).expect("reduces to 255");
        assert_eq!(modulus, 256);
        for value in [0, 255, 256, -1, -257, (1 << 40) + 3] {
            let mut model = FxHashMap::default();
            model.insert("x".to_owned(), SmtValue::Int(value));
            assert_eq!(
                crate::expr::evaluate_expr(&term, &model),
                Some(SmtValue::Int(value.rem_euclid(256))),
                "mask {mask} x {value}"
            );
        }
    }
}

#[test]
fn the_mod_pass_decomposes_the_residue_and_leaves_other_masks_alone() {
    let query = masked_add(7, U32_MAX);
    assert!(query.scan_features().has_mod_or_div);
    let eliminated = query.eliminate_mod();
    assert!(
        !eliminated.scan_features().has_bv,
        "the residue's bit-vector terms are gone: {eliminated}"
    );
    // A `bvand` with a mask that is not 2^k - 1 is not a `mod`.
    let other = mask_term(0xf0, 32, int_var("x"), 32);
    assert!(!other.scan_features().has_mod_or_div);
    assert_eq!(other.eliminate_mod(), other);
}
