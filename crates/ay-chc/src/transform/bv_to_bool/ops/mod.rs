// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Bit-blast encoding of BV operations as Boolean circuits for BvToBool (#5877).

mod circuits;
mod infer;
#[cfg(test)]
mod tests;

use std::sync::Arc;

use crate::{ChcExpr, ChcOp, ChcSort, ChcVar};

use self::circuits::{
    barrel_shift_left, barrel_shift_right_arithmetic, barrel_shift_right_logical, bits_to_int_expr,
    bits_vec_to_int_expr, bitvec_const_to_int_expr, ripple_carry_add, ripple_carry_add_with_carry,
    shift_add_multiply, signed_less_than, unsigned_less_than, xor,
};
use self::infer::{can_bitblast_to_bits, has_bv_operand, infer_bv_width, infer_result_width};

pub(super) fn can_expand_predicate_arg(expr: &ChcExpr) -> bool {
    can_bitblast_to_bits(expr)
}

/// Convert a BV expression to a vector of Bool expressions (one per bit, LSB first).
pub(super) fn expr_to_bits(expr: &ChcExpr, width: u32) -> Vec<ChcExpr> {
    crate::expr::maybe_grow_expr_stack(|| match expr {
        ChcExpr::BitVec(val, _) => (0..width)
            .map(|i| {
                if i >= 128 {
                    ChcExpr::Bool(false) // u128 cannot hold bits beyond 127
                } else {
                    ChcExpr::Bool((*val >> i) & 1 != 0)
                }
            })
            .collect(),
        ChcExpr::Var(v) => match &v.sort {
            ChcSort::BitVec(_) => (0..width)
                .map(|i| ChcExpr::var(ChcVar::new(format!("{}_b{i}", v.name), ChcSort::Bool)))
                .collect(),
            _ => unconstrained_bits(width, &format!("__bb_var_{}", v.name)),
        },
        ChcExpr::Op(op, args) => bitblast_op(op, args, width),
        ChcExpr::FuncApp(name, _sort, _args) => {
            // Structurally keyed: `f(x)` and `f(y)` must NOT share bits (the old
            // name-only prefix aliased them), while two occurrences of `f(x)` must.
            havoc_bits(expr.clone(), width, &format!("fn_{name}_"))
        }
        _ => havoc_bits(expr.clone(), width, "expr"),
    })
}

fn unconstrained_bits(width: u32, prefix: &str) -> Vec<ChcExpr> {
    (0..width)
        .map(|i| ChcExpr::var(ChcVar::new(format!("{prefix}_b{i}"), ChcSort::Bool)))
        .collect()
}

/// Havoc bits for a subterm the blaster leaves UNINTERPRETED (division ops,
/// `FuncApp`s, unsupported expressions), keyed by STRUCTURAL IDENTITY.
///
/// SOUNDNESS (2026-07-08, wishlist rank 2): the old fixed prefixes
/// (`__bb_div`, `__bb_{name}`, `__bb_expr`) gave every occurrence of a KIND the
/// SAME bit variables — so two *different* subterms (e.g. `bvudiv(a, 2)` and
/// `bvudiv(c, d)`) were constrained EQUAL. A phantom equality strengthens the
/// blasted formula and can flip a satisfiable query to UNSAT — a false-Safe
/// channel. Structural keying restores both directions of correctness:
/// identical subterms share bits (congruence, `f(x) = f(x)` stays provable),
/// distinct subterms get fresh bits (no phantom coupling). Thread-local +
/// BTreeMap for deterministic naming (#8529 doctrine); ids stay unique past the
/// registry cap by always bumping the counter (beyond the cap, repeated terms
/// get fresh bits — the weaker, fail-closed direction).
fn havoc_bits(key: ChcExpr, width: u32, kind: &str) -> Vec<ChcExpr> {
    use std::cell::RefCell;
    use std::collections::BTreeMap;
    const REGISTRY_CAP: usize = 1 << 16;
    thread_local! {
        static HAVOC_IDS: RefCell<(BTreeMap<(ChcExpr, u32), usize>, usize)> =
            const { RefCell::new((BTreeMap::new(), 0)) };
    }
    let id = HAVOC_IDS.with(|state| {
        let (map, next) = &mut *state.borrow_mut();
        if let Some(&id) = map.get(&(key.clone(), width)) {
            return id;
        }
        let id = *next;
        *next += 1;
        if map.len() < REGISTRY_CAP {
            map.insert((key, width), id);
        }
        id
    });
    unconstrained_bits(width, &format!("__bb_{kind}{id}"))
}

/// Bit-blast a BV operation into a vector of Bool expressions.
fn bitblast_op(op: &ChcOp, args: &[Arc<ChcExpr>], width: u32) -> Vec<ChcExpr> {
    if let Some(bits) = bitblast_bitwise_op(op, args, width) {
        return bits;
    }
    if let Some(bits) = bitblast_arithmetic_op(op, args, width) {
        return bits;
    }
    if let Some(bits) = bitblast_shift_op(op, args, width) {
        return bits;
    }
    if let Some(bits) = bitblast_shape_op(op, args, width) {
        return bits;
    }
    if let Some(bits) = bitblast_misc_op(op, args, width) {
        return bits;
    }
    // Unhandled op (Select, Store, etc.) — produce unconstrained bits
    // rather than silent zeros. Silent zeros caused false-UNSAT (#7006).
    debug_assert!(
        false,
        "bitblast_op: unhandled op {:?} with {} args, width {}",
        op,
        args.len(),
        width,
    );
    unconstrained_bits(width, &format!("__bb_unk_{op:?}"))
}

fn bitblast_bitwise_op(op: &ChcOp, args: &[Arc<ChcExpr>], width: u32) -> Option<Vec<ChcExpr>> {
    let combine = |f: fn(ChcExpr, ChcExpr) -> ChcExpr| {
        let a = expr_to_bits(&args[0], width);
        let b = expr_to_bits(&args[1], width);
        a.into_iter().zip(b).map(|(ai, bi)| f(ai, bi)).collect()
    };

    match op {
        ChcOp::BvAnd => Some(combine(ChcExpr::and)),
        ChcOp::BvOr => Some(combine(ChcExpr::or)),
        ChcOp::BvXor => Some(combine(xor)),
        ChcOp::BvNot => Some(
            expr_to_bits(&args[0], width)
                .into_iter()
                .map(ChcExpr::not)
                .collect(),
        ),
        ChcOp::BvNand => Some(combine(|a, b| ChcExpr::not(ChcExpr::and(a, b)))),
        ChcOp::BvNor => Some(combine(|a, b| ChcExpr::not(ChcExpr::or(a, b)))),
        ChcOp::BvXnor => Some(combine(|a, b| ChcExpr::not(xor(a, b)))),
        _ => None,
    }
}

fn bitblast_arithmetic_op(op: &ChcOp, args: &[Arc<ChcExpr>], width: u32) -> Option<Vec<ChcExpr>> {
    match op {
        ChcOp::BvAdd => {
            let a = expr_to_bits(&args[0], width);
            let b = expr_to_bits(&args[1], width);
            Some(ripple_carry_add(&a, &b))
        }
        ChcOp::BvSub => {
            let a = expr_to_bits(&args[0], width);
            let b = expr_to_bits(&args[1], width);
            let not_b: Vec<ChcExpr> = b.into_iter().map(ChcExpr::not).collect();
            Some(ripple_carry_add_with_carry(&a, &not_b, ChcExpr::Bool(true)))
        }
        ChcOp::BvNeg => {
            let a = expr_to_bits(&args[0], width);
            let not_a: Vec<ChcExpr> = a.into_iter().map(ChcExpr::not).collect();
            let zero = vec![ChcExpr::Bool(false); width as usize];
            Some(ripple_carry_add_with_carry(
                &zero,
                &not_a,
                ChcExpr::Bool(true),
            ))
        }
        ChcOp::BvMul => {
            let a = expr_to_bits(&args[0], width);
            let b = expr_to_bits(&args[1], width);
            Some(shift_add_multiply(&a, &b, width))
        }
        _ => None,
    }
}

fn bitblast_shift_op(op: &ChcOp, args: &[Arc<ChcExpr>], width: u32) -> Option<Vec<ChcExpr>> {
    match op {
        ChcOp::BvShl | ChcOp::BvLShr | ChcOp::BvAShr if args.len() >= 2 => {
            let a = expr_to_bits(&args[0], width);
            let b = expr_to_bits(&args[1], width);
            match op {
                ChcOp::BvShl => Some(barrel_shift_left(&a, &b, width)),
                ChcOp::BvLShr => Some(barrel_shift_right_logical(&a, &b, width)),
                ChcOp::BvAShr => Some(barrel_shift_right_arithmetic(&a, &b, width)),
                _ => unreachable!(),
            }
        }
        _ => None,
    }
}

fn bitblast_shape_op(op: &ChcOp, args: &[Arc<ChcExpr>], width: u32) -> Option<Vec<ChcExpr>> {
    let target_len = width as usize;
    match op {
        ChcOp::BvExtract(hi, lo) => {
            let a_width = infer_bv_width(&args[0]).unwrap_or(width);
            let a = expr_to_bits(&args[0], a_width);
            let lo = *lo as usize;
            let hi = *hi as usize;
            Some(if hi < a.len() && lo <= hi {
                a[lo..=hi].to_vec()
            } else {
                vec![ChcExpr::Bool(false); target_len]
            })
        }
        ChcOp::BvConcat => {
            let lo_width = infer_bv_width(&args[1]).unwrap_or(width / 2);
            let hi_width = infer_bv_width(&args[0]).unwrap_or(width.saturating_sub(lo_width));
            let mut result = expr_to_bits(&args[1], lo_width);
            result.extend(expr_to_bits(&args[0], hi_width));
            normalize_width(result, target_len, ChcExpr::Bool(false))
        }
        ChcOp::BvZeroExtend(n) => {
            let orig_width = if width > *n { width - n } else { width };
            let bits = expr_to_bits(&args[0], orig_width);
            normalize_width(bits, target_len, ChcExpr::Bool(false))
        }
        ChcOp::BvSignExtend(n) => {
            let orig_width = if width > *n { width - n } else { 1 };
            let bits = expr_to_bits(&args[0], orig_width);
            let sign_bit = bits.last().cloned().unwrap_or(ChcExpr::Bool(false));
            normalize_width(bits, target_len, sign_bit)
        }
        ChcOp::BvComp => {
            let a = expr_to_bits(&args[0], width);
            let b = expr_to_bits(&args[1], width);
            let eq = a
                .into_iter()
                .zip(b)
                .map(|(ai, bi)| ChcExpr::not(xor(ai, bi)))
                .reduce(ChcExpr::and)
                .unwrap_or(ChcExpr::Bool(true));
            Some(vec![eq])
        }
        _ => None,
    }
}

fn bitblast_misc_op(op: &ChcOp, args: &[Arc<ChcExpr>], width: u32) -> Option<Vec<ChcExpr>> {
    let w = width as usize;
    match op {
        ChcOp::BvUDiv | ChcOp::BvURem | ChcOp::BvSDiv | ChcOp::BvSRem | ChcOp::BvSMod => {
            // Structurally keyed havoc: `bvudiv(a, 2)` and `bvudiv(c, d)` must NOT
            // share bits (the old fixed `__bb_div` prefix constrained all division
            // results in scope EQUAL — a phantom equality that could flip a
            // satisfiable query to UNSAT, i.e. a false-Safe channel), while two
            // occurrences of the SAME division keep shared bits (congruence).
            Some(havoc_bits(ChcExpr::Op(*op, args.to_vec()), width, "div"))
        }
        ChcOp::BvRotateLeft(n) => {
            let a = expr_to_bits(&args[0], width);
            let shift = (*n as usize) % w;
            Some((0..w).map(|i| a[(w + i - shift) % w].clone()).collect())
        }
        ChcOp::BvRotateRight(n) => {
            let a = expr_to_bits(&args[0], width);
            let shift = (*n as usize) % w;
            Some((0..w).map(|i| a[(i + shift) % w].clone()).collect())
        }
        ChcOp::BvRepeat(n) => {
            let orig_width = width / n.max(&1);
            let a = expr_to_bits(&args[0], orig_width);
            let mut result = Vec::new();
            for _ in 0..*n {
                result.extend(a.iter().cloned());
            }
            normalize_width(result, w, ChcExpr::Bool(false))
        }
        ChcOp::Bv2Nat => Some(unconstrained_bits(width, "__bb_conv")),
        // ITE on BV: per-bit mux between bitblasted branches.
        ChcOp::Ite if args.len() >= 3 => {
            let cond = bitblast_expr(&args[0]);
            let then_bits = expr_to_bits(&args[1], width);
            let else_bits = expr_to_bits(&args[2], width);
            Some(
                then_bits
                    .into_iter()
                    .zip(else_bits)
                    .map(|(t, e)| {
                        ChcExpr::Op(
                            ChcOp::Ite,
                            vec![Arc::new(cond.clone()), Arc::new(t), Arc::new(e)],
                        )
                    })
                    .collect(),
            )
        }
        // Comparisons return 1-bit BV. Use proper circuits when operands are
        // bitblastable; fall back to unconstrained bits otherwise.
        ChcOp::BvULt
        | ChcOp::BvULe
        | ChcOp::BvUGt
        | ChcOp::BvUGe
        | ChcOp::BvSLt
        | ChcOp::BvSLe
        | ChcOp::BvSGt
        | ChcOp::BvSGe => {
            if args.len() >= 2
                && infer::can_bitblast_to_bits(&args[0])
                && infer::can_bitblast_to_bits(&args[1])
            {
                let a_width = infer_bv_width(&args[0]).unwrap_or(width);
                let a = expr_to_bits(&args[0], a_width);
                let b = expr_to_bits(&args[1], a_width);
                let cmp_bit = match op {
                    ChcOp::BvULt => unsigned_less_than(&a, &b),
                    ChcOp::BvULe => ChcExpr::not(unsigned_less_than(&b, &a)),
                    ChcOp::BvUGt => unsigned_less_than(&b, &a),
                    ChcOp::BvUGe => ChcExpr::not(unsigned_less_than(&a, &b)),
                    ChcOp::BvSLt => signed_less_than(&a, &b),
                    ChcOp::BvSLe => ChcExpr::not(signed_less_than(&b, &a)),
                    ChcOp::BvSGt => signed_less_than(&b, &a),
                    ChcOp::BvSGe => ChcExpr::not(signed_less_than(&a, &b)),
                    _ => unreachable!(),
                };
                let mut result = vec![cmp_bit];
                result.resize(w, ChcExpr::Bool(false));
                Some(result)
            } else {
                Some(unconstrained_bits(width, "__bb_cmp"))
            }
        }
        _ => None,
    }
}

fn normalize_width(
    mut bits: Vec<ChcExpr>,
    target_len: usize,
    pad: ChcExpr,
) -> Option<Vec<ChcExpr>> {
    bits.truncate(target_len);
    while bits.len() < target_len {
        bits.push(pad.clone());
    }
    Some(bits)
}

/// Bit-blast a BV expression that returns a Bool or Int result.
pub(super) fn bitblast_expr(expr: &ChcExpr) -> ChcExpr {
    crate::expr::maybe_grow_expr_stack(|| match expr {
        ChcExpr::BitVec(val, _) => bitvec_const_to_int_expr(*val),
        ChcExpr::Var(v) => match &v.sort {
            ChcSort::BitVec(w) => bits_to_int_expr(&v.name, *w),
            _ => expr.clone(),
        },
        ChcExpr::Op(op, args) => bitblast_bool_op(op, args),
        ChcExpr::PredicateApp(name, id, args) => ChcExpr::PredicateApp(
            name.clone(),
            *id,
            args.iter().map(|a| Arc::new(bitblast_expr(a))).collect(),
        ),
        ChcExpr::FuncApp(name, sort, args) => ChcExpr::FuncApp(
            name.clone(),
            sort.clone(),
            args.iter().map(|a| Arc::new(bitblast_expr(a))).collect(),
        ),
        ChcExpr::ConstArray(ks, val) => {
            ChcExpr::ConstArray(ks.clone(), Arc::new(bitblast_expr(val)))
        }
        _ => expr.clone(),
    })
}

fn bitblast_bool_op(op: &ChcOp, args: &[Arc<ChcExpr>]) -> ChcExpr {
    if let Some(result) = bitblast_comparison_op(op, args) {
        return result;
    }
    if let Some(result) = bitblast_bv_equality_op(op, args) {
        return result;
    }
    if let Some(result) = bitblast_bv_value_op(op, args) {
        return result;
    }
    // If this is a BV operation that couldn't be bit-blasted (e.g., BvConcat
    // with arguments whose width can't be inferred), leave it unchanged for
    // BvToInt to handle. Converting children to Int while preserving the BV
    // op node creates sort-inconsistent trees (#7078).
    if infer::is_bv_op(op) || matches!(op, ChcOp::Bv2Nat | ChcOp::Int2Bv(_)) {
        return ChcExpr::Op(*op, args.to_vec());
    }
    let new_args: Vec<Arc<ChcExpr>> = args.iter().map(|a| Arc::new(bitblast_expr(a))).collect();
    ChcExpr::Op(*op, new_args)
}

fn bitblast_comparison_op(op: &ChcOp, args: &[Arc<ChcExpr>]) -> Option<ChcExpr> {
    if args.len() < 2 {
        return None;
    }
    if !matches!(
        op,
        ChcOp::BvULt
            | ChcOp::BvULe
            | ChcOp::BvUGt
            | ChcOp::BvUGe
            | ChcOp::BvSLt
            | ChcOp::BvSLe
            | ChcOp::BvSGt
            | ChcOp::BvSGe
    ) {
        return None;
    }
    // Bail out if operands contain ops that expr_to_bits cannot decompose
    // (Select, Store, Ite). Same guard as bitblast_bv_equality_op.
    if !can_bitblast_to_bits(&args[0]) || !can_bitblast_to_bits(&args[1]) {
        return None;
    }
    let width = infer_bv_width(&args[0])?;
    let a = expr_to_bits(&args[0], width);
    let b = expr_to_bits(&args[1], width);
    match op {
        ChcOp::BvULt => Some(unsigned_less_than(&a, &b)),
        ChcOp::BvULe => Some(ChcExpr::not(unsigned_less_than(&b, &a))),
        ChcOp::BvUGt => Some(unsigned_less_than(&b, &a)),
        ChcOp::BvUGe => Some(ChcExpr::not(unsigned_less_than(&a, &b))),
        ChcOp::BvSLt => Some(signed_less_than(&a, &b)),
        ChcOp::BvSLe => Some(ChcExpr::not(signed_less_than(&b, &a))),
        ChcOp::BvSGt => Some(signed_less_than(&b, &a)),
        ChcOp::BvSGe => Some(ChcExpr::not(signed_less_than(&a, &b))),
        _ => None,
    }
}

fn bitblast_bv_equality_op(op: &ChcOp, args: &[Arc<ChcExpr>]) -> Option<ChcExpr> {
    if !matches!(op, ChcOp::Eq | ChcOp::Ne) || args.len() < 2 {
        return None;
    }
    if !(has_bv_operand(&args[0]) || has_bv_operand(&args[1])) {
        return None;
    }
    // Bail out if either operand contains ops that expr_to_bits cannot
    // decompose (Select, Store, Ite). Fall through to the generic handler
    // in bitblast_bool_op which uses bitblast_expr (preserves structure).
    if !can_bitblast_to_bits(&args[0]) || !can_bitblast_to_bits(&args[1]) {
        return None;
    }
    let width = infer_bv_width(&args[0]).or_else(|| infer_bv_width(&args[1]))?;
    let a = expr_to_bits(&args[0], width);
    let b = expr_to_bits(&args[1], width);
    Some(match op {
        ChcOp::Eq => a
            .into_iter()
            .zip(b)
            .map(|(ai, bi)| ChcExpr::not(xor(ai, bi)))
            .reduce(ChcExpr::and)
            .unwrap_or(ChcExpr::Bool(true)),
        ChcOp::Ne => a
            .into_iter()
            .zip(b)
            .map(|(ai, bi)| xor(ai, bi))
            .reduce(ChcExpr::or)
            .unwrap_or(ChcExpr::Bool(false)),
        _ => unreachable!(),
    })
}

fn bitblast_bv_value_op(op: &ChcOp, args: &[Arc<ChcExpr>]) -> Option<ChcExpr> {
    match op {
        ChcOp::Bv2Nat => {
            // Preserve opaque BV-valued structure (for example, `select arr i`)
            // so later transforms can keep the array read symbolic instead of
            // blasting it into unconstrained bits (#8739).
            if !can_bitblast_to_bits(&args[0]) {
                return None;
            }
            let width = infer_bv_width(&args[0])?;
            Some(bits_vec_to_int_expr(&expr_to_bits(&args[0], width)))
        }
        ChcOp::Int2Bv(_) => None,
        ChcOp::BvAdd
        | ChcOp::BvSub
        | ChcOp::BvMul
        | ChcOp::BvAnd
        | ChcOp::BvOr
        | ChcOp::BvXor
        | ChcOp::BvNot
        | ChcOp::BvNeg
        | ChcOp::BvShl
        | ChcOp::BvLShr
        | ChcOp::BvAShr
        | ChcOp::BvNand
        | ChcOp::BvNor
        | ChcOp::BvXnor
        | ChcOp::BvConcat
        | ChcOp::BvExtract(_, _)
        | ChcOp::BvZeroExtend(_)
        | ChcOp::BvSignExtend(_)
        | ChcOp::BvRotateLeft(_)
        | ChcOp::BvRotateRight(_)
        | ChcOp::BvRepeat(_)
        | ChcOp::BvComp
        | ChcOp::BvUDiv
        | ChcOp::BvURem
        | ChcOp::BvSDiv
        | ChcOp::BvSRem
        | ChcOp::BvSMod => {
            // Keep BV arithmetic around opaque children for BvToInt; otherwise
            // `expr_to_bits` would replace unsupported subterms like `select`
            // with unconstrained bits and silently lose the array read (#8739).
            if !args.iter().all(|arg| can_bitblast_to_bits(arg)) {
                return None;
            }
            let width = infer_result_width(op, args)?;
            Some(bits_vec_to_int_expr(&bitblast_op(op, args, width)))
        }
        _ => None,
    }
}
