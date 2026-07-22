// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! BV-to-Int operation encoding helpers.
//!
//! Exact modular arithmetic encodings for BV add/sub/mul/neg/div/rem/cmp.
//! Bitwise ops with constant arguments use pattern-specific encodings (#7006).
//! Variable-variable bitwise ops (AND/OR/XOR) use per-bit integer
//! decomposition for widths <= 32, with UF fallback for wider types (#8289).

use std::sync::Arc;

use num_bigint::BigUint;
use num_traits::{One, ToPrimitive, Zero};

use crate::{ChcExpr, ChcOp, ChcSort};

use super::BvIntMap;

/// Dispatch a BV operation to its Int encoding.
///
/// When a BV operation's arguments lack the expected BitVec sort (e.g., from
/// an upstream transform substituting Int-sorted expressions), the operation
/// is over-approximated as a UF rather than panicking (#7078).
pub(super) fn abstract_op(
    op: &ChcOp,
    args: &[Arc<ChcExpr>],
    aa: Vec<ChcExpr>,
    map: &mut BvIntMap,
) -> ChcExpr {
    // For BV ops that need width from the first original argument, check that
    // the expected BitVec sort is present. If not, fall back to UF. (#7078)
    if needs_bv_width_from_args(op) && try_bv_width(args).is_none() {
        return uf_fallback(op, aa, 0, map);
    }
    match op {
        ChcOp::BvAdd => bvadd(&aa, args),
        ChcOp::BvSub => bvsub(&aa, args),
        ChcOp::BvMul => bvmul(&aa, args),
        ChcOp::BvNeg => bvneg(&aa, args),
        ChcOp::BvUDiv => bvudiv(&aa, args),
        ChcOp::BvURem => bvurem(&aa, args),
        ChcOp::BvULt => unsigned_cmp(&aa[0], &aa[1], args, ChcOp::Lt),
        ChcOp::BvULe => unsigned_cmp(&aa[0], &aa[1], args, ChcOp::Le),
        ChcOp::BvUGt => unsigned_cmp(&aa[0], &aa[1], args, ChcOp::Gt),
        ChcOp::BvUGe => unsigned_cmp(&aa[0], &aa[1], args, ChcOp::Ge),
        ChcOp::BvSLt => signed_cmp(&aa[0], &aa[1], args, ChcOp::Lt),
        ChcOp::BvSLe => signed_cmp(&aa[0], &aa[1], args, ChcOp::Le),
        ChcOp::BvSGt => signed_cmp(&aa[0], &aa[1], args, ChcOp::Gt),
        ChcOp::BvSGe => signed_cmp(&aa[0], &aa[1], args, ChcOp::Ge),
        ChcOp::BvComp => {
            let w = try_bv_width(args).unwrap_or(0);
            ChcExpr::ite(
                ChcExpr::eq(
                    normalize_unsigned_if_wide(&aa[0], w),
                    normalize_unsigned_if_wide(&aa[1], w),
                ),
                ChcExpr::int(1),
                ChcExpr::int(0),
            )
        }
        ChcOp::Bv2Nat | ChcOp::BvZeroExtend(_) => {
            let w = try_bv_width(args).unwrap_or(0);
            normalize_unsigned_if_wide(&aa[0], w)
        }
        ChcOp::Int2Bv(w) => ChcExpr::mod_op(aa[0].clone(), int_pow2(*w)),
        ChcOp::BvSignExtend(k) => {
            // sign_extend[k](x) where x is BV(n): produces BV(n+k).
            // Unsigned encoding: if x >= 2^(n-1), add (2^(n+k) - 2^n) to
            // fill the high k bits with 1s (sign extension of negative values).
            let n = match try_bv_width(args) {
                Some(w) => w,
                None => return aa[0].clone(),
            };
            let norm_x = normalize_unsigned_if_wide(&aa[0], n);
            let half = int_pow2(n - 1);
            let fill = ChcExpr::sub(int_pow2(n + k), int_pow2(n));
            ChcExpr::ite(
                ChcExpr::ge(norm_x.clone(), half),
                ChcExpr::add(norm_x.clone(), fill),
                norm_x,
            )
        }
        ChcOp::BvExtract(hi, lo) => bvextract_precise(&aa[0], args, *hi, *lo),
        ChcOp::BvConcat => {
            let w_x = try_bv_width(args).unwrap_or(0);
            let w_y = match args.get(1).and_then(|a| try_bv_width_of(a)) {
                Some(w) => w,
                None => return uf_fallback(op, aa, 0, map),
            };
            ChcExpr::add(
                ChcExpr::mul(normalize_unsigned_if_wide(&aa[0], w_x), int_pow2(w_y)),
                normalize_unsigned_if_wide(&aa[1], w_y),
            )
        }
        // #7006: Precise encoding for common bitwise patterns with constant args.
        // Remaining bitwise ops are over-approximated as uninterpreted functions.
        ChcOp::BvAnd => bvand_precise(&aa, args, map),
        ChcOp::BvOr => bvor_precise(&aa, args, map),
        ChcOp::BvNot => {
            let w = try_bv_width(args).unwrap_or(0);
            if w > 0 {
                let norm_x = normalize_unsigned_if_wide(&aa[0], w);
                // ~x = 2^w - 1 - x
                ChcExpr::sub(ChcExpr::sub(int_pow2(w), ChcExpr::int(1)), norm_x)
            } else {
                uf_fallback(op, aa, 0, map)
            }
        }
        ChcOp::BvShl => bvshl_precise(&aa, args, map),
        ChcOp::BvLShr => bvlshr_precise(&aa, args, map),
        ChcOp::BvAShr => bvashr_precise(&aa, args, map),
        ChcOp::BvXor => bvxor_precise(&aa, args, map),
        ChcOp::BvSDiv
        | ChcOp::BvSRem
        | ChcOp::BvSMod
        | ChcOp::BvNand
        | ChcOp::BvNor
        | ChcOp::BvXnor
        | ChcOp::BvRotateLeft(_)
        | ChcOp::BvRotateRight(_)
        | ChcOp::BvRepeat(_) => {
            let w = try_bv_width(args).unwrap_or(0);
            let name = map.next_uf_name(&format!("{op:?}").to_lowercase(), w);
            ChcExpr::FuncApp(name, ChcSort::Int, aa.into_iter().map(Arc::new).collect())
        }
        // Non-BV: recurse into abstracted args
        _ => ChcExpr::Op(*op, aa.into_iter().map(Arc::new).collect()),
    }
}

/// Relaxed BV→Int encoding: no modular wrapping, no range constraints.
/// BV arithmetic becomes unbounded integer arithmetic. This is a sound
/// over-approximation for safety proofs. Comparisons are mapped to unsigned
/// (non-negative) integer comparisons. Bitwise ops remain UFs. (#5877)
pub(super) fn abstract_op_relaxed(
    op: &ChcOp,
    args: &[Arc<ChcExpr>],
    aa: Vec<ChcExpr>,
    map: &mut BvIntMap,
) -> ChcExpr {
    match op {
        // Arithmetic: plain integer, no modular wrapping
        ChcOp::BvAdd => ChcExpr::add(aa[0].clone(), aa[1].clone()),
        ChcOp::BvSub => ChcExpr::sub(aa[0].clone(), aa[1].clone()),
        ChcOp::BvMul => ChcExpr::mul(aa[0].clone(), aa[1].clone()),
        ChcOp::BvNeg => ChcExpr::sub(ChcExpr::int(0), aa[0].clone()),
        ChcOp::BvUDiv => {
            // Avoid div-by-zero: ite(b=0, 0, a/b)
            ChcExpr::ite(
                ChcExpr::eq(aa[1].clone(), ChcExpr::int(0)),
                ChcExpr::int(0),
                ChcExpr::Op(
                    ChcOp::Div,
                    vec![Arc::new(aa[0].clone()), Arc::new(aa[1].clone())],
                ),
            )
        }
        ChcOp::BvURem => ChcExpr::ite(
            ChcExpr::eq(aa[1].clone(), ChcExpr::int(0)),
            aa[0].clone(),
            ChcExpr::mod_op(aa[0].clone(), aa[1].clone()),
        ),
        // Comparisons: same as exact encoding (unsigned = natural ordering)
        ChcOp::BvULt => ChcExpr::lt(aa[0].clone(), aa[1].clone()),
        ChcOp::BvULe => ChcExpr::le(aa[0].clone(), aa[1].clone()),
        ChcOp::BvUGt => ChcExpr::gt(aa[0].clone(), aa[1].clone()),
        ChcOp::BvUGe => ChcExpr::ge(aa[0].clone(), aa[1].clone()),
        // Signed comparisons: over-approximate as unsigned in relaxed mode
        ChcOp::BvSLt => ChcExpr::lt(aa[0].clone(), aa[1].clone()),
        ChcOp::BvSLe => ChcExpr::le(aa[0].clone(), aa[1].clone()),
        ChcOp::BvSGt => ChcExpr::gt(aa[0].clone(), aa[1].clone()),
        ChcOp::BvSGe => ChcExpr::ge(aa[0].clone(), aa[1].clone()),
        ChcOp::BvComp => ChcExpr::ite(
            ChcExpr::eq(aa[0].clone(), aa[1].clone()),
            ChcExpr::int(1),
            ChcExpr::int(0),
        ),
        ChcOp::Bv2Nat | ChcOp::BvZeroExtend(_) | ChcOp::BvSignExtend(_) | ChcOp::Int2Bv(_) => {
            aa[0].clone()
        }
        ChcOp::BvExtract(hi, lo) => {
            // In relaxed mode with signed constants, sign-bit extraction can be
            // simplified to a sign check rather than div/mod. (#5877)
            let w = match try_bv_width(args) {
                Some(w) => w,
                None => return uf_fallback(op, aa, 0, map),
            };
            if *hi == w - 1 && *lo == w - 1 {
                // Sign bit extraction: ((_ extract (w-1) (w-1)) x)
                // Result is a BV(1): #b1 if x < 0, #b0 if x >= 0.
                // In relaxed signed mode, BV(1) #b1 = -1, #b0 = 0 (signed
                // interpretation: 1 >= 2^0, so 1 - 2^1 = -1). The values
                // here must match how BitVec(1, _) constants are converted.
                ChcExpr::ite(
                    ChcExpr::lt(aa[0].clone(), ChcExpr::int(0)),
                    ChcExpr::int(-1), // #b1 in signed BV(1) = -1
                    ChcExpr::int(0),  // #b0 in signed BV(1) = 0
                )
            } else {
                // General extract: over-approximate as div + mod
                let divisor = int_pow2(*lo);
                let modulus = int_pow2(hi - lo + 1);
                ChcExpr::mod_op(
                    ChcExpr::Op(ChcOp::Div, vec![Arc::new(aa[0].clone()), Arc::new(divisor)]),
                    modulus,
                )
            }
        }
        ChcOp::BvConcat => {
            let w_y = match args.get(1).and_then(|a| try_bv_width_of(a)) {
                Some(w) => w,
                None => return uf_fallback(op, aa, 0, map),
            };
            ChcExpr::add(ChcExpr::mul(aa[0].clone(), int_pow2(w_y)), aa[1].clone())
        }
        // Bitwise ops: UFs (same as exact encoding)
        ChcOp::BvSDiv
        | ChcOp::BvSRem
        | ChcOp::BvSMod
        | ChcOp::BvAnd
        | ChcOp::BvOr
        | ChcOp::BvXor
        | ChcOp::BvNand
        | ChcOp::BvNor
        | ChcOp::BvXnor
        | ChcOp::BvNot
        | ChcOp::BvShl
        | ChcOp::BvLShr
        | ChcOp::BvAShr
        | ChcOp::BvRotateLeft(_)
        | ChcOp::BvRotateRight(_)
        | ChcOp::BvRepeat(_) => {
            let w = try_bv_width(args).unwrap_or(0);
            let name = map.next_uf_name(&format!("{op:?}").to_lowercase(), w);
            ChcExpr::FuncApp(name, ChcSort::Int, aa.into_iter().map(Arc::new).collect())
        }
        // Non-BV: pass through
        _ => ChcExpr::Op(*op, aa.into_iter().map(Arc::new).collect()),
    }
}

fn bvadd(aa: &[ChcExpr], orig: &[Arc<ChcExpr>]) -> ChcExpr {
    let w = bv_width(orig);
    let sum = ChcExpr::add(aa[0].clone(), aa[1].clone());
    let bound = int_pow2(w);
    // #7006: For BV64+, use mod instead of ITE. The ITE comparison
    // `sum < 2^64` introduces a large constant that causes Rational64
    // overflow in the LRA solver. mod(sum, 2^64) is equivalent when
    // inputs are in [0, 2^w) (sum < 2*2^w, so mod wraps at most once).
    if w >= 63 {
        ChcExpr::mod_op(sum, bound)
    } else {
        ChcExpr::ite(
            ChcExpr::lt(sum.clone(), bound.clone()),
            sum.clone(),
            ChcExpr::sub(sum, bound),
        )
    }
}

fn bvsub(aa: &[ChcExpr], orig: &[Arc<ChcExpr>]) -> ChcExpr {
    let w = bv_width(orig);
    let diff = ChcExpr::sub(aa[0].clone(), aa[1].clone());
    let bound = int_pow2(w);
    // #7006: For BV64+, use mod. The ITE `diff >= 0` check is fine
    // but the `diff + 2^64` introduces the large constant. mod handles
    // negative values correctly: mod(-1, 2^64) = 2^64 - 1 = max_val.
    if w >= 63 {
        ChcExpr::mod_op(diff, bound)
    } else {
        ChcExpr::ite(
            ChcExpr::ge(diff.clone(), ChcExpr::int(0)),
            diff.clone(),
            ChcExpr::add(diff, bound),
        )
    }
}

fn bvmul(aa: &[ChcExpr], orig: &[Arc<ChcExpr>]) -> ChcExpr {
    let w = bv_width(orig);
    let product = ChcExpr::mul(aa[0].clone(), aa[1].clone());
    let bound = int_pow2(w);
    // Unsigned BV multiplication: mod(a * b, 2^w).
    // Direct mod avoids ITE, which causes model-verification mismatch after
    // ITE elimination introduces aux variables for both branches.
    ChcExpr::mod_op(product, bound)
}

fn bvneg(aa: &[ChcExpr], orig: &[Arc<ChcExpr>]) -> ChcExpr {
    let w = bv_width(orig);
    let x = normalize_unsigned_if_wide(&aa[0], w);
    ChcExpr::ite(
        ChcExpr::eq(x.clone(), ChcExpr::int(0)),
        ChcExpr::int(0),
        ChcExpr::sub(int_pow2(w), x),
    )
}

fn bvudiv(aa: &[ChcExpr], orig: &[Arc<ChcExpr>]) -> ChcExpr {
    let w = bv_width(orig);
    let lhs = normalize_unsigned_if_wide(&aa[0], w);
    let rhs = normalize_unsigned_if_wide(&aa[1], w);
    // Unsigned max = 2^w - 1 (e.g., 2^64 - 1 for BV64)
    let max_val = ChcExpr::sub(int_pow2(w), ChcExpr::int(1));
    ChcExpr::ite(
        ChcExpr::eq(rhs.clone(), ChcExpr::int(0)),
        max_val,
        ChcExpr::Op(ChcOp::Div, vec![Arc::new(lhs), Arc::new(rhs)]),
    )
}

fn bvurem(aa: &[ChcExpr], orig: &[Arc<ChcExpr>]) -> ChcExpr {
    let w = bv_width(orig);
    let lhs = normalize_unsigned_if_wide(&aa[0], w);
    let rhs = normalize_unsigned_if_wide(&aa[1], w);
    ChcExpr::ite(
        ChcExpr::eq(rhs.clone(), ChcExpr::int(0)),
        lhs.clone(),
        ChcExpr::mod_op(lhs, rhs),
    )
}

fn unsigned_cmp(x: &ChcExpr, y: &ChcExpr, orig: &[Arc<ChcExpr>], cmp: ChcOp) -> ChcExpr {
    let w = bv_width(orig);
    ChcExpr::Op(
        cmp,
        vec![
            Arc::new(normalize_unsigned_if_wide(x, w)),
            Arc::new(normalize_unsigned_if_wide(y, w)),
        ],
    )
}

fn signed_cmp(x: &ChcExpr, y: &ChcExpr, orig: &[Arc<ChcExpr>], cmp: ChcOp) -> ChcExpr {
    let w = bv_width(orig);
    let norm_x = normalize_unsigned_if_wide(x, w);
    let norm_y = normalize_unsigned_if_wide(y, w);
    let half = int_pow2(w.saturating_sub(1));
    let x_neg = ChcExpr::ge(norm_x.clone(), half.clone());
    let y_neg = ChcExpr::ge(norm_y.clone(), half);
    let direct = ChcExpr::Op(
        cmp,
        vec![Arc::new(norm_x.clone()), Arc::new(norm_y.clone())],
    );
    let neg_wins = matches!(cmp, ChcOp::Lt | ChcOp::Le);
    let x_neg_r = ChcExpr::ite(y_neg.clone(), direct.clone(), ChcExpr::Bool(neg_wins));
    let x_pos_r = ChcExpr::ite(y_neg, ChcExpr::Bool(!neg_wins), direct);
    ChcExpr::ite(x_neg, x_neg_r, x_pos_r)
}

// ── Bitwise precise encodings (#7006, #8289) ─────────────────────────────

/// Default maximum BV width for which variable-variable bitwise operations use
/// bit-decomposition instead of UF over-approximation (#8289).
/// For BV8 (8 aux vars per op) and BV16 (16 aux vars) this is always
/// worthwhile. BV32 (32 aux vars) is borderline but still tractable.
/// BV64 (64 aux vars per op) is too expensive — keep UF fallback.
///
/// This default can be overridden via `BvIntMap::decompose_limit` for
/// CEGAR-style refinement: Phase 1 uses 0 (UF-only), Phase 2 uses 64
/// (full decomposition).
pub(super) const DEFAULT_BIT_DECOMPOSITION_WIDTH_LIMIT: u32 = 32;

/// Selector for the per-bit combination in `bitwise_bit_decomposition`.
enum BitwiseOp {
    And,
    Or,
    Xor,
}

/// Encode a binary BV bitwise operation by decomposing both operands into
/// per-bit integer expressions and reconstructing the result as an `Int`.
///
/// For each bit position `i` in `0..w`:
///   bit_a_i = (a / 2^i) mod 2
///   bit_b_i = (b / 2^i) mod 2
///
/// AND: result_i = bit_a_i * bit_b_i
/// OR:  result_i = bit_a_i + bit_b_i - bit_a_i * bit_b_i
/// XOR: result_i = bit_a_i + bit_b_i - 2 * bit_a_i * bit_b_i
///
/// Reconstruct: result = sum(result_i * 2^i for i in 0..w)
///
/// For BV64+ operands are first normalized into `[0, 2^w)`.
fn bitwise_bit_decomposition(lhs: &ChcExpr, rhs: &ChcExpr, w: u32, op: BitwiseOp) -> ChcExpr {
    let lhs = Arc::new(normalize_unsigned_if_wide(lhs, w));
    let rhs = Arc::new(normalize_unsigned_if_wide(rhs, w));
    let two = ChcExpr::int(2);

    let mut result = ChcExpr::int(0);
    for i in 0..w {
        let place = int_pow2(i);

        // Extract bit i: (x / 2^i) mod 2
        let lhs_bit = ChcExpr::mod_op(
            ChcExpr::Op(ChcOp::Div, vec![lhs.clone(), Arc::new(place.clone())]),
            two.clone(),
        );
        let rhs_bit = ChcExpr::mod_op(
            ChcExpr::Op(ChcOp::Div, vec![rhs.clone(), Arc::new(place.clone())]),
            two.clone(),
        );

        let bit_sum = ChcExpr::add(lhs_bit.clone(), rhs_bit.clone());
        let bit_product = ChcExpr::mul(lhs_bit, rhs_bit);

        let result_bit = match op {
            BitwiseOp::And => bit_product,
            BitwiseOp::Or => ChcExpr::sub(bit_sum, bit_product),
            BitwiseOp::Xor => ChcExpr::sub(bit_sum, ChcExpr::mul(two.clone(), bit_product)),
        };

        result = ChcExpr::add(result, ChcExpr::mul(result_bit, place));
    }

    result
}

/// Try to extract a non-negative compile-time integer from an abstracted expr.
///
/// BV64+ constants are often represented as `Add/Sub/Mul` trees instead of a
/// single `Int`, so bitwise pattern matching must understand those trees.
fn try_const_uint(e: &ChcExpr) -> Option<BigUint> {
    match e {
        ChcExpr::Int(v) => u64::try_from(*v).ok().map(BigUint::from),
        ChcExpr::Op(ChcOp::Add, args) => args.iter().try_fold(BigUint::zero(), |acc, arg| {
            Some(acc + try_const_uint(arg.as_ref())?)
        }),
        ChcExpr::Op(ChcOp::Sub, args) if !args.is_empty() => {
            let mut args_iter = args.iter();
            let first = try_const_uint(args_iter.next()?.as_ref())?;
            args_iter.try_fold(first, |acc, arg| {
                let rhs = try_const_uint(arg.as_ref())?;
                if acc < rhs {
                    None
                } else {
                    Some(acc - rhs)
                }
            })
        }
        ChcExpr::Op(ChcOp::Mul, args) => args.iter().try_fold(BigUint::one(), |acc, arg| {
            Some(acc * try_const_uint(arg.as_ref())?)
        }),
        ChcExpr::Op(ChcOp::Div, args) if args.len() == 2 => {
            let lhs = try_const_uint(args[0].as_ref())?;
            let rhs = try_const_uint(args[1].as_ref())?;
            if rhs.is_zero() {
                None
            } else {
                Some(lhs / rhs)
            }
        }
        ChcExpr::Op(ChcOp::Mod, args) if args.len() == 2 => {
            let lhs = try_const_uint(args[0].as_ref())?;
            let rhs = try_const_uint(args[1].as_ref())?;
            if rhs.is_zero() {
                None
            } else {
                Some(lhs % rhs)
            }
        }
        _ => None,
    }
}

fn try_const_shift_amount(e: &ChcExpr) -> Option<BigUint> {
    try_const_uint(e)
}

fn uint_const_expr(value: &BigUint) -> ChcExpr {
    let mut terms = Vec::new();
    for (idx, digit) in value.to_u32_digits().into_iter().enumerate() {
        if digit == 0 {
            continue;
        }
        let term = if idx == 0 {
            ChcExpr::int(i64::from(digit))
        } else {
            ChcExpr::mul(ChcExpr::int(i64::from(digit)), int_pow2((idx as u32) * 32))
        };
        terms.push(term);
    }
    let mut terms_iter = terms.into_iter();
    let Some(first) = terms_iter.next() else {
        return ChcExpr::int(0);
    };
    terms_iter.fold(first, ChcExpr::add)
}

fn low_bit_mask_width(mask: &BigUint) -> Option<u32> {
    if mask.is_zero() {
        return None;
    }
    let bits = mask.bits();
    if mask.count_ones() == bits {
        u32::try_from(bits).ok()
    } else {
        None
    }
}

fn clear_low_bit_mask_width(mask: &BigUint, width: u32) -> Option<u32> {
    let trailing_zeros = u32::try_from(mask.trailing_zeros()?).ok()?;
    if trailing_zeros == 0 || trailing_zeros >= width {
        return None;
    }
    let shifted = mask >> trailing_zeros;
    let kept_width = u64::from(width - trailing_zeros);
    if shifted.bits() == kept_width && shifted.count_ones() == kept_width {
        Some(trailing_zeros)
    } else {
        None
    }
}

fn all_ones_mask(width: u32) -> BigUint {
    (BigUint::one() << width) - BigUint::one()
}

fn clear_low_bits_expr(x: &ChcExpr, k: u32) -> ChcExpr {
    if k == 0 {
        return x.clone();
    }
    let modulus = int_pow2(k);
    ChcExpr::mul(
        ChcExpr::Op(
            ChcOp::Div,
            vec![Arc::new(x.clone()), Arc::new(modulus.clone())],
        ),
        modulus,
    )
}

/// BvAnd with constant mask: `x & (2^k - 1)` → `x mod 2^k`.
/// For variable-variable AND with width <= `map.decompose_limit`,
/// uses per-bit decomposition (#8289). Falls back to UF otherwise.
fn bvand_precise(aa: &[ChcExpr], args: &[Arc<ChcExpr>], map: &mut BvIntMap) -> ChcExpr {
    let w = try_bv_width(args).unwrap_or(0);
    // Try both operand orderings for constant mask
    if let Some(c) = try_const_uint(&aa[1]) {
        if let Some(r) = and_with_const_mask(&aa[0], c, w) {
            return r;
        }
    }
    if let Some(c) = try_const_uint(&aa[0]) {
        if let Some(r) = and_with_const_mask(&aa[1], c, w) {
            return r;
        }
    }
    // #8289: Bit-decomposition for variable-variable AND
    if w > 0 && w <= map.decompose_limit {
        return bitwise_bit_decomposition(&aa[0], &aa[1], w, BitwiseOp::And);
    }
    bitwise_uf_fallback(&ChcOp::BvAnd, aa.to_vec(), w, map)
}

/// Encode `x & mask` when mask is a known constant.
/// Returns `None` if the mask pattern is not recognized.
fn and_with_const_mask(x: &ChcExpr, mask: BigUint, w: u32) -> Option<ChcExpr> {
    let norm_x = normalize_unsigned_if_wide(x, w);
    if mask.is_zero() {
        return Some(ChcExpr::int(0));
    }
    if w == 0 {
        return None;
    }
    // All-ones mask (2^w - 1): identity.
    if mask == all_ones_mask(w) {
        return Some(norm_x);
    }
    // Check if mask = 2^k - 1 for some k (low-bit mask).
    if let Some(k) = low_bit_mask_width(&mask) {
        return Some(ChcExpr::mod_op(x.clone(), int_pow2(k)));
    }
    // Alignment masks of the form `111..111000..000` clear the low k bits.
    if let Some(k) = clear_low_bit_mask_width(&mask, w) {
        return Some(clear_low_bits_expr(&normalize_unsigned_if_wide(x, w), k));
    }
    None
}

/// BvOr with constant: `x | 0` → `x`, `x | (2^k - 1)` sets the low k bits,
/// `x | all_ones` → `all_ones`.
fn bvor_precise(aa: &[ChcExpr], args: &[Arc<ChcExpr>], map: &mut BvIntMap) -> ChcExpr {
    let w = try_bv_width(args).unwrap_or(0);
    let lhs_const = try_const_uint(&aa[0]);
    let rhs_const = try_const_uint(&aa[1]);
    if rhs_const.as_ref().is_some_and(BigUint::is_zero) {
        return normalize_unsigned_if_wide(&aa[0], w);
    }
    if lhs_const.as_ref().is_some_and(BigUint::is_zero) {
        return normalize_unsigned_if_wide(&aa[1], w);
    }
    if w > 0 {
        let all_ones = all_ones_mask(w);
        if rhs_const.as_ref() == Some(&all_ones) || lhs_const.as_ref() == Some(&all_ones) {
            return uint_const_expr(&all_ones);
        }
        if let Some(k) = rhs_const.as_ref().and_then(low_bit_mask_width) {
            return ChcExpr::add(
                clear_low_bits_expr(&normalize_unsigned_if_wide(&aa[0], w), k),
                uint_const_expr(&all_ones_mask(k)),
            );
        }
        if let Some(k) = lhs_const.as_ref().and_then(low_bit_mask_width) {
            return ChcExpr::add(
                clear_low_bits_expr(&normalize_unsigned_if_wide(&aa[1], w), k),
                uint_const_expr(&all_ones_mask(k)),
            );
        }
    }
    // #8289: Bit-decomposition for variable-variable OR
    if w > 0 && w <= map.decompose_limit {
        return bitwise_bit_decomposition(&aa[0], &aa[1], w, BitwiseOp::Or);
    }
    bitwise_uf_fallback(&ChcOp::BvOr, aa.to_vec(), w, map)
}

/// BvShl with constant shift: `x << k` → `(x * 2^k) mod 2^w`.
fn bvshl_precise(aa: &[ChcExpr], args: &[Arc<ChcExpr>], map: &mut BvIntMap) -> ChcExpr {
    let w = try_bv_width(args).unwrap_or(0);
    if let Some(k) = try_const_shift_amount(&aa[1]) {
        if w > 0 && k >= BigUint::from(w) {
            return ChcExpr::int(0); // shift >= width → 0
        }
        if k.is_zero() {
            return normalize_unsigned_if_wide(&aa[0], w); // no shift
        }
        let ku = k
            .to_u32()
            .expect("constant shift amount fits in u32 once bounded by width");
        // (x * 2^k) mod 2^w
        let shifted = ChcExpr::mul(aa[0].clone(), int_pow2(ku));
        if w > 0 {
            return ChcExpr::mod_op(shifted, int_pow2(w));
        }
        return shifted;
    }
    // Variable shift amount: UF + bounded interpreted facts (WORD-BV #8).
    bitwise_uf_fallback(&ChcOp::BvShl, aa.to_vec(), w, map)
}

/// BvLShr with constant shift: `x >> k` → `x / 2^k` (integer division).
fn bvlshr_precise(aa: &[ChcExpr], args: &[Arc<ChcExpr>], map: &mut BvIntMap) -> ChcExpr {
    let w = try_bv_width(args).unwrap_or(0);
    if let Some(k) = try_const_shift_amount(&aa[1]) {
        if w > 0 && k >= BigUint::from(w) {
            return ChcExpr::int(0); // shift >= width → 0
        }
        if k.is_zero() {
            return normalize_unsigned_if_wide(&aa[0], w); // no shift
        }
        let ku = k
            .to_u32()
            .expect("constant shift amount fits in u32 once bounded by width");
        // x / 2^k (integer division, exact for unsigned)
        let norm_x = normalize_unsigned_if_wide(&aa[0], w);
        return ChcExpr::Op(ChcOp::Div, vec![Arc::new(norm_x), Arc::new(int_pow2(ku))]);
    }
    // Variable shift amount: UF + bounded interpreted facts (WORD-BV #8).
    bitwise_uf_fallback(&ChcOp::BvLShr, aa.to_vec(), w, map)
}

/// BvAShr with constant shift: arithmetic right shift.
/// Positive x: same as logical right shift.
/// Negative x (>= 2^(w-1)): fill with 1-bits from the left.
fn bvashr_precise(aa: &[ChcExpr], args: &[Arc<ChcExpr>], map: &mut BvIntMap) -> ChcExpr {
    let w = try_bv_width(args).unwrap_or(0);
    if let Some(k) = try_const_shift_amount(&aa[1]) {
        if w == 0 {
            return uf_fallback(&ChcOp::BvAShr, aa.to_vec(), w, map);
        }
        let norm_x = normalize_unsigned_if_wide(&aa[0], w);
        if k >= BigUint::from(w) {
            // All sign-bit fill: ite(x >= 2^(w-1), 2^w - 1, 0)
            let half = int_pow2(w - 1);
            let all_ones = ChcExpr::sub(int_pow2(w), ChcExpr::int(1));
            return ChcExpr::ite(ChcExpr::ge(norm_x, half), all_ones, ChcExpr::int(0));
        }
        if k.is_zero() {
            return norm_x;
        }
        let ku = k
            .to_u32()
            .expect("constant shift amount fits in u32 once bounded by width");
        let half = int_pow2(w - 1);
        // Logical right shift result
        let lshr = ChcExpr::Op(
            ChcOp::Div,
            vec![Arc::new(norm_x.clone()), Arc::new(int_pow2(ku))],
        );
        // Fill bits for negative: (2^w - 1) - (2^(w-k) - 1) = 2^w - 2^(w-k)
        // These are the high k bits set to 1.
        let fill = ChcExpr::sub(int_pow2(w), int_pow2(w - ku));
        let ashr_neg = ChcExpr::add(lshr.clone(), fill);
        // ite(x >= 2^(w-1), lshr + fill, lshr)
        return ChcExpr::ite(ChcExpr::ge(norm_x, half), ashr_neg, lshr);
    }
    // Variable shift amount: UF + bounded interpreted facts (WORD-BV #8).
    bitwise_uf_fallback(&ChcOp::BvAShr, aa.to_vec(), w, map)
}

/// BvXor with constant or self-XOR: `x ^ 0` → `x`, `x ^ x` → `0`,
/// `x ^ all_ones` → `~x` (= 2^w - 1 - x).
fn bvxor_precise(aa: &[ChcExpr], args: &[Arc<ChcExpr>], map: &mut BvIntMap) -> ChcExpr {
    let w = try_bv_width(args).unwrap_or(0);
    let lhs_const = try_const_uint(&aa[0]);
    let rhs_const = try_const_uint(&aa[1]);
    if rhs_const.as_ref().is_some_and(BigUint::is_zero) {
        return normalize_unsigned_if_wide(&aa[0], w);
    }
    if lhs_const.as_ref().is_some_and(BigUint::is_zero) {
        return normalize_unsigned_if_wide(&aa[1], w);
    }
    if w > 0 {
        let all_ones = all_ones_mask(w);
        if rhs_const.as_ref() == Some(&all_ones) {
            return ChcExpr::sub(
                uint_const_expr(&all_ones),
                normalize_unsigned_if_wide(&aa[0], w),
            );
        }
        if lhs_const.as_ref() == Some(&all_ones) {
            return ChcExpr::sub(
                uint_const_expr(&all_ones),
                normalize_unsigned_if_wide(&aa[1], w),
            );
        }
    }
    // x ^ x = 0 (structural equality check)
    if aa[0] == aa[1] {
        return ChcExpr::int(0);
    }
    // #8289: Bit-decomposition for variable-variable XOR
    if w > 0 && w <= map.decompose_limit {
        return bitwise_bit_decomposition(&aa[0], &aa[1], w, BitwiseOp::Xor);
    }
    bitwise_uf_fallback(&ChcOp::BvXor, aa.to_vec(), w, map)
}

fn bvextract_precise(x: &ChcExpr, args: &[Arc<ChcExpr>], hi: u32, lo: u32) -> ChcExpr {
    let w = try_bv_width(args).unwrap_or(0);
    let width = hi - lo + 1;
    if w == 0 {
        let divisor = int_pow2(lo);
        return ChcExpr::mod_op(
            ChcExpr::Op(ChcOp::Div, vec![Arc::new(x.clone()), Arc::new(divisor)]),
            int_pow2(width),
        );
    }

    let norm_x = normalize_unsigned_if_wide(x, w);
    if hi == w - 1 && lo == 0 {
        return norm_x;
    }
    if lo == 0 {
        return ChcExpr::mod_op(norm_x, int_pow2(width));
    }

    let shifted = ChcExpr::Op(ChcOp::Div, vec![Arc::new(norm_x), Arc::new(int_pow2(lo))]);
    if hi == w - 1 {
        shifted
    } else {
        ChcExpr::mod_op(shifted, int_pow2(width))
    }
}

// ── Utilities ──────────────────────────────────────────────────────────────

/// Extract BV width from the first argument's sort, or `None` if not BitVec.
fn try_bv_width(args: &[Arc<ChcExpr>]) -> Option<u32> {
    match args.first().map(|a| a.sort()) {
        Some(ChcSort::BitVec(w)) => Some(w),
        _ => None,
    }
}

/// Extract BV width from a single expression's sort.
fn try_bv_width_of(expr: &ChcExpr) -> Option<u32> {
    match expr.sort() {
        ChcSort::BitVec(w) => Some(w),
        _ => None,
    }
}

/// Whether this BV op calls `bv_width` on `args[0]` and would panic
/// if the first argument is not BitVec-sorted.
fn needs_bv_width_from_args(op: &ChcOp) -> bool {
    matches!(
        op,
        ChcOp::BvAdd
            | ChcOp::BvSub
            | ChcOp::BvMul
            | ChcOp::BvNeg
            | ChcOp::BvUDiv
            | ChcOp::BvSLt
            | ChcOp::BvSLe
            | ChcOp::BvSGt
            | ChcOp::BvSGe
    )
}

/// Over-approximate a BV op as an uninterpreted function when the expected
/// BitVec sort is missing from the original arguments (#7078).
fn uf_fallback(op: &ChcOp, aa: Vec<ChcExpr>, w: u32, map: &mut BvIntMap) -> ChcExpr {
    let name = map.next_uf_name(&format!("{op:?}").to_lowercase(), w);
    ChcExpr::FuncApp(name, ChcSort::Int, aa.into_iter().map(Arc::new).collect())
}

/// UF fallback specifically for variable-variable bitwise operations (#8289).
/// Like `uf_fallback`, but also sets `had_bitwise_uf_fallback` so the CEGAR
/// loop knows refinement via bit-decomposition could improve precision.
///
/// WORD-BV lazy bitwise (#8, Eldarica FMCAD'18 lazy reduction): instead of
/// leaving the UF fully unconstrained, emit bounded interpreted side
/// constraints (valid facts about the concrete bitwise function) into
/// `map.pending_constraints`; `abstract_problem` conjoins them into the
/// enclosing clause's body constraint. This keeps the abstraction a sound
/// over-approximation while giving LIA engines word-level bounds to reason
/// with. Refinement on demand still goes through `had_bitwise_uf_fallback`.
fn bitwise_uf_fallback(op: &ChcOp, aa: Vec<ChcExpr>, w: u32, map: &mut BvIntMap) -> ChcExpr {
    map.had_bitwise_uf_fallback = true;
    let lazy_bounds = map.lazy_bitwise_bounds && w > 0 && aa.len() == 2;
    let operands = if lazy_bounds {
        Some((aa[0].clone(), aa[1].clone()))
    } else {
        None
    };
    let uf = uf_fallback(op, aa, w, map);
    if let Some((x, y)) = operands {
        push_bitwise_bounds(op, &uf, &x, &y, w, map);
    }
    uf
}

/// Emit bounded interpreted facts about a bitwise UF result `f = op(x, y)`.
///
/// Every emitted constraint is a VALID fact of the concrete bitwise function
/// on unsigned `w`-bit values, so conjoining them into the clause preserves
/// the over-approximation: any original BV behavior still has an abstract
/// counterpart (with the UF interpreted as the real function).
fn push_bitwise_bounds(
    op: &ChcOp,
    f: &ChcExpr,
    x: &ChcExpr,
    y: &ChcExpr,
    w: u32,
    map: &mut BvIntMap,
) {
    let nx = normalize_unsigned_if_wide(x, w);
    let ny = normalize_unsigned_if_wide(y, w);
    let max = uint_const_expr(&all_ones_mask(w));
    let mut bounds = vec![
        ChcExpr::ge(f.clone(), ChcExpr::int(0)),
        ChcExpr::le(f.clone(), max.clone()),
    ];
    match op {
        ChcOp::BvAnd => {
            // 0 <= x&y <= min(x, y), and x&y = x + y - (x|y) >= x + y - (2^w - 1)
            bounds.push(ChcExpr::le(f.clone(), nx.clone()));
            bounds.push(ChcExpr::le(f.clone(), ny.clone()));
            bounds.push(ChcExpr::ge(
                f.clone(),
                ChcExpr::sub(ChcExpr::add(nx, ny), max),
            ));
        }
        ChcOp::BvOr => {
            // max(x, y) <= x|y <= min(x + y, 2^w - 1)
            bounds.push(ChcExpr::ge(f.clone(), nx.clone()));
            bounds.push(ChcExpr::ge(f.clone(), ny.clone()));
            bounds.push(ChcExpr::le(f.clone(), ChcExpr::add(nx, ny)));
        }
        ChcOp::BvXor => {
            // |x - y| <= x^y <= x + y, and x^y = x + y - 2*(x&y) has the same
            // parity as x + y.
            bounds.push(ChcExpr::le(f.clone(), ChcExpr::add(nx.clone(), ny.clone())));
            bounds.push(ChcExpr::ge(f.clone(), ChcExpr::sub(nx.clone(), ny.clone())));
            bounds.push(ChcExpr::ge(f.clone(), ChcExpr::sub(ny.clone(), nx.clone())));
            bounds.push(ChcExpr::eq(
                ChcExpr::mod_op(
                    ChcExpr::sub(ChcExpr::add(nx, ny), f.clone()),
                    ChcExpr::int(2),
                ),
                ChcExpr::int(0),
            ));
        }
        ChcOp::BvShl => {
            // shift 0 is the identity; shift >= w yields 0; shift >= 1 clears bit 0.
            bounds.push(ChcExpr::implies(
                ChcExpr::eq(ny.clone(), ChcExpr::int(0)),
                ChcExpr::eq(f.clone(), nx),
            ));
            bounds.push(ChcExpr::implies(
                ChcExpr::ge(ny.clone(), ChcExpr::int(i64::from(w))),
                ChcExpr::eq(f.clone(), ChcExpr::int(0)),
            ));
            bounds.push(ChcExpr::implies(
                ChcExpr::ge(ny, ChcExpr::int(1)),
                ChcExpr::eq(ChcExpr::mod_op(f.clone(), ChcExpr::int(2)), ChcExpr::int(0)),
            ));
        }
        ChcOp::BvLShr => {
            // Logical right shift never increases an unsigned value.
            bounds.push(ChcExpr::le(f.clone(), nx.clone()));
            bounds.push(ChcExpr::implies(
                ChcExpr::eq(ny.clone(), ChcExpr::int(0)),
                ChcExpr::eq(f.clone(), nx),
            ));
            bounds.push(ChcExpr::implies(
                ChcExpr::ge(ny, ChcExpr::int(i64::from(w))),
                ChcExpr::eq(f.clone(), ChcExpr::int(0)),
            ));
        }
        ChcOp::BvAShr => {
            // Sign bit is preserved: non-negative inputs shrink, negative
            // (>= 2^(w-1)) inputs keep the sign bit set.
            let half = int_pow2(w.saturating_sub(1));
            bounds.push(ChcExpr::implies(
                ChcExpr::eq(ny, ChcExpr::int(0)),
                ChcExpr::eq(f.clone(), nx.clone()),
            ));
            bounds.push(ChcExpr::implies(
                ChcExpr::lt(nx.clone(), half.clone()),
                ChcExpr::le(f.clone(), nx.clone()),
            ));
            bounds.push(ChcExpr::implies(
                ChcExpr::ge(nx, half.clone()),
                ChcExpr::ge(f.clone(), half),
            ));
        }
        _ => {}
    }
    map.pending_constraints.extend(bounds);
}

fn normalize_unsigned_if_wide(expr: &ChcExpr, w: u32) -> ChcExpr {
    if w >= 63 {
        // Literal fold (wishlist rank 3, 2026-07-08): a non-negative i64 literal
        // is always already in [0, 2^w) for w >= 63, so the mod is the identity —
        // fold it away instead of materializing a SYMBOLIC `2^32 * 2^32 * …`
        // modulus (int_pow2 cannot emit a literal above i64), which downstream
        // constant-divisor reasoning (mod_div_elim) cannot recognize and which
        // trips the div-by-nonconstant soundness gate (#C3) on shapes this lane
        // itself manufactures.
        if let ChcExpr::Int(v) = expr {
            if *v >= 0 {
                return expr.clone();
            }
        }
        ChcExpr::mod_op(expr.clone(), int_pow2(w))
    } else {
        expr.clone()
    }
}

pub(super) fn bv_width(args: &[Arc<ChcExpr>]) -> u32 {
    try_bv_width(args).expect("bv_width: first argument must be BitVec (pre-validated by caller)")
}

pub(super) fn int_pow2(w: u32) -> ChcExpr {
    if w < 63 {
        ChcExpr::int(1i64 << w)
    } else {
        // 2^w doesn't fit in i64; decompose: 2^w = 2^32 * 2^(w-32)
        ChcExpr::mul(ChcExpr::int(1i64 << 32), int_pow2(w - 32))
    }
}

pub(super) fn abstract_sort(sort: &ChcSort) -> ChcSort {
    match sort {
        ChcSort::BitVec(_) => ChcSort::Int,
        ChcSort::Array(k, v) => {
            ChcSort::Array(Box::new(abstract_sort(k)), Box::new(abstract_sort(v)))
        }
        other => other.clone(),
    }
}
