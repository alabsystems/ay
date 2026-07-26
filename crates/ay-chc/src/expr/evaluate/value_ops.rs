// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! SmtValue comparison and array evaluation helpers.
//!
//! Contains `smt_values_equal` (cross-sort equality), `eval_array_select`,
//! `eval_array_store`, and `eval_int_cmp` used by the expression evaluator.

use ay_core::kani_compat::DetHashMap as FxHashMap;
use num_bigint::BigInt;
use num_rational::BigRational;

use super::super::{maybe_grow_expr_stack, ChcExpr, ChcOp, ExprDepthGuard};
use super::eval_bv::eval_bv_val;
use super::evaluate_expr;
use crate::smt::SmtValue;

/// Kill switch for the exact-rational (LRA) evaluation lane
/// (`AY_LRA_REAL_EVAL=0` disables it, restoring the pre-fix Real-blind
/// behavior). Cached after first read; only consulted on the Real fallback
/// path (never on the Int/BV fast lanes), so it has zero cost on non-Real
/// atoms. The lane is a completeness-only, soundness-preserving addition:
/// it lets the strict model verifier VALIDATE (or reject) exact rational
/// witnesses instead of abstaining as Indeterminate on every Real atom.
pub(super) fn real_eval_enabled() -> bool {
    static ENABLED: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ENABLED.get_or_init(|| !matches!(std::env::var("AY_LRA_REAL_EVAL").ok().as_deref(), Some("0")))
}

/// Exact rational evaluator for Real-sorted (LRA) arithmetic expressions.
///
/// The Real analog of [`eval_int_big`]: a structural recursion over exactly
/// the linear-real-arithmetic grammar the LRA lane produces — `Real`/`Int`
/// literals, `Var` (reading `SmtValue::Real`, and coercing an integer model
/// value `SmtValue::Int`/`SmtValue::BigInt` up to a rational so mixed LIRA
/// atoms evaluate exactly), n-ary `Add`/`Sub`/`Mul`, `Neg`, real `Div`
/// (`/`), and `Ite` (condition decided by [`evaluate_expr`]). Everything
/// else abstains with `None` (fail-closed), same discipline as the integer
/// lanes.
///
/// SOUNDNESS: all arithmetic is exact `BigRational` — there is no rounding.
/// A value produced here is only ever compared (`=`, `<`, `<=`, `>`, `>=`)
/// to decide a Bool atom, and the model verifier accepts a Sat witness ONLY
/// when the WHOLE original expression evaluates to `Bool(true)`. Division by
/// zero abstains (`None`) rather than inventing a value, because `(/ x 0)` is
/// uninterpreted in SMT-LIB and guessing could fabricate a spurious Valid.
pub(crate) fn eval_real_big(
    expr: &ChcExpr,
    model: &FxHashMap<String, SmtValue>,
) -> Option<BigRational> {
    use num_traits::{One, Zero};
    maybe_grow_expr_stack(|| {
        ExprDepthGuard::check()?;
        match expr {
            ChcExpr::Real(n, d) => {
                if *d == 0 {
                    return None;
                }
                Some(BigRational::new(BigInt::from(*n), BigInt::from(*d)))
            }
            ChcExpr::Int(n) => Some(BigRational::from(BigInt::from(*n))),
            ChcExpr::Var(v) => match model.get(&v.name)? {
                SmtValue::Real(r) => Some(r.clone()),
                SmtValue::Int(n) => Some(BigRational::from(BigInt::from(*n))),
                SmtValue::BigInt(b) => Some(BigRational::from(b.as_ref().clone())),
                _ => None,
            },
            ChcExpr::Op(ChcOp::Add, args) => {
                let mut sum = BigRational::zero();
                for arg in args {
                    sum += eval_real_big(arg, model)?;
                }
                Some(sum)
            }
            ChcExpr::Op(ChcOp::Sub, args) if !args.is_empty() => {
                let first = eval_real_big(&args[0], model)?;
                if args.len() == 1 {
                    return Some(-first);
                }
                let mut result = first;
                for arg in &args[1..] {
                    result -= eval_real_big(arg, model)?;
                }
                Some(result)
            }
            ChcExpr::Op(ChcOp::Mul, args) => {
                let mut product = BigRational::one();
                for arg in args {
                    product *= eval_real_big(arg, model)?;
                }
                Some(product)
            }
            ChcExpr::Op(ChcOp::Neg, args) if args.len() == 1 => {
                Some(-eval_real_big(&args[0], model)?)
            }
            ChcExpr::Op(ChcOp::Div, args) if args.len() == 2 => {
                let a = eval_real_big(&args[0], model)?;
                let b = eval_real_big(&args[1], model)?;
                if b.is_zero() {
                    // (/ x 0) is uninterpreted in SMT-LIB; abstain rather than
                    // fabricate a witness (soundness).
                    None
                } else {
                    Some(a / b)
                }
            }
            ChcExpr::Op(ChcOp::Ite, args) if args.len() == 3 => {
                match evaluate_expr(&args[0], model)? {
                    SmtValue::Bool(true) => eval_real_big(&args[1], model),
                    SmtValue::Bool(false) => eval_real_big(&args[2], model),
                    _ => None,
                }
            }
            _ => None,
        }
    })
}

fn array_lookup<'a>(
    default: &'a SmtValue,
    entries: &'a [(SmtValue, SmtValue)],
    idx: &SmtValue,
) -> Option<&'a SmtValue> {
    for (k, v) in entries.iter().rev() {
        match smt_values_equal(k, idx) {
            Some(true) => return Some(v),
            Some(false) => {}
            None => return None,
        }
    }
    Some(default)
}

/// Cross-sort equality for `SmtValue`.
///
/// Same-sort values use standard equality. For mixed Bool/Int (or Bool/Real),
/// coerces Bool to the arithmetic sort before comparing, matching the semantics
/// of `eliminate_mixed_sort_eq`: `true → 1`, `false → 0`.
///
/// This is needed because the model verifier evaluates the *original* CHC
/// expression (before preprocessing), which may contain mixed-sort equalities
/// like `(= D:Int (= E 0):Bool)`. The solver operates on the rewritten form
/// `(= D:Int (ite (= E 0) 1 0))` and produces Int values, but the verifier
/// must interpret the original cross-sort comparison correctly.
pub(super) fn smt_values_equal(a: &SmtValue, b: &SmtValue) -> Option<bool> {
    match (a, b) {
        // Same-sort cases: use standard equality
        (SmtValue::Bool(x), SmtValue::Bool(y)) => Some(x == y),
        (SmtValue::Int(x), SmtValue::Int(y)) => Some(x == y),
        // Beyond-i128 integers (Phase-2 BigInt escape). Exact structural
        // equality is semantic equality here.
        (SmtValue::BigInt(x), SmtValue::BigInt(y)) => Some(x == y),
        // Int vs BigInt: false BY CANONICALITY — `SmtValue::BigInt` never
        // holds an i128-representable value (int_from_bigint invariant), so
        // the two domains are disjoint and structurally-unequal means
        // semantically-unequal.
        (SmtValue::Int(_), SmtValue::BigInt(_)) | (SmtValue::BigInt(_), SmtValue::Int(_)) => {
            Some(false)
        }
        (SmtValue::BitVec(v1, w1), SmtValue::BitVec(v2, w2)) => Some(v1 == v2 && w1 == w2),
        (SmtValue::Real(x), SmtValue::Real(y)) => Some(x == y),
        (SmtValue::Datatype(ctor1, fields1), SmtValue::Datatype(ctor2, fields2)) => {
            if ctor1 != ctor2 || fields1.len() != fields2.len() {
                return Some(false);
            }
            for (lhs, rhs) in fields1.iter().zip(fields2.iter()) {
                if !smt_values_equal(lhs, rhs)? {
                    return Some(false);
                }
            }
            Some(true)
        }
        (SmtValue::Opaque(x), SmtValue::Opaque(y)) => {
            if x == y {
                Some(true)
            } else {
                None
            }
        }
        (SmtValue::Opaque(_), _) | (_, SmtValue::Opaque(_)) => None,

        // Cross-sort Bool/Int: coerce Bool → Int (true=1, false=0)
        (SmtValue::Bool(b_val), SmtValue::Int(i_val))
        | (SmtValue::Int(i_val), SmtValue::Bool(b_val)) => {
            Some(*i_val == if *b_val { 1 } else { 0 })
        }

        // Cross-sort Bool/Real: coerce Bool → Real (true=1, false=0)
        (SmtValue::Bool(b_val), SmtValue::Real(r_val))
        | (SmtValue::Real(r_val), SmtValue::Bool(b_val)) => {
            use num_traits::{One, Zero};
            if *b_val {
                Some(r_val.is_one())
            } else {
                Some(r_val.is_zero())
            }
        }

        // Array equality: two arrays are equal iff they agree on all indices.
        // For finite representations we check structural equivalence (#6047).
        (SmtValue::ConstArray(d1), SmtValue::ConstArray(d2)) => smt_values_equal(d1, d2),
        (
            SmtValue::ArrayMap {
                default: d1,
                entries: e1,
            },
            SmtValue::ArrayMap {
                default: d2,
                entries: e2,
            },
        ) => {
            if !smt_values_equal(d1, d2)? {
                return Some(false);
            }
            // Compare the observable value at every explicit index from either
            // side, respecting last-store-wins semantics for duplicate writes.
            for (k, _) in e1.iter().chain(e2.iter()) {
                let lhs = array_lookup(d1.as_ref(), e1, k)?;
                let rhs = array_lookup(d2.as_ref(), e2, k)?;
                if !smt_values_equal(lhs, rhs)? {
                    return Some(false);
                }
            }
            Some(true)
        }
        (
            SmtValue::ConstArray(d),
            SmtValue::ArrayMap {
                default: d2,
                entries,
            },
        )
        | (
            SmtValue::ArrayMap {
                default: d2,
                entries,
            },
            SmtValue::ConstArray(d),
        ) => {
            if !smt_values_equal(d, d2)? {
                return Some(false);
            }
            // All observable explicit indices must agree with the const default.
            for (k, _) in entries {
                let observed = array_lookup(d2.as_ref(), entries, k)?;
                if !smt_values_equal(observed, d)? {
                    return Some(false);
                }
            }
            Some(true)
        }

        // All other cross-sort pairs are never equal
        _ => Some(false),
    }
}

/// Look up an index in an array value.
///
/// Walks the store chain (represented by `ArrayMap.entries`) to find the
/// matching index. Falls back to the default value for `ConstArray` or
/// `ArrayMap.default`.
pub(crate) fn eval_array_select(arr: &SmtValue, idx: &SmtValue) -> Option<SmtValue> {
    match arr {
        SmtValue::ConstArray(default) => Some(default.as_ref().clone()),
        SmtValue::ArrayMap { default, entries } => {
            // Search entries in reverse order (last store wins).
            for (k, v) in entries.iter().rev() {
                match smt_values_equal(k, idx) {
                    Some(true) => return Some(v.clone()),
                    Some(false) => {}
                    None => return None,
                }
            }
            Some(default.as_ref().clone())
        }
        _ => None,
    }
}

/// Insert/overwrite an entry in an array value, producing a new array.
pub(in crate::expr) fn eval_array_store(arr: SmtValue, idx: SmtValue, val: SmtValue) -> SmtValue {
    match arr {
        SmtValue::ConstArray(default) => SmtValue::ArrayMap {
            default,
            entries: vec![(idx, val)],
        },
        SmtValue::ArrayMap {
            default,
            mut entries,
        } => {
            // Remove any existing entry with the same index.
            entries.retain(|(k, _)| !matches!(smt_values_equal(k, &idx), Some(true)));
            entries.push((idx, val));
            SmtValue::ArrayMap { default, entries }
        }
        // If arr is not an array value, wrap as ArrayMap with arr as an opaque
        // default (lossy but sound for verification: select on unknown index
        // will return the opaque default → Indeterminate on type mismatch).
        _ => SmtValue::ArrayMap {
            default: Box::new(arr),
            entries: vec![(idx, val)],
        },
    }
}

/// Evaluate an integer-sorted expression to an `i128`, reading model values.
///
/// i128-lockstep: `ChcExpr::Int` now carries `i128` and [`evaluate_expr`]
/// itself folds integer arithmetic with checked `i128` operations, so this is
/// a thin adapter that delegates to the single canonical evaluator and accepts
/// only a concrete `SmtValue::Int` (fail-closed `None` for anything else —
/// missing vars, non-integer sorts, or beyond-i128 overflow during
/// evaluation). It exists so integer comparisons keep one shared entry point
/// (`eval_int_cmp`) as before the widening.
pub(super) fn eval_int_i128(expr: &ChcExpr, model: &FxHashMap<String, SmtValue>) -> Option<i128> {
    match evaluate_expr(expr, model)? {
        SmtValue::Int(n) => Some(n),
        _ => None,
    }
}

/// SMT-LIB Euclidean division on `BigInt`: unique `q` with `a = q*b + r`,
/// `0 <= r < |b|`.
///
/// Mirrors `i128::checked_div_euclid` (used by [`evaluate_expr`]'s `Div` arm)
/// exactly: truncating quotient, adjusted by 1 when the truncating remainder
/// is negative. Divisor must be non-zero (callers handle the SMT-LIB
/// `(div x 0) = 0` total case first, byte-for-byte with `evaluate_expr`).
fn big_div_euclid(a: &BigInt, b: &BigInt) -> BigInt {
    use num_traits::Signed;
    let q = a / b;
    let r = a % b;
    if r.is_negative() {
        if b.is_positive() {
            q - 1_i32
        } else {
            q + 1_i32
        }
    } else {
        q
    }
}

/// SMT-LIB Euclidean remainder on `BigInt`: always non-negative.
///
/// Mirrors `i128::checked_rem_euclid` exactly. Divisor must be non-zero
/// (callers handle the SMT-LIB `(mod x 0) = x` total case first).
fn big_rem_euclid(a: &BigInt, b: &BigInt) -> BigInt {
    use num_traits::Signed;
    let r = a % b;
    if r.is_negative() {
        r + b.abs()
    } else {
        r
    }
}

/// Exact BigInt evaluator for integer-sorted expressions (Phase-2 escape).
///
/// Structural recursion over EXACTLY the integer grammar [`evaluate_expr`]
/// handles — `Int`, `Var` (accepting both `SmtValue::Int` and
/// `SmtValue::BigInt` model values), n-ary `Add`/`Sub`/`Mul`, `Neg`,
/// `Div`/`Mod` with the same SMT-LIB total semantics (`(div x 0) = 0`,
/// `(mod x 0) = x`, Euclidean), `Ite` (condition decided by
/// [`evaluate_expr`]), integer-valued array `Select`, and `Bv2Nat`
/// (u128 → BigInt, always exact). Everything else abstains with `None`
/// (fail-closed), same as the i128 lane.
///
/// This folds the parser's Horner base-10^9 encodings of beyond-i128
/// literals exactly, and lets beyond-i128 model witnesses be validated
/// instead of degrading the verdict to Unknown. It must stay in lockstep
/// with `evaluate_expr`'s integer arms: a semantics split between the fast
/// i128 lane and this slow lane would be a soundness bug (guarded by the
/// `bigint_escape` lockstep property test).
pub(crate) fn eval_int_big(expr: &ChcExpr, model: &FxHashMap<String, SmtValue>) -> Option<BigInt> {
    maybe_grow_expr_stack(|| {
        ExprDepthGuard::check()?;
        match expr {
            ChcExpr::Int(n) => Some(BigInt::from(*n)),
            ChcExpr::Var(v) => match model.get(&v.name)? {
                SmtValue::Int(n) => Some(BigInt::from(*n)),
                SmtValue::BigInt(b) => Some(b.as_ref().clone()),
                _ => None,
            },
            ChcExpr::Op(ChcOp::Add, args) => {
                let mut sum = BigInt::from(0);
                for arg in args {
                    sum += eval_int_big(arg, model)?;
                }
                Some(sum)
            }
            ChcExpr::Op(ChcOp::Sub, args) if !args.is_empty() => {
                let first = eval_int_big(&args[0], model)?;
                if args.len() == 1 {
                    return Some(-first);
                }
                let mut result = first;
                for arg in &args[1..] {
                    result -= eval_int_big(arg, model)?;
                }
                Some(result)
            }
            ChcExpr::Op(ChcOp::Mul, args) => {
                let mut product = BigInt::from(1);
                for arg in args {
                    product *= eval_int_big(arg, model)?;
                }
                Some(product)
            }
            ChcExpr::Op(ChcOp::Neg, args) if args.len() == 1 => {
                Some(-eval_int_big(&args[0], model)?)
            }
            ChcExpr::Op(ChcOp::Div, args) if args.len() == 2 => {
                use num_traits::Zero;
                let a = eval_int_big(&args[0], model)?;
                let b = eval_int_big(&args[1], model)?;
                if b.is_zero() {
                    // SMT-LIB total semantics: (div x 0) = 0.
                    // Must match evaluate_expr's Div arm and eliminate_mod.
                    Some(BigInt::from(0))
                } else {
                    Some(big_div_euclid(&a, &b))
                }
            }
            ChcExpr::Op(ChcOp::Mod, args) if args.len() == 2 => {
                use num_traits::Zero;
                let a = eval_int_big(&args[0], model)?;
                let b = eval_int_big(&args[1], model)?;
                if b.is_zero() {
                    // SMT-LIB total semantics: (mod x 0) = x.
                    // Must match evaluate_expr's Mod arm and eliminate_mod.
                    Some(a)
                } else {
                    Some(big_rem_euclid(&a, &b))
                }
            }
            ChcExpr::Op(ChcOp::Ite, args) if args.len() == 3 => {
                match evaluate_expr(&args[0], model)? {
                    SmtValue::Bool(true) => eval_int_big(&args[1], model),
                    SmtValue::Bool(false) => eval_int_big(&args[2], model),
                    _ => None,
                }
            }
            ChcExpr::Op(ChcOp::Select, args) if args.len() == 2 => {
                // `evaluate_expr` already implements exact array lookup
                // (including store chains and last-write-wins). Convert only
                // a concrete integer result into this lane; other element
                // sorts remain indeterminate. This is needed when the other
                // side of a comparison overflows the i128 fast lane: a small
                // integer select must still participate in the exact retry.
                match evaluate_expr(expr, model)? {
                    SmtValue::Int(n) => Some(BigInt::from(n)),
                    SmtValue::BigInt(b) => Some(b.as_ref().clone()),
                    _ => None,
                }
            }
            ChcExpr::Op(ChcOp::Bv2Nat, args) if args.len() == 1 => {
                let (v, _w) = eval_bv_val(&args[0], model)?;
                // u128 → BigInt is always exact (no fail-closed skip needed).
                Some(BigInt::from(v))
            }
            _ => None,
        }
    })
}

/// Helper: evaluate an integer comparison.
///
/// Operands are evaluated in the widened `i128` domain first (see
/// [`eval_int_i128`]); when either side abstains (beyond-i128 overflow
/// mid-fold, or a beyond-i128 `SmtValue::BigInt` model value), BOTH sides
/// are retried through the exact [`eval_int_big`] lane and compared as
/// BigInts. The comparison is expressed over `Ordering` so the same
/// predicate decides both lanes identically. A genuine indeterminate
/// (missing variable, non-integer subterm) still returns `None`.
pub(super) fn eval_int_cmp(
    lhs: &ChcExpr,
    rhs: &ChcExpr,
    model: &FxHashMap<String, SmtValue>,
    cmp: impl Fn(std::cmp::Ordering) -> bool,
) -> Option<SmtValue> {
    if let (Some(a), Some(b)) = (eval_int_i128(lhs, model), eval_int_i128(rhs, model)) {
        return Some(SmtValue::Bool(cmp(a.cmp(&b))));
    }
    if let (Some(a), Some(b)) = (eval_int_big(lhs, model), eval_int_big(rhs, model)) {
        return Some(SmtValue::Bool(cmp(a.cmp(&b))));
    }
    // Real (LRA) lane: reached only when BOTH integer lanes abstain — i.e. an
    // operand is Real-sorted (or a var is missing, in which case this lane
    // also abstains). Exact rational comparison; never runs for pure-integer
    // atoms, so integer semantics are byte-for-byte unchanged.
    if real_eval_enabled() {
        if let (Some(a), Some(b)) = (eval_real_big(lhs, model), eval_real_big(rhs, model)) {
            return Some(SmtValue::Bool(cmp(a.cmp(&b))));
        }
    }
    None
}
