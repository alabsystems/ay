// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Z3-compatible algebraic-number (`z3_algebraic.h`) and polynomial
//! (`z3_polynomial.h`) C API — REAL over the exact real-algebraic engine
//! ([`ay_nra::rcf_api`] over `RealScalar`).
//!
//! AY's `Real` AST encodes only `BigRational`, so a genuinely irrational
//! algebraic result (e.g. √2 from `Z3_algebraic_root`) is carried by an
//! [`ALGEBRAIC_AST_TAG`]-tagged, context-salted `Z3_ast` handle backed by an
//! exact `RealScalar` in `Z3Context::algebraic_values`; rational results keep
//! flowing through the ordinary numeral-AST path. Every operand is read via
//! [`ast_as_scalar`]
//! (rational numeral OR algebraic handle) and every result interned via
//! [`scalar_to_ast`], so:
//!
//! - Arithmetic (`add`/`sub`/`mul`/`div`/`power`), sign / predicate queries,
//!   ordering, the value predicate, the defining polynomial, the root index,
//!   and `root` (`a^(1/k)`) are all computed exactly over rationals AND real
//!   algebraics — equality/sign GCD-certified, orderings by exact interval
//!   separation, never numeric proximity.
//! - `eval` (sign of `p(a[0..n))`) is exact when the substitution reduces to a
//!   rational; otherwise it diverges rather than guess.
//! - `roots` and `subresultants` are REAL for univariate polynomial terms with
//!   numeral coefficients: an AST→coefficient-vector extractor
//!   ([`term_to_poly`]) feeds the exact engines (`ay_nra::rcf_api::real_roots`
//!   Sturm isolation; exact Sylvester–Habicht `psc` determinants replicating
//!   libz3's `psc_chain` conventions, cross-checked value-for-value).
//!   Non-polynomial / multivariate-parametric input stays an honest
//!   `Z3_INVALID_ARG` + empty vector, never a fabricated value.
//!
//! Every function calling the solver is wrapped in `catch_unwind` via the
//! `ffi_guard_*` helpers (#6192).

use std::cmp::Ordering;
use std::ffi::{c_int, c_uint};

use ay_dpll::api::{Sort, Term};
use ay_nra::{rcf_api, RealScalar};
use num_bigint::{BigInt, Sign};
use num_rational::BigRational;

use super::{
    cache_ast_vector, checked_ast_to_term, decode_indexed_ast, encode_indexed_ast,
    ffi_count_within_limit, ffi_guard_ast, ffi_guard_int, ffi_guard_ptr, ffi_guard_uint,
    record_ast_sort, term_to_ast, Z3Context, Z3_ast, Z3_ast_vector, Z3_context, ALGEBRAIC_AST_TAG,
    HANDLE_TAG_MASK, MAX_FFI_ALGEBRAIC_EXPONENT, MAX_FFI_CONTAINER_ELEMENTS, Z3_INVALID_ARG,
};

// ============================================================================
// Rational bridge (exact numeral parsing).
// ============================================================================

/// Parse a numeral string (`"n"` for an integer, `"n/d"` for a rational) into a
/// reduced `(numerator, denominator)` pair with a strictly positive denominator.
/// Returns `None` on a malformed string or a zero denominator.
fn parse_rational(s: &str) -> Option<(BigInt, BigInt)> {
    let (mut num, mut den) = if let Some((n, d)) = s.split_once('/') {
        (
            n.trim().parse::<BigInt>().ok()?,
            d.trim().parse::<BigInt>().ok()?,
        )
    } else {
        (s.trim().parse::<BigInt>().ok()?, BigInt::from(1))
    };
    match den.sign() {
        Sign::NoSign => return None, // zero denominator
        Sign::Minus => {
            num = -num;
            den = -den;
        }
        Sign::Plus => {}
    }
    Some((num, den))
}

/// Interpret a `Term` as an exact rational, but only when it is a numeral of
/// `Int`/`Real` sort. Returns `None` for non-values.
fn term_rational(ctx: &Z3Context, t: Term) -> Option<(BigInt, BigInt)> {
    if !ctx.solver.is_numeral(t) {
        return None;
    }
    match ctx.solver.sort_of(t) {
        Sort::Int | Sort::Real => {}
        _ => return None,
    }
    parse_rational(&ctx.solver.numeral_string(t)?)
}

/// Interpret a `Z3_ast` as an exact rational algebraic value, or `None`.
fn numeral_as_rational(ctx: &Z3Context, a: Z3_ast) -> Option<(BigInt, BigInt)> {
    term_rational(ctx, checked_ast_to_term(ctx, a)?)
}

/// Sign of a rational (its numerator, denominator being positive) as `1/0/-1`.
fn signum_int(num: &BigInt) -> c_int {
    match num.sign() {
        Sign::Plus => 1,
        Sign::NoSign => 0,
        Sign::Minus => -1,
    }
}

// ============================================================================
// Algebraic-number AST bridge (tagged handles ↔ exact RealScalar).
// ============================================================================

/// Read a `Z3_ast` as an exact [`RealScalar`]: an algebraic-tagged handle yields
/// the stored value; an ordinary `Int`/`Real` numeral yields a rational. `None`
/// for anything else (free variable, non-numeric, dangling index, or a handle
/// owned by another context).
pub(crate) fn ast_as_scalar(ctx: &Z3Context, a: Z3_ast) -> Option<RealScalar> {
    if a & HANDLE_TAG_MASK == ALGEBRAIC_AST_TAG {
        let idx = decode_indexed_ast(ctx, a, ALGEBRAIC_AST_TAG)?;
        return ctx.algebraic_values.get(idx).cloned();
    }
    let (num, den) = numeral_as_rational(ctx, a)?;
    Some(RealScalar::Rational(BigRational::new(num, den)))
}

/// Intern an exact [`RealScalar`] as a `Z3_ast`: a rational (after
/// canonicalization) via the ordinary `Real` numeral path; a genuine irrational
/// algebraic via an [`ALGEBRAIC_AST_TAG`] handle backed by
/// `Z3Context::algebraic_values`. Returns `0` on a refinement cap or exhausted
/// tagged-handle index space — the caller sets the error on `0`.
pub(crate) fn scalar_to_ast(ctx: &mut Z3Context, s: RealScalar) -> Z3_ast {
    match rcf_api::canonicalize(&s) {
        Some(RealScalar::Rational(r)) => {
            let term = ctx.solver.rational_const_bigint(r.numer(), r.denom());
            let ast = term_to_ast(ctx, term);
            record_ast_sort(ctx, ast, Sort::Real);
            ast
        }
        Some(alg) => {
            let Some(ast) = encode_indexed_ast(ctx, ALGEBRAIC_AST_TAG, ctx.algebraic_values.len())
            else {
                return 0;
            };
            ctx.algebraic_values.push(alg);
            ast
        }
        None => 0,
    }
}

/// Read both operands as exact scalars, or `None` if either is not a value.
fn two_scalars(ctx: &Z3Context, a: Z3_ast, b: Z3_ast) -> Option<(RealScalar, RealScalar)> {
    Some((ast_as_scalar(ctx, a)?, ast_as_scalar(ctx, b)?))
}

/// Record `Z3_INVALID_ARG` for a non-value operand.
fn set_not_value(ctx: &mut Z3Context, who: &str) {
    ctx.last_error = Z3_INVALID_ARG;
    ctx.error_msg = Some(format!(
        "{who}: operand is not an algebraic value (Z3_algebraic_is_value precondition violated)"
    ));
}

/// Record `Z3_INVALID_ARG` for an uncomputable (engine refinement cap) result.
fn set_uncomputable(ctx: &mut Z3Context, who: &str) {
    ctx.last_error = Z3_INVALID_ARG;
    ctx.error_msg = Some(format!(
        "{who}: not exactly computable (engine refinement cap) — fail-closed"
    ));
}

// ============================================================================
// Value predicate and sign queries.
// ============================================================================

/// Return `true` iff `a` is a usable algebraic value: an algebraic-tagged handle
/// or an `Int`/`Real` numeral.
///
/// # Safety
/// `c` must point to a live context that is not concurrently accessed for the
/// duration of this call.
#[no_mangle]
pub unsafe extern "C" fn Z3_algebraic_is_value(c: Z3_context, a: Z3_ast) -> bool {
    // SAFETY: `ffi_guard_int` null-checks `c` and catches panics; pure predicate.
    unsafe { ffi_guard_int(c, 0, |ctx| c_int::from(ast_as_scalar(ctx, a).is_some())) != 0 }
}

/// Sign predicate helper over the exact engine; non-value → `Z3_INVALID_ARG`.
///
/// # Safety
/// `c` valid or null.
unsafe fn algebraic_sign_pred(
    c: Z3_context,
    a: Z3_ast,
    who: &str,
    pred: impl FnOnce(i32) -> c_int,
) -> c_int {
    // SAFETY: `ffi_guard_int` null-checks `c` and catches panics.
    unsafe {
        ffi_guard_int(c, 0, |ctx| {
            let Some(s) = ast_as_scalar(ctx, a) else {
                set_not_value(ctx, who);
                return 0;
            };
            match rcf_api::sign(&s) {
                Some(sg) => pred(sg),
                None => {
                    set_uncomputable(ctx, who);
                    0
                }
            }
        })
    }
}

/// Return `1` if `a` is positive, `0` if zero, `-1` if negative.
///
/// # Safety
/// `c` must point to a live context that is not concurrently accessed for the
/// duration of this call.
#[no_mangle]
pub unsafe extern "C" fn Z3_algebraic_sign(c: Z3_context, a: Z3_ast) -> c_int {
    // SAFETY: the caller supplies a valid, exclusively accessed context;
    // `algebraic_sign_pred` rejects a non-algebraic operand before projection.
    unsafe { algebraic_sign_pred(c, a, "Z3_algebraic_sign", |s| s) }
}

/// Return `true` if `a` is positive.
///
/// # Safety
/// `c` must point to a live context that is not concurrently accessed for the
/// duration of this call.
#[no_mangle]
pub unsafe extern "C" fn Z3_algebraic_is_pos(c: Z3_context, a: Z3_ast) -> bool {
    // SAFETY: the caller supplies a valid, exclusively accessed context;
    // `algebraic_sign_pred` rejects a non-algebraic operand before this predicate.
    unsafe { algebraic_sign_pred(c, a, "Z3_algebraic_is_pos", |s| c_int::from(s > 0)) != 0 }
}

/// Return `true` if `a` is negative.
///
/// # Safety
/// `c` must point to a live context that is not concurrently accessed for the
/// duration of this call.
#[no_mangle]
pub unsafe extern "C" fn Z3_algebraic_is_neg(c: Z3_context, a: Z3_ast) -> bool {
    // SAFETY: the caller supplies a valid, exclusively accessed context;
    // `algebraic_sign_pred` rejects a non-algebraic operand before this predicate.
    unsafe { algebraic_sign_pred(c, a, "Z3_algebraic_is_neg", |s| c_int::from(s < 0)) != 0 }
}

/// Return `true` if `a` is zero.
///
/// # Safety
/// `c` must point to a live context that is not concurrently accessed for the
/// duration of this call.
#[no_mangle]
pub unsafe extern "C" fn Z3_algebraic_is_zero(c: Z3_context, a: Z3_ast) -> bool {
    // SAFETY: the caller supplies a valid, exclusively accessed context;
    // `algebraic_sign_pred` rejects a non-algebraic operand before this predicate.
    unsafe { algebraic_sign_pred(c, a, "Z3_algebraic_is_zero", |s| c_int::from(s == 0)) != 0 }
}

// ============================================================================
// Exact field arithmetic (rational + real-algebraic).
// ============================================================================

/// Compute a binary field operation over exact scalars and intern the result.
///
/// # Safety
/// Non-null `c` must point to a live context that is not concurrently accessed
/// for the duration of this call.
unsafe fn algebraic_binop(
    c: Z3_context,
    a: Z3_ast,
    b: Z3_ast,
    who: &str,
    op: impl FnOnce(&RealScalar, &RealScalar) -> Option<RealScalar>,
) -> Z3_ast {
    // SAFETY: `ffi_guard_ast` null-checks `c` and catches panics.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            let Some((x, y)) = two_scalars(ctx, a, b) else {
                set_not_value(ctx, who);
                return 0;
            };
            match op(&x, &y) {
                Some(r) => {
                    let ast = scalar_to_ast(ctx, r);
                    if ast == 0 {
                        set_uncomputable(ctx, who);
                    }
                    ast
                }
                None => {
                    set_uncomputable(ctx, who);
                    0
                }
            }
        })
    }
}

/// Return the exact value `a + b`.
///
/// # Safety
/// `c` must point to a live context that is not concurrently accessed for the
/// duration of this call.
#[no_mangle]
pub unsafe extern "C" fn Z3_algebraic_add(c: Z3_context, a: Z3_ast, b: Z3_ast) -> Z3_ast {
    // SAFETY: the caller grants exclusive access to the live context;
    // `algebraic_binop` rejects invalid operands before allocating the result.
    unsafe { algebraic_binop(c, a, b, "Z3_algebraic_add", |x, y| x.add(y)) }
}

/// Return the exact value `a - b`.
///
/// # Safety
/// `c` must point to a live context that is not concurrently accessed for the
/// duration of this call.
#[no_mangle]
pub unsafe extern "C" fn Z3_algebraic_sub(c: Z3_context, a: Z3_ast, b: Z3_ast) -> Z3_ast {
    // SAFETY: the caller grants exclusive access to the live context;
    // `algebraic_binop` rejects invalid operands before allocating the result.
    unsafe { algebraic_binop(c, a, b, "Z3_algebraic_sub", |x, y| x.add(&y.neg())) }
}

/// Return the exact value `a * b`.
///
/// # Safety
/// `c` must point to a live context that is not concurrently accessed for the
/// duration of this call.
#[no_mangle]
pub unsafe extern "C" fn Z3_algebraic_mul(c: Z3_context, a: Z3_ast, b: Z3_ast) -> Z3_ast {
    // SAFETY: the caller grants exclusive access to the live context;
    // `algebraic_binop` rejects invalid operands before allocating the result.
    unsafe { algebraic_binop(c, a, b, "Z3_algebraic_mul", |x, y| x.mul(y)) }
}

/// Return the exact value `a / b` (`Z3_INVALID_ARG` on a zero divisor).
///
/// # Safety
/// `c` must point to a live context that is not concurrently accessed for the
/// duration of this call.
#[no_mangle]
pub unsafe extern "C" fn Z3_algebraic_div(c: Z3_context, a: Z3_ast, b: Z3_ast) -> Z3_ast {
    // SAFETY: the caller grants exclusive access to the live context;
    // `algebraic_binop` rejects invalid operands before allocating the result.
    unsafe {
        algebraic_binop(c, a, b, "Z3_algebraic_div", |x, y| {
            y.recip().and_then(|iy| x.mul(&iy))
        })
    }
}

/// Return the exact value `a^k` (`k` unsigned; `k == 0` → `1`).
///
/// # Safety
/// `c` must point to a live context that is not concurrently accessed for the
/// duration of this call.
#[no_mangle]
pub unsafe extern "C" fn Z3_algebraic_power(c: Z3_context, a: Z3_ast, k: c_uint) -> Z3_ast {
    // SAFETY: `ffi_guard_ast` null-checks `c` and catches panics.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            if k > MAX_FFI_ALGEBRAIC_EXPONENT {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg = Some(format!(
                    "Z3_algebraic_power: exponent {k} exceeds the supported maximum {MAX_FFI_ALGEBRAIC_EXPONENT}"
                ));
                return 0;
            }
            let Some(x) = ast_as_scalar(ctx, a) else {
                set_not_value(ctx, "Z3_algebraic_power");
                return 0;
            };
            let mut acc = RealScalar::Rational(BigRational::from_integer(BigInt::from(1)));
            for _ in 0..k {
                match acc.mul(&x) {
                    Some(v) => acc = v,
                    None => {
                        set_uncomputable(ctx, "Z3_algebraic_power");
                        return 0;
                    }
                }
            }
            let ast = scalar_to_ast(ctx, acc);
            if ast == 0 {
                set_uncomputable(ctx, "Z3_algebraic_power");
            }
            ast
        })
    }
}

// ============================================================================
// Exact ordering (rational + real-algebraic).
// ============================================================================

/// Exact comparison predicate; non-value → `Z3_INVALID_ARG` + false.
///
/// # Safety
/// Non-null `c` must point to a live context that is not concurrently accessed
/// for the duration of this call.
unsafe fn algebraic_cmp(
    c: Z3_context,
    a: Z3_ast,
    b: Z3_ast,
    who: &str,
    pred: impl FnOnce(Ordering) -> bool,
) -> bool {
    // SAFETY: `ffi_guard_int` null-checks `c` and catches panics.
    unsafe {
        ffi_guard_int(c, 0, |ctx| {
            let Some((x, y)) = two_scalars(ctx, a, b) else {
                set_not_value(ctx, who);
                return 0;
            };
            match x.cmp_exact(&y) {
                Some(ord) => c_int::from(pred(ord)),
                None => {
                    set_uncomputable(ctx, who);
                    0
                }
            }
        }) != 0
    }
}

/// Return `true` if `a < b`.
///
/// # Safety
/// `c` must point to a live context that is not concurrently accessed for the
/// duration of this call.
#[no_mangle]
pub unsafe extern "C" fn Z3_algebraic_lt(c: Z3_context, a: Z3_ast, b: Z3_ast) -> bool {
    // SAFETY: the caller supplies a valid, exclusively accessed context;
    // `algebraic_cmp` rejects non-algebraic operands before this predicate.
    unsafe { algebraic_cmp(c, a, b, "Z3_algebraic_lt", |o| o == Ordering::Less) }
}

/// Return `true` if `a > b`.
///
/// # Safety
/// `c` must point to a live context that is not concurrently accessed for the
/// duration of this call.
#[no_mangle]
pub unsafe extern "C" fn Z3_algebraic_gt(c: Z3_context, a: Z3_ast, b: Z3_ast) -> bool {
    // SAFETY: the caller supplies a valid, exclusively accessed context;
    // `algebraic_cmp` rejects non-algebraic operands before this predicate.
    unsafe { algebraic_cmp(c, a, b, "Z3_algebraic_gt", |o| o == Ordering::Greater) }
}

/// Return `true` if `a <= b`.
///
/// # Safety
/// `c` must point to a live context that is not concurrently accessed for the
/// duration of this call.
#[no_mangle]
pub unsafe extern "C" fn Z3_algebraic_le(c: Z3_context, a: Z3_ast, b: Z3_ast) -> bool {
    // SAFETY: the caller supplies a valid, exclusively accessed context;
    // `algebraic_cmp` rejects non-algebraic operands before this predicate.
    unsafe { algebraic_cmp(c, a, b, "Z3_algebraic_le", |o| o != Ordering::Greater) }
}

/// Return `true` if `a >= b`.
///
/// # Safety
/// `c` must point to a live context that is not concurrently accessed for the
/// duration of this call.
#[no_mangle]
pub unsafe extern "C" fn Z3_algebraic_ge(c: Z3_context, a: Z3_ast, b: Z3_ast) -> bool {
    // SAFETY: the caller supplies a valid, exclusively accessed context;
    // `algebraic_cmp` rejects non-algebraic operands before this predicate.
    unsafe { algebraic_cmp(c, a, b, "Z3_algebraic_ge", |o| o != Ordering::Less) }
}

/// Return `true` if `a == b` (GCD-certified equality).
///
/// # Safety
/// `c` must point to a live context that is not concurrently accessed for the
/// duration of this call.
#[no_mangle]
pub unsafe extern "C" fn Z3_algebraic_eq(c: Z3_context, a: Z3_ast, b: Z3_ast) -> bool {
    // SAFETY: the caller supplies a valid, exclusively accessed context;
    // `algebraic_cmp` rejects non-algebraic operands before this predicate.
    unsafe { algebraic_cmp(c, a, b, "Z3_algebraic_eq", |o| o == Ordering::Equal) }
}

/// Return `true` if `a != b`.
///
/// # Safety
/// `c` must point to a live context that is not concurrently accessed for the
/// duration of this call.
#[no_mangle]
pub unsafe extern "C" fn Z3_algebraic_neq(c: Z3_context, a: Z3_ast, b: Z3_ast) -> bool {
    // SAFETY: the caller supplies a valid, exclusively accessed context;
    // `algebraic_cmp` rejects non-algebraic operands before this predicate.
    unsafe { algebraic_cmp(c, a, b, "Z3_algebraic_neq", |o| o != Ordering::Equal) }
}

// ============================================================================
// AST → univariate-polynomial extractor (backs `Z3_algebraic_roots` and
// `Z3_polynomial_subresultants`).
// ============================================================================

/// Degree cap for the extractor's exact polynomial arithmetic. Anything larger
/// fails CLOSED (`Z3_INVALID_ARG`) — never an approximated polynomial.
const MAX_POLY_DEGREE: usize = 4096;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum PscResourceLimit {
    MatrixEntries,
    AggregateEntries,
    EliminationWork,
}

/// Preflight every Sylvester–Habicht matrix in a PSC chain.
///
/// `rational_det` stores `size²` exact rationals and performs O(`size³`)
/// elimination work for each coefficient. Degree alone does not bound either
/// resource: a degree-4096 pair would try to allocate tens of millions of
/// `BigRational`s for its first matrix and repeat that work thousands of times.
/// Keep both the largest/aggregate matrix footprint and an overflow-safe cubic
/// work estimate within explicit limits before constructing any matrix.
fn psc_resource_preflight(
    m: usize,
    n: usize,
    entry_limit: usize,
    work_limit: usize,
) -> Result<(), PscResourceLimit> {
    let mut aggregate_entries = 0usize;
    let mut aggregate_work = 0usize;
    for j in 0..n {
        let twice_j = j.checked_mul(2).ok_or(PscResourceLimit::MatrixEntries)?;
        let size = m
            .checked_add(n)
            .and_then(|sum| sum.checked_sub(twice_j))
            .ok_or(PscResourceLimit::MatrixEntries)?;
        let entries = size
            .checked_mul(size)
            .filter(|entries| *entries <= entry_limit)
            .ok_or(PscResourceLimit::MatrixEntries)?;
        aggregate_entries = aggregate_entries
            .checked_add(entries)
            .filter(|entries| *entries <= entry_limit)
            .ok_or(PscResourceLimit::AggregateEntries)?;
        let work = entries
            .checked_mul(size)
            .ok_or(PscResourceLimit::EliminationWork)?;
        aggregate_work = aggregate_work
            .checked_add(work)
            .filter(|work| *work <= work_limit)
            .ok_or(PscResourceLimit::EliminationWork)?;
    }
    Ok(())
}

/// Trim trailing zero coefficients (the zero polynomial becomes `[]`).
fn poly_trim(mut p: Vec<BigRational>) -> Vec<BigRational> {
    while p.last().is_some_and(num_traits::Zero::is_zero) {
        p.pop();
    }
    p
}

/// `deg(p)`, with the zero polynomial mapped to `None`.
fn poly_degree(p: &[BigRational]) -> Option<usize> {
    p.len().checked_sub(1)
}

fn poly_add(a: &[BigRational], b: &[BigRational]) -> Vec<BigRational> {
    let mut out = vec![BigRational::from_integer(BigInt::from(0)); a.len().max(b.len())];
    for (i, c) in a.iter().enumerate() {
        out[i] += c;
    }
    for (i, c) in b.iter().enumerate() {
        out[i] += c;
    }
    poly_trim(out)
}

fn poly_neg(a: &[BigRational]) -> Vec<BigRational> {
    a.iter().map(|c| -c).collect()
}

fn poly_mul(a: &[BigRational], b: &[BigRational]) -> Option<Vec<BigRational>> {
    if a.is_empty() || b.is_empty() {
        return Some(Vec::new()); // zero polynomial
    }
    let deg = (a.len() - 1) + (b.len() - 1);
    if deg > MAX_POLY_DEGREE {
        return None; // fail closed on the degree cap
    }
    let mut out = vec![BigRational::from_integer(BigInt::from(0)); deg + 1];
    for (i, ca) in a.iter().enumerate() {
        for (j, cb) in b.iter().enumerate() {
            out[i + j] += ca * cb;
        }
    }
    Some(poly_trim(out))
}

fn poly_pow(a: &[BigRational], k: u64) -> Option<Vec<BigRational>> {
    let mut acc = vec![BigRational::from_integer(BigInt::from(1))];
    for _ in 0..k {
        acc = poly_mul(&acc, a)?;
    }
    Some(acc)
}

/// Collect the DISTINCT variable terms of `t` (DFS). `None` when the term
/// contains a binder/let (not a polynomial candidate).
fn collect_term_vars(ctx: &Z3Context, t: Term) -> Option<Vec<Term>> {
    use ay_dpll::api::TermKind;
    let mut out: Vec<Term> = Vec::new();
    let mut seen: std::collections::HashSet<Term> = std::collections::HashSet::new();
    let mut stack = vec![t];
    let mut visited: std::collections::HashSet<Term> = std::collections::HashSet::new();
    while let Some(cur) = stack.pop() {
        if !visited.insert(cur) {
            continue;
        }
        match ctx.solver.term_kind(cur) {
            TermKind::Var { .. } => {
                if seen.insert(cur) {
                    out.push(cur);
                }
            }
            TermKind::Forall | TermKind::Exists | TermKind::Let => return None,
            _ => stack.extend(ctx.solver.term_children(cur)),
        }
    }
    Some(out)
}

/// Walk `t` into a dense coefficient vector (low→high) of a univariate
/// polynomial in `x` with exact rational coefficients. Supported node kinds:
/// `Int`/`Real` numerals, the variable `x`, `+`, `-` (unary and n-ary), `*`,
/// `^` (non-negative integer numeral exponent), `/` (rational numeral
/// divisor), and the identity coercion `to_real`. Anything else — including
/// any OTHER variable (multivariate input) — returns `None` (the caller sets
/// `Z3_INVALID_ARG`; never an approximated polynomial).
fn term_to_poly(ctx: &Z3Context, t: Term, x: Term) -> Option<Vec<BigRational>> {
    use ay_dpll::api::TermKind;
    if t == x {
        return Some(vec![
            BigRational::from_integer(BigInt::from(0)),
            BigRational::from_integer(BigInt::from(1)),
        ]);
    }
    match ctx.solver.term_kind(t) {
        TermKind::Const => {
            let (num, den) = term_rational(ctx, t)?;
            Some(poly_trim(vec![BigRational::new(num, den)]))
        }
        TermKind::Var { .. } => None, // a DIFFERENT variable: not univariate in x
        TermKind::App { name, num_args } => {
            let args = ctx.solver.term_children(t);
            match name.as_str() {
                "+" => {
                    let mut acc: Vec<BigRational> = Vec::new();
                    for &a in &args {
                        acc = poly_add(&acc, &term_to_poly(ctx, a, x)?);
                    }
                    Some(acc)
                }
                "-" if num_args == 1 => Some(poly_neg(&term_to_poly(ctx, args[0], x)?)),
                "-" if num_args >= 2 => {
                    let mut acc = term_to_poly(ctx, args[0], x)?;
                    for &a in &args[1..] {
                        acc = poly_add(&acc, &poly_neg(&term_to_poly(ctx, a, x)?));
                    }
                    Some(acc)
                }
                "*" => {
                    let mut acc = vec![BigRational::from_integer(BigInt::from(1))];
                    for &a in &args {
                        acc = poly_mul(&acc, &term_to_poly(ctx, a, x)?)?;
                    }
                    Some(acc)
                }
                "^" if num_args == 2 => {
                    let base = term_to_poly(ctx, args[0], x)?;
                    let (en, ed) = term_rational(ctx, args[1])?;
                    if ed != BigInt::from(1) || en.sign() == Sign::Minus {
                        return None; // only non-negative integer exponents
                    }
                    let k = u64::try_from(&en).ok()?;
                    if k as usize > MAX_POLY_DEGREE {
                        return None;
                    }
                    poly_pow(&base, k)
                }
                "/" if num_args == 2 => {
                    let numer = term_to_poly(ctx, args[0], x)?;
                    let (dn, dd) = term_rational(ctx, args[1])?;
                    if dn.sign() == Sign::NoSign {
                        return None; // division by zero: not a polynomial
                    }
                    let inv = BigRational::new(dd, dn);
                    Some(poly_trim(numer.iter().map(|c| c * &inv).collect()))
                }
                // Int→Real coercion is the identity on the polynomial value.
                "to_real" if num_args == 1 => term_to_poly(ctx, args[0], x),
                _ => None,
            }
        }
        _ => None,
    }
}

/// Exact determinant of a square `BigRational` matrix (Gaussian elimination
/// with row pivoting). `None` never occurs for well-formed input; kept total.
fn rational_det(mut m: Vec<Vec<BigRational>>) -> BigRational {
    use num_traits::Zero;
    let n = m.len();
    let zero = BigRational::from_integer(BigInt::from(0));
    let mut det = BigRational::from_integer(BigInt::from(1));
    let mut neg = false;
    for col in 0..n {
        let Some(pivot_row) = (col..n).find(|&r| !m[r][col].is_zero()) else {
            return zero;
        };
        if pivot_row != col {
            m.swap(pivot_row, col);
            neg = !neg;
        }
        let pivot = m[col][col].clone();
        det *= &pivot;
        for r in (col + 1)..n {
            if m[r][col].is_zero() {
                continue;
            }
            let factor = &m[r][col] / &pivot;
            for k in col..n {
                let sub = &factor * &m[col][k];
                m[r][k] -= sub;
            }
        }
    }
    if neg {
        -det
    } else {
        det
    }
}

/// The `j`-th principal subresultant coefficient of `p` (degree `m`) and `q`
/// (degree `n`), `m >= n > j`, via the Sylvester–Habicht determinant: the
/// `(m+n-2j)`-square matrix whose rows are the coefficients of
/// `x^{n-j-1}·p, …, x^0·p` then `x^{m-j-1}·q, …, x^0·q` on the column basis
/// `x^{m+n-j-1}, …, x^j`. Verified against libz3 4.16's `psc_chain` on
/// unequal-degree, equal-degree, swapped and zero-entry cases.
fn psc_coefficient(p: &[BigRational], q: &[BigRational], j: usize) -> BigRational {
    let zero = BigRational::from_integer(BigInt::from(0));
    let m = p.len() - 1;
    let n = q.len() - 1;
    let size = m + n - 2 * j;
    let top_degree = m + n - j - 1;
    let mut rows: Vec<Vec<BigRational>> = Vec::with_capacity(size);
    // coefficient of x^d in x^k · f  =  f[d - k]
    let mut push_shifts = |f: &[BigRational], count: usize| {
        for k in (0..count).rev() {
            let mut row = Vec::with_capacity(size);
            for c in 0..size {
                let d = top_degree - c; // column c carries degree top_degree - c
                let idx = d.checked_sub(k);
                row.push(match idx {
                    Some(i) if i < f.len() => f[i].clone(),
                    _ => zero.clone(),
                });
            }
            rows.push(row);
        }
    };
    push_shifts(p, n - j);
    push_shifts(q, m - j);
    rational_det(rows)
}

// ============================================================================
// Roots and polynomial evaluation.
// ============================================================================

/// Return `a^(1/k)` as an exact algebraic value.
///
/// REAL: the unique real k-th root of `a` (the non-negative one for even `k`,
/// `a > 0`). DIVERGENCE (`Z3_INVALID_ARG` + null): a non-value operand, `k == 0`,
/// an even root of a negative `a` (no real root), or an engine cap.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_algebraic_root(c: Z3_context, a: Z3_ast, k: c_uint) -> Z3_ast {
    // SAFETY: `ffi_guard_ast` null-checks `c` and catches panics.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            if k > MAX_FFI_ALGEBRAIC_EXPONENT {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg = Some(format!(
                    "Z3_algebraic_root: degree {k} exceeds the supported maximum {MAX_FFI_ALGEBRAIC_EXPONENT}"
                ));
                return 0;
            }
            let Some(x) = ast_as_scalar(ctx, a) else {
                set_not_value(ctx, "Z3_algebraic_root");
                return 0;
            };
            match rcf_api::nth_root(&x, k) {
                Some(r) => {
                    let ast = scalar_to_ast(ctx, r);
                    if ast == 0 {
                        set_uncomputable(ctx, "Z3_algebraic_root");
                    }
                    ast
                }
                None => {
                    ctx.last_error = Z3_INVALID_ARG;
                    ctx.error_msg = Some(
                        "Z3_algebraic_root: no real k-th root (k == 0, or even root of a negative), or engine cap".to_string(),
                    );
                    0
                }
            }
        })
    }
}

/// Return the real roots of the univariate polynomial `p(a[0], ..., a[n-1], x)`.
///
/// REAL: the rational arguments are substituted for the bound variables
/// (`__db{i}`, i < n — the same convention as [`Z3_algebraic_eval`] and Z3's
/// own `(:var i)` inputs), the residual is walked into an exact coefficient
/// vector (see [`term_to_poly`]), and the ascending real roots come from the
/// exact engine [`rcf_api::real_roots`] (Sturm isolation) — rational roots as
/// `Real` numerals, irrational ones as exact algebraic handles (`root-obj`),
/// exactly matching libz3's output convention (cross-checked: `x^2-2` →
/// `(root-obj (+ (^ x 2) (- 2)) 1|2)`, `x^2-9 @ a=9` → `-3, 3`).
///
/// DIVERGENCE (`Z3_INVALID_ARG` + empty vector, honest): a non-polynomial /
/// multivariate residual, a constant or zero polynomial (Z3 errors there too),
/// a non-rational (e.g. irrational-algebraic) substitution value, a degree
/// beyond the extractor cap, or an engine refinement cap. Never a fabricated
/// root.
///
/// # Safety
/// `c` must be a valid context pointer. When `n > 0`, `a` must point to at
/// least `n` valid `Z3_ast` elements.
#[no_mangle]
pub unsafe extern "C" fn Z3_algebraic_roots(
    c: Z3_context,
    p: Z3_ast,
    n: c_uint,
    a: *const Z3_ast,
) -> Z3_ast_vector {
    // SAFETY: this public entry point requires `c` to be null or a live,
    // exclusively borrowed context; the bound checker only updates its error state.
    if !unsafe { ffi_count_within_limit(c, "Z3_algebraic_roots", n) } {
        return std::ptr::null_mut();
    }
    let n_usize = n as usize;
    if p == 0 || (n_usize > 0 && a.is_null()) {
        // SAFETY: `ffi_guard_ptr` null-checks `c` and catches panics.
        return unsafe {
            ffi_guard_ptr(c, |ctx| {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg =
                    Some("Z3_algebraic_roots: null polynomial or argument array".to_string());
                cache_ast_vector(ctx, Vec::new())
            })
        };
    }
    // SAFETY: caller guarantees `a` points to at least `n` elements (checked).
    let args: Vec<Z3_ast> = (0..n_usize).map(|i| unsafe { *a.add(i) }).collect();
    // SAFETY: `ffi_guard_ptr` null-checks `c` and catches panics.
    unsafe {
        ffi_guard_ptr(c, move |ctx| {
            let fail = |ctx: &mut Z3Context, msg: &str| {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg = Some(format!("Z3_algebraic_roots: {msg}"));
                cache_ast_vector(ctx, Vec::new())
            };
            let Some(arg_terms) = args
                .iter()
                .map(|&arg| checked_ast_to_term(ctx, arg))
                .collect::<Option<Vec<Term>>>()
            else {
                return fail(ctx, "an argument is invalid or belongs to another context");
            };
            let Some(p_term) = checked_ast_to_term(ctx, p) else {
                return fail(
                    ctx,
                    "the polynomial is invalid or belongs to another context",
                );
            };
            // Substitution values must be RATIONAL numerals: an
            // irrational-algebraic handle has no term to substitute (honest
            // divergence; Z3 accepts algebraic parameter values).
            for &arg_term in &arg_terms {
                if term_rational(ctx, arg_term).is_none() {
                    return fail(ctx, "an argument is not a rational numeral value");
                }
            }
            // Substitute a[i] for the `__db{i}` parameter variables (i < n).
            let decls: Vec<(String, Term)> = ctx
                .solver
                .declared_variables()
                .map(|(name, t)| (name.to_string(), t))
                .collect();
            let mut from: Vec<Term> = Vec::new();
            let mut to: Vec<Term> = Vec::new();
            for (name, var_term) in &decls {
                if let Some(idx) = name
                    .strip_prefix("__db")
                    .and_then(|s| s.parse::<usize>().ok())
                {
                    if idx < n_usize {
                        from.push(*var_term);
                        to.push(arg_terms[idx]);
                    }
                }
            }
            let substituted = ctx.solver.substitute(p_term, &from, &to);
            let simplified = ctx.solver.simplify(substituted);

            // The residual must be univariate: exactly one distinct variable.
            let Some(vars) = collect_term_vars(ctx, simplified) else {
                return fail(ctx, "the expression contains a binder (not a polynomial)");
            };
            let [x] = vars.as_slice() else {
                return fail(
                    ctx,
                    "the residual is not univariate (expected exactly one free variable)",
                );
            };
            let Some(coeffs) = term_to_poly(ctx, simplified, *x) else {
                return fail(
                    ctx,
                    "the expression is not a polynomial with numeral coefficients (or exceeds the degree cap)",
                );
            };
            if coeffs.len() < 2 {
                // Constant / zero polynomial: Z3 rejects these too.
                return fail(ctx, "the polynomial is constant (no univariate root set)");
            }
            let Some(roots) = rcf_api::real_roots(&coeffs) else {
                return fail(
                    ctx,
                    "exact root isolation hit an engine refinement cap — fail-closed",
                );
            };
            let mut asts: Vec<Z3_ast> = Vec::with_capacity(roots.len());
            for r in roots {
                let ast = scalar_to_ast(ctx, r);
                if ast == 0 {
                    return fail(ctx, "a root is not exactly representable — fail-closed");
                }
                asts.push(ast);
            }
            cache_ast_vector(ctx, asts)
        })
    }
}

/// Return the sign of `p(a[0], ..., a[n-1])`.
///
/// REAL WHEN FEASIBLE: the rational arguments are substituted for the bound
/// variables (`__db{i}`) and simplified; if the result is a rational value, its
/// sign is returned exactly. DIVERGENCE (`Z3_INVALID_ARG` + `0`): a non-rational
/// argument, or a residual with free variables / an irrational value.
///
/// # Safety
/// `c` must be a valid context pointer. When `n > 0`, `a` must point to at least
/// `n` valid `Z3_ast` elements.
#[no_mangle]
pub unsafe extern "C" fn Z3_algebraic_eval(
    c: Z3_context,
    p: Z3_ast,
    n: c_uint,
    a: *const Z3_ast,
) -> c_int {
    // SAFETY: this public entry point requires `c` to be null or a live,
    // exclusively borrowed context; the bound checker only updates its error state.
    if !unsafe { ffi_count_within_limit(c, "Z3_algebraic_eval", n) } {
        return 0;
    }
    let n_usize = n as usize;
    if p == 0 || (n_usize > 0 && a.is_null()) {
        // SAFETY: `ffi_guard_int` null-checks `c` and catches panics.
        return unsafe {
            ffi_guard_int(c, 0, |ctx| {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg =
                    Some("Z3_algebraic_eval: null polynomial or argument array".to_string());
                0
            })
        };
    }

    // SAFETY: caller guarantees `a` points to at least `n` elements; `a` was
    // null-checked above.
    let args: Vec<Z3_ast> = (0..n_usize).map(|i| unsafe { *a.add(i) }).collect();

    // SAFETY: `ffi_guard_int` null-checks `c` and catches panics.
    unsafe {
        ffi_guard_int(c, 0, move |ctx| {
            let Some(arg_terms) = args
                .iter()
                .map(|&arg| checked_ast_to_term(ctx, arg))
                .collect::<Option<Vec<Term>>>()
            else {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg = Some(
                    "Z3_algebraic_eval: an argument is invalid or belongs to another context"
                        .to_string(),
                );
                return 0;
            };
            let Some(p_term) = checked_ast_to_term(ctx, p) else {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg = Some(
                    "Z3_algebraic_eval: polynomial is invalid or belongs to another context"
                        .to_string(),
                );
                return 0;
            };
            for &arg_term in &arg_terms {
                if term_rational(ctx, arg_term).is_none() {
                    ctx.last_error = Z3_INVALID_ARG;
                    ctx.error_msg =
                        Some("Z3_algebraic_eval: an argument is not a rational value".to_string());
                    return 0;
                }
            }

            let decls: Vec<(String, Term)> = ctx
                .solver
                .declared_variables()
                .map(|(name, t)| (name.to_string(), t))
                .collect();
            let mut from: Vec<Term> = Vec::new();
            let mut to: Vec<Term> = Vec::new();
            for (name, var_term) in &decls {
                if let Some(idx) = name
                    .strip_prefix("__db")
                    .and_then(|s| s.parse::<usize>().ok())
                {
                    if idx < n_usize {
                        from.push(*var_term);
                        to.push(arg_terms[idx]);
                    }
                }
            }

            let substituted = ctx.solver.substitute(p_term, &from, &to);
            let simplified = ctx.solver.simplify(substituted);

            match term_rational(ctx, simplified) {
                Some((num, _)) => signum_int(&num),
                None => {
                    ctx.last_error = Z3_INVALID_ARG;
                    ctx.error_msg = Some(
                        "Z3_algebraic_eval: polynomial did not reduce to a rational value (free variables or an irrational result) — DIVERGENCE"
                            .to_string(),
                    );
                    0
                }
            }
        })
    }
}

// ============================================================================
// Defining polynomial and root index.
// ============================================================================

/// Return the coefficients of the defining polynomial of `a`, lowest-degree
/// first, as `Int` numeral ASTs.
///
/// REAL: for a rational `num/den` it is `den*x - num` → `[-num, den]`; for a
/// genuine algebraic value it is the square-free integer defining polynomial.
/// DIVERGENCE: non-value `a` or a cap → `Z3_INVALID_ARG` + empty vector.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_algebraic_get_poly(c: Z3_context, a: Z3_ast) -> Z3_ast_vector {
    // SAFETY: `ffi_guard_ptr` null-checks `c` and catches panics.
    unsafe {
        ffi_guard_ptr(c, |ctx| {
            let Some(s) = ast_as_scalar(ctx, a) else {
                set_not_value(ctx, "Z3_algebraic_get_poly");
                return cache_ast_vector(ctx, Vec::new());
            };
            let coeffs = match rcf_api::defining_coeffs(&s) {
                Some(v) => v,
                None => {
                    set_uncomputable(ctx, "Z3_algebraic_get_poly");
                    return cache_ast_vector(ctx, Vec::new());
                }
            };
            let asts: Vec<Z3_ast> = coeffs
                .iter()
                .map(|c0| {
                    let term = ctx.solver.int_const_bigint(c0);
                    let ast = term_to_ast(ctx, term);
                    record_ast_sort(ctx, ast, Sort::Int);
                    ast
                })
                .collect();
            cache_ast_vector(ctx, asts)
        })
    }
}

/// Return which root of its defining polynomial the algebraic number `a` is
/// (1-based, ascending — z3's `[1, num_roots]` convention).
///
/// DIVERGENCE: non-value `a` or a cap → `Z3_INVALID_ARG` + `0`.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_algebraic_get_i(c: Z3_context, a: Z3_ast) -> c_uint {
    // SAFETY: `ffi_guard_uint` null-checks `c` and catches panics.
    unsafe {
        ffi_guard_uint(c, 0, |ctx| {
            let Some(s) = ast_as_scalar(ctx, a) else {
                set_not_value(ctx, "Z3_algebraic_get_i");
                return 0;
            };
            match rcf_api::root_index(&s) {
                Some(k) => k as c_uint,
                None => {
                    set_uncomputable(ctx, "Z3_algebraic_get_i");
                    0
                }
            }
        })
    }
}

// ============================================================================
// Polynomials (z3_polynomial.h).
// ============================================================================

/// Return the nonzero subresultants of `p` and `q` with respect to `x`.
///
/// REAL for univariate inputs: `p` and `q` are walked into exact coefficient
/// vectors in `x` (see [`term_to_poly`]) and the principal subresultant
/// coefficient chain `psc_j` for `j = 0 .. min(deg p, deg q) - 1` is computed
/// by exact Sylvester–Habicht determinants ([`psc_coefficient`]), replicating
/// libz3 4.16's `psc_chain` conventions EXACTLY (cross-checked):
///   * inputs are swapped so the first operand has the larger degree (equal
///     degrees keep the given order — the chain is order-sensitive there);
///   * zero entries are dropped; ascending `j` order;
///   * an empty / all-zero chain (including a constant or zero operand)
///     returns the single numeral `0`.
/// Verified value-for-value against libz3 on: `(x²-2, 2x) → [-8]`,
/// `(x⁴-5x²+4, 4x³-10x) → [5184, -360, -40]`, `(x²-3x+2, x²-1) → [3]`,
/// `(x²+1, x²-x) → [2, -1]` / swapped `[2, 1]`, `(x-2, x³-1) → [-7]` both
/// orders, `(x⁴+x, x²) → [-1]`, `(x⁴, x²) → [0]`, constant/zero → `[0]`.
///
/// DIVERGENCE (`Z3_INVALID_ARG` + empty vector, honest): non-polynomial input,
/// a variable other than `x` occurring in `p`/`q` (parametric/multivariate
/// subresultants — libz3 computes those; AY's extractor is univariate-only), a
/// non-variable `x`, or the degree cap. Never a fabricated value.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_polynomial_subresultants(
    c: Z3_context,
    p: Z3_ast,
    q: Z3_ast,
    x: Z3_ast,
) -> Z3_ast_vector {
    // SAFETY: `ffi_guard_ptr` null-checks `c` and catches panics.
    unsafe {
        ffi_guard_ptr(c, |ctx| {
            use ay_dpll::api::TermKind;
            use num_traits::Zero;
            let fail = |ctx: &mut Z3Context, msg: &str| {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg = Some(format!("Z3_polynomial_subresultants: {msg}"));
                cache_ast_vector(ctx, Vec::new())
            };
            if p == 0 || q == 0 || x == 0 {
                return fail(ctx, "null AST argument");
            }
            let Some(x_term) = checked_ast_to_term(ctx, x) else {
                return fail(ctx, "x is invalid or belongs to another context");
            };
            if !matches!(ctx.solver.term_kind(x_term), TermKind::Var { .. }) {
                return fail(ctx, "x must be a variable/constant term");
            }
            let Some(mut pp) = checked_ast_to_term(ctx, p) else {
                return fail(ctx, "p is invalid or belongs to another context");
            };
            let Some(mut qq) = checked_ast_to_term(ctx, q) else {
                return fail(ctx, "q is invalid or belongs to another context");
            };
            let Some(mut pc) = term_to_poly(ctx, pp, x_term) else {
                return fail(
                    ctx,
                    "p is not a univariate polynomial in x with numeral coefficients (parametric subresultants are an honest divergence)",
                );
            };
            let Some(mut qc) = term_to_poly(ctx, qq, x_term) else {
                return fail(
                    ctx,
                    "q is not a univariate polynomial in x with numeral coefficients (parametric subresultants are an honest divergence)",
                );
            };
            // libz3 canonicalizes so the FIRST operand has the LARGER degree
            // (equal degrees keep the given order; no sign adjustment) —
            // cross-checked on (x-2, x³-1) vs (x³-1, x-2), both → [-7].
            if poly_degree(&pc) < poly_degree(&qc) {
                std::mem::swap(&mut pc, &mut qc);
                std::mem::swap(&mut pp, &mut qq);
            }
            let _ = (pp, qq);
            let degrees = (poly_degree(&pc), poly_degree(&qc));
            let chain_len = match degrees {
                // min(deg p, deg q), with constant/zero operands → empty chain.
                (Some(_), Some(n)) if n >= 1 => n,
                _ => 0,
            };
            if let (Some(m), Some(n)) = degrees {
                let limit = MAX_FFI_CONTAINER_ELEMENTS as usize;
                if let Err(limit_kind) = psc_resource_preflight(m, n, limit, limit) {
                    let detail = match limit_kind {
                        PscResourceLimit::MatrixEntries => "matrix allocation budget exceeded",
                        PscResourceLimit::AggregateEntries => {
                            "aggregate matrix allocation budget exceeded"
                        }
                        PscResourceLimit::EliminationWork => {
                            "exact determinant work budget exceeded"
                        }
                    };
                    return fail(ctx, detail);
                }
            }
            let mut values: Vec<BigRational> = Vec::with_capacity(chain_len);
            for j in 0..chain_len {
                let v = psc_coefficient(&pc, &qc, j);
                if !v.is_zero() {
                    values.push(v);
                }
            }
            if values.is_empty() {
                // libz3's psc_chain pads an empty/all-zero chain with a single 0.
                values.push(BigRational::from_integer(BigInt::from(0)));
            }
            let asts: Vec<Z3_ast> = values
                .into_iter()
                .map(|v| {
                    let term = ctx.solver.rational_const_bigint(v.numer(), v.denom());
                    let ast = term_to_ast(ctx, term);
                    record_ast_sort(ctx, ast, Sort::Real);
                    ast
                })
                .collect();
            cache_ast_vector(ctx, asts)
        })
    }
}

#[cfg(test)]
mod resource_tests {
    use super::*;

    #[test]
    fn psc_resource_preflight_bounds_matrix_and_cubic_work() {
        // A single 10×10 matrix consumes exactly 100 entries / 1000 abstract
        // elimination-work units.
        assert_eq!(psc_resource_preflight(9, 1, 100, 1000), Ok(()));
        assert_eq!(
            psc_resource_preflight(10, 1, 100, usize::MAX),
            Err(PscResourceLimit::MatrixEntries)
        );
        assert_eq!(
            psc_resource_preflight(9, 1, usize::MAX, 999),
            Err(PscResourceLimit::EliminationWork)
        );

        // Repeated matrices are charged cumulatively, not one-at-a-time.
        assert_eq!(
            psc_resource_preflight(5, 2, 50, usize::MAX),
            Err(PscResourceLimit::AggregateEntries)
        );
        assert!(psc_resource_preflight(usize::MAX, 1, usize::MAX, usize::MAX).is_err());
    }
}
