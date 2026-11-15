// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Z3-compatible AST and FuncDecl accessor functions.
//!
//! Implements the subset of z3_api.h "Accessors" section needed for
//! external consumers: AST kind queries, app introspection, func_decl
//! introspection, and boolean value retrieval.
//!
//! All functions that call into the solver are wrapped in `catch_unwind` via
//! the `ffi_guard_*` helpers (#6192) to prevent undefined behavior from panics
//! unwinding across the `extern "C"` boundary.

use std::ffi::{c_int, c_uint};
use std::ptr;

use ay_dpll::api::{Sort, Term, TermKind};

use super::{
    alloc_sort, cache_func_decl_with_params, cache_func_decl_with_symbol, cache_symbol_key,
    cache_value_func_decl, engine_ast, engine_public_sort, ffi_guard_ast, ffi_guard_int,
    ffi_guard_ptr, ffi_guard_uint, finite_set_app_for, finite_set_decl_for,
    finite_set_empty_decl_parameter, parse_indexed_name, public_sort, require_ast_or_return,
    stated_sort, PubTerm, Z3_ast, Z3_context, Z3_func_decl, Z3_sort, Z3_symbol, Z3_APP_AST, Z3_IOB,
    Z3_L_FALSE, Z3_L_TRUE, Z3_L_UNDEF, Z3_NUMERAL_AST, Z3_OP_ANUM, Z3_OP_BNUM, Z3_OP_FALSE,
    Z3_OP_INTERNAL, Z3_OP_TRUE, Z3_PARAMETER_INT, Z3_PARAMETER_SORT, Z3_QUANTIFIER_AST,
    Z3_UNKNOWN_AST, Z3_VAR_AST,
};

// ============================================================================
// AST kind and classification
// ============================================================================

/// Whether `term` is a floating-point value as z3 builds one (`fp.numeral`,
/// NaN, an infinity or a zero): AY's special constants, and `to_fp` of a
/// bit-vector literal (the shape `Z3_mk_fpa_numeral_*` builds). An `fp`
/// application over literals is not a numeral in z3.
fn is_fp_value(ctx: &super::Z3Context, term: Term) -> bool {
    match ctx.solver.term_kind(term) {
        TermKind::App { name, num_args: 0 } => matches!(
            parse_indexed_name(&name).0.as_str(),
            "NaN" | "+zero" | "-zero" | "+oo" | "-oo"
        ),
        TermKind::App { name, num_args: 1 } if parse_indexed_name(&name).0 == "to_fp" => {
            let children = ctx.solver.term_children(term);
            children.len() == 1
                && ctx.solver.is_numeral(children[0])
                && matches!(ctx.solver.term_sort(children[0]), Sort::BitVec(_))
                && ctx.solver.fp_numeral_decode(term).is_some()
        }
        _ => false,
    }
}

/// Whether `term` is one of the five rounding-mode values.
fn is_rounding_mode_value(ctx: &super::Z3Context, term: Term) -> bool {
    matches!(
        ctx.solver.term_kind(term),
        TermKind::App { ref name, num_args: 0 } if matches!(
            name.as_str(),
            "RNE" | "RNA" | "RTP" | "RTN" | "RTZ" | "roundNearestTiesToEven"
                | "roundNearestTiesToAway" | "roundTowardPositive" | "roundTowardNegative"
                | "roundTowardZero"
        )
    )
}

/// True iff `name` is AY's C-API encoding of a de-Bruijn BOUND variable —
/// `__db<index>`, as produced by [`Z3_mk_bound`] and consumed throughout the
/// quantifier machinery (see `ay_dpll::api::compat_ext`).
///
/// A declared CONSTANT (`Z3_mk_const`) and a bound variable are both stored as a
/// core `Var`, but z3 exposes them differently: a declared constant is a nullary
/// APPLICATION (`Z3_APP_AST`) — the shape stock z3py relies on for `to_app`,
/// `decl()`, `children()`, `ForAll`/`Exists` over constants, `m[x]` — while a
/// bound variable is the genuine `Z3_VAR_AST`. The `__db` marker is the only
/// thing that distinguishes them at the C-API boundary, so it is the pivot for
/// every classifier below.
fn is_debruijn_bound_var_name(name: &str) -> bool {
    ay_dpll::api::de_bruijn_index(name).is_some()
}

/// The name of a declared constant (a core `Var` that is NOT a `__db` bound
/// variable), or `None` for anything else. A declared constant is a nullary
/// application in z3 terms.
fn declared_const_name(ctx: &super::Z3Context, term: Term) -> Option<String> {
    match ctx.solver.term_kind(term) {
        TermKind::Var { name } if !is_debruijn_bound_var_name(&name) => Some(name),
        _ => None,
    }
}

/// Get the kind of an AST node.
///
/// Returns one of `Z3_NUMERAL_AST`, `Z3_APP_AST`, `Z3_VAR_AST`,
/// `Z3_QUANTIFIER_AST`, or `Z3_UNKNOWN_AST`.
///
/// # Safety
/// The kind of a tagged non-term handle, or `None` for an ordinary
/// term handle. Each arena lookup is authenticated before reporting
/// even its kind: otherwise a foreign sort/decl handle would be
/// accepted as a local object.
fn tagged_ast_kind(ctx: &mut super::Z3Context, a: Z3_ast) -> Option<c_uint> {
    // Tagged non-term handles never reach the term arena. Authenticate
    // each arena lookup before reporting even its kind: otherwise a
    // foreign sort/decl handle would be accepted as a local object.
    match a & super::HANDLE_TAG_MASK {
        super::SORT_AST_TAG => {
            if super::sort_ast_to_handle(ctx, a).is_null() {
                ctx.last_error = super::Z3_INVALID_ARG;
                ctx.error_msg =
                    Some("Z3_get_ast_kind: invalid or foreign sort AST handle".to_string());
                return Some(Z3_UNKNOWN_AST);
            }
            ctx.last_error = super::Z3_OK;
            return Some(super::Z3_SORT_AST);
        }
        super::FUNC_DECL_AST_TAG => {
            if super::func_decl_ast_to_handle(ctx, a).is_null() {
                ctx.last_error = super::Z3_INVALID_ARG;
                ctx.error_msg =
                    Some("Z3_get_ast_kind: invalid or foreign func-decl AST handle".to_string());
                return Some(Z3_UNKNOWN_AST);
            }
            ctx.last_error = super::Z3_OK;
            return Some(super::Z3_FUNC_DECL_AST);
        }
        super::OO_AST_TAG => {
            if super::decode_oo_ast(ctx, a).is_none() {
                ctx.last_error = super::Z3_INVALID_ARG;
                ctx.error_msg =
                    Some("Z3_get_ast_kind: invalid or foreign oo AST handle".to_string());
                return Some(Z3_UNKNOWN_AST);
            }
            ctx.last_error = super::Z3_OK;
            // z3's `oo` is a nullary application node
            // (measured kind: Z3_APP_AST).
            return Some(super::Z3_APP_AST);
        }
        super::PROOF_AST_TAG => {
            if super::proof_text_for_ast(ctx, a).is_none() {
                ctx.last_error = super::Z3_INVALID_ARG;
                ctx.error_msg =
                    Some("Z3_get_ast_kind: invalid or foreign proof AST handle".to_string());
            } else {
                ctx.last_error = super::Z3_OK;
            }
            return Some(if super::proof_dag::application(ctx, a).is_some() {
                super::Z3_APP_AST
            } else {
                Z3_UNKNOWN_AST
            });
        }
        super::ALGEBRAIC_AST_TAG => {
            if super::algebraic::ast_as_scalar(ctx, a).is_none() {
                ctx.last_error = super::Z3_INVALID_ARG;
                ctx.error_msg =
                    Some("Z3_get_ast_kind: invalid or foreign algebraic AST handle".to_string());
            } else {
                ctx.last_error = super::Z3_OK;
            }
            // AY's opaque algebraic handle has no faithful term kind.
            return Some(Z3_UNKNOWN_AST);
        }
        0 => return None,
        _ => {
            ctx.last_error = super::Z3_INVALID_ARG;
            ctx.error_msg = Some("Z3_get_ast_kind: malformed AST tag".to_string());
            return Some(Z3_UNKNOWN_AST);
        }
    }
}

/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_get_ast_kind(c: Z3_context, a: Z3_ast) -> c_uint {
    if a == 0 {
        return Z3_UNKNOWN_AST;
    }
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_uint` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe {
        ffi_guard_uint(c, Z3_UNKNOWN_AST, |ctx| {
            if let Some(kind) = tagged_ast_kind(ctx, a) {
                return kind;
            }
            let decoded = require_ast_or_return!(ctx, a, "Z3_get_ast_kind", "AST", Z3_UNKNOWN_AST);
            if finite_set_app_for(ctx, decoded).is_some() {
                return Z3_APP_AST;
            }
            let term = decoded.term;
            match ctx.solver.term_kind(term) {
                // z3: `true`, `false` and string literals are applications;
                // only arithmetic and bit-vector numerals are NUMERAL_AST.
                TermKind::Const if !is_numeral_literal(ctx, decoded) => Z3_APP_AST,
                // A rounding-mode value is a numeral in z3 (an FP numeral is
                // an application there, as here).
                _ if is_rounding_mode_value(ctx, term) => Z3_NUMERAL_AST,
                TermKind::Const => Z3_NUMERAL_AST,
                TermKind::App { .. } | TermKind::Not | TermKind::Ite => Z3_APP_AST,
                // A declared constant (`Z3_mk_const`) is a NULLARY APPLICATION in
                // z3 (`Z3_APP_AST`); only a `__db` de-Bruijn bound variable is a
                // true `Z3_VAR_AST`. Reporting VAR for a declared constant made
                // `Z3_to_app` return NULL and broke stock z3py (`m[x]`, `decl()`,
                // `ForAll`/`Exists` over consts).
                TermKind::Var { name } if is_debruijn_bound_var_name(&name) => Z3_VAR_AST,
                TermKind::Var { .. } => Z3_APP_AST,
                TermKind::Forall | TermKind::Exists => Z3_QUANTIFIER_AST,
                TermKind::Let | _ => Z3_UNKNOWN_AST,
            }
        })
    }
}

/// Return true if the AST is a numeral.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_is_numeral_ast(c: Z3_context, a: Z3_ast) -> bool {
    if a == 0 {
        return false;
    }
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_int` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe {
        ffi_guard_int(c, 0, |ctx| {
            let decoded = require_ast_or_return!(ctx, a, "Z3_is_numeral_ast", "AST", 0);
            let term = decoded.term;
            // z3's floating-point numerals (NaN, the infinities and zeros,
            // finite values) and rounding-mode values are numerals too: z3py
            // prints them as values only then.
            i32::from(
                (ctx.solver.is_numeral(term) && is_numeral_literal(ctx, decoded))
                    || is_fp_value(ctx, term)
                    || is_rounding_mode_value(ctx, term),
            )
        }) != 0
    }
}

/// Return true if the AST is an application node.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_is_app(c: Z3_context, a: Z3_ast) -> bool {
    if a == 0 {
        return false;
    }
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_int` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe {
        ffi_guard_int(c, 0, |ctx| {
            if super::proof_dag::application(ctx, a).is_some() {
                return 1;
            }
            let decoded = require_ast_or_return!(ctx, a, "Z3_is_app", "AST", 0);
            let term = decoded.term;
            // A declared constant is a nullary application; the core stores it as
            // a `Var`, so `solver.is_app` alone would miss it (breaking z3py's
            // `is_app`/`to_app`). A numeral is also an application in z3.
            let is_app = finite_set_app_for(ctx, decoded).is_some()
                || ctx.solver.is_app(term)
                || ctx.solver.is_numeral(term)
                || declared_const_name(ctx, term).is_some();
            i32::from(is_app)
        }) != 0
    }
}

/// Convert an AST to an application node.
///
/// In Z3, `Z3_app` is a typedef for `Z3_ast`. This function is a type-checked
/// identity cast: returns the AST unchanged if it represents an application,
/// or 0 (null) if it does not.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_to_app(c: Z3_context, a: Z3_ast) -> Z3_ast {
    if a == 0 {
        return 0;
    }
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_ast` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            if super::proof_dag::application(ctx, a).is_some() {
                return a;
            }
            // A tagged non-term handle (proof/algebraic/sort/func-decl AST) is
            // not an application. z3's identity-cast leniency here is UB we
            // refuse to copy: fail closed with INVALID_ARG.
            if a & super::HANDLE_TAG_MASK != 0 {
                ctx.last_error = super::Z3_INVALID_ARG;
                ctx.error_msg = Some("Z3_to_app: argument is not an application AST".to_string());
                return 0;
            }
            let decoded = require_ast_or_return!(ctx, a, "Z3_to_app", "AST", 0);
            let term = decoded.term;
            if finite_set_app_for(ctx, decoded).is_some()
                || ctx.solver.is_app(term)
                || ctx.solver.is_numeral(term)
                // A declared constant is a nullary application: z3's `Z3_to_app`
                // is a type-checked identity cast that succeeds on it, and stock
                // z3py depends on that (`m[x]`, `decl()`, quantifier construction).
                || declared_const_name(ctx, term).is_some()
            {
                super::pub_to_ast(ctx, decoded)
            } else {
                0
            }
        })
    }
}

// ============================================================================
// Application introspection
// ============================================================================

/// Get the number of arguments of an application AST.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_get_app_num_args(c: Z3_context, a: Z3_ast) -> c_uint {
    if a == 0 {
        return 0;
    }
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_uint` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe {
        ffi_guard_uint(c, 0, |ctx| {
            if let Some(app) = super::proof_dag::application(ctx, a) {
                return app.arguments.len() as c_uint;
            }
            let decoded = require_ast_or_return!(ctx, a, "Z3_get_app_num_args", "application", 0);
            if let Some(app) = finite_set_app_for(ctx, decoded) {
                return app.args.len() as c_uint;
            }
            ctx.solver.app_num_args(decoded.term) as c_uint
        })
    }
}

/// Get the i-th argument of an application AST.
///
/// Returns 0 (null AST) if `a` is not an application or `i` is out of bounds.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_get_app_arg(c: Z3_context, a: Z3_ast, i: c_uint) -> Z3_ast {
    if a == 0 {
        return 0;
    }
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_ast` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            if let Some(app) = super::proof_dag::application(ctx, a) {
                let result = app.arguments.get(i as usize).copied();
                if result.is_none() {
                    ctx.last_error = Z3_IOB;
                }
                return result.unwrap_or(0);
            }
            let decoded = require_ast_or_return!(ctx, a, "Z3_get_app_arg", "application", 0);
            if let Some(app) = finite_set_app_for(ctx, decoded) {
                return app.args.get(i as usize).copied().unwrap_or(0);
            }
            match ctx.solver.app_arg(decoded.term, i as usize) {
                Some(t) => engine_ast(ctx, t),
                None => 0,
            }
        })
    }
}

/// z3's two parameters of a numeral's declaration (`Z3_get_app_decl` on an
/// arithmetic or bit-vector numeral): the value as a rational
/// (`Z3_PARAMETER_RATIONAL`) and an integer (`Z3_PARAMETER_INT`): 1 for an
/// `Int` numeral, 0 for a `Real` one, the width for a bit-vector. `None` for
/// any other declaration.
pub(crate) fn numeral_decl_int_parameter(handle: &super::FuncDeclHandle) -> Option<c_int> {
    let value = handle.value?;
    match (value.kind, handle.decl.range()) {
        (Z3_OP_ANUM, Sort::Int) => Some(1),
        (Z3_OP_ANUM, _) => Some(0),
        (Z3_OP_BNUM, Sort::BitVec(bv)) => c_int::try_from(bv.width).ok(),
        _ => None,
    }
}

/// z3's one parameter of a character literal's declaration (`Z3_get_app_decl`
/// on `CharVal('e')` or a `Char` model value): the code point, as a
/// `Z3_PARAMETER_INT` (libz3 5.1.0: `CharVal('e').decl().params()` is
/// `[101]`; z3py prints a character through it, so a declaration without it
/// made printing any `Char` value raise `IndexError`). `None` for any other
/// declaration.
pub(crate) fn char_decl_code_point(
    ctx: &super::Z3Context,
    handle: &super::FuncDeclHandle,
) -> Option<c_int> {
    let value = handle.value?;
    if value.kind != super::Z3_OP_CHAR_CONST || !handle.decl.range().is_char() {
        return None;
    }
    let code: c_int = ctx.solver.numeral_string(value.term)?.parse().ok()?;
    let max = super::bounded_sort_hi(&Sort::Char)?;
    (0..=max).contains(&i64::from(code)).then_some(code)
}

/// The rational parameter of a numeral's declaration (see
/// [`numeral_decl_int_parameter`]), in z3's spelling (`2`, `-1/2`).
pub(crate) fn numeral_decl_rational_parameter(
    ctx: &super::Z3Context,
    handle: &super::FuncDeclHandle,
) -> Option<String> {
    numeral_decl_int_parameter(handle)?;
    let text = ctx.solver.numeral_string(handle.value?.term)?;
    Some(match text.split_once('/') {
        Some((numer, "1")) => numer.to_string(),
        _ => text,
    })
}

/// One parameter of a character or finite-domain value's declaration.
#[derive(Clone, Debug, PartialEq)]
pub(crate) enum BoundedValueParam {
    Int(c_int),
    Rational(String),
    Sort(Sort),
}

impl BoundedValueParam {
    /// The parameter's `Z3_parameter_kind`.
    pub(crate) fn kind(&self) -> c_uint {
        match self {
            Self::Int(_) => Z3_PARAMETER_INT,
            Self::Rational(_) => super::Z3_PARAMETER_RATIONAL,
            Self::Sort(_) => Z3_PARAMETER_SORT,
        }
    }
}

/// z3's parameters of a character or finite-domain value's declaration, now
/// that such a value is its own AST rather than the integer it is stored as
/// (libz3 5.1.0: `CharVal('a').decl().params()` is `[97]`, one
/// `Z3_PARAMETER_INT`; `FiniteDomainVal(3, S).decl().params()` is `['3', S]`,
/// a `Z3_PARAMETER_RATIONAL` and a `Z3_PARAMETER_SORT`). z3py prints a
/// character value from its parameter. `None` for any other declaration.
pub(crate) fn bounded_value_decl_parameters(
    ctx: &super::Z3Context,
    handle: &super::FuncDeclHandle,
) -> Option<Vec<BoundedValueParam>> {
    let value = handle.value?;
    let text = || ctx.solver.numeral_string(value.term);
    match (value.kind, handle.decl.range()) {
        (super::Z3_OP_FF_NUM, Sort::FiniteField(_)) => {
            Some(vec![BoundedValueParam::Rational(text()?)])
        }
        (super::Z3_OP_CHAR_CONST, Sort::Char) => {
            Some(vec![BoundedValueParam::Int(text()?.parse().ok()?)])
        }
        (super::Z3_OP_FD_CONSTANT, range @ Sort::FiniteDomain(..)) => Some(vec![
            BoundedValueParam::Rational(text()?),
            BoundedValueParam::Sort(range.clone()),
        ]),
        _ => None,
    }
}

/// Whether a literal is a z3 NUMERAL: true for every term except the Boolean
/// and string literals, which z3 reports as applications that are not numerals
/// (`Z3_get_ast_kind` is `Z3_APP_AST`, `Z3_is_numeral_ast` is false).
fn is_numeral_literal(ctx: &super::Z3Context, decoded: PubTerm) -> bool {
    // A character (stored as its Int code point) is an application too.
    !matches!(stated_sort(ctx, decoded), Some(Sort::Char))
        && !matches!(ctx.solver.sort_of(decoded.term), Sort::Bool | Sort::String)
}

/// z3's declaration of the literal `term` (`Z3_get_app_decl` on a value), named
/// and kinded from the literal itself and its public sort, never from a name
/// (see [`super::ValueDecl`]). Null plus `Z3_INVALID_ARG` for a literal whose
/// declaration AY does not model.
fn value_decl_for_literal(ctx: &mut super::Z3Context, decoded: PubTerm) -> Z3_func_decl {
    let term = decoded.term;
    let range = public_sort(ctx, decoded);
    let named = match (ctx.solver.bool_value(term), &range) {
        (Some(true), _) => Some(("true", Z3_OP_TRUE)),
        (Some(false), _) => Some(("false", Z3_OP_FALSE)),
        (None, Sort::Int) => Some(("Int", Z3_OP_ANUM)),
        (None, Sort::Real) => Some(("Real", Z3_OP_ANUM)),
        (None, Sort::FiniteField(_)) => Some(("ff", super::Z3_OP_FF_NUM)),
        (None, Sort::BitVec(_)) => Some(("bv", Z3_OP_BNUM)),
        (None, Sort::String) => Some(("String", Z3_OP_INTERNAL)),
        (None, Sort::Char) => Some(("Char", super::Z3_OP_CHAR_CONST)),
        (None, Sort::FiniteDomain(name, _)) => Some((name.as_str(), super::Z3_OP_FD_CONSTANT)),
        _ => None,
    }
    .map(|(name, kind)| (name.to_string(), kind));
    match named {
        Some((name, kind)) => {
            cache_value_func_decl(ctx, &name, range, super::ValueDecl { term, kind })
        }
        None => no_app_decl(
            ctx,
            &format!("no declaration for a literal of sort {range}"),
        ),
    }
}

/// The datatype constructor, tester or accessor declaration `Z3_mk_datatype`
/// handed out with exactly this name and signature, so the decl of a
/// datatype application carries its operator kind (`Z3_OP_DT_*`) and applies
/// through the datatype builders, as the decl the caller built with does.
///
/// A constructor application whose exact signature was never handed out (a
/// model value such as `cons(3, nil)` or an enum value, whose sorts may be
/// spelled differently) still gets its constructor declaration when its
/// datatype has a constructor of that name and arity: user functions never
/// share a datatype member's name (the frontend refuses that collision, and
/// API functions carry private identities).
fn datatype_decl_for(
    ctx: &mut super::Z3Context,
    name: &str,
    domain: &[Sort],
    range: &Sort,
) -> Option<Z3_func_decl> {
    if ctx.dt_decl_index.is_empty() {
        return None;
    }
    if let Some(&handle) =
        ctx.dt_decl_index
            .get(&(name.to_string(), domain.to_vec(), range.clone()))
    {
        return Some(handle);
    }
    let Sort::Datatype(dt) = range else {
        return None;
    };
    let constructor = dt
        .constructors
        .iter()
        .find(|c| c.name == name && c.fields.len() == domain.len())?;
    let decl = ay_dpll::api::FuncDecl::new(
        constructor.name.clone(),
        constructor.fields.iter().map(|f| f.sort.clone()).collect(),
        range.clone(),
    );
    let op = super::DatatypeOp::Constructor {
        dt: dt.clone(),
        ctor: constructor.name.clone(),
    };
    Some(super::cache_dt_func_decl(ctx, decl, op))
}

/// A declared constant is a nullary application; its decl is a 0-arity
/// function named after the constant, ranging over its sort. z3py's
/// `x.decl()` returns exactly this, so it must not be NULL. A nullary
/// datatype constructor (an enum value) gets its constructor declaration.
fn declared_const_decl(
    ctx: &mut super::Z3Context,
    decoded: PubTerm,
    const_name: String,
) -> Z3_func_decl {
    let term = decoded.term;
    let range = public_sort(ctx, decoded);
    if let Some((identity, symbol)) = ctx.ffi_const_metadata.get(&term).cloned() {
        return cache_func_decl_with_symbol(
            ctx,
            ay_dpll::api::FuncDecl::new(identity, Vec::new(), range),
            symbol,
        );
    }
    if let Some(constructor) = datatype_decl_for(ctx, &const_name, &[], &range) {
        return constructor;
    }
    // Any other constant (a model value such as `@S!0`, a parsed constant):
    // an uninterpreted nullary decl that, applied to no arguments, is exactly
    // this constant, as in z3 (z3py's model enumeration builds `d() != m[d]`;
    // before, applying it failed as an unregistered declaration).
    cache_value_func_decl(
        ctx,
        &const_name,
        range,
        super::ValueDecl {
            term,
            kind: super::Z3_OP_UNINTERPRETED,
        },
    )
}

/// `Z3_get_app_decl`'s failure: z3 sets `Z3_INVALID_ARG` when it has no
/// declaration to return; a silent null made every consumer (z3py's
/// `is_true`, the printer) read a default instead of raising.
fn no_app_decl(ctx: &mut super::Z3Context, why: &str) -> Z3_func_decl {
    ctx.last_error = super::Z3_INVALID_ARG;
    ctx.error_msg = Some(format!("Z3_get_app_decl: {why}"));
    ptr::null_mut()
}

/// Get the function declaration of an application AST.
///
/// For built-in operators (and, or, not, +, -, etc.) this returns a synthetic
/// func_decl with the operator name; for a literal, z3's value declaration
/// (`true`, `false`, `Int`/`Real`, `bv`, `String`).
///
/// Returns null and sets `Z3_INVALID_ARG` if `a` is not an application.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_get_app_decl(c: Z3_context, a: Z3_ast) -> Z3_func_decl {
    if a == 0 {
        return ptr::null_mut();
    }
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_ptr` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe {
        ffi_guard_ptr(c, |ctx| {
            if let Some(app) = super::proof_dag::application(ctx, a) {
                return app.declaration;
            }
            let decoded =
                require_ast_or_return!(ctx, a, "Z3_get_app_decl", "application", ptr::null_mut());
            if let Some(decl) = finite_set_decl_for(ctx, decoded) {
                return decl;
            }
            let term = decoded.term;
            if let Some(const_name) = declared_const_name(ctx, term) {
                return declared_const_decl(ctx, decoded, const_name);
            }
            if matches!(ctx.solver.term_kind(term), TermKind::Const) {
                return value_decl_for_literal(ctx, decoded);
            }
            let Some(name) = ctx.solver.app_symbol_name(term) else {
                return no_app_decl(ctx, "the AST is not an application");
            };
            let num_args = ctx.solver.app_num_args(term);
            // Parse indexed operator name and extract parameters (#6580 F2).
            let (base_name, params) = parse_indexed_name(&name);
            // z3py reports the if-then-else operator's canonical decl name as
            // "if" (its native syntax), while AY's core / SMT-LIB symbol is
            // "ite". Canonicalize here so `decl().name()` matches z3py exactly;
            // the decl kind stays Z3_OP_ITE (operator_name_to_decl_kind maps
            // both spellings). The core's SMT-LIB printing is untouched.
            let base_name = if base_name == "ite" {
                "if".to_string()
            } else {
                base_name
            };
            // Reconstruct real domain sorts from the application's children (#6580 F3).
            // Falls back to null if any child lookup fails.
            let domain: Option<Vec<_>> = (0..num_args)
                .map(|i| {
                    ctx.solver
                        .app_arg(term, i)
                        .map(|arg| engine_public_sort(ctx, arg))
                })
                .collect();
            let Some(domain) = domain else {
                return no_app_decl(ctx, "an argument of the application has no term");
            };
            let (domain, range) =
                if let Some((domain, range)) = ctx.finite_set_decl_signatures.get(&name).cloned() {
                    (domain, range)
                } else {
                    (domain, public_sort(ctx, decoded))
                };
            if let Some(datatype_decl) = datatype_decl_for(ctx, &name, &domain, &range) {
                return datatype_decl;
            }
            // A recursive function (`Z3_mk_rec_func_decl`) has its own private
            // identity beside the uninterpreted ones (T5 P0.2 Q5).
            if let Some(authenticated) = ctx
                .ffi_func_decls
                .values()
                .chain(ctx.ffi_rec_func_decls.values())
                .find(|decl| {
                    decl.declaration_identity_name() == name && decl.arity() == domain.len()
                })
                .cloned()
            {
                let instantiated = authenticated.with_instantiated_signature(domain, range);
                return cache_func_decl_with_params(ctx, instantiated, params);
            }
            cache_func_decl_with_params(
                ctx,
                ay_dpll::api::FuncDecl::new(base_name, domain, range),
                params,
            )
        })
    }
}

// ============================================================================
// FuncDecl introspection
// ============================================================================

/// Get the name of a function declaration as a symbol.
///
/// # Safety
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_get_decl_name(c: Z3_context, d: Z3_func_decl) -> Z3_symbol {
    if d.is_null() {
        return ptr::null_mut();
    }
    // SAFETY: `d` was null-checked above and originates from a prior AY FFI allocation whose
    // handle is kept alive by the owning `Z3Context` (see handle caches in `mod.rs`). Reading
    // `.decl` is a shared-read with no concurrent mutation because the Z3 C API is
    // single-threaded per context.
    let handle = unsafe { &*d };
    // z3 names every recognizer `is` (its constructor is the decl's one
    // parameter), whatever symbol `Z3_mk_constructor` was given.
    let symbol = if matches!(handle.dt_op, Some(super::DatatypeOp::Recognizer { .. })) {
        super::SymbolKey::String("is".to_string())
    } else {
        handle
            .symbol
            .clone()
            .unwrap_or_else(|| super::SymbolKey::String(handle.decl.name().to_string()))
    };
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_ptr` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe { ffi_guard_ptr(c, |ctx| cache_symbol_key(ctx, symbol.clone())) }
}

/// Get the number of arguments (arity) of a function declaration.
///
/// # Safety
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_get_arity(_c: Z3_context, d: Z3_func_decl) -> c_uint {
    if d.is_null() {
        return 0;
    }
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_uint` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe {
        ffi_guard_uint(_c, 0, |_ctx| {
            let decl = &(*d).decl;
            decl.arity() as c_uint
        })
    }
}

/// Get the number of parameters in a function declaration (always 0 for AY).
///
/// # Safety
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_get_domain_size(_c: Z3_context, d: Z3_func_decl) -> c_uint {
    if d.is_null() {
        return 0;
    }
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_uint` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe {
        ffi_guard_uint(_c, 0, |_ctx| {
            let decl = &(*d).decl;
            decl.arity() as c_uint
        })
    }
}

/// Get the i-th domain sort of a function declaration.
///
/// # Safety
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_get_domain(c: Z3_context, d: Z3_func_decl, i: c_uint) -> Z3_sort {
    if d.is_null() {
        return ptr::null_mut();
    }
    // SAFETY: `d` was null-checked above and originates from a prior AY FFI allocation whose
    // handle is kept alive by the owning `Z3Context` (see handle caches in `mod.rs`). Reading
    // `.decl` is a shared-read with no concurrent mutation because the Z3 C API is
    // single-threaded per context.
    let decl = unsafe { &(*d).decl };
    // SAFETY: `c` is valid or null under this function's contract; `as_ref`
    // handles null and only takes a shared borrow for the signature lookup.
    let public_signature = unsafe {
        c.as_ref()
            .and_then(|ctx| ctx.finite_set_decl_signatures.get(decl.name()))
    };
    let sort = match public_signature
        .map(|(domain, _)| domain.as_slice())
        .unwrap_or_else(|| decl.domain())
        .get(i as usize)
    {
        Some(s) => s.clone(),
        None => return ptr::null_mut(),
    };
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_ptr` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe { ffi_guard_ptr(c, |ctx| alloc_sort(ctx, sort.clone())) }
}

/// Get the range (return) sort of a function declaration.
///
/// # Safety
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_get_range(c: Z3_context, d: Z3_func_decl) -> Z3_sort {
    if d.is_null() {
        return ptr::null_mut();
    }
    // SAFETY: `d` was null-checked above and originates from a prior AY FFI allocation whose
    // handle is kept alive by the owning `Z3Context` (see handle caches in `mod.rs`). Reading
    // `.decl` is a shared-read with no concurrent mutation because the Z3 C API is
    // single-threaded per context.
    let decl = unsafe { &(*d).decl };
    // SAFETY: `c` is valid or null under this function's contract; `as_ref`
    // handles null and the signature map is only read.
    let sort = unsafe {
        c.as_ref()
            .and_then(|ctx| ctx.finite_set_decl_signatures.get(decl.name()))
            .map_or_else(|| decl.range().clone(), |(_, range)| range.clone())
    };
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_ptr` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe { ffi_guard_ptr(c, |ctx| alloc_sort(ctx, sort.clone())) }
}

// ============================================================================
// Boolean value
// ============================================================================

/// Get the boolean value of a constant AST.
///
/// Returns `Z3_L_TRUE`, `Z3_L_FALSE`, or `Z3_L_UNDEF` if not a boolean constant.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_get_bool_value(c: Z3_context, a: Z3_ast) -> c_int {
    if a == 0 {
        return Z3_L_UNDEF;
    }
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_int` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe {
        ffi_guard_int(c, Z3_L_UNDEF, |ctx| {
            let term =
                require_ast_or_return!(ctx, a, "Z3_get_bool_value", "Boolean term", Z3_L_UNDEF)
                    .term;
            match ctx.solver.bool_value(term) {
                Some(true) => Z3_L_TRUE,
                Some(false) => Z3_L_FALSE,
                None => Z3_L_UNDEF,
            }
        })
    }
}

// ============================================================================
// Numeral extraction
// ============================================================================

/// Try to extract an i32 value from a numeral AST.
///
/// Returns true and writes to `*v` if successful, false otherwise.
///
/// # Safety
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_get_numeral_int(c: Z3_context, a: Z3_ast, v: *mut c_int) -> bool {
    if a == 0 || v.is_null() {
        return false;
    }
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_int` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe {
        ffi_guard_int(c, 0, |ctx| {
            let term = require_ast_or_return!(ctx, a, "Z3_get_numeral_int", "numeral", 0).term;
            if let Some(s) = ctx.solver.numeral_string(term) {
                if let Ok(val) = s.parse::<c_int>() {
                    *v = val;
                    return 1;
                }
            }
            0
        }) != 0
    }
}

/// Try to extract a u32 value from a numeral AST.
///
/// Returns true and writes to `*v` if successful, false otherwise.
///
/// # Safety
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_get_numeral_uint(c: Z3_context, a: Z3_ast, v: *mut c_uint) -> bool {
    if a == 0 || v.is_null() {
        return false;
    }
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_int` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe {
        ffi_guard_int(c, 0, |ctx| {
            let term = require_ast_or_return!(ctx, a, "Z3_get_numeral_uint", "numeral", 0).term;
            if let Some(s) = ctx.solver.numeral_string(term) {
                if let Ok(val) = s.parse::<c_uint>() {
                    *v = val;
                    return 1;
                }
            }
            0
        }) != 0
    }
}

/// Try to extract an i64 value from a numeral AST.
///
/// Returns true and writes to `*v` if successful, false otherwise.
///
/// # Safety
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_get_numeral_int64(c: Z3_context, a: Z3_ast, v: *mut i64) -> bool {
    if a == 0 || v.is_null() {
        return false;
    }
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_int` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe {
        ffi_guard_int(c, 0, |ctx| {
            let term = require_ast_or_return!(ctx, a, "Z3_get_numeral_int64", "numeral", 0).term;
            if let Some(s) = ctx.solver.numeral_string(term) {
                if let Ok(val) = s.parse::<i64>() {
                    *v = val;
                    return 1;
                }
            }
            0
        }) != 0
    }
}

/// Try to extract a u64 value from a numeral AST.
///
/// Returns true and writes to `*v` if successful, false otherwise.
///
/// # Safety
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_get_numeral_uint64(c: Z3_context, a: Z3_ast, v: *mut u64) -> bool {
    if a == 0 || v.is_null() {
        return false;
    }
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_int` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe {
        ffi_guard_int(c, 0, |ctx| {
            let term = require_ast_or_return!(ctx, a, "Z3_get_numeral_uint64", "numeral", 0).term;
            if let Some(s) = ctx.solver.numeral_string(term) {
                if let Ok(val) = s.parse::<u64>() {
                    *v = val;
                    return 1;
                }
            }
            0
        }) != 0
    }
}

// ============================================================================
// Function declaration parameter introspection
// ============================================================================

/// Get the number of parameters associated with a function declaration.
///
/// For indexed operators like `(_ extract 7 4)`, returns the number of
/// integer parameters (2 in that case). For non-indexed operators, returns 0.
///
/// # Safety
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_get_decl_num_parameters(_c: Z3_context, d: Z3_func_decl) -> c_uint {
    if d.is_null() {
        return 0;
    }
    // SAFETY: the context guard catches panics and `d` is a context-owned,
    // null-checked declaration handle under the C API contract.
    unsafe {
        ffi_guard_uint(_c, 0, |ctx| {
            if finite_set_empty_decl_parameter(ctx, &(*d).decl).is_some()
                || super::getters_ext::as_array_decl_inner_name(&(*d).decl).is_some()
                || super::datatypes::is_recognizer_decl(d)
                || char_decl_code_point(ctx, &*d).is_some()
            {
                1
            } else if numeral_decl_int_parameter(&*d).is_some() {
                2
            } else if let Some(params) = bounded_value_decl_parameters(ctx, &*d) {
                params.len() as c_uint
            } else {
                (*d).params.len() as c_uint
            }
        })
    }
}

/// Get an integer parameter from a function declaration.
///
/// For indexed operators, returns the parameter at `idx`. For example,
/// `(_ extract 7 4)` has parameter 0 = 7 and parameter 1 = 4.
/// Returns 0 if `idx` is out of bounds or the decl has no parameters.
///
/// # Safety
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_get_decl_int_parameter(
    c: Z3_context,
    d: Z3_func_decl,
    idx: c_uint,
) -> c_int {
    if d.is_null() {
        return 0;
    }
    // SAFETY: `d` was null-checked above and originates from a prior AY FFI allocation whose
    // handle is kept alive by the owning `Z3Context` (see handle caches in `mod.rs`). Reading
    // `.params` is a shared-read with no concurrent mutation because the Z3 C API is
    // single-threaded per context. `ffi_guard_int` null-checks `c` and catches panics.
    unsafe {
        if idx == 1 {
            if let Some(value) = numeral_decl_int_parameter(&*d) {
                return value;
            }
        }
        let params = &(*d).params;
        let declared = params.get(idx as usize).copied().unwrap_or(0);
        if (*d)
            .value
            .is_none_or(|value| value.kind != super::Z3_OP_CHAR_CONST)
        {
            return declared;
        }
        ffi_guard_int(c, declared, |ctx| {
            match bounded_value_decl_parameters(ctx, &*d)
                .and_then(|params| params.get(idx as usize).cloned())
            {
                Some(BoundedValueParam::Int(value)) => value,
                _ => declared,
            }
        })
    }
}

/// Get the `Z3_parameter_kind` of a function declaration's `idx`-th parameter.
///
/// AY's indexed operators — `(_ extract h l)`, `(_ sign_extend n)`,
/// `(_ zero_extend n)`, `(_ repeat n)`, `(_ rotate_left n)`, … — report
/// `Z3_PARAMETER_INT`; Z3 5.0.0 finite-set `set.empty` reports one
/// `Z3_PARAMETER_SORT`. Read values through the corresponding typed getter.
///
/// For `idx >= Z3_get_decl_num_parameters(c, d)` this sets `Z3_IOB` (index out of
/// bounds) and returns `Z3_PARAMETER_INT` (`0`) as a benign default — the caller
/// should honor the `idx < num_parameters` precondition and check the error code.
///
/// # Safety
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_get_decl_parameter_kind(
    c: Z3_context,
    d: Z3_func_decl,
    idx: c_uint,
) -> c_uint {
    if d.is_null() {
        return Z3_PARAMETER_INT;
    }
    // SAFETY: `c` is guarded by `ffi_guard_uint`; `d` is a valid, non-aliasing
    // func_decl handle owned by the context (single-threaded read of `.params`).
    unsafe {
        ffi_guard_uint(c, Z3_PARAMETER_INT, |ctx| {
            if super::getters_ext::as_array_decl_inner_name(&(*d).decl).is_some() {
                if idx == 0 {
                    return super::Z3_PARAMETER_FUNC_DECL;
                }
                ctx.last_error = Z3_IOB;
                ctx.error_msg = Some(format!(
                    "Z3_get_decl_parameter_kind: index {idx} out of bounds (1 parameter)"
                ));
                return Z3_PARAMETER_INT;
            }
            if finite_set_empty_decl_parameter(ctx, &(*d).decl).is_some() {
                if idx == 0 {
                    return Z3_PARAMETER_SORT;
                }
                ctx.last_error = Z3_IOB;
                ctx.error_msg = Some(format!(
                    "Z3_get_decl_parameter_kind: index {idx} out of bounds (1 parameter)"
                ));
                return Z3_PARAMETER_INT;
            }
            if numeral_decl_int_parameter(&*d).is_some() {
                match idx {
                    0 => return super::Z3_PARAMETER_RATIONAL,
                    1 => return Z3_PARAMETER_INT,
                    _ => {
                        ctx.last_error = Z3_IOB;
                        ctx.error_msg = Some(format!(
                            "Z3_get_decl_parameter_kind: index {idx} out of bounds (2 parameters)"
                        ));
                        return Z3_PARAMETER_INT;
                    }
                }
            }
            if let Some(params) = bounded_value_decl_parameters(ctx, &*d) {
                if let Some(param) = params.get(idx as usize) {
                    return param.kind();
                }
                ctx.last_error = Z3_IOB;
                ctx.error_msg = Some(format!(
                    "Z3_get_decl_parameter_kind: index {idx} out of bounds ({} parameter(s))",
                    params.len()
                ));
                return Z3_PARAMETER_INT;
            }
            if super::datatypes::is_recognizer_decl(d) {
                if idx == 0 {
                    return super::Z3_PARAMETER_FUNC_DECL;
                }
                ctx.last_error = Z3_IOB;
                ctx.error_msg = Some(format!(
                    "Z3_get_decl_parameter_kind: index {idx} out of bounds (1 parameter)"
                ));
                return Z3_PARAMETER_INT;
            }
            let params = &(*d).params;
            if (idx as usize) < params.len() {
                // AY's only decl parameters are integers (indexed BV operators).
                Z3_PARAMETER_INT
            } else {
                ctx.last_error = Z3_IOB;
                ctx.error_msg = Some(format!(
                    "Z3_get_decl_parameter_kind: index {idx} out of bounds ({} parameter(s))",
                    params.len()
                ));
                Z3_PARAMETER_INT
            }
        })
    }
}
