// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Z3-compatible arithmetic, comparison, conversion, array, and AST inspection functions.
//!
//! All functions that call into the solver are wrapped in `catch_unwind` via
//! the `ffi_guard_*` helpers (#6192) to prevent undefined behavior from panics
//! unwinding across the `extern "C"` boundary.

use std::ffi::c_uint;

use super::complex::{arithmetic as complex_arithmetic, ComplexArithmetic};
use ay_dpll::api::{SolverError, Sort, Term};

use super::{
    alloc_sort, bounded_sort_hi, ffi_count_within_limit, ffi_guard_ast, ffi_guard_mk,
    ffi_guard_ptr, finite_set_engine_public_sort, has_unsupported_finite_set_datatype_embedding,
    mk_ast, pub_to_ast, public_sort, render_public_sort, require_ast_or_return,
    require_asts_or_return, stated_sort, PubTerm, Z3Context, Z3_ast, Z3_context, Z3_sort,
    Z3_INVALID_ARG, Z3_SORT_ERROR,
};

// ---- Arithmetic operations ----
//
// z3 types arithmetic by its operands' sorts and coerces a mixed Int/Real
// application the way the SMT-LIB arithmetic logics do: each Int operand of an
// operation that has a Real operand becomes `(to_real t)`, and the result is
// Real (libz3 5.1.0, measured through the C API: `Z3_mk_add(dx:Int, dy:Real)`
// is `(+ (to_real dx) dy)` of sort Real; `Z3_mk_gt` and `Z3_mk_eq` likewise;
// judge_fid/f1.py d). AY's builders take one arithmetic sort, so a mixed call
// used to PANIC inside `add_many` (caught at the FFI boundary as
// "panic in FFI"). An operand that is neither Int nor Real is a sort error, as
// in z3 for bit-vectors, finite domains and characters (measured); z3 also
// coerces a Bool operand to `(ite b 1 0)`, and a Real operand of an integer
// operator to the LOSSY `(to_int t)`, both of which AY refuses instead (T5
// design §4 P0.2 Q4: z3's shape or an error, never a panic).

/// Which operand sorts an operation admits.
#[derive(Clone, Copy)]
enum Operands {
    /// Int and Real only: z3's arithmetic operators.
    Arithmetic,
    /// Int and Real, and a Char or finite-domain operand compared by its Int
    /// carrier. z3 refuses that operand (measured); AY keeps accepting it in
    /// comparisons, whose Bool result cannot leave the carrier, as its
    /// soundness tests pin (`bounded_gap_tests`, `feasible_tier_tests`).
    Comparison,
}

/// Whether a public operand sort is Real (`Some(true)`), Int or an admitted
/// Int carrier (`Some(false)`), or not admitted (`None`).
fn arith_is_real(sort: &Sort, admit: Operands) -> Option<bool> {
    match (sort, admit) {
        (Sort::Int, _) => Some(false),
        (Sort::Real, _) => Some(true),
        (_, Operands::Comparison) if bounded_sort_hi(sort).is_some() => Some(false),
        _ => None,
    }
}

/// Report a non-arithmetic operand as z3 does (`Z3_SORT_ERROR`).
fn arith_operand_error(ctx: &mut Z3Context, entry: &str, position: usize, sort: &Sort) {
    let shown = render_public_sort(ctx, sort);
    ctx.last_error = Z3_SORT_ERROR;
    ctx.error_msg = Some(format!(
        "{entry}: Sort mismatch at argument #{position}: supplied sort is {shown}, but an \
         arithmetic operand must be Int or Real"
    ));
}

/// Report a builder refusal as a sort error (never a panic).
fn arith_builder_error(ctx: &mut Z3Context, entry: &str, error: &SolverError) {
    ctx.last_error = Z3_SORT_ERROR;
    ctx.error_msg = Some(format!("{entry}: {error}"));
}

/// Whether each operand is Real; `None` (with `Z3_SORT_ERROR` set) when one
/// is not admitted.
fn arith_operand_kinds(
    ctx: &mut Z3Context,
    entry: &str,
    operands: &[PubTerm],
    admit: Operands,
) -> Option<Vec<bool>> {
    let mut kinds = Vec::with_capacity(operands.len());
    for (position, &operand) in operands.iter().enumerate() {
        let sort = public_sort(ctx, operand);
        let Some(is_real) = arith_is_real(&sort, admit) else {
            arith_operand_error(ctx, entry, position + 1, &sort);
            return None;
        };
        kinds.push(is_real);
    }
    Some(kinds)
}

/// `(to_real t)` for each Int operand, the operand itself for a Real one.
fn lift_to_real(
    ctx: &mut Z3Context,
    entry: &str,
    terms: &[Term],
    kinds: &[bool],
) -> Option<Vec<Term>> {
    let mut lifted = Vec::with_capacity(terms.len());
    for (&term, &is_real) in terms.iter().zip(kinds) {
        if is_real {
            lifted.push(term);
            continue;
        }
        match ctx.solver.try_int_to_real(term) {
            Ok(real) => lifted.push(real),
            Err(e) => {
                arith_builder_error(ctx, entry, &e);
                return None;
            }
        }
    }
    Some(lifted)
}

/// z3's Int/Real coercion of an operation's operands: every Int operand
/// becomes `(to_real t)` when any operand is Real. Returns the operands and
/// their common sort; `None` (with the error set) when one is not admitted.
fn coerce_arith_operands(
    ctx: &mut Z3Context,
    entry: &str,
    operands: &[PubTerm],
    admit: Operands,
) -> Option<(Vec<Term>, Sort)> {
    let kinds = arith_operand_kinds(ctx, entry, operands, admit)?;
    let terms: Vec<Term> = operands.iter().map(|operand| operand.term).collect();
    if kinds.iter().any(|&is_real| is_real) {
        Some((lift_to_real(ctx, entry, &terms, &kinds)?, Sort::Real))
    } else {
        Some((terms, Sort::Int))
    }
}

/// Refuse a Real operand of an integer operator: z3 inserts the LOSSY
/// `(to_int t)` (measured: `Z3_mk_mod(y:Real, y:Real)` is
/// `(mod (to_int y) (to_int y))`), which AY does not do silently.
fn lossy_coercion_error(ctx: &mut Z3Context, entry: &str, position: usize) {
    ctx.last_error = Z3_SORT_ERROR;
    ctx.error_msg = Some(format!(
        "{entry}: argument #{position} is Real, and this operator takes Int; z3 coerces it \
         with the lossy (to_int ..), which AY does not insert; refusing"
    ));
}

/// z3's coercion for an operation whose operands must share ONE sort but may
/// be any sort (`=`, `distinct`, `ite` branches): when every operand is Int or
/// Real and both occur, each Int operand becomes `(to_real t)` and the common
/// sort is Real (measured: `Z3_mk_eq(dx:Int, dy:Real)` is
/// `(= (to_real dx) dy)`). `None` when the sorts are not such a mix, so the
/// caller keeps its own same-sort check; `Some(Err(()))` when the lift failed
/// (the error is set).
pub(crate) fn coerce_mixed_int_real(
    ctx: &mut Z3Context,
    entry: &str,
    terms: &[Term],
    sorts: &[Sort],
) -> Option<Result<Vec<Term>, ()>> {
    if sorts.iter().any(|sort| sort == &Sort::Complex)
        && sorts
            .iter()
            .all(|sort| matches!(sort, Sort::Int | Sort::Real | Sort::Complex))
    {
        return Some(super::complex::lift_scalars(ctx, terms, sorts));
    }
    let kinds: Option<Vec<bool>> = sorts
        .iter()
        .map(|sort| arith_is_real(sort, Operands::Arithmetic))
        .collect();
    let kinds = kinds?;
    let any_real = kinds.iter().any(|&is_real| is_real);
    let any_int = kinds.iter().any(|&is_real| !is_real);
    if !(any_real && any_int) {
        return None;
    }
    Some(lift_to_real(ctx, entry, terms, &kinds).ok_or(()))
}

/// Helper for n-ary arithmetic operations: z3's Int/Real coercion, then the
/// fallible builder; the result sort is the operands' common sort.
macro_rules! arith_nary_op {
    ($name:ident, $operator:ident, $complex:ident) => {
        /// # Safety
        /// All pointers must be valid. `args` must point to `num_args` elements.
        #[no_mangle]
        pub unsafe extern "C" fn $name(
            c: Z3_context,
            num_args: c_uint,
            args: *const Z3_ast,
        ) -> Z3_ast {
            // SAFETY: this public entry point requires `c` to be null or a live,
            // exclusively borrowed context; the bound checker only updates its error state.
            if !unsafe { ffi_count_within_limit(c, stringify!($name), num_args) } {
                return 0;
            }
            if num_args == 0 || args.is_null() {
                // z3: "no arguments supplied to arithmetical operator" (measured).
                // SAFETY: `c` is the caller's context pointer; the guard null-checks it.
                return unsafe {
                    ffi_guard_ast(c, |ctx| {
                        ctx.last_error = Z3_INVALID_ARG;
                        ctx.error_msg = Some(format!(
                            "{}: no arguments supplied to an arithmetic operator",
                            stringify!($name)
                        ));
                        0
                    })
                };
            }
            // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on
            // this extern "C" function requires it to be a valid, non-aliased pointer (or
            // null). `ffi_guard_ast` handles the null case internally and catches any
            // unwinding panic so it cannot cross the FFI boundary.
            unsafe {
                super::ffi_guard_arithmetic_owned(
                    c,
                    stringify!($name),
                    num_args as usize,
                    |ctx, operation| {
                        let owner = operation.admission();
                        let mut arg_asts = Vec::new();
                        if ay_core::term::reserve_counted(&mut arg_asts, num_args as usize, owner)
                            .is_err()
                            || owner
                                .admit(
                                    num_args as usize,
                                    (num_args as usize)
                                        .checked_mul(std::mem::size_of::<PubTerm>())
                                        .unwrap_or(usize::MAX),
                                )
                                .is_err()
                            || !operation.validate(&ctx.solver)
                        {
                            ctx.last_error = super::Z3_EXCEPTION;
                            return 0;
                        }
                        for i in 0..num_args as usize {
                            // SAFETY: count/null checks above and the caller's
                            // allocation contract cover each original argument.
                            arg_asts.push(*args.add(i));
                        }
                        let operands =
                            require_asts_or_return!(ctx, &arg_asts, stringify!($name), 0);
                        let mut kinds = Vec::new();
                        if ay_core::term::reserve_counted(&mut kinds, operands.len(), owner)
                            .is_err()
                        {
                            ctx.last_error = super::Z3_EXCEPTION;
                            return 0;
                        }
                        let mut complex = false;
                        for (position, operand) in operands.iter().enumerate() {
                            // A public FD/Char alias must not acquire arithmetic
                            // semantics through its internal Int carrier.
                            if super::lookup_ast_sort(ctx, arg_asts[position]).is_some_and(|sort| {
                                !matches!(sort, Sort::Int | Sort::Real | Sort::Complex)
                            }) {
                                ctx.last_error = Z3_SORT_ERROR;
                                return 0;
                            }
                            let mut found = None;
                            for (sort, real) in [
                                (Sort::Int, false),
                                (Sort::Real, true),
                                (Sort::Complex, false),
                            ] {
                                match ctx.solver.term_has_sort_in_operation(
                                    operation,
                                    operand.term,
                                    &sort,
                                ) {
                                    Ok(true) => {
                                        complex |= sort == Sort::Complex;
                                        found = Some(real);
                                        break;
                                    }
                                    Ok(false) => {}
                                    Err(error) => {
                                        arith_builder_error(ctx, stringify!($name), &error);
                                        return 0;
                                    }
                                }
                            }
                            let Some(real) = found else {
                                ctx.last_error = Z3_SORT_ERROR;
                                return 0;
                            };
                            kinds.push(real);
                        }
                        if complex {
                            if let Some(result) = complex_arithmetic(
                                ctx,
                                stringify!($name),
                                &operands,
                                ComplexArithmetic::$complex,
                            ) {
                                return result;
                            }
                            ctx.last_error = Z3_SORT_ERROR;
                            return 0;
                        }
                        if owner.admit(kinds.len(), 0).is_err() || !operation.validate(&ctx.solver)
                        {
                            ctx.last_error = super::Z3_EXCEPTION;
                            return 0;
                        }
                        let real = kinds.iter().any(|value| *value);
                        let mut terms = Vec::new();
                        if ay_core::term::reserve_counted(&mut terms, operands.len(), owner)
                            .is_err()
                            || owner.admit(operands.len(), 0).is_err()
                            || !operation.validate(&ctx.solver)
                        {
                            ctx.last_error = super::Z3_EXCEPTION;
                            return 0;
                        }
                        for (operand, already_real) in operands.iter().zip(kinds) {
                            let term = if real && !already_real {
                                match ctx.solver.try_arithmetic_application_in_operation(
                                    operation,
                                    ay_core::term::CountedRingBuiltin::ToReal,
                                    &[operand.term],
                                ) {
                                    Ok(term) => term,
                                    Err(error) => {
                                        arith_builder_error(ctx, stringify!($name), &error);
                                        return 0;
                                    }
                                }
                            } else {
                                operand.term
                            };
                            terms.push(term);
                        }
                        let t = match ctx.solver.try_arithmetic_application_in_operation(
                            operation,
                            ay_core::term::CountedRingBuiltin::$operator,
                            &terms,
                        ) {
                            Ok(t) => t,
                            Err(e) => {
                                arith_builder_error(ctx, stringify!($name), &e);
                                return 0;
                            }
                        };
                        match ctx.pub_ast.engine_node_owned(t, Some(owner)) {
                            Some(id) if operation.validate(&ctx.solver) => {
                                super::pub_id_to_ast(ctx, id)
                            }
                            _ => {
                                ctx.last_error = super::Z3_EXCEPTION;
                                0
                            }
                        }
                    },
                )
            }
        }
    };
}

arith_nary_op!(Z3_mk_add, Add, Add);
arith_nary_op!(Z3_mk_mul, Multiply, Multiply);

/// Create subtraction (left-associative).
///
/// z3 coerces each step: `Z3_mk_sub(x:Int, x:Int, y:Real)` is
/// `(- (to_real (- x x)) y)` (measured). With one argument z3 returns that
/// argument itself (measured: `sub1` is `eq` to its argument).
///
/// # Safety
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_sub(c: Z3_context, num_args: c_uint, args: *const Z3_ast) -> Z3_ast {
    // SAFETY: this public entry point requires `c` to be null or a live,
    // exclusively borrowed context; the bound checker only updates its error state.
    if !unsafe { ffi_count_within_limit(c, "Z3_mk_sub", num_args) } {
        return 0;
    }
    if num_args == 0 || args.is_null() {
        // SAFETY: `c` is the caller's context pointer; the guard null-checks it.
        return unsafe {
            ffi_guard_ast(c, |ctx| {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg = Some("Z3_mk_sub requires at least one argument".to_string());
                0
            })
        };
    }
    let arg_asts: Vec<_> = (0..num_args as usize)
        // SAFETY: The caller's `# Safety` contract guarantees `args` points to at least the
        // declared number of elements. The count was range-checked above, and null-checked
        // before entering this block, so `args.add(i)` stays within the caller's allocation.
        .map(|i| unsafe { *args.add(i) })
        .collect();
    if let [only] = arg_asts.as_slice() {
        let only = *only;
        // The argument itself, unchanged: no new term, so no construction
        // record (`ffi_guard_mk` would mark the caller's term ambiguous).
        // SAFETY: `c` is the caller's context pointer; the guard null-checks it.
        return unsafe {
            ffi_guard_ast(c, |ctx| {
                let operand = require_ast_or_return!(ctx, only, "Z3_mk_sub", "operand", 0);
                if public_sort(ctx, operand) == Sort::Complex {
                    return pub_to_ast(ctx, operand);
                }
                match arith_operand_kinds(ctx, "Z3_mk_sub", &[operand], Operands::Arithmetic) {
                    Some(_) => pub_to_ast(ctx, operand),
                    None => 0,
                }
            })
        };
    }

    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_ast` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe {
        ffi_guard_mk(c, "Z3_mk_sub", |ctx| {
            let decoded = require_asts_or_return!(ctx, &arg_asts, "Z3_mk_sub", 0);
            if let Some(result) =
                complex_arithmetic(ctx, "Z3_mk_sub", &decoded, ComplexArithmetic::Subtract)
            {
                return result;
            }
            let Some(kinds) = arith_operand_kinds(ctx, "Z3_mk_sub", &decoded, Operands::Arithmetic)
            else {
                return 0;
            };
            let mut operands = decoded.iter().map(|operand| operand.term).zip(kinds);
            let Some((mut result, mut result_real)) = operands.next() else {
                return 0;
            };
            for (term, is_real) in operands {
                let to_real = result_real || is_real;
                let pair = if to_real {
                    let lifted =
                        lift_to_real(ctx, "Z3_mk_sub", &[result, term], &[result_real, is_real]);
                    let Some(lifted) = lifted else {
                        return 0;
                    };
                    lifted
                } else {
                    vec![result, term]
                };
                let [left, right] = pair.as_slice() else {
                    return 0;
                };
                result = match ctx.solver.try_sub(*left, *right) {
                    Ok(t) => t,
                    Err(e) => {
                        arith_builder_error(ctx, "Z3_mk_sub", &e);
                        return 0;
                    }
                };
                result_real = to_real;
            }
            mk_ast(
                ctx,
                result,
                if result_real { Sort::Real } else { Sort::Int },
            )
        })
    }
}

/// Create unary minus.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_unary_minus(c: Z3_context, arg: Z3_ast) -> Z3_ast {
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_ast` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe {
        ffi_guard_mk(c, "Z3_mk_unary_minus", |ctx| {
            let operand = require_ast_or_return!(ctx, arg, "Z3_mk_unary_minus", "operand", 0);
            if let Some(result) = complex_arithmetic(
                ctx,
                "Z3_mk_unary_minus",
                &[operand],
                ComplexArithmetic::Negate,
            ) {
                return result;
            }
            let Some((_, sort)) =
                coerce_arith_operands(ctx, "Z3_mk_unary_minus", &[operand], Operands::Arithmetic)
            else {
                return 0;
            };
            let t = match ctx.solver.try_neg(operand.term) {
                Ok(t) => t,
                Err(e) => {
                    arith_builder_error(ctx, "Z3_mk_unary_minus", &e);
                    return 0;
                }
            };
            mk_ast(ctx, t, sort)
        })
    }
}

/// Create division (integer or real based on argument sort).
///
/// As in z3, the first operand chooses: a Real dividend is real `/`, and an
/// Int divisor becomes `(to_real d)` (measured: `Z3_mk_div(y:Real, x:Int)` is
/// `(/ y (to_real x))`); an Int dividend is integer `div`. z3 lowers a Real
/// divisor of `div` with the lossy `(to_int d)` (measured), which AY refuses.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_div(c: Z3_context, arg1: Z3_ast, arg2: Z3_ast) -> Z3_ast {
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_ast` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe {
        ffi_guard_mk(c, "Z3_mk_div", |ctx| {
            let dividend = require_ast_or_return!(ctx, arg1, "Z3_mk_div", "dividend", 0);
            let divisor = require_ast_or_return!(ctx, arg2, "Z3_mk_div", "divisor", 0);
            if let Some(result) = complex_arithmetic(
                ctx,
                "Z3_mk_div",
                &[dividend, divisor],
                ComplexArithmetic::Divide,
            ) {
                return result;
            }
            let Some(kinds) =
                arith_operand_kinds(ctx, "Z3_mk_div", &[dividend, divisor], Operands::Arithmetic)
            else {
                return 0;
            };
            let (arg1_term, arg2_term) = (dividend.term, divisor.term);
            let real_dividend = kinds.first().copied().unwrap_or(false);
            let real_divisor = kinds.get(1).copied().unwrap_or(false);
            let built = if real_dividend {
                let divisor = if real_divisor {
                    Ok(arg2_term)
                } else {
                    ctx.solver.try_int_to_real(arg2_term)
                };
                divisor.and_then(|divisor| ctx.solver.try_div(arg1_term, divisor))
            } else if real_divisor {
                lossy_coercion_error(ctx, "Z3_mk_div", 2);
                return 0;
            } else {
                ctx.solver.try_int_div(arg1_term, arg2_term)
            };
            let t = match built {
                Ok(t) => t,
                Err(e) => {
                    arith_builder_error(ctx, "Z3_mk_div", &e);
                    return 0;
                }
            };
            mk_ast(ctx, t, if real_dividend { Sort::Real } else { Sort::Int })
        })
    }
}

/// The two operands of an integer-only operation (`mod`, `rem`). `None` (with
/// the error set) when an operand is not arithmetic, or is Real: z3 lowers a
/// Real operand with the lossy `(to_int t)` (measured: `Z3_mk_mod(y:Real,
/// y:Real)` is `(mod (to_int y) (to_int y))`), which AY refuses.
fn int_operands(ctx: &mut Z3Context, entry: &str, operands: [PubTerm; 2]) -> Option<(Term, Term)> {
    let kinds = arith_operand_kinds(ctx, entry, &operands, Operands::Arithmetic)?;
    if let Some(position) = kinds.iter().position(|&is_real| is_real) {
        lossy_coercion_error(ctx, entry, position + 1);
        return None;
    }
    let [a, b] = operands;
    Some((a.term, b.term))
}

/// Create integer modulo.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_mod(c: Z3_context, arg1: Z3_ast, arg2: Z3_ast) -> Z3_ast {
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_ast` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe {
        ffi_guard_mk(c, "Z3_mk_mod", |ctx| {
            let a1 = require_ast_or_return!(ctx, arg1, "Z3_mk_mod", "dividend", 0);
            let a2 = require_ast_or_return!(ctx, arg2, "Z3_mk_mod", "divisor", 0);
            let Some((a1, a2)) = int_operands(ctx, "Z3_mk_mod", [a1, a2]) else {
                return 0;
            };
            let t = match ctx.solver.try_modulo(a1, a2) {
                Ok(t) => t,
                Err(e) => {
                    arith_builder_error(ctx, "Z3_mk_mod", &e);
                    return 0;
                }
            };
            mk_ast(ctx, t, Sort::Int)
        })
    }
}

/// Create integer remainder (truncation remainder).
///
/// Unlike `mod` (Euclidean, always non-negative), `rem` has the same sign as
/// the dividend `a`. Defined as:
/// ```text
/// rem(a, b) = ite(a mod b = 0, 0, ite(a >= 0, a mod b, (a mod b) - |b|))
/// ```
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_rem(c: Z3_context, arg1: Z3_ast, arg2: Z3_ast) -> Z3_ast {
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_ast` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe {
        ffi_guard_mk(c, "Z3_mk_rem", |ctx| {
            let a = require_ast_or_return!(ctx, arg1, "Z3_mk_rem", "dividend", 0);
            let b = require_ast_or_return!(ctx, arg2, "Z3_mk_rem", "divisor", 0);
            let Some((a, b)) = int_operands(ctx, "Z3_mk_rem", [a, b]) else {
                return 0;
            };
            let zero = ctx.solver.int_const(0);
            // a mod b is Euclidean (always >= 0) in SMT-LIB
            let a_mod_b = ctx.solver.modulo(a, b);
            let mod_is_zero = ctx.solver.eq(a_mod_b, zero);
            let a_ge_zero = ctx.solver.ge(a, zero);
            let abs_b = ctx.solver.abs(b);
            // When a < 0 and mod != 0: rem = (a mod b) - |b| (makes result negative)
            let neg_case = ctx.solver.sub(a_mod_b, abs_b);
            let nonzero_case = ctx.solver.ite(a_ge_zero, a_mod_b, neg_case);
            let t = ctx.solver.ite(mod_is_zero, zero, nonzero_case);
            mk_ast(ctx, t, Sort::Int)
        })
    }
}

/// Helper for binary comparison operations (result is Bool), with z3's
/// Int/Real coercion of the operands.
macro_rules! arith_cmp_op {
    ($name:ident, $method:ident) => {
        /// # Safety
        /// `c` must be a valid context pointer.
        #[no_mangle]
        pub unsafe extern "C" fn $name(c: Z3_context, t1: Z3_ast, t2: Z3_ast) -> Z3_ast {
            // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on
            // this extern "C" function requires it to be a valid, non-aliased pointer (or
            // null). `ffi_guard_ast` handles the null case internally and catches any
            // unwinding panic so it cannot cross the FFI boundary.
            unsafe {
                ffi_guard_mk(c, stringify!($name), |ctx| {
                    let left =
                        require_ast_or_return!(ctx, t1, stringify!($name), "left operand", 0);
                    let right =
                        require_ast_or_return!(ctx, t2, stringify!($name), "right operand", 0);
                    let Some((operands, _)) = coerce_arith_operands(
                        ctx,
                        stringify!($name),
                        &[left, right],
                        Operands::Comparison,
                    ) else {
                        return 0;
                    };
                    let [left, right] = operands.as_slice() else {
                        return 0;
                    };
                    let t = match ctx.solver.$method(*left, *right) {
                        Ok(t) => t,
                        Err(e) => {
                            arith_builder_error(ctx, stringify!($name), &e);
                            return 0;
                        }
                    };
                    mk_ast(ctx, t, Sort::Bool)
                })
            }
        }
    };
}

arith_cmp_op!(Z3_mk_lt, try_lt);
arith_cmp_op!(Z3_mk_le, try_le);
arith_cmp_op!(Z3_mk_gt, try_gt);
arith_cmp_op!(Z3_mk_ge, try_ge);

/// Report an operand of the wrong arithmetic sort for a conversion.
fn conversion_operand_error(ctx: &mut Z3Context, entry: &str, expected: &str, sort: &Sort) {
    let shown = render_public_sort(ctx, sort);
    ctx.last_error = Z3_SORT_ERROR;
    ctx.error_msg = Some(format!(
        "{entry}: Sort mismatch at argument #1: supplied sort is {shown}, expected {expected}"
    ));
}

/// Convert int to real.
///
/// The operand must be Int (z3 also accepts a Real operand and keeps
/// `(to_real y)`; AY refuses it).
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_int2real(c: Z3_context, t1: Z3_ast) -> Z3_ast {
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_ast` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe {
        ffi_guard_mk(c, "Z3_mk_int2real", |ctx| {
            let operand = require_ast_or_return!(ctx, t1, "Z3_mk_int2real", "operand", 0);
            let sort = public_sort(ctx, operand);
            if sort != Sort::Int {
                conversion_operand_error(ctx, "Z3_mk_int2real", "Int", &sort);
                return 0;
            }
            let t = match ctx.solver.try_int_to_real(operand.term) {
                Ok(t) => t,
                Err(e) => {
                    arith_builder_error(ctx, "Z3_mk_int2real", &e);
                    return 0;
                }
            };
            mk_ast(ctx, t, Sort::Real)
        })
    }
}

/// A Real operand for a Real-domain operation (`to_int`, `is_int`): as in z3,
/// an Int operand becomes `(to_real t)` (measured: `Z3_mk_is_int(x:Int)` is
/// `(is_int (to_real x))`). `None` (with the error set) otherwise.
fn real_operand(ctx: &mut Z3Context, entry: &str, operand: PubTerm) -> Option<Term> {
    let sort = public_sort(ctx, operand);
    match arith_is_real(&sort, Operands::Arithmetic) {
        Some(true) => Some(operand.term),
        Some(false) => match ctx.solver.try_int_to_real(operand.term) {
            Ok(real) => Some(real),
            Err(e) => {
                arith_builder_error(ctx, entry, &e);
                None
            }
        },
        None => {
            conversion_operand_error(ctx, entry, "Real", &sort);
            None
        }
    }
}

/// Convert real to int (floor).
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_real2int(c: Z3_context, t1: Z3_ast) -> Z3_ast {
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_ast` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe {
        ffi_guard_mk(c, "Z3_mk_real2int", |ctx| {
            let operand = require_ast_or_return!(ctx, t1, "Z3_mk_real2int", "operand", 0);
            let Some(t1) = real_operand(ctx, "Z3_mk_real2int", operand) else {
                return 0;
            };
            let t = match ctx.solver.try_real_to_int(t1) {
                Ok(t) => t,
                Err(e) => {
                    arith_builder_error(ctx, "Z3_mk_real2int", &e);
                    return 0;
                }
            };
            mk_ast(ctx, t, Sort::Int)
        })
    }
}

/// Check if a real is an integer.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_is_int(c: Z3_context, t1: Z3_ast) -> Z3_ast {
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_ast` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe {
        ffi_guard_mk(c, "Z3_mk_is_int", |ctx| {
            let operand = require_ast_or_return!(ctx, t1, "Z3_mk_is_int", "operand", 0);
            let Some(t1) = real_operand(ctx, "Z3_mk_is_int", operand) else {
                return 0;
            };
            let t = match ctx.solver.try_is_int(t1) {
                Ok(t) => t,
                Err(e) => {
                    arith_builder_error(ctx, "Z3_mk_is_int", &e);
                    return 0;
                }
            };
            mk_ast(ctx, t, Sort::Bool)
        })
    }
}

/// Create absolute value.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_abs(c: Z3_context, arg: Z3_ast) -> Z3_ast {
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_ast` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe {
        ffi_guard_mk(c, "Z3_mk_abs", |ctx| {
            let operand = require_ast_or_return!(ctx, arg, "Z3_mk_abs", "operand", 0);
            let Some((_, sort)) =
                coerce_arith_operands(ctx, "Z3_mk_abs", &[operand], Operands::Arithmetic)
            else {
                return 0;
            };
            let t = match ctx.solver.try_abs(operand.term) {
                Ok(t) => t,
                Err(e) => {
                    arith_builder_error(ctx, "Z3_mk_abs", &e);
                    return 0;
                }
            };
            mk_ast(ctx, t, sort)
        })
    }
}

/// Create exponentiation (arg1 ^ arg2).
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_power(c: Z3_context, arg1: Z3_ast, arg2: Z3_ast) -> Z3_ast {
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_ast` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe {
        ffi_guard_mk(c, "Z3_mk_power", |ctx| {
            let base = require_ast_or_return!(ctx, arg1, "Z3_mk_power", "base", 0);
            let exponent = require_ast_or_return!(ctx, arg2, "Z3_mk_power", "exponent", 0);
            // Mixed operands: z3 gives `(^ (to_real x) y)` (measured).
            let Some((operands, _)) =
                coerce_arith_operands(ctx, "Z3_mk_power", &[base, exponent], Operands::Arithmetic)
            else {
                return 0;
            };
            let [base, exponent] = operands.as_slice() else {
                return 0;
            };
            // Z3 types `^` as `Real` even over `Int` operands (z3 5.1:
            // `(a**2).sort()` is `Real`); the result sort is the term's own.
            let t = match ctx.solver.try_power(*base, *exponent) {
                Ok(t) => t,
                Err(e) => {
                    arith_builder_error(ctx, "Z3_mk_power", &e);
                    return 0;
                }
            };
            let sort = ctx.solver.term_sort(t);
            mk_ast(ctx, t, sort)
        })
    }
}

// ---- Array operations ----

/// Create array select (read).
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_select(c: Z3_context, a: Z3_ast, i: Z3_ast) -> Z3_ast {
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_ast` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe {
        ffi_guard_mk(c, "Z3_mk_select", |ctx| {
            let array = require_ast_or_return!(ctx, a, "Z3_mk_select", "array", 0);
            let index = require_ast_or_return!(ctx, i, "Z3_mk_select", "index", 0);
            let public_array = public_sort(ctx, array);
            let Sort::Array(public_array) = public_array else {
                ctx.last_error = Z3_SORT_ERROR;
                ctx.error_msg =
                    Some("Z3_mk_select: public operand sort is not an Array".to_string());
                return 0;
            };
            let public_index = public_sort(ctx, index);
            if public_index != public_array.index_sort {
                ctx.last_error = Z3_SORT_ERROR;
                ctx.error_msg = Some(format!(
                    "Z3_mk_select: public index sort {public_index} differs from array domain {}",
                    public_array.index_sort
                ));
                return 0;
            }
            let t = ctx.solver.select(array.term, index.term);
            mk_ast(ctx, t, public_array.element_sort)
        })
    }
}

/// Create array store (write).
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_store(c: Z3_context, a: Z3_ast, i: Z3_ast, v: Z3_ast) -> Z3_ast {
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_ast` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe {
        ffi_guard_mk(c, "Z3_mk_store", |ctx| {
            let array = require_ast_or_return!(ctx, a, "Z3_mk_store", "array", 0);
            let index = require_ast_or_return!(ctx, i, "Z3_mk_store", "index", 0);
            let value = require_ast_or_return!(ctx, v, "Z3_mk_store", "value", 0);
            let public_array = public_sort(ctx, array);
            let Sort::Array(public_array_info) = &public_array else {
                ctx.last_error = Z3_SORT_ERROR;
                ctx.error_msg =
                    Some("Z3_mk_store: public operand sort is not an Array".to_string());
                return 0;
            };
            let public_index = public_sort(ctx, index);
            let public_value = public_sort(ctx, value);
            if public_index != public_array_info.index_sort
                || public_value != public_array_info.element_sort
            {
                ctx.last_error = Z3_SORT_ERROR;
                ctx.error_msg = Some(format!(
                    "Z3_mk_store: expected public index/value sorts {}/{}; got {public_index}/{public_value}",
                    public_array_info.index_sort, public_array_info.element_sort
                ));
                return 0;
            }
            let t = ctx.solver.store(array.term, index.term, value.term);
            mk_ast(ctx, t, public_array)
        })
    }
}

/// Create a constant array.
///
/// # Safety
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_const_array(c: Z3_context, domain: Z3_sort, v: Z3_ast) -> Z3_ast {
    if domain.is_null() {
        return 0;
    }
    // SAFETY: `domain` was null-checked above and originates from a prior AY FFI allocation
    // whose handle is kept alive by the owning `Z3Context` (see handle caches in `mod.rs`).
    // Reading `.sort` is a shared-read with no concurrent mutation because the Z3 C API is
    // single-threaded per context.
    let domain_sort = unsafe { (*domain).sort.clone() };

    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_ast` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe {
        ffi_guard_mk(c, "Z3_mk_const_array", |ctx| {
            let value = require_ast_or_return!(ctx, v, "Z3_mk_const_array", "value", 0);
            if has_unsupported_finite_set_datatype_embedding(ctx, &domain_sort) {
                ctx.last_error = Z3_SORT_ERROR;
                ctx.error_msg = Some(
                    "Z3_mk_const_array: a datatype containing FiniteSet fields cannot be lowered"
                        .to_string(),
                );
                return 0;
            }
            let element_sort = public_sort(ctx, value);
            let engine_domain = finite_set_engine_public_sort(ctx, &domain_sort);
            let t = ctx.solver.const_array(engine_domain, value.term);
            mk_ast(ctx, t, Sort::array(domain_sort, element_sort))
        })
    }
}

// ---- AST inspection ----

/// Get the sort of an AST.
///
/// # Safety
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_get_sort(c: Z3_context, a: Z3_ast) -> Z3_sort {
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_ptr` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe {
        ffi_guard_ptr(c, |ctx| {
            if super::proof_dag::application(ctx, a).is_some() {
                return alloc_sort(ctx, super::proof_dag::proof_sort());
            }
            let decoded =
                require_ast_or_return!(ctx, a, "Z3_get_sort", "AST", std::ptr::null_mut());
            if let Some(sort) = stated_sort(ctx, decoded).cloned() {
                return alloc_sort(ctx, sort);
            }
            // No public sort was stated for a term surfaced from INSIDE the
            // engine (e.g. normalized consequence clauses from
            // Z3_solver_get_consequences, units/trail literals). Use the
            // solver's own sort for the term, the ground truth, and state it:
            // the node has no sort yet, so it takes this one in place and
            // keeps its handle.
            let sort = ctx.solver.term_sort(decoded.term);
            let _same_handle = mk_ast(ctx, decoded.term, sort.clone());
            alloc_sort(ctx, sort)
        })
    }
}
