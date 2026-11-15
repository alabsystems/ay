// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Z3 5.3 Complex constructors, backed by exact native component arithmetic.

use ay_dpll::api::{Solver, SolverError, Sort, Term};

use super::{
    alloc_sort, ffi_guard_mk, ffi_guard_ptr, mk_ast, require_term_ast_or_return, Z3Context, Z3_ast,
    Z3_context, Z3_sort, Z3_EXCEPTION,
};

pub(super) enum ComplexArithmetic {
    Add,
    Subtract,
    Multiply,
    Divide,
    Negate,
}

/// Claim only operations with a Complex operand; the existing scalar path
/// keeps its own coercion and integer-division contracts.
pub(super) fn arithmetic(
    ctx: &mut Z3Context,
    entry: &'static str,
    operands: &[super::PubTerm],
    operation: ComplexArithmetic,
) -> Option<Z3_ast> {
    if !operands
        .iter()
        .any(|operand| super::public_sort(ctx, *operand) == Sort::Complex)
    {
        return None;
    }
    let terms: Vec<_> = operands.iter().map(|operand| operand.term).collect();
    let sorts: Vec<_> = operands
        .iter()
        .map(|operand| super::public_sort(ctx, *operand))
        .collect();
    let terms = match lift_scalars(ctx, &terms, &sorts) {
        Ok(terms) => terms,
        Err(()) => return Some(0),
    };
    let result = match operation {
        ComplexArithmetic::Add => ctx.solver.try_add_many(&terms),
        ComplexArithmetic::Multiply => ctx.solver.try_mul_many(&terms),
        ComplexArithmetic::Subtract => subtract(&mut ctx.solver, &terms),
        ComplexArithmetic::Divide => match terms.as_slice() {
            [left, right] => ctx.solver.try_div(*left, *right),
            _ => Err(SolverError::InvalidArgument {
                operation: entry,
                message: "division requires two operands".to_string(),
            }),
        },
        ComplexArithmetic::Negate => match terms.as_slice() {
            [value] => ctx.solver.try_neg(*value),
            _ => Err(SolverError::InvalidArgument {
                operation: entry,
                message: "negation requires one operand".to_string(),
            }),
        },
    };
    Some(match result {
        Ok(term) => mk_ast(ctx, term, Sort::Complex),
        Err(error) => complex_error(ctx, error),
    })
}

fn subtract(solver: &mut Solver, terms: &[Term]) -> Result<Term, SolverError> {
    let Some((&first, rest)) = terms.split_first() else {
        return Err(SolverError::InvalidArgument {
            operation: "Z3_mk_sub",
            message: "subtraction requires an operand".to_string(),
        });
    };
    let mut result = first;
    for &term in rest {
        result = solver.try_sub(result, term)?;
    }
    Ok(result)
}

/// Promote equality/ITE operands to Complex when their builtin numeric join
/// is Complex. User-function application retains its declared domain checks.
pub(super) fn lift_scalars(
    ctx: &mut Z3Context,
    terms: &[Term],
    sorts: &[Sort],
) -> Result<Vec<Term>, ()> {
    let zero = ctx.solver.int_const(0);
    terms
        .iter()
        .zip(sorts)
        .map(|(&term, sort)| {
            if sort == &Sort::Complex {
                return Ok(term);
            }
            ctx.solver.try_complex(term, zero).map_err(|error| {
                complex_error(ctx, error);
            })
        })
        .collect()
}

/// Construct the nominal Complex sort.
///
/// # Safety
/// `c` must be null or a live context exclusively owned by the calling thread.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_complex_sort(c: Z3_context) -> Z3_sort {
    // SAFETY: the context ownership contract is forwarded to the null/panic guard.
    unsafe { ffi_guard_ptr(c, |ctx| alloc_sort(ctx, Sort::Complex)) }
}

/// Construct a Complex value from two Real components, promoting Int exactly.
///
/// # Safety
/// `c` must be live and exclusively owned, and both AST handles must belong to it.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_complex(c: Z3_context, real: Z3_ast, imaginary: Z3_ast) -> Z3_ast {
    // SAFETY: the guard and handle checks enforce the caller's context/AST contract.
    unsafe {
        ffi_guard_mk(c, "Z3_mk_complex", |ctx| {
            let real = require_term_ast_or_return!(ctx, real, "Z3_mk_complex", "real", 0);
            let imaginary =
                require_term_ast_or_return!(ctx, imaginary, "Z3_mk_complex", "imaginary", 0);
            match ctx.solver.try_complex(real, imaginary) {
                Ok(term) => mk_ast(ctx, term, Sort::Complex),
                Err(error) => complex_error(ctx, error),
            }
        })
    }
}

/// Return the real component, promoting an Int/Real scalar exactly.
///
/// # Safety
/// `c` must be live and exclusively owned, and `value` must belong to it.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_real_part(c: Z3_context, value: Z3_ast) -> Z3_ast {
    // SAFETY: the guard and handle check enforce the caller's context/AST contract.
    unsafe {
        ffi_guard_mk(c, "Z3_mk_real_part", |ctx| {
            project(ctx, value, "Z3_mk_real_part", Solver::try_real_part)
        })
    }
}

/// Return the imaginary component (zero for an Int/Real scalar).
///
/// # Safety
/// `c` must be live and exclusively owned, and `value` must belong to it.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_imag_part(c: Z3_context, value: Z3_ast) -> Z3_ast {
    // SAFETY: the guard and handle check enforce the caller's context/AST contract.
    unsafe {
        ffi_guard_mk(c, "Z3_mk_imag_part", |ctx| {
            project(ctx, value, "Z3_mk_imag_part", Solver::try_imag_part)
        })
    }
}

fn project(
    ctx: &mut Z3Context,
    value: Z3_ast,
    entry: &'static str,
    projection: fn(&mut Solver, Term) -> Result<Term, SolverError>,
) -> Z3_ast {
    let value = require_term_ast_or_return!(ctx, value, entry, "operand", 0);
    match projection(&mut ctx.solver, value) {
        Ok(term) => mk_ast(ctx, term, Sort::Real),
        Err(error) => complex_error(ctx, error),
    }
}

fn complex_error(ctx: &mut Z3Context, error: SolverError) -> Z3_ast {
    ctx.last_error = Z3_EXCEPTION;
    ctx.error_msg = Some(error.to_string());
    0
}
