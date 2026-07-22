// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Z3-compatible incremental SMT-LIB parser context
//! (`Z3_mk_parser_context` + `Z3_parser_context_*`).
//!
//! # What this is
//!
//! Z3's `Z3_parser_context` lets a consumer parse SMT-LIB2 text INCREMENTALLY:
//! declarations (sorts / functions) added directly via
//! [`Z3_parser_context_add_sort`] / [`Z3_parser_context_add_decl`], and those
//! introduced by an earlier [`Z3_parser_context_from_string`], persist and are
//! visible to later parses through a shared symbol table.
//!
//! # How AY backs it (real, not a stub)
//!
//! Every call routes through AY's real SMT-LIB2 front-end,
//! [`Solver::parse_smtlib2`](ay_dpll::api::Solver::parse_smtlib2) — the SAME
//! parser/elaborator the CLI and [`Z3_parse_smtlib2_string`] use. That parser's
//! executor keeps a PERSISTENT symbol table across calls, so declarations from
//! one parse are automatically in scope for the next; that is exactly the
//! incremental behaviour Z3's parser context provides.
//!
//! AY has a single `Solver` per `Z3_context`, and its term store is the store
//! every `Z3_ast` handle indexes. Parsing therefore routes through THAT solver
//! (`ctx.solver`), so the assertion terms the parser context returns are
//! interned in — and valid against — the parent `Z3_context`: the consumer can
//! immediately inspect them (`Z3_get_ast_kind`, `Z3_ast_to_string`, …) and solve
//! them on any `Z3_solver` of the same context. (Handing back a term from a
//! private, separate solver would alias a foreign term store — a soundness bug —
//! so we deliberately do not do that.) The consequence is that AY's parser
//! context threads its declarations into the context's shared symbol table
//! rather than an isolated one; this is documented and honest.
//!
//! `add_sort`/`add_decl` record the injected sort/decl on the handle; at parse
//! time [`Z3_parser_context_from_string`] (re-)threads them into the solver's
//! symbol table (uninterpreted-sort `declare-sort` and arity>0 function
//! signatures are idempotent, rebind-safe symbol-table insertions) so the string
//! can reference them by name. Datatype sorts and any function created by
//! `Z3_mk_func_decl` are already registered on the solver when they are built, so
//! re-threading them is unnecessary and skipped (re-declaring an arity-0 constant
//! would mint a FRESH term — an aliasing hazard — so we never do).
//!
//! All functions calling into the solver are wrapped via the `ffi_guard_*`
//! helpers (#6192) to keep panics from unwinding across the FFI boundary.

use std::ffi::CStr;

use ay_dpll::api::{FuncDecl, Sort};

use super::{
    cache_ast_vector, cache_parser_context, ffi_guard_ptr, ffi_guard_void, term_to_ast, Z3Context,
    Z3_ast_vector, Z3_context, Z3_func_decl, Z3_parser_context, Z3_sort, Z3_string, Z3_EXCEPTION,
    Z3_INVALID_ARG, Z3_OK,
};

/// Render `name` as an SMT-LIB symbol usable inside a synthesized command.
///
/// Returns the bare name when it is already a valid SMT-LIB *simple* symbol,
/// otherwise a `|...|`-quoted form. Returns `None` for a name that cannot be
/// represented as a quoted symbol (empty, or containing `|`/`\`). Callers reject
/// such declarations instead of recording a name that cannot later resolve.
fn smtlib_symbol(name: &str) -> Option<String> {
    if name.is_empty() {
        return None;
    }
    // SMT-LIB 2.6 simple-symbol character set.
    const EXTRA: &str = "~!@$%^&*_-+=<>.?/";
    let first = name.chars().next().unwrap_or('0');
    let is_simple = !first.is_ascii_digit()
        && name
            .chars()
            .all(|ch| ch.is_ascii_alphanumeric() || EXTRA.contains(ch));
    if is_simple {
        Some(name.to_string())
    } else if !name.contains('|') && !name.contains('\\') {
        Some(format!("|{name}|"))
    } else {
        None
    }
}

/// Declare `sort`'s NAME into the context solver's symbol table so a subsequent
/// parse resolves references to it.
///
/// - `Uninterpreted(name)` → `(declare-sort name 0)` (idempotent; a
///   `Z3_mk_uninterpreted_sort` sort is otherwise a handle only, unknown to the
///   parser).
/// - `Datatype`/built-in sorts are already known to the parser (a datatype comes
///   from `Z3_mk_datatype`, which declares it; `Int`/`Bool`/`(Array …)`/… are
///   primitive), so nothing is done.
fn declare_sort_into_solver(ctx: &mut Z3Context, sort: &Sort) -> Result<(), String> {
    if let Sort::Uninterpreted(name) = sort {
        let sym = smtlib_symbol(name).ok_or_else(|| {
            format!("uninterpreted sort name {name:?} cannot be represented in SMT-LIB")
        })?;
        // Idempotent: `declare-sort` just maps the name to an uninterpreted
        // sort in `sort_defs` (a plain insert), binding no term.
        ctx.solver
            .parse_smtlib2(&format!("(declare-sort {sym} 0)"))
            .map_err(|e| format!("cannot thread sort {name:?}: {e}"))?;
    }
    Ok(())
}

/// (Re-)thread a parser context's recorded declarations into the solver's
/// symbol table ahead of a parse. Idempotent and rebind-safe: uninterpreted
/// sorts and arity>0 function signatures are pure symbol-table insertions that
/// never rebind a term. Arity-0 constants are left alone (they were bound once,
/// at `Z3_mk_func_decl` time; re-declaring would mint a fresh term).
fn thread_declarations(
    ctx: &mut Z3Context,
    sorts: &[Sort],
    decls: &[FuncDecl],
) -> Result<(), String> {
    for s in sorts {
        declare_sort_into_solver(ctx, s)?;
    }
    for d in decls {
        if d.arity() > 0 {
            ctx.solver
                .try_declare_fun(d.name(), d.domain(), d.range().clone())
                .map_err(|e| format!("cannot thread declaration {:?}: {e}", d.name()))?;
        }
    }
    Ok(())
}

/// Create a new incremental parser context (Z3's `Z3_mk_parser_context`).
///
/// The handle is arena-owned by the context and lives until `Z3_del_context`.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_parser_context(c: Z3_context) -> Z3_parser_context {
    // SAFETY: `c` is the caller's context pointer (valid or null per the FFI
    // contract). `ffi_guard_ptr` handles the null case and catches panics.
    unsafe { ffi_guard_ptr(c, cache_parser_context) }
}

/// Increment the parser context's reference count (Z3's
/// `Z3_parser_context_inc_ref`).
///
/// Bookkeeping only: the handle is arena-owned and freed solely by
/// `Z3_del_context`, so this never allocates or frees. A null `pc` is a no-op.
///
/// # Safety
/// `c` must be a valid context pointer; `pc`, when non-null, a valid parser
/// context handle owned by `c`.
#[no_mangle]
pub unsafe extern "C" fn Z3_parser_context_inc_ref(c: Z3_context, pc: Z3_parser_context) {
    // SAFETY: `ffi_guard_void` validates/guards `c`; `pc` is null-checked via
    // `as_mut` and lives in a separate allocation, so it never aliases `*ctx`.
    unsafe {
        ffi_guard_void(c, |_ctx| {
            if let Some(handle) = pc.as_mut() {
                handle.refcount = handle.refcount.saturating_add(1);
            }
        });
    }
}

/// Decrement the parser context's reference count (Z3's
/// `Z3_parser_context_dec_ref`).
///
/// Bookkeeping only: NEVER frees the handle (it lives until `Z3_del_context`).
/// The count saturates at 0. A null `pc` is a no-op.
///
/// # Safety
/// `c` must be a valid context pointer; `pc`, when non-null, a valid parser
/// context handle owned by `c`.
#[no_mangle]
pub unsafe extern "C" fn Z3_parser_context_dec_ref(c: Z3_context, pc: Z3_parser_context) {
    // SAFETY: see `Z3_parser_context_inc_ref`.
    unsafe {
        ffi_guard_void(c, |_ctx| {
            if let Some(handle) = pc.as_mut() {
                handle.refcount = handle.refcount.saturating_sub(1);
            }
        });
    }
}

/// Add a sort to the parser context's symbol table (Z3's
/// `Z3_parser_context_add_sort`).
///
/// Records the sort on the handle and threads its declaration into the context
/// solver's symbol table, so a subsequent [`Z3_parser_context_from_string`] can
/// reference the sort by name. A null `pc`/`s` is a no-op.
///
/// # Safety
/// `c` must be a valid context pointer; `pc`, when non-null, a valid parser
/// context handle; `s`, when non-null, a valid sort handle — all owned by `c`.
#[no_mangle]
pub unsafe extern "C" fn Z3_parser_context_add_sort(
    c: Z3_context,
    pc: Z3_parser_context,
    s: Z3_sort,
) {
    // SAFETY: `ffi_guard_void` guards `c`; `pc`/`s` are separate allocations.
    unsafe {
        ffi_guard_void(c, |ctx| {
            if !ctx.decision_engine_is_usable("Z3_parser_context_add_sort") {
                return;
            }
            let Some(handle) = pc.as_mut() else {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg = Some("Z3_parser_context_add_sort: null parser context".to_string());
                return;
            };
            // MANDATORY decode before any deref: stock z3py passes
            // `sort.as_ast()` here (z3.py:9531) — a TAGGED u64 reinterpreted
            // as a pointer. A raw deref of that value is a garbage-pointer
            // SEGV, not a catchable panic. `sort_arg_handle` resolves tagged
            // values through the context's decode table and rejects
            // null/dangling ones.
            let Some(s) = super::sort_arg_handle(ctx, s) else {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg = Some("Z3_parser_context_add_sort: null sort".to_string());
                return;
            };
            // SAFETY: `s` was resolved to a live arena-owned handle above.
            let sort = (*s).sort.clone();
            if let Err(e) = declare_sort_into_solver(ctx, &sort) {
                ctx.last_error = Z3_EXCEPTION;
                ctx.error_msg = Some(format!("Z3_parser_context_add_sort: {e}"));
                return;
            }
            handle.added_sorts.push(sort);
            ctx.last_error = Z3_OK;
        });
    }
}

/// Add a function declaration to the parser context's symbol table (Z3's
/// `Z3_parser_context_add_decl`).
///
/// Records the decl on the handle. A function created by `Z3_mk_func_decl` is
/// already registered on the context solver (so it is immediately resolvable by
/// name in a subsequent parse); recording it lets
/// [`Z3_parser_context_from_string`] re-thread its signature defensively. A null
/// `pc`/`f` is a no-op.
///
/// # Safety
/// `c` must be a valid context pointer; `pc`, when non-null, a valid parser
/// context handle; `f`, when non-null, a valid func_decl handle — all owned by
/// `c`.
#[no_mangle]
pub unsafe extern "C" fn Z3_parser_context_add_decl(
    c: Z3_context,
    pc: Z3_parser_context,
    f: Z3_func_decl,
) {
    // SAFETY: `ffi_guard_void` guards `c`; `pc`/`f` are separate allocations.
    unsafe {
        ffi_guard_void(c, |ctx| {
            if !ctx.decision_engine_is_usable("Z3_parser_context_add_decl") {
                return;
            }
            let Some(handle) = pc.as_mut() else {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg = Some("Z3_parser_context_add_decl: null parser context".to_string());
                return;
            };
            // MANDATORY decode before any deref: stock z3py passes
            // `decl.as_ast()` here (z3.py:9534) — a TAGGED u64 reinterpreted
            // as a pointer; a raw deref would SEGV. See
            // `Z3_parser_context_add_sort`.
            let Some(f) = super::func_decl_arg_handle(ctx, f) else {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg = Some("Z3_parser_context_add_decl: null func_decl".to_string());
                return;
            };
            // SAFETY: `f` was resolved to a live arena-owned handle above.
            let decl = (*f).decl.clone();
            let display_name = (*f)
                .symbol
                .as_ref()
                .map(super::SymbolKey::display_name)
                .unwrap_or_else(|| decl.name().to_string());
            // Ensure an arity>0 signature is present (idempotent; a no-op when
            // `Z3_mk_func_decl` already declared it). Arity-0 constants are left
            // as-is to avoid rebinding their term (see module docs).
            if decl.arity() > 0 {
                if let Err(e) = ctx
                    .solver
                    .try_register_native_function_alias(&display_name, &decl)
                {
                    ctx.last_error = Z3_EXCEPTION;
                    ctx.error_msg = Some(format!("Z3_parser_context_add_decl: {e}"));
                    return;
                }
            }
            if !handle.added_decls.contains(&decl) {
                handle.added_decls.push(decl);
            }
            ctx.last_error = Z3_OK;
        });
    }
}

/// Parse an SMT-LIB2 string through the parser context, returning the parsed
/// assertions as an AST vector (Z3's `Z3_parser_context_from_string`).
///
/// Declarations and assertions in `s` are processed by AY's real SMT-LIB2
/// front-end; query commands (`check-sat`, `get-model`, …) are ignored. Any
/// sorts/decls added earlier via `add_sort`/`add_decl`, or declared by a
/// PREVIOUS `from_string` on this context, remain in scope — so parsing is
/// genuinely incremental. The returned vector holds exactly the assertions this
/// call added (matching Z3), each a real term valid in the parent `Z3_context`.
///
/// On a parse error the error state is set and an EMPTY vector is returned
/// (never a fabricated assertion). State-control commands are rejected before
/// execution; a late semantic error permanently fails the shared decision engine
/// closed rather than exposing partially changed declaration/option state.
///
/// # Safety
/// `c` must be a valid context pointer; `pc`, when non-null, a valid parser
/// context handle owned by `c`; `s`, when non-null, a valid null-terminated C
/// string.
#[no_mangle]
pub unsafe extern "C" fn Z3_parser_context_from_string(
    c: Z3_context,
    pc: Z3_parser_context,
    s: Z3_string,
) -> Z3_ast_vector {
    // Extract the input string outside the guard (raw-pointer deref).
    let input: Option<Result<String, ()>> = if s.is_null() {
        None
    } else {
        // SAFETY: caller contract: `s` is a valid null-terminated C string.
        Some(
            unsafe { CStr::from_ptr(s) }
                .to_str()
                .map(str::to_string)
                .map_err(|_| ()),
        )
    };
    // SAFETY: `ffi_guard_ptr` guards `c`; `pc` is a separate allocation.
    unsafe {
        ffi_guard_ptr(c, |ctx| {
            let Some(handle) = pc.as_mut() else {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg =
                    Some("Z3_parser_context_from_string: null parser context".to_string());
                return cache_ast_vector(ctx, Vec::new());
            };
            let text = match input {
                None => {
                    ctx.last_error = Z3_INVALID_ARG;
                    ctx.error_msg =
                        Some("Z3_parser_context_from_string: null input string".to_string());
                    return cache_ast_vector(ctx, Vec::new());
                }
                Some(Err(())) => {
                    ctx.last_error = Z3_EXCEPTION;
                    ctx.error_msg =
                        Some("Z3_parser_context_from_string: invalid UTF-8 in input".to_string());
                    return cache_ast_vector(ctx, Vec::new());
                }
                Some(Ok(t)) => t,
            };
            // (Re-)thread this context's recorded declarations so the string can
            // reference them (cloned to detach the borrow from `ctx`).
            let sorts = handle.added_sorts.clone();
            let decls = handle.added_decls.clone();
            if let Err(e) = thread_declarations(ctx, &sorts, &decls) {
                ctx.last_error = Z3_EXCEPTION;
                ctx.error_msg = Some(format!("Z3_parser_context_from_string: {e}"));
                return cache_ast_vector(ctx, Vec::new());
            }
            let terms = super::solver::parse_solver_transaction(
                ctx,
                &text,
                "Z3_parser_context_from_string",
            )
            .unwrap_or_default();
            let asts = terms.into_iter().map(term_to_ast).collect();
            cache_ast_vector(ctx, asts)
        })
    }
}

#[cfg(test)]
#[path = "parser_context_ffi_tests.rs"]
mod parser_context_ffi_tests;
