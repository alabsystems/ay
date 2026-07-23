// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Z3-compatible `Fixedpoint` extension surface: the `Z3_fixedpoint_*` C-API
//! entry points beyond the core declare/add-rule/query set implemented in the
//! sibling `fixedpoint` module.
//!
//! This file splits into two honest halves:
//!
//! # Real functions (reuse the existing `FixedpointHandle` machinery)
//!
//! - [`Z3_fixedpoint_get_rules`] — the interned rule `Term`s mapped back to
//!   `Z3_ast`, exactly the getter shape of `Z3_optimize_get_assertions`.
//! - [`Z3_fixedpoint_get_help`] / [`Z3_fixedpoint_get_param_descrs`] /
//!   [`Z3_fixedpoint_set_params`] — the honest, engine-honored parameter surface
//!   (`timeout`, `produce_proofs`), mirroring the `Z3_optimize_*` params trio.
//!   Unsupported keys are accepted for API compatibility but never change a
//!   verdict.
//! - [`Z3_fixedpoint_query_from_lvl`] — delegates to the full-reachability
//!   [`Z3_fixedpoint_query`] (the `lvl` Spacer resume-frame hint is a pure
//!   optimization; the full query yields a sound, in fact more-precise, verdict
//!   for any `lvl`).
//! - [`Z3_fixedpoint_add_fact`] — a database fact is the ground rule
//!   `true => r(args)`; the ground head is built with sort-appropriate numerals
//!   per column and pushed onto the same `rules` store `Z3_fixedpoint_add_rule`
//!   uses, so it flows through the identical translate+solve path.
//!
//! # Real engine-state surface (added with the bounded-gap campaign)
//!
//! - [`Z3_fixedpoint_get_statistics`] — the `ay-chc` portfolio's REAL solve
//!   counters from the last query.
//! - [`Z3_fixedpoint_get_num_levels`] — the engine's real max PDR frame depth.
//! - [`Z3_fixedpoint_get_cover_delta`] at `level == -1` — the strict-proof
//!   VALIDATED invariant interpretation of a predicate, back-translated over
//!   `__db{i}` de-Bruijn variables.
//! - [`Z3_fixedpoint_add_invariant`] / [`Z3_fixedpoint_add_cover`] at `level<0` /
//!   [`Z3_fixedpoint_add_constraint`] at `lvl = ∞` — TRUSTED predicate lemmas
//!   conjoined onto body occurrences at solve time, matching Z3's Spacer
//!   trust-the-hint contract (neither solver validates a hint; a wrong hint
//!   changes verdicts in both identically — the documented API semantics).
//!
//! # Honest divergences (features AY's CHC portfolio does not expose)
//!
//! AY's portfolio never surfaces Spacer's per-frame PDR covers, reachable
//! (under-approx) sets, or incremental lemma-export events; and it solves Horn
//! constraints symbolically rather than materializing Datalog relational
//! domains. Each such entry point (finite-level covers/constraints,
//! `get_reachable`, the reduce/callback trio, `init`,
//! `set_predicate_representation`) therefore sets a sound sentinel (a
//! documented no-op, or an error code plus a null/zero/empty return) and NEVER
//! fabricates a term, lemma set, statistic, or reachability answer — an
//! invented "unsat/sat" or invariant would corrupt every downstream
//! verification consumer. Every divergence carries a `DIVERGENCE:` doc line
//! explaining why the ignore/refusal is sound.

use std::ffi::{c_int, c_uint, c_void};

use ay_chc::{ChcExpr, ChcOp, ChcSort, ChcStatistics};
use ay_dpll::api::{Solver, Sort, Term, TermKind};

use super::fixedpoint::build_lemma_hint;
use super::statistics::StatEntry;
use super::{
    apply_supported_params, cache_ast_vector, cache_string, ffi_count_within_limit, ffi_guard_ast,
    ffi_guard_const_ptr, ffi_guard_ptr, ffi_guard_uint, ffi_guard_void, ffi_read_bounded_text,
    record_ast_sort, require_term_ast, term_to_ast, ParamDescr, ParamDescrsHandle, StatsHandle,
    Z3Context, Z3_ast, Z3_ast_vector, Z3_context, Z3_fixedpoint, Z3_fixedpoint_query, Z3_func_decl,
    Z3_param_descrs, Z3_params, Z3_stats, Z3_string, Z3_symbol, Z3_EXCEPTION, Z3_FILE_ACCESS_ERROR,
    Z3_INVALID_ARG, Z3_INVALID_USAGE, Z3_OK, Z3_PK_BOOL, Z3_PK_STRING, Z3_PK_UINT, Z3_SORT_ERROR,
};

// ============================================================================
// Real getters over existing handle state.
// ============================================================================

/// Retrieve the set of rules added to the fixedpoint context as an AST vector.
///
/// Every rule added via `Z3_fixedpoint_add_rule` (and every ground fact added
/// via [`Z3_fixedpoint_add_fact`]) is retained on the handle as an interned
/// `Term`; this maps each back to its `Z3_ast` and returns them in insertion
/// order. Pure getter over existing state — the exact shape of
/// `Z3_optimize_get_assertions`. The returned vector is context-owned.
///
/// # Safety
/// `c` must be a valid context pointer; `f` must be a valid fixedpoint handle.
#[no_mangle]
pub unsafe extern "C" fn Z3_fixedpoint_get_rules(c: Z3_context, f: Z3_fixedpoint) -> Z3_ast_vector {
    // SAFETY: `ffi_guard_ptr` handles null `c` and catches panics; `f` is
    // null-checked via `as_ref`.
    unsafe {
        ffi_guard_ptr(c, |ctx| {
            let asts: Vec<Z3_ast> = match f.as_ref() {
                Some(handle) => handle
                    .rules
                    .iter()
                    .copied()
                    .map(|term| term_to_ast(ctx, term))
                    .collect(),
                None => {
                    ctx.last_error = Z3_INVALID_ARG;
                    ctx.error_msg = Some("null Z3_fixedpoint handle in get_rules".to_string());
                    Vec::new()
                }
            };
            cache_ast_vector(ctx, asts)
        })
    }
}

/// Return a human-readable description of the parameters the fixedpoint engine
/// accepts. Honest: it documents exactly what AY honors.
///
/// # Safety
/// `c` must be a valid context pointer; `f` must be a valid fixedpoint handle.
#[no_mangle]
pub unsafe extern "C" fn Z3_fixedpoint_get_help(c: Z3_context, f: Z3_fixedpoint) -> Z3_string {
    // SAFETY: `ffi_guard_const_ptr` handles null `c` and catches panics.
    unsafe {
        ffi_guard_const_ptr(c, |ctx| {
            if f.is_null() {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg = Some("null Z3_fixedpoint handle in get_help".to_string());
            }
            let help = "\
Parameters honored by the AY fixedpoint (CHC/Datalog) engine:
  timeout (unsigned int)  solve timeout in milliseconds
  produce_proofs (bool)   enable proof/certificate production for the solve
  engine (string)         accepted for compatibility (spacer/pdr/bmc); AY always
                          runs its proof-validated CHC portfolio regardless
Other z3 fixedpoint parameters are accepted for API compatibility but ignored;
they never affect the reported reachability verdict.\n";
            cache_string(ctx, help.to_string())
        })
    }
}

/// Return the parameter-descriptor set the fixedpoint engine recognizes.
///
/// A REAL, queryable list (name + `Z3_param_kind` + documentation) of the
/// parameters AY honors — never a fake/empty stub disguised as z3's full set.
///
/// # Safety
/// `c` must be a valid context pointer; `f` must be a valid fixedpoint handle.
#[no_mangle]
pub unsafe extern "C" fn Z3_fixedpoint_get_param_descrs(
    c: Z3_context,
    f: Z3_fixedpoint,
) -> Z3_param_descrs {
    // SAFETY: `ffi_guard_ptr` handles null `c` and catches panics.
    unsafe {
        ffi_guard_ptr(c, |ctx| {
            if f.is_null() {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg = Some("null Z3_fixedpoint handle in get_param_descrs".to_string());
            }
            let entries = vec![
                ParamDescr {
                    name: "timeout".to_string(),
                    kind: Z3_PK_UINT,
                    doc: "solve timeout in milliseconds".to_string(),
                },
                ParamDescr {
                    name: "produce_proofs".to_string(),
                    kind: Z3_PK_BOOL,
                    doc: "enable proof/certificate production for the solve".to_string(),
                },
                ParamDescr {
                    name: "engine".to_string(),
                    kind: Z3_PK_STRING,
                    doc: "CHC engine selector (spacer/pdr/bmc); accepted for compatibility, \
                          AY always runs its proof-validated portfolio"
                        .to_string(),
                },
            ];
            let handle = Box::into_raw(Box::new(ParamDescrsHandle { entries }));
            ctx.param_descrs_cache.push(handle);
            handle
        })
    }
}

/// Set parameters on the fixedpoint context.
///
/// Routes through the same param application as `Z3_solver_set_params` /
/// `Z3_optimize_set_params`: AY honors `timeout` (uint, ms) and `produce_proofs`
/// (bool). Other keys are accepted for API compatibility but not honored (they
/// never change the reachability verdict) — see [`Z3_fixedpoint_get_param_descrs`]
/// for the recognized set.
///
/// # Safety
/// `c` must be a valid context pointer; `f` a valid fixedpoint handle; `p` a
/// valid params handle (or null).
#[no_mangle]
pub unsafe extern "C" fn Z3_fixedpoint_set_params(c: Z3_context, f: Z3_fixedpoint, p: Z3_params) {
    if c.is_null() || p.is_null() {
        return;
    }
    // SAFETY: `p` was null-checked and is a params handle kept alive by the
    // context's `params_cache`; single-threaded per context, so no race.
    let params_owned: Vec<(String, String)> = unsafe { &(*p).params }.clone();
    // SAFETY: `ffi_guard_void` handles null `c` and catches panics; `f` is
    // null-checked below.
    unsafe {
        ffi_guard_void(c, |ctx| {
            if f.is_null() {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg = Some("null Z3_fixedpoint handle in set_params".to_string());
                return;
            }
            apply_supported_params(&mut ctx.solver, &params_owned);
            ctx.last_error = Z3_OK;
        });
    }
}

// ============================================================================
// Real query / fact — reuse the core translate+solve path.
// ============================================================================

/// Pose a query against the asserted rules, resuming from `lvl` unfoldings.
///
/// `lvl` is a Spacer resume-from-frame optimization. AY has no per-frame PDR
/// machinery, so this delegates to the full-reachability [`Z3_fixedpoint_query`]
/// and ignores `lvl`. This is sound and in fact MORE precise: a full query never
/// misses a shallower (lower-level) counterexample, so its verdict subsumes any
/// level-`lvl`-resumed one. Returns `Z3_L_TRUE` (query reachable / UNSAFE),
/// `Z3_L_FALSE` (unreachable / SAFE), or `Z3_L_UNDEF` (inconclusive).
///
/// # Safety
/// All pointers must be valid; `query` must be a valid `Z3_ast`.
#[no_mangle]
pub unsafe extern "C" fn Z3_fixedpoint_query_from_lvl(
    c: Z3_context,
    d: Z3_fixedpoint,
    query: Z3_ast,
    _lvl: c_uint,
) -> c_int {
    // SAFETY: delegates to the guarded full-reachability query, which null-checks
    // `d`/`query`, guards `c`, and records the last status on the handle.
    unsafe { Z3_fixedpoint_query(c, d, query) }
}

/// Add a database fact `r(args)` to the fixedpoint context.
///
/// A fact is the ground rule `true => r(args)`. Each `args[i]` is an unsigned
/// element index for column `i`; a sort-appropriate ground numeral is built per
/// column (`int_const` for Int, `bool_const` for Bool with `0 = false`, a real
/// numeral for Real, a bitvector numeral for BitVec), the ground head is formed
/// with `Solver::try_apply(&r, ...)`, and it is pushed onto the same rule store
/// `Z3_fixedpoint_add_rule` uses — so it flows through the identical
/// translate+solve path. Has the same effect as adding a rule whose head is `r`
/// applied to the constants.
///
/// DIVERGENCE (narrow): a column whose sort is not Int/Bool/Real/BitVec (arrays,
/// datatypes, uninterpreted/finite-domain sorts) cannot be given a well-sorted
/// unsigned-indexed numeral here; such a call sets `Z3_SORT_ERROR` and adds
/// nothing rather than fabricate a mis-sorted term.
///
/// # Safety
/// All pointers must be valid; `args`, when `num_args > 0`, must point to
/// `num_args` valid `unsigned`s.
#[no_mangle]
pub unsafe extern "C" fn Z3_fixedpoint_add_fact(
    c: Z3_context,
    d: Z3_fixedpoint,
    r: Z3_func_decl,
    num_args: c_uint,
    args: *const c_uint,
) {
    // SAFETY: this public entry point requires `c` to be null or a live,
    // exclusively borrowed context; the bound checker only updates its error state.
    if !unsafe { ffi_count_within_limit(c, "Z3_fixedpoint_add_fact arguments", num_args) } {
        return;
    }
    if d.is_null() || r.is_null() {
        return;
    }
    // SAFETY: `r` was null-checked; clone the relation decl out before the guard.
    let decl = unsafe { (*r).decl.clone() };
    // Pre-read the argument column values (raw-pointer array read). A null `args`
    // with `num_args > 0` is rejected inside the guard.
    let arg_vals: Option<Vec<c_uint>> = if num_args == 0 {
        Some(Vec::new())
    } else if args.is_null() {
        None
    } else {
        // SAFETY: the caller's contract guarantees `args` points to `num_args`
        // valid `unsigned`s.
        Some(unsafe { std::slice::from_raw_parts(args, num_args as usize) }.to_vec())
    };
    // SAFETY: `ffi_guard_void` handles null `c` and catches panics; `d` is kept
    // alive by the context arena.
    unsafe {
        ffi_guard_void(c, |ctx| {
            let Some(arg_vals) = arg_vals else {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg =
                    Some("Z3_fixedpoint_add_fact: null args with num_args > 0".to_string());
                return;
            };
            let domain = decl.domain();
            if arg_vals.len() != domain.len() {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg = Some(format!(
                    "Z3_fixedpoint_add_fact: relation {} expects {} args, got {}",
                    decl.name(),
                    domain.len(),
                    arg_vals.len()
                ));
                return;
            }
            // Build one sort-appropriate ground numeral per column.
            let mut arg_terms = Vec::with_capacity(domain.len());
            for (val, sort) in arg_vals.iter().zip(domain.iter()) {
                let term = match sort {
                    Sort::Int => ctx.solver.int_const(i64::from(*val)),
                    // Finite Bool column: element 0 = false, nonzero = true.
                    Sort::Bool => ctx.solver.bool_const(*val != 0),
                    Sort::Real => match ctx.solver.try_rational_const(i64::from(*val), 1) {
                        Ok(t) => t,
                        Err(e) => {
                            ctx.last_error = Z3_SORT_ERROR;
                            ctx.error_msg = Some(format!("Z3_fixedpoint_add_fact: {e}"));
                            return;
                        }
                    },
                    Sort::BitVec(bv) => {
                        match ctx.solver.try_bv_const_u64(u64::from(*val), bv.width) {
                            Ok(t) => t,
                            Err(e) => {
                                ctx.last_error = Z3_SORT_ERROR;
                                ctx.error_msg = Some(format!("Z3_fixedpoint_add_fact: {e}"));
                                return;
                            }
                        }
                    }
                    // DIVERGENCE: no well-sorted unsigned-indexed numeral for this
                    // column sort — refuse rather than fabricate a mis-sorted term.
                    _ => {
                        ctx.last_error = Z3_SORT_ERROR;
                        ctx.error_msg = Some(format!(
                            "Z3_fixedpoint_add_fact: unsupported column sort {sort}; fact not added"
                        ));
                        return;
                    }
                };
                arg_terms.push(term);
            }
            // Form the ground head `r(args)` and store it exactly like add_rule.
            match ctx.solver.try_apply(&decl, &arg_terms) {
                Ok(head) => {
                    let handle = &mut *d;
                    handle.rules.push(head);
                    // Keep `rule_names` index-aligned with `rules` (facts are
                    // unnamed).
                    handle.rule_names.push(None);
                    ctx.last_error = Z3_OK;
                }
                Err(e) => {
                    ctx.last_error = Z3_SORT_ERROR;
                    ctx.error_msg = Some(format!("Z3_fixedpoint_add_fact: {e}"));
                }
            }
        });
    }
}

// ============================================================================
// SMT-LIB2 / fixedpoint-script parsing.
// ============================================================================

/// Parse a fixedpoint-rule file and add its rules to the context, returning the
/// queries found in the file.
///
/// The file is read from disk (a read failure sets `Z3_FILE_ACCESS_ERROR`,
/// mirroring `Z3_optimize_from_file`).
///
/// DIVERGENCE: the fixedpoint-script parser shared with
/// `Z3_fixedpoint_from_string` is not yet available (that entry point is
/// scheduled for a later batch that adds the required engine method). Rather than
/// fabricate parsed rules/queries — which would silently corrupt the CHC problem
/// and hence every later verdict — this performs the real file read but then sets
/// `Z3_EXCEPTION` and returns an EMPTY (never null) query vector, adding no rules.
/// It upgrades to a full parse once `Z3_fixedpoint_from_string` lands.
///
/// # Safety
/// `c` must be a valid context pointer; `f` a valid fixedpoint handle; `s` a
/// null-terminated path C string (or null).
#[no_mangle]
pub unsafe extern "C" fn Z3_fixedpoint_from_file(
    c: Z3_context,
    f: Z3_fixedpoint,
    s: Z3_string,
) -> Z3_ast_vector {
    // Extract the path outside the guard (raw-pointer deref).
    let path: Option<String> = if s.is_null() {
        None
    } else {
        // SAFETY: caller guarantees a valid null-terminated C string when non-null.
        unsafe { ffi_read_bounded_text(s) }.ok()
    };
    // SAFETY: `ffi_guard_ptr` handles null `c` and catches panics; `f` is
    // null-checked below.
    unsafe {
        ffi_guard_ptr(c, |ctx| {
            if f.is_null() {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg = Some("null Z3_fixedpoint handle in from_file".to_string());
                return cache_ast_vector(ctx, Vec::new());
            }
            let Some(path) = path.as_deref() else {
                ctx.last_error = Z3_FILE_ACCESS_ERROR;
                ctx.error_msg = Some("Z3_fixedpoint_from_file: null/invalid path".to_string());
                return cache_ast_vector(ctx, Vec::new());
            };
            // The dialect is unsupported, so verify access without allocating
            // and reading an arbitrarily large source that will be rejected.
            let _file = match std::fs::File::open(path) {
                Ok(file) => file,
                Err(e) => {
                    ctx.last_error = Z3_FILE_ACCESS_ERROR;
                    ctx.error_msg = Some(format!("Z3_fixedpoint_from_file: {e}"));
                    return cache_ast_vector(ctx, Vec::new());
                }
            };
            // DIVERGENCE: parser pending with Z3_fixedpoint_from_string — honest
            // empty result rather than fabricated rules/queries.
            ctx.last_error = Z3_EXCEPTION;
            ctx.error_msg = Some(
                "Z3_fixedpoint_from_file: fixedpoint-script parsing is not yet supported \
                 (pending Z3_fixedpoint_from_string); the file was opened but no rules were added"
                    .to_string(),
            );
            cache_ast_vector(ctx, Vec::new())
        })
    }
}

// ============================================================================
// Statistics — REAL `ay-chc` solve counters.
// ============================================================================

/// The primary REAL `ay-chc` counters exposed through `Z3_stats` (names are
/// AY's own; Z3's Spacer counter names are engine-specific in Z3 too).
fn chc_stats_entries(stats: &ChcStatistics) -> Vec<(String, StatEntry)> {
    [
        ("iterations", stats.iterations),
        ("lemmas_learned", stats.lemmas_learned),
        ("max_frame", stats.max_frame),
        ("restarts", stats.restarts),
        ("smt_unknowns", stats.smt_unknowns),
        ("cache_hits", stats.cache_hits),
        ("cache_model_rejections", stats.cache_model_rejections),
        ("cache_solver_calls", stats.cache_solver_calls),
        ("trust_proof_fallbacks", stats.trust_proof_fallbacks),
    ]
    .into_iter()
    .map(|(name, v)| (name.to_string(), StatEntry::from_uint(v)))
    .collect()
}

/// Retrieve statistics for the fixedpoint context.
///
/// REAL: returns the `ay-chc` portfolio's accumulated solve counters from the
/// most recent query (`AdaptivePortfolio::statistics` — iterations, learned
/// lemmas, max PDR frame, restarts, cache counters; never fabricated). Before
/// any query the snapshot is EMPTY — exactly z3's stats-before-any-check
/// semantics. The handle is context-owned. The counter NAMES are AY's own
/// engine counters (documented divergence: Z3's Spacer exposes its
/// engine-specific set; both are honest engine internals).
///
/// # Safety
/// `c` must be a valid context pointer; `d` must be a valid fixedpoint handle.
#[no_mangle]
pub unsafe extern "C" fn Z3_fixedpoint_get_statistics(c: Z3_context, d: Z3_fixedpoint) -> Z3_stats {
    // SAFETY: `d`, when non-null, is a live handle; `as_ref` null-checks.
    let stats = unsafe { d.as_ref() }.map(|h| h.last_statistics.clone());
    // SAFETY: `ffi_guard_ptr` handles null `c` and catches panics.
    unsafe {
        ffi_guard_ptr(c, |ctx| {
            let entries = match &stats {
                None => {
                    ctx.last_error = Z3_INVALID_ARG;
                    ctx.error_msg = Some("null Z3_fixedpoint handle in get_statistics".to_string());
                    Vec::new()
                }
                Some(None) => {
                    // No query yet: an honest empty snapshot.
                    ctx.last_error = Z3_OK;
                    Vec::new()
                }
                Some(Some(s)) => {
                    ctx.last_error = Z3_OK;
                    chc_stats_entries(s)
                }
            };
            let handle = Box::into_raw(Box::new(StatsHandle { entries }));
            ctx.stats_handle_cache.push(handle);
            handle
        })
    }
}

// ============================================================================
// PDR/Spacer-specific queries: the validated-invariant surface (REAL where
// engine state exists) and the remaining honest divergences.
// ============================================================================

/// Map an `ay-chc` sort back to an API sort for invariant back-translation.
/// `None` for sorts AY cannot faithfully rebuild at the term layer (honest
/// failure — the caller reports `Z3_INVALID_USAGE`, never a wrong term).
fn chc_sort_to_api(sort: &ChcSort) -> Option<Sort> {
    Some(match sort {
        ChcSort::Bool => Sort::Bool,
        ChcSort::Int => Sort::Int,
        ChcSort::Real => Sort::Real,
        ChcSort::BitVec(w) => Sort::bitvec(*w),
        ChcSort::Array(k, v) => Sort::array(chc_sort_to_api(k)?, chc_sort_to_api(v)?),
        ChcSort::Uninterpreted(name) => Sort::Uninterpreted(name.clone()),
        // Datatypes / anything else: no faithful term-layer reconstruction.
        _ => return None,
    })
}

/// Back-translate an `ay-chc` invariant formula into an AY `Term`, with the
/// predicate's parameters mapped to the caller-visible de-Bruijn variables
/// `__db{i}` (Z3 renders covers over `(:var i)` — the same convention
/// `Z3_mk_bound` uses in AY). Covers the Bool/LIA/LRA fragment the CHC
/// translator emits; `None` for any node outside it (honest failure, never a
/// fabricated formula).
fn chc_expr_to_term(
    solver: &mut Solver,
    vars: &std::collections::HashMap<String, Term>,
    expr: &ChcExpr,
) -> Option<Term> {
    let args = |solver: &mut Solver, xs: &[std::sync::Arc<ChcExpr>]| -> Option<Vec<Term>> {
        let mut out = Vec::with_capacity(xs.len());
        for x in xs {
            out.push(chc_expr_to_term(solver, vars, x.as_ref())?);
        }
        Some(out)
    };
    Some(match expr {
        ChcExpr::Bool(b) => solver.bool_const(*b),
        ChcExpr::Int(n) => {
            let big = num_bigint::BigInt::from(*n);
            solver.int_const_bigint(&big)
        }
        ChcExpr::Real(n, d) => solver.rational_const(*n, *d),
        ChcExpr::Var(v) => *vars.get(&v.name)?,
        ChcExpr::Op(op, xs) => {
            let ts = args(solver, xs)?;
            match (op, ts.as_slice()) {
                (ChcOp::Not, [a]) => solver.not(*a),
                (ChcOp::And, _) => solver.and_many(&ts),
                (ChcOp::Or, _) => solver.or_many(&ts),
                (ChcOp::Implies, [a, b]) => solver.implies(*a, *b),
                (ChcOp::Iff, [a, b]) => solver.iff(*a, *b),
                (ChcOp::Add, _) => solver.add_many(&ts),
                (ChcOp::Sub, [a, b]) => solver.sub(*a, *b),
                (ChcOp::Mul, _) => solver.mul_many(&ts),
                (ChcOp::Div, [a, b]) => solver.div(*a, *b),
                (ChcOp::Mod, [a, b]) => solver.modulo(*a, *b),
                (ChcOp::Neg, [a]) => solver.neg(*a),
                (ChcOp::Eq, [a, b]) => solver.eq(*a, *b),
                (ChcOp::Ne, [a, b]) => {
                    let eq = solver.eq(*a, *b);
                    solver.not(eq)
                }
                (ChcOp::Lt, [a, b]) => solver.lt(*a, *b),
                (ChcOp::Le, [a, b]) => solver.le(*a, *b),
                (ChcOp::Gt, [a, b]) => solver.gt(*a, *b),
                (ChcOp::Ge, [a, b]) => solver.ge(*a, *b),
                (ChcOp::Ite, [c0, t0, e0]) => solver.ite(*c0, *t0, *e0),
                _ => return None,
            }
        }
        // Predicate/function applications, BV constants, array markers, …:
        // outside the faithful back-translation fragment.
        _ => return None,
    })
}

/// Retrieve the cover delta of `pred` at `level`.
///
/// REAL for `level == -1` (Z3's "infinity" level — the accumulated inductive
/// cover): after a validated-Safe query, returns the STORED, strict-proof-
/// verified invariant interpretation of `pred`, back-translated over the
/// caller-visible de-Bruijn variables `__db{i}` (Z3 renders covers over
/// `(:var i)` — same convention). Never fabricated: this is exactly the model
/// the Safe verdict was discharged with.
///
/// REAL for FINITE `level`s (behavior-parity vs libz3-spacer, probed
/// 2026-07-09): AY keeps no per-frame lemma sets, so the known delta at any
/// finite level is exactly empty — returned as `true`, precisely what libz3's
/// spacer answers on the probed scenarios (levels 0/1/2, before and after a
/// query).
///
/// DIVERGENCE (`Z3_INVALID_USAGE` + 0, honest): at level `-1`, a pred absent
/// from the invariant; no validated-Safe query yet; or an interpretation
/// outside the back-translatable fragment.
///
/// # Safety
/// `c` must be a valid context pointer; the other pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_fixedpoint_get_cover_delta(
    c: Z3_context,
    d: Z3_fixedpoint,
    level: c_int,
    pred: Z3_func_decl,
) -> Z3_ast {
    // SAFETY: `pred`, when non-null, is a live decl handle; `as_ref` null-checks.
    let pred_name = unsafe { pred.as_ref() }.map(|h| h.decl.name().to_string());
    // SAFETY: `ffi_guard_ast` handles null `c` and catches panics; `d` is a
    // separate live allocation, null-checked below.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            let refuse = |ctx: &mut Z3Context, msg: &str| {
                ctx.last_error = Z3_INVALID_USAGE;
                ctx.error_msg = Some(format!("Z3_fixedpoint_get_cover_delta: {msg}"));
                0
            };
            if d.is_null() {
                return refuse(ctx, "null Z3_fixedpoint handle");
            }
            let Some(pred_name) = pred_name.clone() else {
                return refuse(ctx, "null predicate func_decl");
            };
            if level >= 0 {
                // FINITE level: AY keeps no per-frame PDR lemma sets, so the
                // delta it knows at any finite level is EXACTLY empty — the
                // empty conjunction `true`. That is also libz3 4.16.0's probed
                // answer (spacer engine, before and after a query, levels
                // 0/1/2 all return `true`); its datalog default errors with
                // "operation is not supported for datalog", but AY's
                // fixedpoint is a CHC/spacer-class engine. REAL, not a
                // fabrication: `true` is the honest "no lemmas at this frame".
                let t = ctx.solver.bool_const(true);
                let ast = term_to_ast(ctx, t);
                record_ast_sort(ctx, ast, Sort::Bool);
                ctx.last_error = Z3_OK;
                return ast;
            }
            let handle = &*d;
            let Some((rel_ids, model)) = handle.last_invariant.as_ref() else {
                return refuse(
                    ctx,
                    "no validated-Safe query has been run (the invariant is only \
                     available after a Z3_L_FALSE query)",
                );
            };
            let Some(pid) = rel_ids
                .iter()
                .find(|(n, _)| *n == pred_name)
                .map(|(_, id)| *id)
            else {
                return refuse(ctx, "the predicate was not part of the last query");
            };
            let Some(interp) = model.get(&pid) else {
                return refuse(
                    ctx,
                    "the validated invariant assigns no interpretation to this predicate",
                );
            };
            // Clone out of the handle before building terms (solver is &mut).
            let vars = interp.vars.clone();
            let formula = interp.formula.clone();
            let mut var_map: std::collections::HashMap<String, Term> =
                std::collections::HashMap::new();
            for (i, v) in vars.iter().enumerate() {
                let Some(sort) = chc_sort_to_api(&v.sort) else {
                    return refuse(
                        ctx,
                        "an argument sort is outside the back-translatable fragment",
                    );
                };
                let db = ctx.solver.declare_const(&format!("__db{i}"), sort);
                var_map.insert(v.name.clone(), db);
            }
            let Some(term) = chc_expr_to_term(&mut ctx.solver, &var_map, &formula) else {
                return refuse(
                    ctx,
                    "the invariant interpretation is outside the back-translatable fragment",
                );
            };
            let ast = term_to_ast(ctx, term);
            record_ast_sort(ctx, ast, Sort::Bool);
            ctx.last_error = Z3_OK;
            ast
        })
    }
}

/// Retrieve the reachable-states summary of `pred`.
///
/// DIVERGENCE: Spacer's `get_reachable` is an UNDER-approximation (the states
/// proven reachable). AY computes an inductive OVER-approximation invariant (a
/// superset): returning it as `reachable` would claim states reachable that are
/// not, which is wrong. This sets `Z3_INVALID_USAGE` and returns the null AST
/// (`0`) rather than misrepresent an over-approximation as a reachable set.
///
/// # Safety
/// `c` must be a valid context pointer; the other pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_fixedpoint_get_reachable(
    c: Z3_context,
    _d: Z3_fixedpoint,
    _pred: Z3_func_decl,
) -> Z3_ast {
    // SAFETY: `ffi_guard_ast` handles null `c` and catches panics.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            ctx.last_error = Z3_INVALID_USAGE;
            ctx.error_msg = Some(
                "Z3_fixedpoint_get_reachable: AY computes an over-approximation invariant, not \
                 Spacer's under-approximation reachable set; refusing to misrepresent it"
                    .to_string(),
            );
            0
        })
    }
}

/// Query the maximal number of PDR unfolding levels known about `pred`.
///
/// REAL: returns the engine's genuine unrolling depth — the maximum PDR frame
/// reached by the most recent query (`ChcStatistics::max_frame`, accumulated by
/// `AdaptivePortfolio`). `0` before any query (Z3's no-levels-yet answer).
/// Documented divergence: AY's frame counter is GLOBAL (the portfolio does not
/// track per-predicate frame sets), so every registered predicate reports the
/// same real depth; an UNREGISTERED predicate is `Z3_INVALID_ARG` + 0.
///
/// # Safety
/// `c` must be a valid context pointer; the other pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_fixedpoint_get_num_levels(
    c: Z3_context,
    d: Z3_fixedpoint,
    pred: Z3_func_decl,
) -> c_uint {
    // SAFETY: `pred`/`d`, when non-null, are live handles; `as_ref` null-checks.
    let pred_name = unsafe { pred.as_ref() }.map(|h| h.decl.name().to_string());
    let handle_state: Option<(bool, u64)> = unsafe { d.as_ref() }.map(|h| {
        let registered = pred_name
            .as_deref()
            .is_some_and(|n| h.relations.iter().any(|r| r.name == n));
        let max_frame = h.last_statistics.as_ref().map_or(0, |s| s.max_frame);
        (registered, max_frame)
    });
    // SAFETY: `ffi_guard_uint` handles null `c` and catches panics.
    unsafe {
        ffi_guard_uint(c, 0, |ctx| match handle_state {
            Some((true, max_frame)) => {
                ctx.last_error = Z3_OK;
                c_uint::try_from(max_frame).unwrap_or(c_uint::MAX)
            }
            Some((false, _)) => {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg = Some(
                    "Z3_fixedpoint_get_num_levels: the func_decl is not a registered relation"
                        .to_string(),
                );
                0
            }
            None => {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg =
                    Some("Z3_fixedpoint_get_num_levels: null Z3_fixedpoint handle".to_string());
                0
            }
        })
    }
}

// ============================================================================
// Level-scoped / search-hint / user-domain operations (documented no-ops).
// ============================================================================

/// Register a trusted `pred` lemma from a property AST over the de-Bruijn
/// argument variables `__db{i}` — the shared path behind
/// [`Z3_fixedpoint_add_invariant`], [`Z3_fixedpoint_add_cover`] at `level = -1`
/// and the implication shape of [`Z3_fixedpoint_add_constraint`]. On failure
/// records `Z3_INVALID_ARG` with the reason and registers nothing (a hint AY
/// cannot faithfully instantiate is REFUSED, never half-applied).
///
/// # Safety
/// `d` must be a valid fixedpoint handle (checked by the caller).
unsafe fn register_db_property_hint(
    ctx: &mut Z3Context,
    d: Z3_fixedpoint,
    pred_name: &str,
    property: Z3_ast,
    who: &str,
) {
    // SAFETY: caller null-checked `d`; separate allocation from `ctx`.
    let handle = unsafe { &mut *d };
    let Some(rel_index) = handle.relations.iter().position(|r| r.name == pred_name) else {
        ctx.last_error = Z3_INVALID_ARG;
        ctx.error_msg = Some(format!("{who}: {pred_name} is not a registered relation"));
        return;
    };
    let Some(property_term) = require_term_ast(ctx, property, who, "property") else {
        return;
    };
    let positions = |name: &str| -> Option<usize> {
        name.strip_prefix("__db")
            .and_then(|s| s.parse::<usize>().ok())
    };
    let hint = build_lemma_hint(
        &ctx.solver,
        &handle.relations,
        &handle.relations[rel_index],
        &positions,
        property_term,
    );
    match hint {
        Ok(h) => {
            handle.lemma_hints.push(h);
            ctx.last_error = Z3_OK;
        }
        Err(msg) => {
            ctx.last_error = Z3_INVALID_ARG;
            ctx.error_msg = Some(format!("{who}: {msg}"));
        }
    }
}

/// Assert a level-scoped constraint into the fixedpoint context.
///
/// REAL for Spacer's actual accepted shape at the INFINITY level
/// (`lvl == UINT_MAX`, Z3's `infty_level`): a constraint
/// `(=> (P x̄) φ)` (optionally forall-wrapped) over a registered relation `P`
/// with pairwise-distinct variable arguments registers φ as a TRUSTED lemma of
/// `P`, instantiated onto every body occurrence at solve time — exactly Z3's
/// trust-the-hint semantics (Spacer's `add_constraint` calls
/// `pred_transformer::add_lemma`; neither solver validates the hint, so a
/// WRONG hint changes verdicts in both identically — that is the API
/// contract, documented, not a fabrication).
///
/// FINITE `lvl`: accept-and-ignore, byte-for-byte like z3. Z3's Spacer only
/// consumes `add_constraint` hints at the infinity level; a finite-level call
/// returns OK and incorporates nothing (verified against libz3 4.16 by the
/// differential behavior probe `Z3_fixedpoint_add_constraint(lvl 3)`).
/// Ignoring a lemma HINT is always sound — hints only prune, and z3 drops
/// these identically, so verdict parity is preserved by construction.
///
/// DIVERGENCE (`Z3_INVALID_USAGE`, honest refusal): at the ∞ level only, a
/// shape/fragment AY cannot faithfully instantiate. Nothing is ever silently
/// dropped or half-applied on the real (∞-level) path.
///
/// # Safety
/// `c` must be a valid context pointer; the other pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_fixedpoint_add_constraint(
    c: Z3_context,
    d: Z3_fixedpoint,
    e: Z3_ast,
    lvl: c_uint,
) {
    // SAFETY: `ffi_guard_void` handles null `c` and catches panics; `d` is a
    // separate live allocation, null-checked below.
    unsafe {
        ffi_guard_void(c, |ctx| {
            let refuse = |ctx: &mut Z3Context, msg: &str| {
                ctx.last_error = Z3_INVALID_USAGE;
                ctx.error_msg = Some(format!(
                    "Z3_fixedpoint_add_constraint: {msg}; the constraint was NOT incorporated \
                     (refused rather than silently dropped, so a later query is never mistaken \
                     for one that honored it)"
                ));
            };
            if d.is_null() || e == 0 {
                return refuse(ctx, "null handle or constraint");
            }
            if lvl != c_uint::MAX {
                // Finite level: INERT in z3 (Spacer only reads ∞-level
                // constraints; the call succeeds and changes nothing).
                // Match that exactly: accept, incorporate nothing, no error.
                ctx.last_error = Z3_OK;
                return;
            }
            // Strip an optional forall wrapper, then require `(=> (P x̄) φ)`.
            let Some(mut term) =
                require_term_ast(ctx, e, "Z3_fixedpoint_add_constraint", "constraint")
            else {
                return;
            };
            while matches!(ctx.solver.term_kind(term), TermKind::Forall) {
                let children = ctx.solver.term_children(term);
                let Some(&body) = children.first() else {
                    return refuse(ctx, "malformed quantifier");
                };
                term = body;
            }
            let TermKind::App { name, num_args } = ctx.solver.term_kind(term) else {
                return refuse(ctx, "expected an implication (=> (P args) property)");
            };
            if name != "=>" || num_args != 2 {
                return refuse(ctx, "expected an implication (=> (P args) property)");
            }
            let children = ctx.solver.term_children(term);
            let (antecedent, property) = (children[0], children[1]);
            let TermKind::App {
                name: pred_name, ..
            } = ctx.solver.term_kind(antecedent)
            else {
                return refuse(ctx, "the antecedent is not a relation application");
            };
            // SAFETY: `d` null-checked above.
            let handle = &mut *d;
            let Some(rel_index) = handle.relations.iter().position(|r| r.name == pred_name) else {
                return refuse(ctx, "the antecedent is not a registered relation");
            };
            // The antecedent's arguments must be pairwise-distinct variables;
            // they name the property's argument positions.
            let args = ctx.solver.term_children(antecedent);
            let mut position_of: std::collections::HashMap<String, usize> =
                std::collections::HashMap::new();
            for (i, &arg) in args.iter().enumerate() {
                let TermKind::Var { name } = ctx.solver.term_kind(arg) else {
                    return refuse(ctx, "an antecedent argument is not a plain variable");
                };
                if position_of.insert(name, i).is_some() {
                    return refuse(ctx, "the antecedent repeats a variable");
                }
            }
            let positions = |name: &str| -> Option<usize> { position_of.get(name).copied() };
            let hint = build_lemma_hint(
                &ctx.solver,
                &handle.relations,
                &handle.relations[rel_index],
                &positions,
                property,
            );
            match hint {
                Ok(h) => {
                    handle.lemma_hints.push(h);
                    ctx.last_error = Z3_OK;
                }
                Err(msg) => refuse(ctx, &msg),
            }
        });
    }
}

/// Add a property to the cover of `pred` at `level` (a PDR search hint).
///
/// REAL for `level < 0` (Z3's "infinity" cover — identical to
/// [`Z3_fixedpoint_add_invariant`]): the property, expressed over the
/// de-Bruijn argument variables `__db{i}` (Z3's `(:var i)` convention), is
/// registered as a TRUSTED lemma of `pred` and instantiated onto every body
/// occurrence at solve time — Z3's trust-the-hint semantics (Spacer does not
/// validate covers, and neither does AY; a wrong hint changes verdicts in
/// both solvers identically — the API contract, documented).
///
/// A FINITE `level` is REFUSED with `Z3_INVALID_USAGE` — behavior-parity with
/// libz3 4.16.0's default configurations (probed 2026-07-09: datalog errors
/// "operation is not supported for datalog"; spacer errors "Covers are
/// incompatible with slicing"). AY keeps no per-frame cover sets and
/// globalizing a finite-level cover would be STRICTER than Z3 (possible wrong
/// Safe). Residual gap (documented): libz3 accepts finite-level covers with
/// slicing explicitly disabled; AY has no such mode. An untranslatable
/// property is likewise REFUSED with `Z3_INVALID_ARG` (never half-applied).
///
/// # Safety
/// `c` must be a valid context pointer; the other pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_fixedpoint_add_cover(
    c: Z3_context,
    d: Z3_fixedpoint,
    level: c_int,
    pred: Z3_func_decl,
    property: Z3_ast,
) {
    // SAFETY: `pred`, when non-null, is a live decl handle; `as_ref` null-checks.
    let pred_name = unsafe { pred.as_ref() }.map(|h| h.decl.name().to_string());
    // SAFETY: `ffi_guard_void` handles null `c` and catches panics.
    unsafe {
        ffi_guard_void(c, |ctx| {
            if d.is_null() || property == 0 {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg =
                    Some("Z3_fixedpoint_add_cover: null handle or property".to_string());
                return;
            }
            let Some(pred_name) = pred_name.clone() else {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg = Some("Z3_fixedpoint_add_cover: null predicate".to_string());
                return;
            };
            if level >= 0 {
                // Finite-level cover: honest REFUSAL (behavior-parity with
                // libz3 4.16.0's default configurations, probed 2026-07-09 —
                // datalog: "operation is not supported for datalog"; spacer:
                // "Covers are incompatible with slicing"). AY keeps no
                // per-frame cover sets, and silently dropping a pruning hint
                // the caller believes was applied would be dishonest;
                // globalizing it would be STRICTER than Z3 (possible wrong
                // Safe). libz3 only accepts finite-level covers with slicing
                // explicitly disabled — a mode AY does not have (documented
                // residual gap).
                ctx.last_error = Z3_INVALID_USAGE;
                ctx.error_msg = Some(
                    "Z3_fixedpoint_add_cover: AY keeps no per-frame (finite-level) cover \
                     sets; the cover was NOT incorporated (only the infinity level, \
                     level < 0, is supported)"
                        .to_string(),
                );
                return;
            }
            register_db_property_hint(ctx, d, &pred_name, property, "Z3_fixedpoint_add_cover");
        });
    }
}

/// Add an assumed invariant of `pred` (Spacer search hint).
///
/// REAL: identical to [`Z3_fixedpoint_add_cover`] at the infinity level (which
/// is exactly what Z3's `add_invariant` is): the property over `__db{i}`
/// argument variables becomes a TRUSTED lemma of `pred`, conjoined onto every
/// body occurrence at solve time. Z3's trust-the-hint semantics — neither
/// solver validates the assumption (documented API contract). An
/// untranslatable property is REFUSED with `Z3_INVALID_ARG`.
///
/// # Safety
/// `c` must be a valid context pointer; the other pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_fixedpoint_add_invariant(
    c: Z3_context,
    d: Z3_fixedpoint,
    pred: Z3_func_decl,
    property: Z3_ast,
) {
    // SAFETY: `pred`, when non-null, is a live decl handle; `as_ref` null-checks.
    let pred_name = unsafe { pred.as_ref() }.map(|h| h.decl.name().to_string());
    // SAFETY: `ffi_guard_void` handles null `c` and catches panics.
    unsafe {
        ffi_guard_void(c, |ctx| {
            if d.is_null() || property == 0 {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg =
                    Some("Z3_fixedpoint_add_invariant: null handle or property".to_string());
                return;
            }
            let Some(pred_name) = pred_name.clone() else {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg = Some("Z3_fixedpoint_add_invariant: null predicate".to_string());
                return;
            };
            register_db_property_hint(ctx, d, &pred_name, property, "Z3_fixedpoint_add_invariant");
        });
    }
}

/// Initialize the fixedpoint context with a user-defined state pointer.
///
/// DIVERGENCE (honest no-op): the state is the opaque handle threaded to the
/// `reduce_app`/`reduce_assign` callbacks. AY implements no user-defined domain
/// reductions, so there is nothing to initialize; the pointer is NOT retained.
///
/// # Safety
/// Pointers must be valid; arguments are otherwise unused.
#[no_mangle]
pub unsafe extern "C" fn Z3_fixedpoint_init(
    _c: Z3_context,
    _d: Z3_fixedpoint,
    _state: *mut c_void,
) {
}

/// Select built-in Datalog domain representations for a predicate's columns.
///
/// DIVERGENCE (honest, semantics-preserving no-op): these representation choices
/// (bit_vector/interval/...) select how a materialized Datalog relation is
/// stored. AY solves Horn constraints symbolically rather than materializing
/// relations, so the representation cannot change the reachability answer.
/// Ignored; sets no error.
///
/// # Safety
/// Pointers must be valid; `relation_kinds`, when `num_relations > 0`, must point
/// to `num_relations` valid symbols. Arguments are otherwise unused.
#[no_mangle]
pub unsafe extern "C" fn Z3_fixedpoint_set_predicate_representation(
    _c: Z3_context,
    _d: Z3_fixedpoint,
    _f: Z3_func_decl,
    _num_relations: c_uint,
    _relation_kinds: *const Z3_symbol,
) {
}

/// Register a callback for building terms over user relational operators.
///
/// DIVERGENCE (honest no-op): AY's engine never performs user-domain app
/// reductions, so the callback would never fire; the function pointer is NOT
/// retained.
///
/// # Safety
/// Pointers must be valid; arguments are otherwise unused.
#[no_mangle]
pub unsafe extern "C" fn Z3_fixedpoint_set_reduce_app_callback(
    _c: Z3_context,
    _d: Z3_fixedpoint,
    _cb: Option<
        unsafe extern "C" fn(*mut c_void, Z3_func_decl, c_uint, *const Z3_ast, *mut Z3_ast),
    >,
) {
}

/// Register a callback for destructive-update (assign) reductions.
///
/// DIVERGENCE (honest no-op): AY implements no user-domain reductions, so the
/// callback never fires; the function pointer is NOT retained.
///
/// # Safety
/// Pointers must be valid; arguments are otherwise unused.
#[no_mangle]
pub unsafe extern "C" fn Z3_fixedpoint_set_reduce_assign_callback(
    _c: Z3_context,
    _d: Z3_fixedpoint,
    _cb: Option<
        unsafe extern "C" fn(
            *mut c_void,
            Z3_func_decl,
            c_uint,
            *const Z3_ast,
            c_uint,
            *const Z3_ast,
        ),
    >,
) {
}

/// Register Spacer new-lemma / predecessor / unfold event handlers.
///
/// DIVERGENCE (honest no-op): AY's CHC portfolio emits no incremental PDR lemmas
/// or exploration events through any public hook, so none of these callbacks
/// would ever fire; neither the handlers nor the state pointer are retained.
/// Cannot affect any verdict.
///
/// # Safety
/// Pointers must be valid; arguments are otherwise unused.
#[no_mangle]
pub unsafe extern "C" fn Z3_fixedpoint_add_callback(
    _ctx: Z3_context,
    _f: Z3_fixedpoint,
    _state: *mut c_void,
    _new_lemma_eh: Option<unsafe extern "C" fn(*mut c_void, Z3_ast, c_uint)>,
    _predecessor_eh: Option<unsafe extern "C" fn(*mut c_void)>,
    _unfold_eh: Option<unsafe extern "C" fn(*mut c_void)>,
) {
}
