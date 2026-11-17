// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Z3-compatible `Fixedpoint` extension surface (batch 2): background axioms,
//! the assertion getter, the Spacer counterexample-trace family, multi-relation
//! queries, and named-rule update — all backed by the same `FixedpointHandle`
//! machinery and the `ay-chc` portfolio that `fixedpoint`/`fixedpoint_ext` use.
//!
//! # Real functions
//!
//! - [`Z3_fixedpoint_assert`] / [`Z3_fixedpoint_get_assertions`] — the
//!   background-axiom store; each axiom is folded into every clause body as a
//!   global constraint during problem construction (see
//!   `super::fixedpoint::build_problem_base`).
//! - [`Z3_fixedpoint_update_rule`] — named-rule upsert over the parallel
//!   `rules`/`rule_names` stores.
//! - [`Z3_fixedpoint_query_relations`] — reachability of ANY of a set of
//!   relations, built as per-relation `R(x̄) => false` safety clauses over the
//!   same translated rule set and solved by the same portfolio.
//! - [`Z3_fixedpoint_get_reason_unknown`] — the honest reason recorded on the
//!   last `Z3_L_UNDEF` query.
//! - [`Z3_fixedpoint_get_ground_sat_answer`] /
//!   [`Z3_fixedpoint_get_rules_along_trace`] /
//!   [`Z3_fixedpoint_get_rule_names_along_trace`] — the retained-counterexample
//!   trace family; valid only after an `Unsafe` (`Z3_L_TRUE`) query and derived
//!   strictly from real counterexample data (never fabricated).
//!
//! # Honest divergences
//!
//! - [`Z3_fixedpoint_from_string`] (and `_from_file` in
//!   `fixedpoint_ext.rs`) parse the SMT-LIB2 fixedpoint script dialect
//!   for real (see the section at the bottom of this file); the only
//!   boundary is that script relations live under their written names,
//!   disjoint from C-API-registered relations' private names.
//! - The trace-family functions map the counterexample's engine-reported
//!   `clause_index` back onto the asserted rule snapshot. When the portfolio's
//!   internal transforms renumber clauses the mapping may be partial; it is
//!   bounded to in-range indices and therefore only ever yields REAL asserted
//!   rules/names or nothing — it never invents a rule, name, or ground fact.

use std::ffi::{c_int, c_uint};

use ay_chc::{ChcExpr, ChcSort, ChcVar, ClauseBody, ClauseHead, HornClause};
use ay_dpll::api::Term;

use super::fixedpoint::{
    apply_lemma_hints_to_clause, build_problem_base, fold_axioms_into_clause, record_outcome,
    solve_problem, QueryOutcome, TranslateErr, REASON_UNTRANSLATABLE,
};
use super::{
    cache_ast_vector, cache_string, cache_symbol, ffi_count_within_limit, ffi_guard_const_ptr,
    ffi_guard_int, ffi_guard_produced, ffi_guard_ptr, ffi_guard_void, require_term_ast_or_return,
    term_to_ast, Z3_ast, Z3_ast_vector, Z3_context, Z3_fixedpoint, Z3_func_decl, Z3_string,
    Z3_symbol, Z3_INVALID_ARG, Z3_INVALID_USAGE, Z3_L_TRUE, Z3_L_UNDEF, Z3_OK,
};

// ============================================================================
// Background axioms.
// ============================================================================

/// Assert a background axiom into the fixedpoint context.
///
/// Z3 uses background axioms (in PDR/Spacer mode) as constraints that hold in
/// every state. AY stores the axiom on the handle and folds it — as a global
/// constraint — into every clause body (and the query body) when it builds the
/// `ay-chc` problem for a query. A background axiom only ever ADDS a constraint;
/// an axiom that cannot be translated into AY's CHC fragment makes the next
/// query return `Z3_L_UNDEF` (never a wrong verdict).
///
/// # Safety
/// `c` must be a valid context pointer; `d` a valid fixedpoint handle; `axiom`
/// a valid `Z3_ast`.
#[no_mangle]
pub unsafe extern "C" fn Z3_fixedpoint_assert(c: Z3_context, d: Z3_fixedpoint, axiom: Z3_ast) {
    if d.is_null() {
        return;
    }
    // SAFETY: `ffi_guard_void` null-checks `c` and catches panics; `d` is a
    // separate arena allocation, kept alive by the context.
    unsafe {
        ffi_guard_void(c, |ctx| {
            let term = require_term_ast_or_return!(ctx, axiom, "Z3_fixedpoint_assert", "axiom");
            let handle = &mut *d;
            handle.assertions.push(term);
            ctx.last_error = Z3_OK;
        });
    }
}

/// Retrieve the background axioms asserted via [`Z3_fixedpoint_assert`] as an
/// AST vector, in insertion order. Pure getter over existing handle state; the
/// returned vector is context-owned.
///
/// # Safety
/// `c` must be a valid context pointer; `f` a valid fixedpoint handle.
#[no_mangle]
pub unsafe extern "C" fn Z3_fixedpoint_get_assertions(
    c: Z3_context,
    f: Z3_fixedpoint,
) -> Z3_ast_vector {
    // SAFETY: `ffi_guard_ptr` null-checks `c` and catches panics; `f` is
    // null-checked via `as_ref`.
    unsafe {
        ffi_guard_ptr(c, |ctx| {
            let asts: Vec<Z3_ast> = match f.as_ref() {
                Some(handle) => handle
                    .assertions
                    .iter()
                    .copied()
                    .map(|term| term_to_ast(ctx, term))
                    .collect(),
                None => {
                    ctx.last_error = Z3_INVALID_ARG;
                    ctx.error_msg = Some("null Z3_fixedpoint handle in get_assertions".to_string());
                    Vec::new()
                }
            };
            cache_ast_vector(ctx, asts)
        })
    }
}

// ============================================================================
// Named-rule update.
// ============================================================================

/// Update (or add) a named rule.
///
/// Z3's `update_rule` replaces the rule previously created with `name`. AY plumbs
/// rule names into a `rule_names` vector parallel to `rules` (see
/// `Z3_fixedpoint_add_rule`), so this upserts: if a rule with `name` exists its
/// term is replaced in place; otherwise the rule is appended as a new named rule.
/// A null `name` appends an anonymous rule. Either way `rules`/`rule_names` stay
/// index-aligned.
///
/// # Safety
/// `c` must be a valid context pointer; `d` a valid fixedpoint handle; `a` a
/// valid `Z3_ast`; `name` a valid `Z3_symbol` (or null).
#[no_mangle]
pub unsafe extern "C" fn Z3_fixedpoint_update_rule(
    c: Z3_context,
    d: Z3_fixedpoint,
    a: Z3_ast,
    name: Z3_symbol,
) {
    if d.is_null() {
        return;
    }
    // Read the optional rule name outside the guard (raw-pointer deref).
    // SAFETY: `name` is null or a valid `SymbolHandle` in the context arena.
    let rule_name: Option<String> = unsafe { name.as_ref() }.map(super::SymbolHandle::display_name);
    // SAFETY: `ffi_guard_void` null-checks `c` and catches panics; `d` is kept
    // alive by the context arena.
    unsafe {
        ffi_guard_void(c, |ctx| {
            let term = require_term_ast_or_return!(ctx, a, "Z3_fixedpoint_update_rule", "rule");
            let handle = &mut *d;
            match &rule_name {
                Some(nm) => {
                    if let Some(pos) = handle
                        .rule_names
                        .iter()
                        .position(|n| n.as_deref() == Some(nm.as_str()))
                    {
                        handle.rules[pos] = term;
                    } else {
                        handle.rules.push(term);
                        handle.rule_names.push(Some(nm.clone()));
                    }
                }
                None => {
                    handle.rules.push(term);
                    handle.rule_names.push(None);
                }
            }
            ctx.last_error = Z3_OK;
        });
    }
}

// ============================================================================
// Multi-relation query.
// ============================================================================

/// Query whether ANY of `relations` is reachable/derivable under the asserted
/// rules.
///
/// Builds the same translated rule set as `Z3_fixedpoint_query` (relations,
/// rules, background axioms), then appends one safety clause `R(x̄) => false`
/// per requested relation (over fresh variables of the relation's domain sorts)
/// and solves with the same proof-validated portfolio. Reachable iff the problem
/// is `Unsafe`. Returns `Z3_L_TRUE` (some relation reachable), `Z3_L_FALSE`
/// (none reachable / SAFE), or `Z3_L_UNDEF` (inconclusive / untranslatable).
/// Sets `Z3_INVALID_ARG` if any `Z3_func_decl` is not a registered relation.
///
/// # Safety
/// `c` must be a valid context pointer; `d` a valid fixedpoint handle;
/// `relations`, when `num_relations > 0`, must point to `num_relations` valid
/// `Z3_func_decl`s.
#[no_mangle]
pub unsafe extern "C" fn Z3_fixedpoint_query_relations(
    c: Z3_context,
    d: Z3_fixedpoint,
    num_relations: c_uint,
    relations: *const Z3_func_decl,
) -> c_int {
    // SAFETY: this public entry point requires `c` to be null or a live,
    // exclusively borrowed context; the bound checker only updates its error state.
    if !unsafe { ffi_count_within_limit(c, "Z3_fixedpoint_query_relations", num_relations) } {
        return Z3_L_UNDEF;
    }
    if d.is_null() {
        return Z3_L_UNDEF;
    }
    // Pre-read the relation-decl pointer array (raw-pointer array read). A null
    // array with num_relations > 0 is rejected inside the guard.
    let decl_ptrs: Option<Vec<Z3_func_decl>> = if num_relations == 0 {
        Some(Vec::new())
    } else if relations.is_null() {
        None
    } else {
        // SAFETY: caller guarantees `relations` points to `num_relations` valid
        // `Z3_func_decl`s.
        Some(unsafe { std::slice::from_raw_parts(relations, num_relations as usize) }.to_vec())
    };
    // SAFETY: `ffi_guard_int` null-checks `c` and catches panics; `d` is kept
    // alive by the context arena and is a separate allocation from the context.
    unsafe {
        ffi_guard_int(c, Z3_L_UNDEF, |ctx| {
            let Some(decl_ptrs) = decl_ptrs else {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg = Some(
                    "Z3_fixedpoint_query_relations: null relations array with num_relations > 0"
                        .to_string(),
                );
                return Z3_L_UNDEF;
            };
            let handle = &mut *d;

            // Resolve each requested decl to a registered relation (name +
            // argument sorts). Any unregistered decl is an invalid argument.
            let mut requested: Vec<(String, Vec<ChcSort>)> = Vec::with_capacity(decl_ptrs.len());
            for &ptr in &decl_ptrs {
                if ptr.is_null() {
                    ctx.last_error = Z3_INVALID_ARG;
                    ctx.error_msg = Some(
                        "Z3_fixedpoint_query_relations: null Z3_func_decl in relations array"
                            .to_string(),
                    );
                    return Z3_L_UNDEF;
                }
                let name = (*ptr).decl.name().to_string();
                match handle.relations.iter().find(|r| r.name == name) {
                    Some(rel) => requested.push((name, rel.arg_sorts.clone())),
                    None => {
                        ctx.last_error = Z3_INVALID_ARG;
                        ctx.error_msg = Some(format!(
                            "Z3_fixedpoint_query_relations: {name} is not a registered relation"
                        ));
                        return Z3_L_UNDEF;
                    }
                }
            }

            // Recursive-definition gate (P1.1): same fail-close as
            // `Z3_fixedpoint_query` — a rule/assertion mentioning a
            // `Z3_add_rec_def` name would be solved with it as a plain
            // uninterpreted symbol. Refuse honestly.
            if !ctx.rec_fun_defs.is_empty() {
                let mut scan: Vec<Term> = handle.rules.clone();
                scan.extend(handle.assertions.iter().copied());
                if ctx.solver.contains_rec_fun_apps(&scan, &ctx.rec_fun_defs) {
                    let outcome = QueryOutcome::undef(
                        "recursive function definitions (Z3_add_rec_def) are not \
                         expanded on the fixedpoint path; refusing to treat a \
                         recursively defined function as a plain uninterpreted symbol"
                            .to_string(),
                    );
                    let status = record_outcome(handle, outcome);
                    ctx.last_error = Z3_OK;
                    return status;
                }
            }

            // Build the base problem (relations + rules + folded axioms).
            let (mut problem, rel_ids, axioms) = match build_problem_base(&ctx.solver, handle) {
                Ok(v) => v,
                Err(TranslateErr) => {
                    let out = QueryOutcome::undef(REASON_UNTRANSLATABLE.to_string());
                    let status = record_outcome(handle, out);
                    ctx.last_error = Z3_OK;
                    return status;
                }
            };

            // Append one safety clause `R(fresh...) => false` per requested
            // relation. Reachability of any of them ⇒ the problem is Unsafe.
            for (i, (name, arg_sorts)) in requested.iter().enumerate() {
                let Some(id) = rel_ids.iter().find(|(n, _)| n == name).map(|(_, pid)| *pid) else {
                    // Declared for every registered relation above; defensive.
                    continue;
                };
                let mut args: Vec<ChcExpr> = Vec::with_capacity(arg_sorts.len());
                for (j, s) in arg_sorts.iter().enumerate() {
                    args.push(ChcExpr::var(ChcVar::new(format!("__qr{i}_{j}"), s.clone())));
                }
                let body = ClauseBody::new(vec![(id, args)], None);
                let clause = HornClause::new(body, ClauseHead::False);
                let clause = apply_lemma_hints_to_clause(clause, &handle.lemma_hints, &rel_ids);
                problem.add_clause(fold_axioms_into_clause(clause, &axioms));
            }

            let outcome = solve_problem(problem, rel_ids);
            let status = record_outcome(handle, outcome);
            ctx.last_error = Z3_OK;
            status
        })
    }
}

// ============================================================================
// Reason-unknown.
// ============================================================================

/// Return an honest reason for the most recent inconclusive (`Z3_L_UNDEF`)
/// query: untranslatable rules/query, a portfolio-inconclusive result, or a
/// SAFE verdict that failed the strict-proof discharge gate. Returns the empty
/// string when the last query did not end unknown (matching Z3). The returned
/// pointer is context-owned.
///
/// # Safety
/// `c` must be a valid context pointer; `d` a valid fixedpoint handle.
#[no_mangle]
pub unsafe extern "C" fn Z3_fixedpoint_get_reason_unknown(
    c: Z3_context,
    d: Z3_fixedpoint,
) -> Z3_string {
    // SAFETY: `ffi_guard_const_ptr` null-checks `c` and catches panics.
    unsafe {
        ffi_guard_const_ptr(c, |ctx| {
            let reason = match d.as_ref() {
                Some(handle) => handle.last_reason_unknown.clone().unwrap_or_default(),
                None => {
                    ctx.last_error = Z3_INVALID_ARG;
                    ctx.error_msg =
                        Some("null Z3_fixedpoint handle in get_reason_unknown".to_string());
                    String::new()
                }
            };
            cache_string(ctx, reason)
        })
    }
}

// ============================================================================
// Counterexample trace family (valid only after an Unsafe / Z3_L_TRUE query).
// ============================================================================

/// Return the ground (concrete) witness of the last `Unsafe` query as an AST.
///
/// Valid only after a query returned `Z3_L_TRUE`; otherwise sets
/// `Z3_INVALID_USAGE` and returns the null AST (`0`).
///
/// DIVERGENCE: AY's retained counterexample carries per-step, name-keyed integer
/// model assignments (not positionally-ordered relation tuples), so the ground
/// answer is rendered as a conjunction of concrete equalities `var@step = value`
/// drawn verbatim from the counterexample — a faithful, satisfiable witness of
/// the trace (step-namespaced so distinct states never contradict). Nothing is
/// fabricated. A trace with no recorded numeric assignments yields `true`.
///
/// # Safety
/// `c` must be a valid context pointer; `d` a valid fixedpoint handle.
#[no_mangle]
pub unsafe extern "C" fn Z3_fixedpoint_get_ground_sat_answer(
    c: Z3_context,
    d: Z3_fixedpoint,
) -> Z3_ast {
    // SAFETY: `ffi_guard_ast` null-checks `c` and catches panics; `d` is
    // dereferenced only after an explicit null-check.
    unsafe {
        ffi_guard_produced(c, |ctx| {
            if d.is_null() {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg =
                    Some("null Z3_fixedpoint handle in get_ground_sat_answer".to_string());
                return 0;
            }
            let handle = &*d;
            if handle.last_status != Z3_L_TRUE || handle.last_cex.is_none() {
                ctx.last_error = Z3_INVALID_USAGE;
                ctx.error_msg = Some(
                    "Z3_fixedpoint_get_ground_sat_answer: no ground answer available; valid only \
                     after a query returned Z3_L_TRUE (UNSAFE / reachable)"
                        .to_string(),
                );
                return 0;
            }
            // Collect step-namespaced (name, value) pairs from the counterexample.
            let mut pairs: Vec<(String, i64)> = Vec::new();
            if let Some(cex) = handle.last_cex.as_ref() {
                for (si, step) in cex.steps.iter().enumerate() {
                    let mut kv: Vec<(&String, &i64)> = step.assignments.iter().collect();
                    kv.sort_by(|a, b| a.0.cmp(b.0));
                    for (k, v) in kv {
                        pairs.push((format!("{k}@{si}"), *v));
                    }
                }
            }
            // Build the ground witness: a conjunction of concrete equalities.
            let mut eqs: Vec<Term> = Vec::with_capacity(pairs.len());
            for (name, val) in &pairs {
                let var = ctx.solver.int_var(name);
                let value = ctx.solver.int_const(*val);
                if let Ok(eq) = ctx.solver.try_eq(var, value) {
                    eqs.push(eq);
                }
            }
            let answer = if eqs.is_empty() {
                ctx.solver.bool_const(true)
            } else {
                ctx.solver.and_many(&eqs)
            };
            ctx.last_error = Z3_OK;
            term_to_ast(ctx, answer)
        })
    }
}

/// Return the rules along the last `Unsafe` counterexample trace as an AST
/// vector.
///
/// Valid only after a query returned `Z3_L_TRUE`; otherwise sets
/// `Z3_INVALID_USAGE` and returns an empty vector. Each counterexample step's
/// engine-reported `clause_index` is mapped back onto the rule snapshot taken at
/// query time; only in-range indices contribute, so the result contains only
/// REAL asserted rule ASTs (never a fabricated rule). The returned vector is
/// context-owned.
///
/// # Safety
/// `c` must be a valid context pointer; `d` a valid fixedpoint handle.
#[no_mangle]
pub unsafe extern "C" fn Z3_fixedpoint_get_rules_along_trace(
    c: Z3_context,
    d: Z3_fixedpoint,
) -> Z3_ast_vector {
    // SAFETY: `ffi_guard_ptr` null-checks `c` and catches panics; `d` is
    // dereferenced only after an explicit null-check.
    unsafe {
        ffi_guard_ptr(c, |ctx| {
            if d.is_null() {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg =
                    Some("null Z3_fixedpoint handle in get_rules_along_trace".to_string());
                return cache_ast_vector(ctx, Vec::new());
            }
            let handle = &*d;
            if handle.last_status != Z3_L_TRUE || handle.last_cex.is_none() {
                ctx.last_error = Z3_INVALID_USAGE;
                ctx.error_msg = Some(
                    "Z3_fixedpoint_get_rules_along_trace: no trace available; valid only after a \
                     query returned Z3_L_TRUE (UNSAFE / reachable)"
                        .to_string(),
                );
                return cache_ast_vector(ctx, Vec::new());
            }
            let mut asts: Vec<Z3_ast> = Vec::new();
            if let Some(cex) = handle.last_cex.as_ref() {
                for step in &cex.steps {
                    if let Some(i) = step.clause_index {
                        if let Some(&rule) = handle.last_query_rules.get(i) {
                            asts.push(term_to_ast(ctx, rule));
                        }
                    }
                }
            }
            ctx.last_error = Z3_OK;
            cache_ast_vector(ctx, asts)
        })
    }
}

/// Return the joined names of the rules along the last `Unsafe` counterexample
/// trace as a single `Z3_symbol` (Z3 returns one symbol).
///
/// Valid only after a query returned `Z3_L_TRUE`; otherwise sets
/// `Z3_INVALID_USAGE` and returns an empty-string symbol. Names are drawn from
/// the rule-name snapshot taken at query time, mapped by each step's in-range
/// `clause_index`; only real, previously-set rule names contribute (unnamed
/// rules are skipped). The returned symbol is context-owned.
///
/// # Safety
/// `c` must be a valid context pointer; `d` a valid fixedpoint handle.
#[no_mangle]
pub unsafe extern "C" fn Z3_fixedpoint_get_rule_names_along_trace(
    c: Z3_context,
    d: Z3_fixedpoint,
) -> Z3_symbol {
    // SAFETY: `ffi_guard_ptr` null-checks `c` and catches panics; `d` is
    // dereferenced only after an explicit null-check.
    unsafe {
        ffi_guard_ptr(c, |ctx| {
            if d.is_null() {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg =
                    Some("null Z3_fixedpoint handle in get_rule_names_along_trace".to_string());
                return cache_symbol(ctx, String::new());
            }
            let handle = &*d;
            if handle.last_status != Z3_L_TRUE || handle.last_cex.is_none() {
                ctx.last_error = Z3_INVALID_USAGE;
                ctx.error_msg = Some(
                    "Z3_fixedpoint_get_rule_names_along_trace: no trace available; valid only \
                     after a query returned Z3_L_TRUE (UNSAFE / reachable)"
                        .to_string(),
                );
                return cache_symbol(ctx, String::new());
            }
            let mut names: Vec<String> = Vec::new();
            if let Some(cex) = handle.last_cex.as_ref() {
                for step in &cex.steps {
                    if let Some(i) = step.clause_index {
                        if let Some(Some(name)) = handle.last_query_rule_names.get(i) {
                            names.push(name.clone());
                        }
                    }
                }
            }
            ctx.last_error = Z3_OK;
            cache_symbol(ctx, names.join(" "))
        })
    }
}

// ============================================================================
// SMT-LIB2 fixedpoint-script parsing (`declare-rel` / `declare-var` /
// `rule` / `query`).
// ============================================================================
//
// z3's `Z3_fixedpoint_from_string`/`_from_file` parse the SMT-LIB2
// fixedpoint dialect: relations are registered, rules added, plain
// assertions become background theory, and the queries are returned as an
// AST vector. AY implements that contract here over the real shared
// front-end: each command is split with `ay_frontend::CommandStream`
// (exact source slices), declarations are threaded into the context
// solver's persistent symbol table as `declare-fun`/`declare-const`
// (relations are Bool-valued functions; rule variables are constants the
// CHC translator reads as clause variables), and rule/query/assertion
// terms are elaborated through `Solver::parse_smtlib2` inside one
// push/pop scope so no rule formula lingers as a solver assertion.
// Relation argument sorts are recovered from a probe atom's elaborated
// children, so datatype and other non-builtin column sorts are exact.
// Any parse or elaboration failure adds nothing to the handle and is
// reported as `Z3_PARSER_ERROR` with a null return — the shapes z3's
// header documents. (Shipped libz3 4.16/5.1.0 in fact segfault inside
// `Z3_fixedpoint_from_string` on any script that registers a rule;
// measured 2026-10-17. AY implements the documented contract instead of
// reproducing the crash.)
//
// One deliberate superset: z3's script grammar accepts only a bare
// relation name in `(query ...)`; AY additionally accepts a ground or
// open relation application there, matching `Z3_fixedpoint_query`'s
// own argument contract. Scripts valid in z3 behave identically.
//
// Known boundary, shared with the rest of this surface: relation
// identity here is the SMT-LIB written name. A relation previously
// registered through the C API lives under its private FFI name, so a
// script rule cannot reference it (and vice versa); such a rule fails
// translation and the query answers `Z3_L_UNDEF` rather than guessing.

/// Render a parsed sort back to SMT-LIB text (structural; sort symbols
/// are quoted when they are not simple symbols). `None` for a future
/// sort-AST variant this renderer does not know — callers fail closed
/// rather than emit a guessed rendering.
fn render_parsed_sort(sort: &ay_frontend::Sort) -> Option<String> {
    match sort {
        ay_frontend::Sort::Simple(name) => Some(ay_core::quote_symbol(name)),
        ay_frontend::Sort::Parameterized(name, params) => {
            let inner: Option<Vec<String>> = params.iter().map(render_parsed_sort).collect();
            Some(format!(
                "({} {})",
                ay_core::quote_symbol(name),
                inner?.join(" ")
            ))
        }
        ay_frontend::Sort::Indexed(name, indices) => {
            let inner: Vec<&str> = indices.iter().map(ay_frontend::Index::text).collect();
            Some(format!(
                "(_ {} {})",
                ay_core::quote_symbol(name),
                inner.join(" ")
            ))
        }
        _ => None,
    }
}

/// The term text inside a one-term command slice `(head <term>)`.
fn command_term_text(slice: &str) -> Option<&str> {
    let trimmed = slice.trim();
    let inner = trimmed.strip_prefix('(')?.strip_suffix(')')?;
    let (_, rest) = inner.split_once(char::is_whitespace)?;
    Some(rest.trim())
}

/// Elaborate exactly one formula through the shared parse bridge and
/// return its term.
fn elaborate_one_assertion(
    ctx: &mut super::Z3Context,
    who: &str,
    script: &str,
) -> Result<Term, String> {
    let terms = ctx
        .solver
        .parse_smtlib2(script)
        .map_err(|e| format!("{who}: {e}"))?;
    match terms.as_slice() {
        [term] => Ok(*term),
        _ => Err(format!(
            "{who}: expected exactly one elaborated formula, got {}",
            terms.len()
        )),
    }
}

/// Split a script into (exact source slice, command) pairs. Done before
/// any solver mutation: a script that does not even split must not
/// touch the symbol table.
fn split_fixedpoint_script(
    source: &str,
    who: &str,
) -> Result<Vec<(String, ay_frontend::Command)>, String> {
    use ay_frontend::{CommandStream, CommandStreamItem};
    let mut stream = CommandStream::new(source);
    let mut items = Vec::new();
    loop {
        let start = stream.position();
        match stream.next_command() {
            None => return Ok(items),
            Some(CommandStreamItem::Error(e)) => return Err(format!("{who}: {e}")),
            Some(CommandStreamItem::Command(cmd)) => {
                let end = stream.position();
                items.push((source[start..end].to_string(), *cmd));
            }
        }
    }
}

/// Declaration phase (persistent): relations and rule variables become
/// ordinary solver symbols; every other non-rule command executes
/// verbatim through the shared bridge. Returns each declared
/// relation's name and rendered argument sorts.
fn declare_fixedpoint_script_symbols(
    ctx: &mut super::Z3Context,
    items: &[(String, ay_frontend::Command)],
    who: &str,
) -> Result<Vec<(String, Vec<String>)>, String> {
    use ay_frontend::Command;
    let mut relations: Vec<(String, Vec<String>)> = Vec::new();
    for (slice, cmd) in items {
        match cmd {
            Command::DeclareRel(name, sorts) => {
                let sort_texts: Option<Vec<String>> =
                    sorts.iter().map(render_parsed_sort).collect();
                let sort_texts = sort_texts
                    .ok_or_else(|| format!("{who}: declare-rel {name}: unsupported sort form"))?;
                let decl = format!(
                    "(declare-fun {} ({}) Bool)",
                    ay_core::quote_symbol(name),
                    sort_texts.join(" ")
                );
                ctx.solver
                    .parse_smtlib2(&decl)
                    .map_err(|e| format!("{who}: declare-rel {name}: {e}"))?;
                relations.push((name.clone(), sort_texts));
            }
            Command::DeclareVar(name, sort) => {
                let sort_text = render_parsed_sort(sort)
                    .ok_or_else(|| format!("{who}: declare-var {name}: unsupported sort form"))?;
                let decl = format!(
                    "(declare-const {} {})",
                    ay_core::quote_symbol(name),
                    sort_text
                );
                ctx.solver
                    .parse_smtlib2(&decl)
                    .map_err(|e| format!("{who}: declare-var {name}: {e}"))?;
            }
            Command::Rule(_) | Command::Query(_) | Command::Assert(_) => {}
            _ => {
                ctx.solver
                    .parse_smtlib2(slice)
                    .map_err(|e| format!("{who}: {e}"))?;
            }
        }
    }
    Ok(relations)
}

/// Recover each relation's elaborated argument sorts from a probe
/// atom's children (exact for datatype and other non-builtin sorts).
fn probe_relation_arg_sorts(
    ctx: &mut super::Z3Context,
    who: &str,
    relations: &[(String, Vec<String>)],
) -> Result<Vec<(String, Vec<ChcSort>)>, String> {
    let mut rel_sorts: Vec<(String, Vec<ChcSort>)> = Vec::new();
    for (r, (name, sort_texts)) in relations.iter().enumerate() {
        if sort_texts.is_empty() {
            rel_sorts.push((name.clone(), Vec::new()));
            continue;
        }
        let mut probe = String::new();
        let mut args: Vec<String> = Vec::new();
        for (i, st) in sort_texts.iter().enumerate() {
            let v = format!("ay-fp-probe-{r}-{i}");
            probe.push_str(&format!("(declare-const {v} {st})"));
            args.push(v);
        }
        probe.push_str(&format!(
            "(assert ({} {}))",
            ay_core::quote_symbol(name),
            args.join(" ")
        ));
        let atom = elaborate_one_assertion(ctx, who, &probe)?;
        let arg_sorts = ctx
            .solver
            .term_children(atom)
            .iter()
            .map(|&child| ChcSort::from(ctx.solver.term_sort(child)))
            .collect();
        rel_sorts.push((name.clone(), arg_sorts));
    }
    Ok(rel_sorts)
}

/// The material captured from one script, before it is committed to
/// the handle: relation signatures, rule terms, background axioms,
/// and query terms.
type CapturedScript = (Vec<(String, Vec<ChcSort>)>, Vec<Term>, Vec<Term>, Vec<Term>);

/// Elaborate relation signatures, rules, background assertions, and
/// queries inside one push/pop scope so no captured formula stays
/// asserted on the solver.
fn capture_fixedpoint_script_terms(
    ctx: &mut super::Z3Context,
    who: &str,
    items: &[(String, ay_frontend::Command)],
    relations: &[(String, Vec<String>)],
) -> Result<CapturedScript, String> {
    use ay_frontend::Command;
    ctx.solver.try_push().map_err(|e| format!("{who}: {e}"))?;
    let body = (|| {
        let rel_sorts = probe_relation_arg_sorts(ctx, who, relations)?;
        let mut rules: Vec<Term> = Vec::new();
        let mut axioms: Vec<Term> = Vec::new();
        let mut queries: Vec<Term> = Vec::new();
        for (slice, cmd) in items {
            match cmd {
                Command::Rule(_) => {
                    let text = command_term_text(slice)
                        .ok_or_else(|| format!("{who}: malformed rule command"))?;
                    rules.push(elaborate_one_assertion(
                        ctx,
                        who,
                        &format!("(assert {text})"),
                    )?);
                }
                Command::Assert(_) => {
                    let terms = ctx
                        .solver
                        .parse_smtlib2(slice)
                        .map_err(|e| format!("{who}: {e}"))?;
                    axioms.extend(terms);
                }
                Command::Query(term) => {
                    queries.push(elaborate_query(
                        ctx,
                        who,
                        slice,
                        term,
                        relations,
                        queries.len(),
                    )?);
                }
                _ => {}
            }
        }
        Ok((rel_sorts, rules, axioms, queries))
    })();
    match ctx.solver.try_pop() {
        Ok(()) => body,
        Err(e) => Err(format!("{who}: {e}")),
    }
}

/// Parse a whole fixedpoint script into `handle` (see the section docs).
/// Returns the query ASTs on success; on any failure nothing is added
/// to the handle.
pub(super) fn fixedpoint_parse_script(
    ctx: &mut super::Z3Context,
    handle: &mut super::FixedpointHandle,
    source: &str,
    who: &str,
) -> Result<Vec<Z3_ast>, String> {
    let items = split_fixedpoint_script(source, who)?;
    let relations = declare_fixedpoint_script_symbols(ctx, &items, who)?;
    let (rel_sorts, rules, axioms, queries) =
        capture_fixedpoint_script_terms(ctx, who, &items, &relations)?;
    for (name, arg_sorts) in rel_sorts {
        if !handle.relations.iter().any(|r| r.name == name) {
            handle
                .relations
                .push(super::RegisteredRelation { name, arg_sorts });
        }
    }
    for rule in rules {
        handle.rules.push(rule);
        handle.rule_names.push(None);
    }
    handle.assertions.extend(axioms);
    Ok(queries.iter().map(|&t| term_to_ast(ctx, t)).collect())
}

/// Elaborate one `(query ...)` term: an application is asserted as-is;
/// a bare relation symbol of positive arity becomes an atom over fresh
/// probe constants (reachability of some instance, as in z3).
fn elaborate_query(
    ctx: &mut super::Z3Context,
    who: &str,
    slice: &str,
    term: &ay_frontend::Term,
    relations: &[(String, Vec<String>)],
    ordinal: usize,
) -> Result<Term, String> {
    use ay_frontend::Term as ParsedTerm;
    if let ParsedTerm::Symbol(name) = term {
        if let Some((_, sort_texts)) = relations.iter().find(|(n, _)| n == name) {
            if !sort_texts.is_empty() {
                let mut probe = String::new();
                let mut args: Vec<String> = Vec::new();
                for (i, st) in sort_texts.iter().enumerate() {
                    let v = format!("ay-fp-query-{ordinal}-{i}");
                    probe.push_str(&format!("(declare-const {v} {st})"));
                    args.push(v);
                }
                probe.push_str(&format!(
                    "(assert ({} {}))",
                    ay_core::quote_symbol(name),
                    args.join(" ")
                ));
                return elaborate_one_assertion(ctx, who, &probe);
            }
        }
    }
    let text = command_term_text(slice).ok_or_else(|| format!("{who}: malformed query command"))?;
    elaborate_one_assertion(ctx, who, &format!("(assert {text})"))
}

/// Parse a fixedpoint-rule script string and add its rules, returning the
/// queries found (see the section docs for the dialect and the one
/// documented naming boundary).
///
/// # Safety
/// `c` must be a valid context pointer; `f` a valid fixedpoint handle; `s` a
/// null-terminated C string (or null).
#[no_mangle]
pub unsafe extern "C" fn Z3_fixedpoint_from_string(
    c: Z3_context,
    f: Z3_fixedpoint,
    s: Z3_string,
) -> Z3_ast_vector {
    let source: Option<String> = if s.is_null() {
        None
    } else {
        // SAFETY: caller guarantees a valid null-terminated C string when non-null.
        unsafe { super::ffi_read_bounded_parser_text(s) }.ok()
    };
    // SAFETY: `ffi_guard_ptr` null-checks `c` and catches panics; `f` is
    // null-checked below.
    unsafe {
        ffi_guard_ptr(c, |ctx| {
            if f.is_null() {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg = Some("null Z3_fixedpoint handle in from_string".to_string());
                return cache_ast_vector(ctx, Vec::new());
            }
            let Some(source) = source.as_deref() else {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg = Some("Z3_fixedpoint_from_string: null source".to_string());
                return cache_ast_vector(ctx, Vec::new());
            };
            let handle = &mut *f;
            match fixedpoint_parse_script(ctx, handle, source, "Z3_fixedpoint_from_string") {
                Ok(queries) => {
                    ctx.last_error = Z3_OK;
                    cache_ast_vector(ctx, queries)
                }
                Err(message) => {
                    ctx.last_error = super::Z3_PARSER_ERROR;
                    ctx.error_msg = Some(message);
                    std::ptr::null_mut()
                }
            }
        })
    }
}

#[cfg(test)]
#[path = "fixedpoint_ext2_tests.rs"]
mod fixedpoint_ext2_tests;
