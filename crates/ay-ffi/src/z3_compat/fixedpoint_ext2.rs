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
//! - [`Z3_fixedpoint_from_string`]: AY does not parse Z3's fixedpoint/Datalog
//!   *script* dialect (declare-rel/declare-var/rule/query). Rather than
//!   fabricate a rule/query set — which would silently corrupt every later
//!   verdict — it sets `Z3_EXCEPTION` and returns an EMPTY (never null) query
//!   vector, adding nothing.
//! - The trace-family functions map the counterexample's engine-reported
//!   `clause_index` back onto the asserted rule snapshot. When the portfolio's
//!   internal transforms renumber clauses the mapping may be partial; it is
//!   bounded to in-range indices and therefore only ever yields REAL asserted
//!   rules/names or nothing — it never invents a rule, name, or ground fact.

use std::ffi::{c_int, c_uint, CStr};

use ay_chc::{ChcExpr, ChcSort, ChcVar, ClauseBody, ClauseHead, HornClause};
use ay_dpll::api::Term;

use super::fixedpoint::{
    apply_lemma_hints_to_clause, build_problem_base, fold_axioms_into_clause, record_outcome,
    solve_problem, QueryOutcome, TranslateErr, REASON_UNTRANSLATABLE,
};
use super::{
    ast_to_term, cache_ast_vector, cache_string, cache_symbol, ffi_guard_ast, ffi_guard_const_ptr,
    ffi_guard_int, ffi_guard_ptr, ffi_guard_void, term_to_ast, Z3_ast, Z3_ast_vector, Z3_context,
    Z3_fixedpoint, Z3_func_decl, Z3_string, Z3_symbol, Z3_EXCEPTION, Z3_INVALID_ARG,
    Z3_INVALID_USAGE, Z3_L_TRUE, Z3_L_UNDEF, Z3_OK,
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
    if d.is_null() || axiom == 0 {
        return;
    }
    // SAFETY: `ffi_guard_void` null-checks `c` and catches panics; `d` is a
    // separate arena allocation, kept alive by the context.
    unsafe {
        ffi_guard_void(c, |ctx| {
            let handle = &mut *d;
            handle.assertions.push(ast_to_term(axiom));
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
                Some(handle) => handle.assertions.iter().copied().map(term_to_ast).collect(),
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
    if d.is_null() || a == 0 {
        return;
    }
    // Read the optional rule name outside the guard (raw-pointer deref).
    // SAFETY: `name` is null or a valid `SymbolHandle` in the context arena.
    let rule_name: Option<String> = unsafe { name.as_ref() }.map(super::SymbolHandle::display_name);
    // SAFETY: `ffi_guard_void` null-checks `c` and catches panics; `d` is kept
    // alive by the context arena.
    unsafe {
        ffi_guard_void(c, |ctx| {
            let handle = &mut *d;
            let term = ast_to_term(a);
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
        ffi_guard_ast(c, |ctx| {
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
            term_to_ast(answer)
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
                            asts.push(term_to_ast(rule));
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
// SMT-LIB2 / fixedpoint-script parsing (honest divergence).
// ============================================================================

/// Parse a fixedpoint-rule script string and add its rules, returning the
/// queries found.
///
/// DIVERGENCE: AY does not parse Z3's fixedpoint/Datalog *script* dialect
/// (`declare-rel` / `declare-var` / `rule` / `query`). Rather than fabricate a
/// rule/query set — which would silently corrupt the CHC problem and every later
/// verdict — this sets `Z3_EXCEPTION` and returns an EMPTY (never null) query
/// vector, adding no rules. Rules must be built with `Z3_fixedpoint_add_rule` /
/// `Z3_fixedpoint_register_relation` instead.
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
    // Extract the script text outside the guard (raw-pointer deref).
    let script: Option<String> = if s.is_null() {
        None
    } else {
        // SAFETY: caller guarantees a valid null-terminated C string when non-null.
        match unsafe { CStr::from_ptr(s) }.to_str() {
            Ok(v) => Some(v.to_string()),
            Err(_) => None,
        }
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
            let _script = script;
            // DIVERGENCE: no fixedpoint-script parser — honest empty result
            // rather than fabricated rules/queries.
            ctx.last_error = Z3_EXCEPTION;
            ctx.error_msg = Some(
                "Z3_fixedpoint_from_string: parsing the Z3 fixedpoint/Datalog script dialect is \
                 not supported; build rules via Z3_fixedpoint_add_rule instead. No rules were \
                 added and an empty query vector is returned."
                    .to_string(),
            );
            cache_ast_vector(ctx, Vec::new())
        })
    }
}

#[cfg(test)]
#[path = "fixedpoint_ext2_tests.rs"]
mod fixedpoint_ext2_tests;
