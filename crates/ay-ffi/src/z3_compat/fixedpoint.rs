// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Z3-compatible `Fixedpoint` (CHC / Datalog) sub-API, backed by AY's
//! Spacer-class CHC engine (`ay-chc`).
//!
//! Implements the subset of the Z3 `Z3_fixedpoint_*` C API that a consumer
//! needs to declare relations, add Horn rules, and query reachability:
//!
//! - [`Z3_mk_fixedpoint`] / [`Z3_fixedpoint_inc_ref`] / [`Z3_fixedpoint_dec_ref`]
//! - [`Z3_fixedpoint_register_relation`] — register a predicate/relation
//!   (a Bool-range `Z3_func_decl`).
//! - [`Z3_fixedpoint_add_rule`] — add a Horn clause, typically
//!   `(forall vars (=> body head))`, a bare fact, or a bare relation head.
//! - [`Z3_fixedpoint_query`] — query reachability of a relation.
//! - [`Z3_fixedpoint_to_string`] / [`Z3_fixedpoint_get_answer`].
//!
//! # How CHC is driven (genuine, not faked)
//!
//! The handle records the registered relations (as `ay-chc` predicates) and the
//! added rule ASTs. On `Z3_fixedpoint_query`, the rules + query are translated
//! from AY's interned `Term`s into an [`ay_chc::ChcProblem`] (predicates,
//! [`ay_chc::HornClause`]s with body/head over [`ay_chc::ChcExpr`]) and solved by
//! [`ay_chc::AdaptivePortfolio::solve`] — the same proof-validated portfolio the
//! `ay` CLI uses for `(set-logic HORN)` files. There is no hard-coded or guessed
//! answer; every verdict is a real `ay-chc` solve.
//!
//! # Query polarity (matches Z3 exactly)
//!
//! Z3's fixedpoint query returns `Z3_L_TRUE` when the query relation is
//! reachable/derivable (i.e. the system is UNSAFE) and `Z3_L_FALSE` when it is
//! unreachable (SAFE). This is the INVERSE of the SMT-LIB HORN sat/unsat
//! convention and matches `ay_chc::ChcProblem::is_fixedpoint_format` and the
//! `ay` CLI's fixedpoint emitter (`Safe => unsat`, `Unsafe => sat`). So:
//!
//! - `ay-chc` `Unsafe` (query reachable) → `Z3_L_TRUE`
//! - `ay-chc` `Safe`   (query unreachable) → `Z3_L_FALSE`
//! - `ay-chc` `Unknown` / untranslatable / undischarged → `Z3_L_UNDEF`
//!
//! A `Safe` verdict is additionally passed through the same final soundness
//! discharge gate the CLI uses ([`ay_chc::engines::external_invariant_model_excludes_error`]):
//! if the invariant does not provably exclude the error, the result is demoted
//! to `Z3_L_UNDEF` rather than reported as a (possibly false) SAFE.
//!
//! # Handle model
//!
//! A `Z3_fixedpoint` is a context-arena-owned handle, like `Z3_optimize` /
//! `Z3_solver`. `inc_ref`/`dec_ref` are bookkeeping-only no-ops; the handle
//! lives until `Z3_del_context` frees the arena.
//!
//! # Scope / limitations (honest)
//!
//! The Term→ChcExpr translator covers the common LIA/LRA/Bool transition-system
//! fragment (relations over Int/Real/Bool, the standard arithmetic/boolean/
//! comparison operators, ITE, and predicate applications). A rule shape it cannot
//! translate exactly — or a query over an undeclared/non-relation term — yields
//! an error (and `Z3_fixedpoint_query` returns `Z3_L_UNDEF`); it never silently
//! produces a wrong verdict.

use std::ffi::c_int;
use std::ptr;

use ay_chc::{
    AdaptiveConfig, AdaptivePortfolio, ChcExpr, ChcProblem, ChcSort, ChcStatistics, ChcVar,
    ClauseBody, ClauseHead, Counterexample, HornClause, InvariantModel, PdrConfig, PredicateId,
    VerifiedChcResult,
};
use ay_dpll::api::{Solver, Term, TermKind};

use super::{
    ast_to_term, cache_string, ffi_guard_const_ptr, ffi_guard_int, ffi_guard_ptr, ffi_guard_void,
    FixedpointHandle, FixedpointLemmaHint, RegisteredRelation, Z3_ast, Z3_context, Z3_fixedpoint,
    Z3_func_decl, Z3_string, Z3_symbol, Z3_L_FALSE, Z3_L_TRUE, Z3_L_UNDEF, Z3_OK,
};

// ---- Fixedpoint lifecycle ----

/// Create a fixedpoint (CHC/Datalog) context.
///
/// The returned handle is owned by the context arena and lives until
/// `Z3_del_context`.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_fixedpoint(c: Z3_context) -> Z3_fixedpoint {
    // SAFETY: `c` is the caller-supplied context pointer; `ffi_guard_ptr`
    // null-checks it and catches panics. The handle is registered in
    // `fixedpoint_handle_cache` and freed once, on context drop.
    unsafe {
        ffi_guard_ptr(c, |ctx| {
            let handle = Box::into_raw(Box::new(FixedpointHandle {
                _ctx: c,
                relations: Vec::new(),
                rules: Vec::new(),
                rule_names: Vec::new(),
                assertions: Vec::new(),
                last_status: Z3_L_UNDEF,
                last_reason_unknown: None,
                last_cex: None,
                last_query_rules: Vec::new(),
                last_query_rule_names: Vec::new(),
                last_statistics: None,
                last_invariant: None,
                lemma_hints: Vec::new(),
            }));
            ctx.fixedpoint_handle_cache.push(handle);
            handle
        })
    }
}

/// Increment fixedpoint reference count (bookkeeping no-op).
///
/// The handle is arena-owned and freed only by `Z3_del_context`.
///
/// # Safety
/// Pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_fixedpoint_inc_ref(_c: Z3_context, _d: Z3_fixedpoint) {}

/// Decrement fixedpoint reference count (bookkeeping no-op).
///
/// The handle is arena-owned and freed only by `Z3_del_context` (no early-free).
///
/// # Safety
/// Pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_fixedpoint_dec_ref(_c: Z3_context, _d: Z3_fixedpoint) {}

// ---- Relation / rule registration ----

/// Register a relation (predicate) with the fixedpoint engine.
///
/// `f` must be a Bool-range function declaration; its domain sorts become the
/// relation's argument sorts.
///
/// # Safety
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_fixedpoint_register_relation(
    c: Z3_context,
    d: Z3_fixedpoint,
    f: Z3_func_decl,
) {
    if d.is_null() || f.is_null() {
        return;
    }
    // SAFETY: `f` was null-checked above; the handle is kept alive by the owning
    // context arena and read single-threaded per Z3 API contract.
    let decl = unsafe { (*f).decl.clone() };
    // SAFETY: see ffi_guard_void; `d` is kept alive by the context arena.
    unsafe {
        ffi_guard_void(c, |ctx| {
            let name = decl.name().to_string();
            let arg_sorts: Vec<ChcSort> = decl
                .domain()
                .iter()
                .map(|s| ChcSort::from(s.clone()))
                .collect();
            let handle = &mut *d;
            // Idempotent: re-registering the same relation name is a no-op.
            if handle.relations.iter().any(|r| r.name == name) {
                return;
            }
            handle
                .relations
                .push(RegisteredRelation { name, arg_sorts });
            ctx.last_error = Z3_OK;
        });
    }
}

/// Add a Horn rule to the fixedpoint engine.
///
/// `rule` is typically `(forall vars (=> body head))`, a bare fact
/// (`(=> constraint (P args))` with no relation in the body), or a bare relation
/// head. `name` is an optional, currently-unused rule name (recorded for
/// `Z3_fixedpoint_to_string` parity in a future revision).
///
/// # Safety
/// All pointers must be valid; `rule` must be a valid `Z3_ast`.
#[no_mangle]
pub unsafe extern "C" fn Z3_fixedpoint_add_rule(
    c: Z3_context,
    d: Z3_fixedpoint,
    rule: Z3_ast,
    name: Z3_symbol,
) {
    if d.is_null() || rule == 0 {
        return;
    }
    // Read the optional rule name outside the guard (raw-pointer deref). A null
    // symbol means an unnamed rule.
    // SAFETY: `name` is either null or a valid `SymbolHandle` kept alive by the
    // context's `symbol_cache`; single-threaded per Z3 API contract.
    let rule_name: Option<String> = unsafe { name.as_ref() }.map(super::SymbolHandle::display_name);
    // SAFETY: see ffi_guard_void; `d` is kept alive by the context arena.
    unsafe {
        ffi_guard_void(c, |ctx| {
            let handle = &mut *d;
            handle.rules.push(ast_to_term(rule));
            // Keep `rule_names` index-aligned with `rules`.
            handle.rule_names.push(rule_name);
            ctx.last_error = Z3_OK;
        });
    }
}

// ---- Query ----

/// Query reachability of `query` against the registered rules.
///
/// Returns `Z3_L_TRUE` if the query relation is reachable/derivable (UNSAFE),
/// `Z3_L_FALSE` if it is unreachable (SAFE), and `Z3_L_UNDEF` if the engine is
/// inconclusive or the rules/query could not be translated exactly.
///
/// # Safety
/// All pointers must be valid; `query` must be a valid `Z3_ast`.
#[no_mangle]
pub unsafe extern "C" fn Z3_fixedpoint_query(
    c: Z3_context,
    d: Z3_fixedpoint,
    query: Z3_ast,
) -> c_int {
    if d.is_null() || query == 0 {
        return Z3_L_UNDEF;
    }
    // SAFETY: see ffi_guard_int; `d` is kept alive by the context arena.
    unsafe {
        ffi_guard_int(c, Z3_L_UNDEF, |ctx| {
            let handle = &mut *d;
            let query_term = ast_to_term(query);
            // Recursive-definition gate (P1.1): the fixedpoint path neither
            // injects the defining axioms nor expands rec-f applications, so
            // a rule/assertion/query mentioning a `Z3_add_rec_def` name would
            // be solved with it as a plain uninterpreted symbol — exactly the
            // forbidden wrong-verdict class. Fail closed to unknown.
            if !ctx.rec_fun_defs.is_empty() {
                let mut scan: Vec<Term> = handle.rules.clone();
                scan.extend(handle.assertions.iter().copied());
                scan.push(query_term);
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
            // `run_query` records last_status/last_cex/last_reason_unknown on the
            // handle via `record_outcome`.
            let status = run_query(&ctx.solver, handle, query_term);
            ctx.last_error = Z3_OK;
            status
        })
    }
}

/// Outcome of a single CHC solve: the fixedpoint-polarity `Z3_lbool`, the
/// retained counterexample (only for `Unsafe`), — for any `Z3_L_UNDEF` path —
/// an honest human-readable reason for `Z3_fixedpoint_get_reason_unknown`,
/// the engine's REAL solve counters, and (for a validated `Safe`) the
/// verified invariant model with its predicate-resolution table.
pub(super) struct QueryOutcome {
    pub(super) status: c_int,
    pub(super) cex: Option<Counterexample>,
    pub(super) reason: Option<String>,
    pub(super) statistics: Option<ChcStatistics>,
    pub(super) invariant: Option<(Vec<(String, PredicateId)>, InvariantModel)>,
}

impl QueryOutcome {
    /// An inconclusive outcome with an honest reason (no stats / invariant).
    pub(super) fn undef(reason: String) -> Self {
        Self {
            status: Z3_L_UNDEF,
            cex: None,
            reason: Some(reason),
            statistics: None,
            invariant: None,
        }
    }
}

/// Record a completed solve outcome on the handle: last status, retained
/// counterexample, reason-unknown, statistics, validated invariant, and the
/// rule/name snapshots the trace family maps clause indices against. Shared by
/// `Z3_fixedpoint_query` and `Z3_fixedpoint_query_relations`.
pub(super) fn record_outcome(handle: &mut FixedpointHandle, outcome: QueryOutcome) -> c_int {
    handle.last_status = outcome.status;
    handle.last_cex = outcome.cex;
    handle.last_reason_unknown = outcome.reason;
    handle.last_statistics = outcome.statistics;
    handle.last_invariant = outcome.invariant;
    handle.last_query_rules = handle.rules.clone();
    handle.last_query_rule_names = handle.rule_names.clone();
    outcome.status
}

/// Translate collision-proof function names in formatted solver terms back to
/// their caller-visible Z3 symbols. Internal names remain authoritative in the
/// CHC translator and solver; this is used only at the string API boundary.
///
/// The small lexer deliberately skips SMT string literals, so a user string
/// that happens to contain an internal-name spelling is never rewritten.
fn fixedpoint_surface_text(ctx: &super::Z3Context, rendered: &str) -> String {
    let replacements: std::collections::HashMap<String, String> = ctx
        .ffi_decl_symbols
        .iter()
        .map(|(internal, symbol)| {
            (
                ay_core::quote_symbol(internal),
                ay_core::quote_symbol(&symbol.display_name()),
            )
        })
        .collect();
    if replacements.is_empty() {
        return rendered.to_string();
    }

    let bytes = rendered.as_bytes();
    let mut out = String::with_capacity(rendered.len());
    let mut i = 0;
    while i < bytes.len() {
        if bytes[i] == b'"' {
            // SMT-LIB escapes a quote inside a string by doubling it.
            let start = i;
            i += 1;
            while i < bytes.len() {
                if bytes[i] == b'"' {
                    if i + 1 < bytes.len() && bytes[i + 1] == b'"' {
                        i += 2;
                        continue;
                    }
                    i += 1;
                    break;
                }
                i += 1;
            }
            out.push_str(&rendered[start..i]);
            continue;
        }

        let start = i;
        if bytes[i] == b'|' {
            i += 1;
            while i < bytes.len() && bytes[i] != b'|' {
                i += 1;
            }
            i = (i + 1).min(bytes.len());
        } else if bytes[i].is_ascii_whitespace() || matches!(bytes[i], b'(' | b')') {
            i += 1;
        } else {
            while i < bytes.len()
                && !bytes[i].is_ascii_whitespace()
                && !matches!(bytes[i], b'(' | b')')
            {
                i += 1;
            }
        }
        let token = &rendered[start..i];
        out.push_str(replacements.get(token).map_or(token, String::as_str));
    }
    out
}

/// Render the fixedpoint rule set as a string (best-effort, context-owned).
///
/// # Safety
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_fixedpoint_to_string(c: Z3_context, d: Z3_fixedpoint) -> Z3_string {
    if d.is_null() {
        return ptr::null();
    }
    // SAFETY: see ffi_guard_const_ptr; `d` is kept alive by the context arena.
    unsafe {
        ffi_guard_const_ptr(c, |ctx| {
            let handle = &*d;
            let mut out = String::new();
            for rel in &handle.relations {
                out.push_str("(declare-rel ");
                let surface_name = ctx
                    .ffi_decl_symbols
                    .get(&rel.name)
                    .map(super::SymbolKey::display_name)
                    .unwrap_or_else(|| rel.name.clone());
                out.push_str(&ay_core::quote_symbol(&surface_name));
                out.push_str(" (");
                for (i, s) in rel.arg_sorts.iter().enumerate() {
                    if i > 0 {
                        out.push(' ');
                    }
                    out.push_str(&s.to_string());
                }
                out.push_str("))\n");
            }
            for &rule in &handle.rules {
                out.push_str("(rule ");
                let rendered = ctx.solver.format_term(rule);
                out.push_str(&fixedpoint_surface_text(ctx, &rendered));
                out.push_str(")\n");
            }
            cache_string(ctx, out)
        })
    }
}

/// Return the last query answer as a string (`"sat"` / `"unsat"` / `"unknown"`).
///
/// Z3 returns a derivation/ground answer AST here; AY exposes the verdict text
/// since it does not synthesize a Datalog answer relation. The returned pointer
/// is context-owned.
///
/// # Safety
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_fixedpoint_get_answer(c: Z3_context, d: Z3_fixedpoint) -> Z3_string {
    if d.is_null() {
        return ptr::null();
    }
    // SAFETY: see ffi_guard_const_ptr; `d` is kept alive by the context arena.
    unsafe {
        ffi_guard_const_ptr(c, |ctx| {
            let handle = &*d;
            let verdict = match handle.last_status {
                Z3_L_TRUE => "sat",
                Z3_L_FALSE => "unsat",
                _ => "unknown",
            };
            cache_string(ctx, verdict.to_string())
        })
    }
}

// ============================================================================
// Term -> ChcProblem translation + solve
// ============================================================================

/// A translation failure. Surfaced as `Z3_L_UNDEF` (never a wrong verdict).
pub(super) struct TranslateErr;

/// The stable reason recorded for a query that could not be translated exactly.
pub(super) const REASON_UNTRANSLATABLE: &str =
    "the rule set or query could not be translated into AY's CHC fragment exactly; \
     reported UNKNOWN rather than risk a wrong verdict";

/// Build the `ChcProblem` from the handle's relations + rules + the query, solve
/// it with `ay-chc`, record the outcome on the handle, and return the mapped
/// `Z3_lbool` (Z3's fixedpoint polarity).
fn run_query(solver: &Solver, handle: &mut FixedpointHandle, query: Term) -> c_int {
    let outcome = match build_problem(solver, handle, query) {
        Ok((problem, rel_ids)) => solve_problem(problem, rel_ids),
        Err(TranslateErr) => QueryOutcome::undef(REASON_UNTRANSLATABLE.to_string()),
    };
    record_outcome(handle, outcome)
}

/// Declare every registered relation and translate every rule (folding any
/// background axioms into each clause body). Returns the partially-built problem,
/// the `(name -> PredicateId)` resolution table, and the translated background
/// axiom constraints (so callers can fold them into any additional clauses they
/// append — the query clause or per-relation safety clauses).
///
/// Shared by [`build_problem`] (query path) and `Z3_fixedpoint_query_relations`.
pub(super) fn build_problem_base(
    solver: &Solver,
    handle: &FixedpointHandle,
) -> Result<(ChcProblem, Vec<(String, PredicateId)>, Vec<ChcExpr>), TranslateErr> {
    let mut problem = ChcProblem::new();
    // Mark fixedpoint polarity for any internal consumer; we map the verdict
    // explicitly below regardless.
    problem.set_fixedpoint_format();

    let mut tr = Translator {
        solver,
        relations: &handle.relations,
    };

    // Declare relations up-front so predicate IDs are stable and resolvable by
    // name during rule translation.
    let mut rel_ids: Vec<(String, PredicateId)> = Vec::with_capacity(handle.relations.len());
    for rel in &handle.relations {
        let id = problem.declare_predicate(rel.name.clone(), rel.arg_sorts.clone());
        rel_ids.push((rel.name.clone(), id));
    }
    let resolve = |name: &str| -> Option<PredicateId> {
        rel_ids.iter().find(|(n, _)| n == name).map(|(_, id)| *id)
    };

    // Translate background axioms (Z3_fixedpoint_assert) into constraints. An
    // axiom that references a relation symbol, or that falls outside the
    // interpreted fragment, is a `TranslateErr` → the whole query is UNKNOWN
    // (a background axiom must never silently drop, which could flip a verdict).
    let mut axioms: Vec<ChcExpr> = Vec::with_capacity(handle.assertions.len());
    for &axiom in &handle.assertions {
        axioms.push(tr.term_to_expr(axiom, &resolve)?);
    }

    for &rule in &handle.rules {
        let clause = tr.rule_to_clause(rule, &resolve)?;
        let clause = apply_lemma_hints_to_clause(clause, &handle.lemma_hints, &rel_ids);
        problem.add_clause(fold_axioms_into_clause(clause, &axioms));
    }

    Ok((problem, rel_ids, axioms))
}

/// Conjoin every trusted lemma hint (see [`FixedpointLemmaHint`]) onto the
/// BODY occurrences of its predicate: for each body atom `P(args)` with a hint
/// `φ` over `P`'s argument positions, `φ[params := args]` is added to the
/// clause constraint. This is EXACTLY how a Spacer lemma is used (the engine
/// ASSUMES it of every reachable `P`-state) — Z3's trust-the-hint contract.
pub(super) fn apply_lemma_hints_to_clause(
    mut clause: HornClause,
    hints: &[FixedpointLemmaHint],
    rel_ids: &[(String, PredicateId)],
) -> HornClause {
    if hints.is_empty() {
        return clause;
    }
    let name_of = |pid: PredicateId| -> Option<&str> {
        rel_ids
            .iter()
            .find(|(_, id)| *id == pid)
            .map(|(n, _)| n.as_str())
    };
    let mut extra: Vec<ChcExpr> = Vec::new();
    for (pid, args) in &clause.body.predicates {
        let Some(pred_name) = name_of(*pid) else {
            continue;
        };
        for hint in hints.iter().filter(|h| h.pred == pred_name) {
            let subst: Vec<(ChcVar, ChcExpr)> = hint
                .vars
                .iter()
                .filter_map(|(pos, var)| args.get(*pos).map(|a| (var.clone(), a.clone())))
                .collect();
            // Positions were arity-checked at registration; a mismatch here
            // (defensive) skips the hint rather than instantiating it wrongly.
            if subst.len() == hint.vars.len() {
                extra.push(hint.expr.substitute(&subst));
            }
        }
    }
    if extra.is_empty() {
        return clause;
    }
    let mut conj: Vec<ChcExpr> = Vec::with_capacity(extra.len() + 1);
    if let Some(existing) = clause.body.constraint.take() {
        conj.push(existing);
    }
    conj.extend(extra);
    clause.body.constraint = Some(ChcExpr::and_all(conj));
    clause
}

/// Construct the full `ay-chc` query problem: the base (relations + rules +
/// axioms) plus the query encoded as a safety clause `query-body => false`.
/// Also returns the `(name, PredicateId)` resolution table so the caller can
/// key a retained invariant model by predicate.
fn build_problem(
    solver: &Solver,
    handle: &FixedpointHandle,
    query: Term,
) -> Result<(ChcProblem, Vec<(String, PredicateId)>), TranslateErr> {
    let (mut problem, rel_ids, axioms) = build_problem_base(solver, handle)?;
    let resolve = |name: &str| -> Option<PredicateId> {
        rel_ids.iter().find(|(n, _)| n == name).map(|(_, id)| *id)
    };
    let mut tr = Translator {
        solver,
        relations: &handle.relations,
    };
    let query_clause = tr.query_to_clause(query, &resolve)?;
    let query_clause = apply_lemma_hints_to_clause(query_clause, &handle.lemma_hints, &rel_ids);
    problem.add_clause(fold_axioms_into_clause(query_clause, &axioms));
    Ok((problem, rel_ids))
}

/// Conjoin the background-axiom constraints into a clause's body (a global
/// invariant that holds in every state). Leaves the clause unchanged when there
/// are no axioms.
pub(super) fn fold_axioms_into_clause(mut clause: HornClause, axioms: &[ChcExpr]) -> HornClause {
    if axioms.is_empty() {
        return clause;
    }
    let mut conj: Vec<ChcExpr> = Vec::with_capacity(axioms.len() + 1);
    if let Some(existing) = clause.body.constraint.take() {
        conj.push(existing);
    }
    for a in axioms {
        conj.push(a.clone());
    }
    clause.body.constraint = Some(ChcExpr::and_all(conj));
    clause
}

/// Solve the problem with `ay-chc`, mapping the verdict to a fixedpoint-polarity
/// `Z3_lbool` and capturing the counterexample / reason-unknown for the handle.
///
/// `Unsafe` (query reachable) → `Z3_L_TRUE`; `Safe` (query unreachable, and the
/// invariant provably excludes the error) → `Z3_L_FALSE`; everything else →
/// `Z3_L_UNDEF` (with an honest reason).
pub(super) fn solve_problem(
    problem: ChcProblem,
    rel_ids: Vec<(String, PredicateId)>,
) -> QueryOutcome {
    let portfolio = AdaptivePortfolio::new(problem.clone(), AdaptiveConfig::default());
    let result = portfolio.solve();
    // REAL accumulated engine counters for this run (never fabricated) —
    // captured for `Z3_fixedpoint_get_statistics` / `_get_num_levels`.
    let statistics = Some(portfolio.statistics());
    match result {
        VerifiedChcResult::Unsafe(vcex) => QueryOutcome {
            status: Z3_L_TRUE,
            cex: Some(vcex.counterexample().clone()),
            reason: None,
            statistics,
            invariant: None,
        },
        VerifiedChcResult::Safe(inv) => {
            // Final soundness discharge gate, mirroring the `ay` CLI: only report
            // SAFE (L_FALSE) if the invariant provably excludes the error.
            let config = PdrConfig::default().with_strict_proofs(true);
            match ay_chc::engines::external_invariant_model_excludes_error(
                &problem,
                inv.model(),
                &config,
            ) {
                Ok(true) => QueryOutcome {
                    status: Z3_L_FALSE,
                    cex: None,
                    reason: None,
                    statistics,
                    // The VALIDATED invariant (the exact model the gate just
                    // verified) — backs `Z3_fixedpoint_get_cover_delta(-1, ·)`.
                    invariant: Some((rel_ids, inv.model().clone())),
                },
                _ => QueryOutcome {
                    status: Z3_L_UNDEF,
                    cex: None,
                    reason: Some(
                        "the CHC portfolio reported SAFE but its invariant did not provably \
                         exclude the error under strict proofs; demoted to UNKNOWN"
                            .to_string(),
                    ),
                    statistics,
                    invariant: None,
                },
            }
        }
        VerifiedChcResult::Unknown(marker) => QueryOutcome {
            status: Z3_L_UNDEF,
            cex: None,
            reason: Some(format!("the CHC portfolio was inconclusive: {marker}")),
            statistics,
            invariant: None,
        },
        // `VerifiedChcResult` is `#[non_exhaustive]`: any future variant is
        // treated as inconclusive (never a wrong SAFE/UNSAFE verdict).
        _ => QueryOutcome {
            status: Z3_L_UNDEF,
            cex: None,
            reason: Some(
                "the CHC portfolio returned an unrecognized result variant; treated as UNKNOWN"
                    .to_string(),
            ),
            statistics,
            invariant: None,
        },
    }
}

/// Translator from AY interned `Term`s to `ay-chc` expressions/clauses.
/// Build a [`FixedpointLemmaHint`] from a property TERM over a registered
/// predicate's argument positions. `positions` maps a variable NAME occurring
/// in the property to the predicate argument position it denotes (`__db{i}`
/// for the cover/invariant surface; the antecedent's variable names for the
/// `add_constraint` implication shape). Fails honestly — with a reason — when
/// the property mentions an unmapped/out-of-arity variable, contains a
/// relation symbol, is not Bool-sorted, or falls outside AY's translatable
/// CHC fragment. Never registers a hint it could mis-instantiate.
pub(super) fn build_lemma_hint(
    solver: &Solver,
    relations: &[RegisteredRelation],
    pred: &RegisteredRelation,
    positions: &dyn Fn(&str) -> Option<usize>,
    property: Term,
) -> Result<FixedpointLemmaHint, String> {
    let arity = pred.arg_sorts.len();
    // Collect the property's distinct variable terms (DFS over the DAG).
    let mut var_terms: Vec<Term> = Vec::new();
    {
        let mut stack = vec![property];
        let mut visited: std::collections::HashSet<Term> = std::collections::HashSet::new();
        while let Some(cur) = stack.pop() {
            if !visited.insert(cur) {
                continue;
            }
            match solver.term_kind(cur) {
                TermKind::Var { .. } => {
                    if !var_terms.contains(&cur) {
                        var_terms.push(cur);
                    }
                }
                TermKind::Forall | TermKind::Exists | TermKind::Let => {
                    return Err("the property contains a binder".to_string());
                }
                _ => stack.extend(solver.term_children(cur)),
            }
        }
    }
    let mut vars: Vec<(usize, ChcVar)> = Vec::with_capacity(var_terms.len());
    for vt in var_terms {
        let TermKind::Var { name } = solver.term_kind(vt) else {
            continue;
        };
        let Some(pos) = positions(&name) else {
            return Err(format!(
                "the property mentions variable '{name}', which is not an argument of {}",
                pred.name
            ));
        };
        if pos >= arity {
            return Err(format!(
                "argument position {pos} is out of range for {} (arity {arity})",
                pred.name
            ));
        }
        // The exact `ChcVar` the translator will emit for this variable.
        let sort = ChcSort::from(solver.term_sort(vt));
        vars.push((pos, ChcVar::new(name, sort)));
    }
    let mut tr = Translator { solver, relations };
    let expr = tr
        .term_to_expr(property, &|_| None)
        .map_err(|TranslateErr| {
            "the property is outside AY's translatable CHC fragment (or mentions a relation)"
                .to_string()
        })?;
    Ok(FixedpointLemmaHint {
        pred: pred.name.clone(),
        expr,
        vars,
    })
}

struct Translator<'a> {
    solver: &'a Solver,
    relations: &'a [RegisteredRelation],
}

impl Translator<'_> {
    fn is_relation(&self, name: &str) -> bool {
        self.relations.iter().any(|r| r.name == name)
    }

    /// Translate a rule term into a `HornClause`.
    ///
    /// Accepts (after stripping `forall`):
    /// - `(=> antecedent consequent)` — antecedent→body, consequent→head.
    /// - `(or head ¬a ¬b ...)` — AY's eager simplifier rewrites `(=> (and a b) head)`
    ///   into this clausal form; `head` is the sole positive relation literal (or
    ///   `false`/absent → a query) and the negated literals form the body.
    /// - a bare relation application — a fact `true => P(args)`.
    fn rule_to_clause(
        &mut self,
        term: Term,
        resolve: &impl Fn(&str) -> Option<PredicateId>,
    ) -> Result<HornClause, TranslateErr> {
        match self.solver.term_kind(term) {
            TermKind::Forall => {
                let children = self.solver.term_children(term);
                let body = *children.first().ok_or(TranslateErr)?;
                self.rule_to_clause(body, resolve)
            }
            TermKind::App { name, num_args } if name == "=>" && num_args == 2 => {
                let antecedent = self.solver.app_arg(term, 0).ok_or(TranslateErr)?;
                let consequent = self.solver.app_arg(term, 1).ok_or(TranslateErr)?;
                let body = self.body_to_clause_body(antecedent, resolve)?;
                let head = self.head_to_clause_head(consequent, resolve)?;
                Ok(HornClause::new(body, head))
            }
            // Clausal (disjunctive) Horn form produced by the simplifier.
            TermKind::App { name, .. } if name == "or" => {
                self.clause_from_disjunction(term, resolve, false)
            }
            // A bare predicate-application head is a fact: `true => P(args)`.
            TermKind::App { ref name, .. } if self.is_relation(name) => {
                let head = self.head_to_clause_head(term, resolve)?;
                Ok(HornClause::new(ClauseBody::empty(), head))
            }
            _ => Err(TranslateErr),
        }
    }

    /// Translate a clausal Horn disjunction `(or L1 L2 ...)` into a `HornClause`.
    ///
    /// Each literal is either positive (the head, must be a relation app — at
    /// most one) or negative `(not φ)` (a body conjunct). A positive non-relation
    /// literal `φ` becomes a body conjunct `¬φ` (since `head ∨ φ ≡ ¬(¬head) ∨ φ`,
    /// i.e. `¬φ ⇒ head`). With no positive relation literal, the head is `false`
    /// (a query/safety clause). When `force_query` is set, the head is forced to
    /// `false` and any positive relation literal is treated as a body atom — used
    /// for query goals expressed as `¬goal` clauses.
    fn clause_from_disjunction(
        &mut self,
        term: Term,
        resolve: &impl Fn(&str) -> Option<PredicateId>,
        force_query: bool,
    ) -> Result<HornClause, TranslateErr> {
        let mut predicates: Vec<(PredicateId, Vec<ChcExpr>)> = Vec::new();
        let mut constraints: Vec<ChcExpr> = Vec::new();
        let mut head: Option<ClauseHead> = None;

        for lit in self.solver.term_children(term) {
            match self.solver.term_kind(lit) {
                // Negative literal `(not φ)` → body conjunct φ.
                TermKind::Not => {
                    let inner = self.solver.app_arg(lit, 0).ok_or(TranslateErr)?;
                    self.collect_conjuncts(inner, resolve, &mut predicates, &mut constraints)?;
                }
                // Positive relation literal → the head (at most one), unless this
                // is a query clause (then it is a body atom).
                TermKind::App { ref name, .. } if self.is_relation(name) => {
                    if force_query {
                        let id = resolve(name).ok_or(TranslateErr)?;
                        let args = self.app_args_to_exprs(lit, resolve)?;
                        predicates.push((id, args));
                    } else if head.is_some() {
                        // More than one positive relation literal: not Horn.
                        return Err(TranslateErr);
                    } else {
                        let id = resolve(name).ok_or(TranslateErr)?;
                        let args = self.app_args_to_exprs(lit, resolve)?;
                        head = Some(ClauseHead::Predicate(id, args));
                    }
                }
                // Positive interpreted literal φ → body conjunct ¬φ.
                _ => {
                    let expr = self.term_to_expr(lit, resolve)?;
                    constraints.push(ChcExpr::not(expr));
                }
            }
        }

        let constraint = if constraints.is_empty() {
            None
        } else {
            Some(ChcExpr::and_all(constraints))
        };
        let body = ClauseBody::new(predicates, constraint);
        let head = if force_query {
            ClauseHead::False
        } else {
            head.unwrap_or(ClauseHead::False)
        };
        Ok(HornClause::new(body, head))
    }

    /// Translate the query term into a safety clause `query-goal => false`.
    ///
    /// Z3's `Z3_fixedpoint_query` takes the goal whose reachability is tested:
    /// a relation application, a conjunction of a relation app and constraints,
    /// or a `(forall vars (=> body false))`-style goal (which the simplifier may
    /// present as a disjunction `(or ¬a ¬b ...)`).
    fn query_to_clause(
        &mut self,
        term: Term,
        resolve: &impl Fn(&str) -> Option<PredicateId>,
    ) -> Result<HornClause, TranslateErr> {
        match self.solver.term_kind(term) {
            TermKind::Forall => {
                let children = self.solver.term_children(term);
                let body = *children.first().ok_or(TranslateErr)?;
                self.query_to_clause(body, resolve)
            }
            // `(=> body false)` goal form.
            TermKind::App { name, num_args } if name == "=>" && num_args == 2 => {
                let antecedent = self.solver.app_arg(term, 0).ok_or(TranslateErr)?;
                let body = self.body_to_clause_body(antecedent, resolve)?;
                Ok(HornClause::new(body, ClauseHead::False))
            }
            // Clausal goal form: `(or ¬a ¬b ...)` ≡ `(=> (and a b) false)`.
            TermKind::App { name, .. } if name == "or" => {
                self.clause_from_disjunction(term, resolve, true)
            }
            // A conjunctive goal `(and (P args) constraints...)` or a bare
            // relation application: reachable iff the goal body is derivable.
            _ => {
                let body = self.body_to_clause_body(term, resolve)?;
                Ok(HornClause::new(body, ClauseHead::False))
            }
        }
    }

    /// Translate an antecedent into a `ClauseBody`: split top-level conjunction
    /// into relation applications (predicates) and interpreted constraints.
    fn body_to_clause_body(
        &mut self,
        term: Term,
        resolve: &impl Fn(&str) -> Option<PredicateId>,
    ) -> Result<ClauseBody, TranslateErr> {
        let mut predicates: Vec<(PredicateId, Vec<ChcExpr>)> = Vec::new();
        let mut constraints: Vec<ChcExpr> = Vec::new();
        self.collect_conjuncts(term, resolve, &mut predicates, &mut constraints)?;
        let constraint = if constraints.is_empty() {
            None
        } else {
            Some(ChcExpr::and_all(constraints))
        };
        Ok(ClauseBody::new(predicates, constraint))
    }

    /// Recursively flatten top-level `and` into predicate apps + constraints.
    fn collect_conjuncts(
        &mut self,
        term: Term,
        resolve: &impl Fn(&str) -> Option<PredicateId>,
        predicates: &mut Vec<(PredicateId, Vec<ChcExpr>)>,
        constraints: &mut Vec<ChcExpr>,
    ) -> Result<(), TranslateErr> {
        if let TermKind::App { name, .. } = self.solver.term_kind(term) {
            if name == "and" {
                for child in self.solver.term_children(term) {
                    self.collect_conjuncts(child, resolve, predicates, constraints)?;
                }
                return Ok(());
            }
            if self.is_relation(&name) {
                let id = resolve(&name).ok_or(TranslateErr)?;
                let args = self.app_args_to_exprs(term, resolve)?;
                predicates.push((id, args));
                return Ok(());
            }
        }
        // `true` is a vacuous conjunct; drop it.
        if matches!(self.solver.bool_value(term), Some(true)) {
            return Ok(());
        }
        constraints.push(self.term_to_expr(term, resolve)?);
        Ok(())
    }

    /// Translate a consequent into a `ClauseHead`.
    fn head_to_clause_head(
        &mut self,
        term: Term,
        resolve: &impl Fn(&str) -> Option<PredicateId>,
    ) -> Result<ClauseHead, TranslateErr> {
        // Literal `false` head.
        if matches!(self.solver.bool_value(term), Some(false)) {
            return Ok(ClauseHead::False);
        }
        if let TermKind::App { name, .. } = self.solver.term_kind(term) {
            if self.is_relation(&name) {
                let id = resolve(&name).ok_or(TranslateErr)?;
                let args = self.app_args_to_exprs(term, resolve)?;
                return Ok(ClauseHead::Predicate(id, args));
            }
        }
        Err(TranslateErr)
    }

    /// Translate the argument terms of an application into `ChcExpr`s.
    fn app_args_to_exprs(
        &mut self,
        term: Term,
        resolve: &impl Fn(&str) -> Option<PredicateId>,
    ) -> Result<Vec<ChcExpr>, TranslateErr> {
        let n = self.solver.app_num_args(term);
        let mut out = Vec::with_capacity(n);
        for i in 0..n {
            let arg = self.solver.app_arg(term, i).ok_or(TranslateErr)?;
            out.push(self.term_to_expr(arg, resolve)?);
        }
        Ok(out)
    }

    /// Translate an interpreted (non-relation) term into a `ChcExpr`.
    ///
    /// Covers the LIA/LRA/Bool fragment: variables, Int/Bool/Real constants, the
    /// standard boolean/arithmetic/comparison operators, negation, and ITE. Any
    /// unsupported construct (arrays, bitvectors, uninterpreted functions, a
    /// relation symbol appearing inside an arithmetic context, etc.) is rejected
    /// with `TranslateErr` so the query returns `Z3_L_UNDEF` rather than a wrong
    /// verdict.
    fn term_to_expr(
        &mut self,
        term: Term,
        resolve: &impl Fn(&str) -> Option<PredicateId>,
    ) -> Result<ChcExpr, TranslateErr> {
        match self.solver.term_kind(term) {
            TermKind::Var { name } => {
                let sort = ChcSort::from(self.solver.term_sort(term));
                Ok(ChcExpr::var(ChcVar::new(name, sort)))
            }
            TermKind::Const => self.const_to_expr(term),
            TermKind::Not => {
                let inner = self.solver.app_arg(term, 0).ok_or(TranslateErr)?;
                Ok(ChcExpr::not(self.term_to_expr(inner, resolve)?))
            }
            TermKind::Ite => {
                let c = self.solver.app_arg(term, 0).ok_or(TranslateErr)?;
                let t = self.solver.app_arg(term, 1).ok_or(TranslateErr)?;
                let e = self.solver.app_arg(term, 2).ok_or(TranslateErr)?;
                Ok(ChcExpr::ite(
                    self.term_to_expr(c, resolve)?,
                    self.term_to_expr(t, resolve)?,
                    self.term_to_expr(e, resolve)?,
                ))
            }
            TermKind::App { name, num_args } => {
                // A relation symbol must not appear inside an interpreted
                // expression context (it is only valid as a body/head atom).
                if self.is_relation(&name) {
                    return Err(TranslateErr);
                }
                let args = self.app_args_to_exprs(term, resolve)?;
                self.op_to_expr(&name, num_args, args)
            }
            TermKind::Forall | TermKind::Exists | TermKind::Let => Err(TranslateErr),
            // `TermKind` is `#[non_exhaustive]`: reject any unknown kind rather
            // than guess a translation (keeps the verdict sound).
            _ => Err(TranslateErr),
        }
    }

    /// Translate a constant term into a `ChcExpr` (Bool / Int / Real only).
    fn const_to_expr(&self, term: Term) -> Result<ChcExpr, TranslateErr> {
        if let Some(b) = self.solver.bool_value(term) {
            return Ok(ChcExpr::Bool(b));
        }
        let s = self.solver.numeral_string(term).ok_or(TranslateErr)?;
        if let Ok(n) = s.parse::<i64>() {
            return Ok(ChcExpr::int(n));
        }
        if let Some((num, den)) = s.split_once('/') {
            if let (Ok(n), Ok(d)) = (num.trim().parse::<i64>(), den.trim().parse::<i64>()) {
                return Ok(ChcExpr::Real(n, d));
            }
        }
        Err(TranslateErr)
    }

    /// Map an interpreted operator name + translated args to a `ChcExpr`.
    fn op_to_expr(
        &self,
        name: &str,
        num_args: usize,
        mut args: Vec<ChcExpr>,
    ) -> Result<ChcExpr, TranslateErr> {
        // Helpers for binary / variadic shapes.
        let two = |a: Vec<ChcExpr>| -> Result<(ChcExpr, ChcExpr), TranslateErr> {
            let mut it = a.into_iter();
            let x = it.next().ok_or(TranslateErr)?;
            let y = it.next().ok_or(TranslateErr)?;
            Ok((x, y))
        };
        match name {
            "true" => Ok(ChcExpr::Bool(true)),
            "false" => Ok(ChcExpr::Bool(false)),
            "and" => Ok(ChcExpr::and_all(args)),
            "or" => Ok(ChcExpr::or_all(args)),
            "=>" | "implies" => {
                let (a, b) = two(args)?;
                Ok(ChcExpr::implies(a, b))
            }
            "=" => {
                let (a, b) = two(args)?;
                Ok(ChcExpr::eq(a, b))
            }
            "distinct" => {
                let (a, b) = two(args)?;
                Ok(ChcExpr::ne(a, b))
            }
            "<" => {
                let (a, b) = two(args)?;
                Ok(ChcExpr::lt(a, b))
            }
            "<=" => {
                let (a, b) = two(args)?;
                Ok(ChcExpr::le(a, b))
            }
            ">" => {
                let (a, b) = two(args)?;
                Ok(ChcExpr::gt(a, b))
            }
            ">=" => {
                let (a, b) = two(args)?;
                Ok(ChcExpr::ge(a, b))
            }
            "+" => {
                if args.is_empty() {
                    return Err(TranslateErr);
                }
                let mut acc = args.remove(0);
                for a in args {
                    acc = ChcExpr::add(acc, a);
                }
                Ok(acc)
            }
            "*" => {
                if args.is_empty() {
                    return Err(TranslateErr);
                }
                let mut acc = args.remove(0);
                for a in args {
                    acc = ChcExpr::mul(acc, a);
                }
                Ok(acc)
            }
            "-" => {
                // Unary minus or binary subtraction.
                if num_args == 1 {
                    Ok(ChcExpr::neg(args.into_iter().next().ok_or(TranslateErr)?))
                } else {
                    let (a, b) = two(args)?;
                    Ok(ChcExpr::sub(a, b))
                }
            }
            "mod" => {
                let (a, b) = two(args)?;
                Ok(ChcExpr::mod_op(a, b))
            }
            _ => Err(TranslateErr),
        }
    }
}
