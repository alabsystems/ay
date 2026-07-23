// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Z3-compatible solver *user-propagator*, *solved-form*, and *solver-extras*
//! surface (`Z3_solver_propagate_*`, `Z3_solver_cube`, `Z3_solver_get_levels`,
//! `Z3_solver_solve_for`, `Z3_solver_congruence_explain`, ...).
//!
//! USER PROPAGATOR — REAL via a SOUND FINAL-CHECK LOOP.
//! ------------------------------------------------------
//! Z3's user-propagator lets a consumer bolt a *custom theory* onto CDCL. AY's
//! CDCL core exposes no in-search callback hooks, so AY realizes the propagator
//! contract at the FFI solve level with a **final-check loop** (the standard way
//! solvers without in-engine hooks bolt on user propagation):
//!
//! 1. `Z3_solver_propagate_init`/`_fixed`/`_eq`/`_diseq`/`_final`/`_created`/
//!    `_register`(+`_cb`) genuinely store the callbacks + registered terms on
//!    the solver handle ([`UserPropagator`]).
//! 2. `Z3_solver_check` (when a propagator is registered) runs
//!    [`user_propagator_check`]: solve; on SAT, extract the candidate model's
//!    value for every registered term, then invoke `push_eh`, `fixed_eh(t, v)`
//!    per registered term with a ground value, best-effort `eq_eh`/`diseq_eh`
//!    for same-sort registered pairs the model equates/distinguishes, and
//!    `final_eh`. Callbacks may call `Z3_solver_propagate_consequence`, which
//!    RECORDS (justification ⇒ consequence) lemmas on the callback object.
//! 3. If the round recorded no lemmas and registered no new terms, the model
//!    passed the user theory → SAT. Otherwise every recorded lemma is asserted
//!    (as the guarded implication over its justification literals) and the loop
//!    re-solves. Rounds are bounded; exhaustion → `unknown` (sound).
//!
//! **SOUNDNESS ARGUMENT** (matching Z3's user-propagator contract):
//!   * SAT is only returned when a full notification round (`push` → `fixed`* →
//!     `eq`/`diseq`* → `final`) completed with ZERO recorded consequences and
//!     zero new registrations — i.e. the user's final check raised no objection
//!     to the candidate model, exactly Z3's acceptance condition.
//!   * UNSAT only ever comes from the engine, with the user's consequence
//!     lemmas added as constraints. Each lemma is the user-provided axiom
//!     `(∧ justification) ⇒ consequence` — Z3 trusts propagator lemmas
//!     identically (they are the consumer's theory, by contract true).
//!   * Every inconclusive path (round cap, un-evaluable registered term,
//!     ineffective lemmas) returns `unknown` + `Z3_EXCEPTION` — never a guess.
//!
//! Remaining HONEST DIVERGENCES on this surface (all heuristic/observer-only,
//! so ignoring them cannot change any verdict):
//!   * `decide_eh` / `Z3_solver_next_split` — in-search branching hints; AY
//!     keeps its own decision heuristic (sound: hints never change semantics).
//!   * `on_binding_eh` — quantifier-instantiation observer; never fired (not
//!     firing never *blocks* an instantiation, and instantiations are sound).
//!   * `fresh_eh` — AY never spawns nested propagator solvers; never fired.
//!   * `Z3_solver_register_on_clause` — AY exposes no live learned-clause event
//!     stream; observer-only no-op (suppressing notifications never changes
//!     SAT/UNSAT or any model).
//!
//! The genuinely-real members of this surface — `Z3_solver_propagate_declare`
//! (declares an ordinary uninterpreted function symbol),
//! `Z3_solver_get_param_descrs` (a real queryable parameter list),
//! `Z3_solver_get_levels` (the level-0 unit trail), `Z3_solver_cube` (real
//! lookahead cubes over the Tseitin skeleton), and `Z3_solver_solve_for` (the
//! direct top-level solved forms) — are implemented over real engine state.
//! The remaining solver-extras (`congruence_explain` — exact under its
//! precondition, `next_split`, `set_initial_value`, `import_model_converter`)
//! diverge honestly where AY has no backing, always with a SOUND sentinel and
//! never a fabricated term.
//!
//! All entry points are wrapped in `catch_unwind` via the `ffi_guard_*` helpers
//! (#6192) to prevent undefined behavior from panics unwinding across the
//! `extern "C"` boundary. During user-callback invocation NO `&mut Z3Context`
//! borrow is live, so callbacks may freely re-enter the C API (build terms,
//! record consequences) on the same context, exactly like Z3.

use std::collections::{HashMap, HashSet};
use std::ffi::{c_int, c_uint, c_void};
use std::ptr;

use ay_dpll::api::{Sort, Term, TermKind};

use super::model_params::Z3_model_eval;
use super::solver::{check_solver_handle, is_unit_literal, DimacsEncoder, Z3_solver_get_model};
use super::{
    cache_ast_vector, cache_func_decl_with_symbol, ffi_count_within_limit, ffi_counts_within_limit,
    ffi_guard_ast, ffi_guard_int, ffi_guard_ptr, ffi_guard_void, ffi_try_declare_function,
    record_ast_sort, require_term_ast, require_term_ast_or_return, term_to_ast, ParamDescr,
    ParamDescrsHandle, SymbolKey, Z3Context, Z3_ast, Z3_ast_vector, Z3_context, Z3_func_decl,
    Z3_param_descrs, Z3_solver, Z3_sort, Z3_symbol, Z3_EXCEPTION, Z3_INVALID_ARG, Z3_INVALID_USAGE,
    Z3_L_TRUE, Z3_L_UNDEF, Z3_OK, Z3_PK_UINT, Z3_SORT_ERROR,
};

// ============================================================================
// User-propagator callback typedefs (C ABI).
//
// These mirror the `Z3_DECLARE_CLOSURE` typedefs in `z3_api.h` (lines 1433-1442).
// Each is an `Option<extern "C" fn(...)>` so that a C `NULL` callback maps to
// `None` (Z3's own "unregister" convention).
//
// `Z3_ast` is AY's `u64` handle, ABI-identical to C's `Z3_ast` pointer on
// 64-bit targets (both are 8-byte integer-class values); every other extern "C"
// entry point in this crate uses the same representation.
// ============================================================================

/// User-propagator callback context (Z3's `Z3_solver_callback`).
///
/// One is constructed per final-check notification round (and per
/// registration-time `created` firing) by [`user_propagator_check`] /
/// [`register_terms_and_fire_created`]; it lives on that caller's stack for
/// exactly the duration of the user callbacks. In-callback entry points
/// (`Z3_solver_propagate_consequence`, `Z3_solver_propagate_register_cb`,
/// `Z3_solver_next_split`) RECORD onto this object; the loop converts the
/// records into asserted lemmas / new registrations after the callbacks return.
pub struct SolverCallbackObj {
    /// This round's model values for registered terms: term AST → ground value
    /// AST. Consulted by `Z3_solver_propagate_consequence` to validate `fixed`
    /// justifications (a term with no recorded fixed value cannot justify a
    /// consequence and the call is honestly refused with `false`).
    values: HashMap<Z3_ast, Z3_ast>,
    /// Consequence lemmas recorded by the user callbacks this round.
    consequences: Vec<RecordedConsequence>,
    /// Terms newly registered via `Z3_solver_propagate_register_cb`.
    new_registrations: Vec<Z3_ast>,
}

/// One `Z3_solver_propagate_consequence` record: the lemma
/// `(∧_i fixed_i = value(fixed_i)) ∧ (∧_j eq_lhs_j = eq_rhs_j) ⇒ conseq`.
struct RecordedConsequence {
    /// Justification terms fixed to this round's model values (each is a key of
    /// [`SolverCallbackObj::values`], validated at record time).
    fixed: Vec<Z3_ast>,
    /// Justification equalities `(lhs, rhs)`.
    eqs: Vec<(Z3_ast, Z3_ast)>,
    /// The propagated consequence (a Boolean term; `false` for a conflict).
    conseq: Z3_ast,
}

/// `Z3_solver_callback`: handle passed to in-callback propagator APIs.
pub type Z3_solver_callback = *mut SolverCallbackObj;

/// `Z3_push_eh`: invoked when the solver pushes a scope.
pub type Z3_push_eh = Option<unsafe extern "C" fn(*mut c_void, Z3_solver_callback)>;

/// `Z3_pop_eh`: invoked when the solver pops `num_scopes` scopes.
pub type Z3_pop_eh = Option<unsafe extern "C" fn(*mut c_void, Z3_solver_callback, c_uint)>;

/// `Z3_fresh_eh`: produces a fresh `user_context` for an internally-spawned solver.
pub type Z3_fresh_eh = Option<unsafe extern "C" fn(*mut c_void, Z3_context) -> *mut c_void>;

/// `Z3_fixed_eh`: invoked when a registered expression is fixed to a value `(t := value)`.
pub type Z3_fixed_eh =
    Option<unsafe extern "C" fn(*mut c_void, Z3_solver_callback, Z3_ast, Z3_ast)>;

/// `Z3_eq_eh`: invoked on an expression equality (also used for dis-equality) `(s = t)`.
pub type Z3_eq_eh = Option<unsafe extern "C" fn(*mut c_void, Z3_solver_callback, Z3_ast, Z3_ast)>;

/// `Z3_final_eh`: invoked on final check (all decision variables assigned).
pub type Z3_final_eh = Option<unsafe extern "C" fn(*mut c_void, Z3_solver_callback)>;

/// `Z3_created_eh`: invoked when a term over a propagator-declared function is created.
pub type Z3_created_eh = Option<unsafe extern "C" fn(*mut c_void, Z3_solver_callback, Z3_ast)>;

/// `Z3_decide_eh`: invoked when the solver decides to split on a registered expression.
pub type Z3_decide_eh =
    Option<unsafe extern "C" fn(*mut c_void, Z3_solver_callback, Z3_ast, c_uint, bool)>;

/// `Z3_on_binding_eh`: invoked on a quantifier-instantiation binding `(q, inst)`.
/// Returns `false` to block the instantiation.
pub type Z3_on_binding_eh =
    Option<unsafe extern "C" fn(*mut c_void, Z3_solver_callback, Z3_ast, Z3_ast) -> bool>;

/// `Z3_on_clause_eh`: invoked on asserted/inferred/deleted clauses (proof logging).
pub type Z3_on_clause_eh =
    Option<unsafe extern "C" fn(*mut c_void, Z3_ast, c_uint, *const c_uint, Z3_ast_vector)>;

// ============================================================================
// User-propagator state (stored on the solver handle) + the final-check loop.
// ============================================================================

/// A user propagator registered on a `Z3_solver` handle: the callbacks from
/// `Z3_solver_propagate_init`/`_fixed`/`_eq`/`_diseq`/`_final`/`_created`/
/// `_decide`/`_on_binding`, the registered watch terms, and any consequence
/// lemmas recorded at registration time (from `created_eh` firings).
pub(crate) struct UserPropagator {
    /// Monotonic configuration/watch-set generation. A final-check callback is
    /// allowed to re-enter the API; SAT may only be admitted if the propagator
    /// that inspected the candidate is still exactly the active generation.
    pub(crate) revision: u64,
    /// The consumer's opaque state, passed as the first argument of every
    /// callback.
    pub(crate) user_context: *mut c_void,
    pub(crate) push_eh: Z3_push_eh,
    pub(crate) pop_eh: Z3_pop_eh,
    /// Stored but never fired: AY never spawns nested propagator solvers
    /// (documented divergence; retained so the registration round-trips).
    #[allow(dead_code)]
    pub(crate) fresh_eh: Z3_fresh_eh,
    pub(crate) fixed_eh: Z3_fixed_eh,
    pub(crate) eq_eh: Z3_eq_eh,
    pub(crate) diseq_eh: Z3_eq_eh,
    pub(crate) final_eh: Z3_final_eh,
    pub(crate) created_eh: Z3_created_eh,
    /// Stored but never fired: AY exposes no in-search decision events. A
    /// decide hook is a heuristic override; not consulting it cannot change any
    /// verdict (sound).
    pub(crate) decide_eh: Z3_decide_eh,
    /// Stored but never fired: AY exposes no quantifier-instantiation binding
    /// event stream. Not firing never *blocks* an instantiation, and every
    /// instantiation is a sound instance of an asserted quantifier.
    pub(crate) on_binding_eh: Z3_on_binding_eh,
    /// Terms registered for notification (`Z3_solver_propagate_register`/
    /// `_register_cb`), deduplicated.
    pub(crate) registered: Vec<Term>,
    /// User lemmas recorded outside a final-check round (consequences pushed
    /// from a registration-time `created_eh`). Converted into asserted lemma
    /// terms at the start of every propagator check.
    pub(crate) pending: Vec<PendingLemma>,
}

/// An eq-justified (or unconditional) user lemma recorded outside a
/// final-check round, kept as raw AST handles until a check converts it.
pub(crate) struct PendingLemma {
    pub(crate) eqs: Vec<(Z3_ast, Z3_ast)>,
    pub(crate) conseq: Z3_ast,
}

/// Round bound for the final-check loop; exhaustion → `unknown` (sound).
const MAX_FINAL_CHECK_ROUNDS: usize = 10_000;

/// Registered-term bound for the O(n²) best-effort `eq_eh`/`diseq_eh` pair
/// notifications (beyond it the pair scan is skipped; `fixed`/`final` still
/// fire, and Z3's own contract makes `final_eh` the only completeness point).
const MAX_EQ_PAIR_TERMS: usize = 512;

/// Record an error + `unknown` verdict on the context (used by the loop's
/// inconclusive paths — never a fabricated verdict).
///
/// # Safety
/// `c` must be a valid context pointer (or null); no other `&mut Z3Context`
/// may be live (the loop only calls this between guarded sections).
unsafe fn propagator_unknown(c: Z3_context, s: Z3_solver, msg: &str) -> c_int {
    let msg = msg.to_string();
    // SAFETY: `ffi_guard_int` null-checks `c` and catches panics; per the
    // caller contract no other context borrow is live.
    unsafe {
        ffi_guard_int(c, Z3_L_UNDEF, move |ctx| {
            ctx.last_error = Z3_EXCEPTION;
            ctx.error_msg = Some(msg.clone());
            // A rejected candidate is not a model. Revoke every
            // outcome-dependent snapshot through the same authority used by
            // ordinary solver checks, including all fail-closed exits below.
            // SAFETY: `s`, when non-null, is an arena-owned solver handle in a
            // disjoint allocation from `ctx`.
            if let Some(handle) = s.as_mut() {
                handle.last_reason_unknown = Some(msg);
                handle.record_check_outcome(super::SolverCheckOutcome::Unknown);
            }
            Z3_L_UNDEF
        })
    }
}

/// The SOUND FINAL-CHECK LOOP: `Z3_solver_check`/`_check_assumptions` dispatch
/// here when the handle carries a registered [`UserPropagator`]. See the module
/// docs for the architecture and the soundness argument.
///
/// # Safety
/// `c` must be a valid, non-aliased context pointer with NO outstanding
/// `&mut Z3Context` borrow (this function creates its own scoped borrows and
/// releases them before invoking any user callback); `s`, when non-null, must
/// be a live solver handle owned by `c`'s arena. User callbacks must honor the
/// Z3 callback contract (no concurrent use of the context, callback object not
/// retained past the callback).
pub(crate) unsafe fn user_propagator_check(
    c: Z3_context,
    s: Z3_solver,
    assumptions: Option<&[Term]>,
) -> c_int {
    // Accumulated user lemmas (theory axioms) asserted at every (re-)solve.
    let mut lemmas: Vec<Term> = Vec::new();
    let mut lemma_set: HashSet<Term> = HashSet::new();

    // Convert registration-time pending lemmas (from `created_eh` firings)
    // before the first solve — they are user axioms and must constrain it.
    {
        let pending: Vec<PendingLemma> = match unsafe { s.as_mut() } {
            Some(handle) => match handle.propagator.as_mut() {
                Some(prop) => std::mem::take(&mut prop.pending),
                None => Vec::new(),
            },
            None => Vec::new(),
        };
        if !pending.is_empty() {
            let ok = unsafe {
                // SAFETY: scoped context borrow; no user callback is running.
                ffi_guard_int(c, 0, |ctx| {
                    for p in &pending {
                        let Some(lemma) = build_lemma(ctx, &HashMap::new(), &[], &p.eqs, p.conseq)
                        else {
                            return 0;
                        };
                        if lemma_set.insert(lemma) {
                            lemmas.push(lemma);
                        }
                    }
                    1
                })
            };
            if ok == 0 {
                return unsafe {
                    propagator_unknown(
                        c,
                        s,
                        "user propagator: a registration-time consequence lemma could not be \
                         converted — fail-closed",
                    )
                };
            }
        }
    }

    for _round in 0..MAX_FINAL_CHECK_ROUNDS {
        // (1) Solve the handle's goal plus the accumulated user lemmas.
        //     UNSAT/UNKNOWN pass straight through: UNSAT is the engine's verdict
        //     on goal ∧ user-axioms; UNKNOWN stays honest.
        // SAFETY: scoped context borrow; released before callbacks run.
        let verdict = unsafe {
            ffi_guard_int(c, Z3_L_UNDEF, |ctx| {
                check_solver_handle(ctx, s, assumptions, &lemmas)
            })
        };
        if verdict != Z3_L_TRUE {
            return verdict;
        }

        // (2) Snapshot the propagator (callbacks are Copy fn pointers; the
        //     registered list is cloned so callbacks can register more).
        // SAFETY: `s` is a live handle (checked by the solve above); the
        // reference is scoped to this block, no context borrow involved.
        let Some(handle) = (unsafe { s.as_mut() }) else {
            return Z3_L_UNDEF;
        };
        let Some(prop) = handle.propagator.as_ref() else {
            // Propagator was somehow removed mid-loop: the SAT verdict from (1)
            // is an ordinary engine verdict, valid as-is.
            return verdict;
        };
        let user_ctx = prop.user_context;
        let (push_eh, pop_eh, fixed_eh, eq_eh, diseq_eh, final_eh) = (
            prop.push_eh,
            prop.pop_eh,
            prop.fixed_eh,
            prop.eq_eh,
            prop.diseq_eh,
            prop.final_eh,
        );
        let registered: Vec<Term> = prop.registered.clone();
        let inspected_revision = prop.revision;

        // (3) Extract this candidate model's value for every registered term
        //     via the public C API (no borrow is held across these calls).
        // SAFETY: no outstanding context borrow; `Z3_solver_get_model` and
        // `Z3_model_eval` take their own scoped borrows.
        let model = unsafe { Z3_solver_get_model(c, s) };
        if model.is_null() {
            return unsafe {
                propagator_unknown(
                    c,
                    s,
                    "user propagator: SAT verdict produced no model — fail-closed",
                )
            };
        }
        // Convert registered terms to ASTs under a SCOPED context borrow,
        // released before the raw model-eval calls below (the surrounding
        // section's no-outstanding-borrow invariant).
        let term_asts: Vec<(Term, Z3_ast)> = {
            // SAFETY: same invariant as ffi_guard_*: `c` is a live context
            // pointer and no other borrow is outstanding in this block.
            let Some(ctx) = (unsafe { c.as_mut() }) else {
                return unsafe {
                    propagator_unknown(
                        c,
                        s,
                        "user propagator: context unavailable for term \
                         conversion — fail-closed",
                    )
                };
            };
            registered
                .iter()
                .map(|&t| (t, term_to_ast(ctx, t)))
                .collect()
        };
        let mut raw_values: Vec<(Term, Z3_ast, Z3_ast)> = Vec::with_capacity(registered.len());
        for &(t, t_ast) in &term_asts {
            let mut v: Z3_ast = 0;
            // SAFETY: no outstanding context borrow; `model` is a live handle
            // from this context's arena; `&mut v` is a valid out-slot.
            let ok = unsafe { Z3_model_eval(c, model, t_ast, true, &raw mut v) };
            if !ok || v == 0 {
                return unsafe {
                    propagator_unknown(
                        c,
                        s,
                        "user propagator: a registered term could not be evaluated in the \
                         candidate model — cannot run the user theory faithfully, fail-closed",
                    )
                };
            }
            raw_values.push((t, t_ast, v));
        }

        // (4) Classify values (ground numeral/Bool → eligible for `fixed_eh`
        //     and exact pair notifications) and collect sorts, in one guard.
        let mut entries: Vec<(Z3_ast, Z3_ast, bool, Sort)> = Vec::with_capacity(raw_values.len());
        // SAFETY: scoped context borrow; released before callbacks run.
        let classified = unsafe {
            ffi_guard_int(c, 0, |ctx| {
                for &(t, t_ast, v_ast) in &raw_values {
                    let v_term = require_term_ast_or_return!(
                        ctx,
                        v_ast,
                        "user propagator model-value classification",
                        "model value",
                        0
                    );
                    let is_value =
                        ctx.solver.is_numeral(v_term) || ctx.solver.bool_value(v_term).is_some();
                    let sort = ctx.solver.term_sort(t);
                    entries.push((t_ast, v_ast, is_value, sort));
                }
                1
            })
        };
        if classified == 0 {
            return unsafe {
                propagator_unknown(
                    c,
                    s,
                    "user propagator: model-value classification failed — fail-closed",
                )
            };
        }

        // (5) Run the notification round. NO context borrow is live from here
        //     until the callbacks return, so user code may freely re-enter the
        //     C API (build terms, record consequences) — exactly like Z3.
        let mut cb = SolverCallbackObj {
            values: entries
                .iter()
                .filter(|(_, _, is_value, _)| *is_value)
                .map(|&(t_ast, v_ast, _, _)| (t_ast, v_ast))
                .collect(),
            consequences: Vec::new(),
            new_registrations: Vec::new(),
        };
        let cbp: Z3_solver_callback = &raw mut cb;
        // SAFETY (all callback invocations below): the fn pointers were
        // supplied through `Z3_solver_propagate_*` whose contracts require
        // valid `extern "C"` functions; `cbp` points to a live stack object
        // that outlives the round; no `&mut Z3Context` is outstanding.
        unsafe {
            if let Some(push) = push_eh {
                push(user_ctx, cbp);
            }
            for &(t_ast, v_ast, is_value, _) in &entries {
                if is_value {
                    if let Some(fixed) = fixed_eh {
                        fixed(user_ctx, cbp, t_ast, v_ast);
                    }
                }
            }
            // Best-effort eq/diseq: same-sort registered pairs whose GROUND
            // values coincide/differ (value-term identity is exact for interned
            // numeral/Bool literals). Z3's completeness point is `final_eh`;
            // these notifications are a best-effort superset/subset of Z3's
            // e-graph events either way (documented divergence).
            if (eq_eh.is_some() || diseq_eh.is_some()) && entries.len() <= MAX_EQ_PAIR_TERMS {
                for i in 0..entries.len() {
                    for j in (i + 1)..entries.len() {
                        let (a_ast, a_val, a_isv, ref a_sort) = entries[i];
                        let (b_ast, b_val, b_isv, ref b_sort) = entries[j];
                        if !(a_isv && b_isv) || a_sort != b_sort {
                            continue;
                        }
                        if a_val == b_val {
                            if let Some(eq) = eq_eh {
                                eq(user_ctx, cbp, a_ast, b_ast);
                            }
                        } else if let Some(diseq) = diseq_eh {
                            diseq(user_ctx, cbp, a_ast, b_ast);
                        }
                    }
                }
            }
            if let Some(fin) = final_eh {
                fin(user_ctx, cbp);
            }
            if let Some(pop) = pop_eh {
                pop(user_ctx, cbp, 1);
            }
        }
        let SolverCallbackObj {
            values,
            consequences,
            new_registrations,
        } = cb;

        // (6) Acceptance: no objection and nothing new to watch → the model
        //     passed the user theory. The artefacts (model/stats) materialized
        //     by the accepting solve in (1) are exactly this model's.
        let new_regs: Vec<Z3_ast> = new_registrations.into_iter().filter(|&e| e != 0).collect();
        let candidate_still_authoritative = unsafe { s.as_ref() }.is_some_and(|handle| {
            handle.last_check_outcome == Some(super::SolverCheckOutcome::Sat)
                && handle.last_model.is_some()
                && handle
                    .propagator
                    .as_ref()
                    .is_some_and(|prop| prop.revision == inspected_revision)
        });
        if consequences.is_empty() && new_regs.is_empty() && candidate_still_authoritative {
            return Z3_L_TRUE;
        }

        // Merge new registrations (fires `created_eh` per genuinely-new term,
        // consistent with registration-time creation announcements).
        let mut progress = false;
        if !new_regs.is_empty() {
            // SAFETY: no outstanding context borrow; see the helper's contract.
            progress = unsafe { register_terms_and_fire_created(c, s, new_regs) };
        }

        // (7) Convert the recorded consequences into asserted lemma terms.
        // SAFETY: scoped context borrow; the callbacks have returned.
        let converted = unsafe {
            ffi_guard_int(c, 0, |ctx| {
                for rc in &consequences {
                    let Some(lemma) = build_lemma(ctx, &values, &rc.fixed, &rc.eqs, rc.conseq)
                    else {
                        return 0;
                    };
                    if lemma_set.insert(lemma) {
                        lemmas.push(lemma);
                        progress = true;
                    }
                }
                1
            })
        };
        if converted == 0 {
            return unsafe {
                propagator_unknown(
                    c,
                    s,
                    "user propagator: a consequence lemma could not be converted — fail-closed",
                )
            };
        }
        // Re-check any pending lemmas a created_eh just recorded.
        let pending: Vec<PendingLemma> = match unsafe { s.as_mut() } {
            Some(handle) => match handle.propagator.as_mut() {
                Some(prop) => std::mem::take(&mut prop.pending),
                None => Vec::new(),
            },
            None => Vec::new(),
        };
        if !pending.is_empty() {
            // SAFETY: scoped context borrow; no callback running.
            let ok = unsafe {
                ffi_guard_int(c, 0, |ctx| {
                    for p in &pending {
                        let Some(lemma) = build_lemma(ctx, &HashMap::new(), &[], &p.eqs, p.conseq)
                        else {
                            return 0;
                        };
                        if lemma_set.insert(lemma) {
                            lemmas.push(lemma);
                            progress = true;
                        }
                    }
                    1
                })
            };
            if ok == 0 {
                return unsafe {
                    propagator_unknown(
                        c,
                        s,
                        "user propagator: a created-time consequence lemma could not be \
                         converted — fail-closed",
                    )
                };
            }
        }
        // Reentrant assertion/configuration/watch-set changes invalidate the
        // inspected candidate. They are genuine progress even when the user
        // emitted no new lemma, and must be solved before SAT can be admitted.
        if !candidate_still_authoritative {
            continue;
        }
        // The user objected, but every recorded lemma was already asserted and
        // the candidate model still satisfied them: re-solving would loop on
        // the identical state. Honest `unknown`, never a forced verdict.
        if !progress {
            return unsafe {
                propagator_unknown(
                    c,
                    s,
                    "user propagator objected in final check, but its consequence lemmas do \
                     not exclude the candidate model — inconclusive, fail-closed",
                )
            };
        }
    }
    unsafe {
        propagator_unknown(
            c,
            s,
            "user propagator: final-check round bound (10000) exhausted — inconclusive, \
             fail-closed",
        )
    }
}

/// Build the lemma term `(∧ fixed_i = value_i ∧ eq_j) ⇒ conseq` from a recorded
/// consequence. `None` when a `fixed` justification has no recorded value this
/// round (cannot be represented faithfully — the caller fails closed).
fn build_lemma(
    ctx: &mut Z3Context,
    values: &HashMap<Z3_ast, Z3_ast>,
    fixed: &[Z3_ast],
    eqs: &[(Z3_ast, Z3_ast)],
    conseq: Z3_ast,
) -> Option<Term> {
    // Authenticate every caller-originating handle before interning any lemma
    // nodes, keeping failure atomic even when a later justification is invalid.
    let mut fixed_terms: Vec<(Term, Term)> = Vec::with_capacity(fixed.len());
    for &f in fixed {
        let &v = values.get(&f)?;
        let f_term = require_term_ast(ctx, f, "user propagator consequence", "fixed term")?;
        let v_term = require_term_ast(ctx, v, "user propagator consequence", "fixed value")?;
        fixed_terms.push((f_term, v_term));
    }
    let mut equality_terms: Vec<(Term, Term)> = Vec::with_capacity(eqs.len());
    for &(l, r) in eqs {
        let l_term = require_term_ast(ctx, l, "user propagator consequence", "equality lhs")?;
        let r_term = require_term_ast(ctx, r, "user propagator consequence", "equality rhs")?;
        equality_terms.push((l_term, r_term));
    }
    let conseq_term = require_term_ast(ctx, conseq, "user propagator consequence", "consequence")?;
    let mut just: Vec<Term> = Vec::with_capacity(fixed.len() + eqs.len());
    just.extend(
        fixed_terms
            .into_iter()
            .map(|(fixed_term, value_term)| ctx.solver.eq(fixed_term, value_term)),
    );
    just.extend(
        equality_terms
            .into_iter()
            .map(|(lhs, rhs)| ctx.solver.eq(lhs, rhs)),
    );
    Some(if just.is_empty() {
        conseq_term
    } else {
        let conj = ctx.solver.and_many(&just);
        ctx.solver.implies(conj, conseq_term)
    })
}

/// Register `queue`'s terms on the handle's propagator (dedup) and fire
/// `created_eh` once per genuinely-new term ("registered-term creation at
/// registration time"). Consequences a `created_eh` records are stashed as
/// [`PendingLemma`]s (converted at the next check); recursive `register_cb`
/// calls are processed through the same worklist (bounded).
///
/// # Safety
/// `c` must be a valid context pointer with NO outstanding `&mut Z3Context`
/// borrow; `s`, when non-null, a live solver handle. Callback contract as in
/// [`user_propagator_check`].
unsafe fn register_terms_and_fire_created(c: Z3_context, s: Z3_solver, queue: Vec<Z3_ast>) -> bool {
    let mut queue = queue;
    let mut changed = false;
    // Defensive bound on recursive registration cascades.
    let mut budget: usize = 65_536;
    while let Some(ast) = queue.pop() {
        if ast == 0 || budget == 0 {
            break;
        }
        budget -= 1;
        // SAFETY: `s` null-checked by `as_mut`; scoped handle borrow (the
        // handle is its own allocation — no `Z3Context` borrow involved).
        let Some(handle) = (unsafe { s.as_mut() }) else {
            return changed;
        };
        let Some(prop) = handle.propagator.as_mut() else {
            return changed;
        };
        let term = {
            // SAFETY: callers guarantee `c` is live and no context borrow is
            // outstanding. This borrow ends before `created_eh` can re-enter.
            let Some(ctx) = (unsafe { c.as_mut() }) else {
                return changed;
            };
            let Some(term) =
                require_term_ast(ctx, ast, "Z3_solver_propagate_register", "registered term")
            else {
                return changed;
            };
            term
        };
        if prop.registered.contains(&term) {
            continue;
        }
        prop.registered.push(term);
        prop.revision = prop.revision.wrapping_add(1);
        changed = true;
        let created_eh = prop.created_eh;
        let user_ctx = prop.user_context;
        let _ = prop;
        handle.clear_check_artifacts();
        if let Some(created) = created_eh {
            let mut cb = SolverCallbackObj {
                values: HashMap::new(),
                consequences: Vec::new(),
                new_registrations: Vec::new(),
            };
            let cbp: Z3_solver_callback = &raw mut cb;
            // End the handle borrow (`prop`/`handle`) before the callback runs:
            // the callback may re-enter registration APIs that re-borrow `s`.
            // SAFETY: `created` is a valid extern "C" fn per the registration
            // contract; `cbp` points to a live stack object that outlives the
            // call; no `&mut Z3Context` and no handle borrow is outstanding.
            unsafe { created(user_ctx, cbp, ast) };
            let SolverCallbackObj {
                consequences,
                new_registrations,
                ..
            } = cb;
            // SAFETY: fresh scoped handle borrow (previous one released).
            if let Some(handle) = unsafe { s.as_mut() } {
                if let Some(prop) = handle.propagator.as_mut() {
                    prop.pending
                        .extend(consequences.into_iter().map(|rc| PendingLemma {
                            eqs: rc.eqs,
                            conseq: rc.conseq,
                        }));
                }
            }
            queue.extend(new_registrations.into_iter().filter(|&e| e != 0));
        }
    }
    changed
}

// ============================================================================
// REAL implementations (backed by engine state).
// ============================================================================

/// Return the parameter-descriptor set the solver recognizes (Z3's
/// `Z3_solver_get_param_descrs`).
///
/// A REAL, queryable list (name + `Z3_param_kind` + documentation) of the
/// parameters AY's solver actually honors — see `apply_supported_params` in
/// `mod.rs`, which consumes `timeout` and `proof`/`produce_proofs`. Never a fake
/// full-z3 set disguised as real. Mirrors `Z3_optimize_get_param_descrs`.
///
/// # Safety
/// `c` must be a valid context pointer; `s` a valid solver handle.
#[no_mangle]
pub unsafe extern "C" fn Z3_solver_get_param_descrs(
    c: Z3_context,
    s: Z3_solver,
) -> Z3_param_descrs {
    // SAFETY: `ffi_guard_ptr` handles null `c` and catches panics.
    unsafe {
        ffi_guard_ptr(c, |ctx| {
            if s.is_null() {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg = Some("null Z3_solver handle in get_param_descrs".to_string());
            }
            let entries = vec![
                ParamDescr {
                    name: "timeout".to_string(),
                    kind: Z3_PK_UINT,
                    doc: "check-sat timeout in milliseconds (0 = no limit)".to_string(),
                },
                ParamDescr {
                    name: "produce_proofs".to_string(),
                    kind: super::Z3_PK_BOOL,
                    doc: "enable proof production for the solve (default: false)".to_string(),
                },
            ];
            let handle = Box::into_raw(Box::new(ParamDescrsHandle { entries }));
            ctx.param_descrs_cache.push(handle);
            handle
        })
    }
}

/// Declare an uninterpreted function symbol usable in propagator terms (Z3's
/// `Z3_solver_propagate_declare`).
///
/// Despite the `propagate` name, this is NOT a divergence: it simply declares a
/// plugin/uninterpreted function exactly like `Z3_mk_func_decl`. AY's engine
/// treats the resulting symbol as an ordinary uninterpreted function — fully
/// sound. (The propagator-specific `created` callback that would fire on terms
/// over this symbol is what diverges; see `Z3_solver_propagate_created`.)
///
/// # Safety
/// All pointers must be valid; `domain` must point to `n` `Z3_sort` elements.
#[no_mangle]
pub unsafe extern "C" fn Z3_solver_propagate_declare(
    c: Z3_context,
    name: Z3_symbol,
    n: c_uint,
    domain: *const Z3_sort,
    range: Z3_sort,
) -> Z3_func_decl {
    // SAFETY: this public entry point requires `c` to be null or a live,
    // exclusively borrowed context; the bound checker only updates its error state.
    if !unsafe { ffi_count_within_limit(c, "Z3_solver_propagate_declare domain", n) } {
        return ptr::null_mut();
    }
    if name.is_null() || range.is_null() {
        return ptr::null_mut();
    }
    if n > 0 && domain.is_null() {
        return ptr::null_mut();
    }

    // Pre-extract data from raw pointers before entering the guard, mirroring
    // `Z3_mk_func_decl` (terms.rs).
    // SAFETY: `name` was null-checked above and originates from a prior AY FFI
    // allocation kept alive by the owning `Z3Context`. Reading `.key` is a
    // shared-read with no concurrent mutation (the Z3 C API is single-threaded
    // per context).
    let symbol = unsafe { (*name).key.clone() };
    let display_name = symbol.display_name();
    let mut dom_sorts: Vec<Sort> = Vec::with_capacity(n as usize);
    for i in 0..n as usize {
        // SAFETY: the caller's contract guarantees `domain` points to at least
        // `n` elements; the count was range-checked and null-checked above, so
        // `domain.add(i)` stays within the caller's allocation.
        let sort_ptr = unsafe { *domain.add(i) };
        if sort_ptr.is_null() {
            return ptr::null_mut();
        }
        // SAFETY: `sort_ptr` was null-checked above and is a live AY sort handle
        // owned by the context; reading `.sort` is a shared-read.
        dom_sorts.push(unsafe { (*sort_ptr).sort.clone() });
    }
    // SAFETY: `range` was null-checked above and is a live AY sort handle owned
    // by the context; reading `.sort` is a shared-read.
    let range_sort = unsafe { (*range).sort.clone() };

    // SAFETY: `ffi_guard_ptr` handles null `c` and catches panics.
    unsafe {
        ffi_guard_ptr(c, |ctx| {
            if matches!(&symbol, SymbolKey::String(_)) {
                if let Some(msg) = super::reserved_name_error(&display_name) {
                    ctx.last_error = Z3_INVALID_ARG;
                    ctx.error_msg = Some(msg);
                    return ptr::null_mut();
                }
            }
            match ffi_try_declare_function(ctx, &symbol, &dom_sorts, &range_sort) {
                Ok(decl) => {
                    ctx.ffi_used_decl_names.insert(display_name.clone());
                    cache_func_decl_with_symbol(ctx, decl, symbol.clone())
                }
                Err(e) => {
                    ctx.last_error = Z3_SORT_ERROR;
                    ctx.error_msg = Some(format!("{e}"));
                    ptr::null_mut()
                }
            }
        })
    }
}

// ============================================================================
// Honest divergences with SOUND sentinels (real engine lacks the backing).
// ============================================================================

/// Provide an initial decision-phase / value HINT for a variable (Z3's
/// `Z3_solver_set_initial_value`). HONEST NO-OP.
///
/// `(v := val)` is only a search-order hint: it biases the initial phase/value
/// but can NEVER change the reported SAT/UNSAT verdict, so ignoring it is fully
/// SOUND (the same result is still found). Direct precedent:
/// `Z3_optimize_set_initial_value` is already an honest no-op. Documented rather
/// than faked; no fabricated engine state.
///
/// # Safety
/// Pointers must be valid; arguments are otherwise unused.
#[no_mangle]
pub unsafe extern "C" fn Z3_solver_set_initial_value(
    _c: Z3_context,
    _s: Z3_solver,
    _v: Z3_ast,
    _val: Z3_ast,
) {
}

/// Import `src`'s model converter into `dst` (Z3's
/// `Z3_solver_import_model_converter`). HONEST NO-OP.
///
/// DIVERGENCE: AY solvers carry no detachable model-converter object. Models are
/// reconstructed internally by the tactic pipeline in `Z3SolverHandle`; there is
/// no standalone converter to copy from `src` into `dst`. This is SOUND: with no
/// separate converter, its omission cannot corrupt `dst`'s future models — `dst`
/// continues to build its own models correctly. Null-checks `src`/`dst`.
///
/// # Safety
/// `c` must be a valid context pointer; `src`/`dst` valid solver handles.
#[no_mangle]
pub unsafe extern "C" fn Z3_solver_import_model_converter(
    c: Z3_context,
    src: Z3_solver,
    dst: Z3_solver,
) {
    // SAFETY: `ffi_guard_void` handles null `c` and catches panics.
    unsafe {
        ffi_guard_void(c, |ctx| {
            if src.is_null() || dst.is_null() {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg = Some("null Z3_solver handle in import_model_converter".to_string());
            }
            // No-op: AY exposes no detachable model converter to import.
        })
    }
}

/// Retrieve an explanation term for the congruence of `a` and `b` (Z3's
/// `Z3_solver_congruence_explain`; `\pre root(a) = root(b)`).
///
/// DIVERGENCE: AY exposes no e-graph congruence-derivation ring, consistent with
/// the honest singleton congruence model already used by
/// `Z3_solver_congruence_root`/`_next` (each term is its own singleton class).
/// SOUND sentinel:
///   * if `a == b` syntactically, the congruence holds with the EMPTY
///     explanation → return `mk_true`;
///   * otherwise `a` and `b` are not congruent in AY's singleton model → set
///     `Z3_INVALID_ARG` and return null.
/// Never a fabricated equality chain.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_solver_congruence_explain(
    c: Z3_context,
    _s: Z3_solver,
    a: Z3_ast,
    b: Z3_ast,
) -> Z3_ast {
    // SAFETY: `ffi_guard_ast` guards `c`.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            if a == 0 || b == 0 {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg = Some("Z3_solver_congruence_explain: null AST".to_string());
                return 0;
            }
            if a == b {
                // Congruent with the empty explanation.
                let t = ctx.solver.bool_const(true);
                let ast = term_to_ast(ctx, t);
                record_ast_sort(ctx, ast, Sort::Bool);
                ast
            } else {
                // Distinct terms are in distinct singleton classes: AY cannot
                // (and must not) fabricate a congruence explanation.
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg = Some(
                    "Z3_solver_congruence_explain: AY models singleton congruence classes; \
                     no explanation exists for distinct terms"
                        .to_string(),
                );
                0
            }
        })
    }
}

/// Lookahead split depth for `Z3_solver_cube`: up to `2^depth` cubes per
/// generation round. Small and fixed — cubes are a work-splitting hint, and
/// every returned set is a sound COVER of the search space regardless of depth.
const CUBE_LOOKAHEAD_DEPTH: usize = 2;

/// Extract a cube for cube-and-conquer (Z3's `Z3_solver_cube`).
///
/// REAL: bridges AY's propositional lookahead cube generator
/// (`ay_sat::Solver::generate_cubes`) over this handle's Tseitin-encoded
/// Boolean skeleton (the same [`DimacsEncoder`] behind
/// `Z3_solver_to_dimacs_string`). One cube is returned per call; when the
/// generated set is exhausted the EMPTY vector is returned — Z3's own protocol,
/// where the final empty cube denotes the remainder of the space (z3py's
/// `Solver.cube()` yields it and stops). If the skeleton is refuted at decision
/// level 0, the single cube `[false]` is returned (Z3's "inconsistent"
/// convention).
///
/// SOUNDNESS (cover property): the generated cubes, together with the final
/// empty (= `true`) cube, cover the whole search space — a consumer solving
/// `assertions ∧ cube` for every returned cube can never miss a model.
/// Cube literals are only ever atoms the encoder round-trips (`atom` /
/// `not atom`); lookahead literals over Tseitin AUXILIARY variables are
/// dropped, which only WEAKENS (enlarges) a cube — the union stays a cover.
/// Pruned cubes were refuted at level 0 of the equisatisfiable CNF, so no
/// model is lost there either. Never a fabricated literal.
///
/// Documented hint-level divergences: the `vars` in/out restriction vector and
/// `backtrack_level` are accepted but not consulted (they only steer WHICH
/// splits Z3 prefers, never soundness); the cube set is regenerated after any
/// assertion-stack mutation.
///
/// # Safety
/// `c` must be a valid context pointer; `s`, when non-null, a valid solver
/// handle.
#[no_mangle]
pub unsafe extern "C" fn Z3_solver_cube(
    c: Z3_context,
    s: Z3_solver,
    _vars: Z3_ast_vector,
    _backtrack_level: c_uint,
) -> Z3_ast_vector {
    // SAFETY: `ffi_guard_ptr` guards `c`; `s` is a separate live allocation
    // owned by the context arena, null-checked below.
    unsafe {
        ffi_guard_ptr(c, |ctx| {
            if s.is_null() {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg = Some("Z3_solver_cube: null solver handle".to_string());
                return cache_ast_vector(ctx, Vec::new());
            }
            let handle = &mut *s;
            if handle.pending_cubes.is_none() {
                handle.pending_cubes = Some(generate_cube_queue(ctx, &handle.assertions));
            }
            let next = handle
                .pending_cubes
                .as_mut()
                .and_then(std::collections::VecDeque::pop_front);
            match next {
                Some(lits) => {
                    let asts: Vec<Z3_ast> = lits
                        .into_iter()
                        .map(|(atom, positive)| {
                            let t = if positive { atom } else { ctx.solver.not(atom) };
                            let ast = term_to_ast(ctx, t);
                            record_ast_sort(ctx, ast, Sort::Bool);
                            ast
                        })
                        .collect();
                    cache_ast_vector(ctx, asts)
                }
                // Exhausted: the empty ("rest of the space") terminator cube.
                None => cache_ast_vector(ctx, Vec::new()),
            }
        })
    }
}

/// Exact unit propagation to fixpoint over a DIMACS clause list at decision
/// level 0. Returns `true` iff propagation derives a conflict — i.e. the
/// skeleton is refuted at level 0, Z3's "[false] cube" condition. (The cube
/// generator itself keeps such an instance as an empty cube, so this check is
/// what makes the `[false]` convention exact.)
fn level0_units_conflict(clauses: &[Vec<i32>], num_vars: usize) -> bool {
    let mut assign: Vec<Option<bool>> = vec![None; num_vars + 1];
    loop {
        let mut changed = false;
        for clause in clauses {
            let mut satisfied = false;
            let mut unassigned: Option<i32> = None;
            let mut unassigned_count = 0usize;
            for &lit in clause {
                let var = lit.unsigned_abs() as usize;
                match assign.get(var).copied().flatten() {
                    Some(v) if v == (lit > 0) => {
                        satisfied = true;
                        break;
                    }
                    Some(_) => {}
                    None => {
                        unassigned = Some(lit);
                        unassigned_count += 1;
                    }
                }
            }
            if satisfied {
                continue;
            }
            match unassigned_count {
                0 => return true, // every literal false: conflict
                1 => {
                    let lit = unassigned.expect("exactly one unassigned literal");
                    assign[lit.unsigned_abs() as usize] = Some(lit > 0);
                    changed = true;
                }
                _ => {}
            }
        }
        if !changed {
            return false;
        }
    }
}

/// Generate the cube queue for a solver handle's assertions: Tseitin-encode the
/// Boolean skeleton, run the REAL lookahead cube generator at level 0, and map
/// each cube literal back to its atom term. See [`Z3_solver_cube`] for the
/// cover-property argument.
fn generate_cube_queue(
    ctx: &mut Z3Context,
    assertions: &[Term],
) -> std::collections::VecDeque<Vec<(Term, bool)>> {
    // Encode the skeleton (scoped so the `&Z3Context` borrow ends before any
    // mutable use of `ctx`).
    let (clauses, atoms, num_vars) = {
        let mut enc = DimacsEncoder::new(ctx);
        for &t in assertions {
            enc.assert_formula(t);
        }
        (enc.clauses().to_vec(), enc.atoms().to_vec(), enc.num_vars())
    };
    let atom_of: HashMap<i32, Term> = atoms.into_iter().collect();
    let mut sat = ay_sat::Solver::new(num_vars);
    let mut root_conflict = level0_units_conflict(&clauses, num_vars);
    for cl in &clauses {
        let lits: Vec<ay_sat::Literal> = cl
            .iter()
            .map(|&l| ay_sat::Literal::from_dimacs(l))
            .collect();
        if !sat.add_clause(lits) {
            root_conflict = true;
            break;
        }
    }
    let raw = if root_conflict {
        Vec::new()
    } else {
        sat.generate_cubes(CUBE_LOOKAHEAD_DEPTH)
    };
    if raw.is_empty() {
        // Refuted at level 0 of the equisatisfiable CNF: Z3's convention is a
        // single `[false]` cube (then the empty terminator).
        let f = ctx.solver.bool_const(false);
        return std::collections::VecDeque::from(vec![vec![(f, true)]]);
    }
    let mut queue: std::collections::VecDeque<Vec<(Term, bool)>> =
        std::collections::VecDeque::new();
    for cube in raw {
        let mut mapped: Vec<(Term, bool)> = Vec::with_capacity(cube.len());
        for lit in cube {
            let dimacs = lit.to_dimacs();
            // Only atoms the encoder round-trips become literals; Tseitin
            // auxiliaries are dropped (weakens the cube — still a cover).
            if let Some(&atom) = atom_of.get(&dimacs.abs()) {
                mapped.push((atom, dimacs > 0));
            }
        }
        if mapped.is_empty() {
            // A cube that filtered to `true` covers the whole space by itself;
            // the empty terminator already plays that role — drop the queue.
            return std::collections::VecDeque::new();
        }
        queue.push_back(mapped);
    }
    queue
}

/// Retrieve per-literal decision levels (Z3's `Z3_solver_get_levels`).
///
/// REAL over AY's level-0 trail: reuses the exact machinery
/// `Z3_solver_get_trail`/`_get_units` expose — the handle's `assertions` filtered
/// by [`is_unit_literal`] are precisely the literals assigned at decision level 0.
/// For each queried literal that IS such an input unit we write `0` (its genuine
/// decision level); every other literal gets `UINT_MAX` (Z3's "unknown level"
/// sentinel). SOUND: `0` is only ever claimed for a literal we can prove is a
/// level-0 input unit; AY never fabricates a deeper level it cannot prove.
///
/// # Safety
/// `c` must be a valid context pointer; `s`, when non-null, a valid solver handle;
/// if `sz > 0`, `levels` must point to at least `sz` writable `unsigned` elements.
#[no_mangle]
pub unsafe extern "C" fn Z3_solver_get_levels(
    c: Z3_context,
    s: Z3_solver,
    literals: Z3_ast_vector,
    sz: c_uint,
    levels: *mut c_uint,
) {
    // SAFETY: this public entry point requires `c` to be null or a live,
    // exclusively borrowed context; the bound checker only updates its error state.
    if !unsafe { ffi_count_within_limit(c, "Z3_solver_get_levels output", sz) } {
        return;
    }
    // Pre-extract the queried literals and the handle's assertions outside the
    // guard (raw derefs).
    // SAFETY: caller contract: `literals` is a valid vector handle (or null).
    let queried: Vec<Z3_ast> = unsafe { literals.as_ref() }
        .map(|v| v.asts.clone())
        .unwrap_or_default();
    // SAFETY: `s`, when non-null, is a live handle; `as_ref` null-checks.
    let assertions: Vec<Term> = unsafe { s.as_ref() }
        .map(|h| h.assertions.clone())
        .unwrap_or_default();
    // SAFETY: `ffi_guard_void` guards `c`.
    unsafe {
        ffi_guard_void(c, |ctx| {
            if sz > 0 && levels.is_null() {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg = Some("Z3_solver_get_levels: null levels[] array".to_string());
                return;
            }
            // The level-0 trail: input assertions that are unit literals (exactly
            // what `Z3_solver_get_trail` returns).
            let unit_set: HashSet<Term> = assertions
                .into_iter()
                .filter(|&t| is_unit_literal(ctx, t))
                .collect();
            let mut queried_terms: Vec<Option<Term>> = Vec::with_capacity(sz as usize);
            for i in 0..sz as usize {
                let ast = queried.get(i).copied().unwrap_or(0);
                if ast == 0 {
                    queried_terms.push(None);
                } else {
                    let Some(term) =
                        require_term_ast(ctx, ast, "Z3_solver_get_levels", "queried literal")
                    else {
                        return;
                    };
                    queried_terms.push(Some(term));
                }
            }
            for (i, term) in queried_terms.into_iter().enumerate() {
                let level = term.map_or(c_uint::MAX, |t| {
                    if unit_set.contains(&t) {
                        0
                    } else {
                        c_uint::MAX
                    }
                });
                // SAFETY: `levels` was null-checked when `sz > 0`; the caller's
                // contract guarantees it points to at least `sz` elements, so
                // `levels.add(i)` is in-bounds and writable.
                ptr::write(levels.add(i), level);
            }
        })
    }
}

/// True iff variable `v` occurs in `t` (DFS over the term DAG with a visited
/// set). The occurs-check behind [`Z3_solver_solve_for`].
fn term_contains_var(ctx: &Z3Context, t: Term, v: Term) -> bool {
    let mut stack = vec![t];
    let mut visited: HashSet<Term> = HashSet::new();
    while let Some(cur) = stack.pop() {
        if cur == v {
            return true;
        }
        if visited.insert(cur) {
            stack.extend(ctx.solver.term_children(cur));
        }
    }
    false
}

/// Flatten top-level `and`s of the assertion list into `out`.
fn flatten_top_conjuncts(ctx: &Z3Context, t: Term, out: &mut Vec<Term>) {
    if let TermKind::App { name, .. } = ctx.solver.term_kind(t) {
        if name == "and" {
            for child in ctx.solver.term_children(t) {
                flatten_top_conjuncts(ctx, child, out);
            }
            return;
        }
    }
    out.push(t);
}

/// Retrieve a solved form for `variables` (Z3's `Z3_solver_solve_for`).
///
/// REAL (sound subset): scans this handle's asserted formulas (with top-level
/// conjunctions flattened) for DIRECT solved forms — a top-level equality
/// `(= v t)` or `(= t v)` where `v` is one of the queried variables and `t`
/// does not contain `v` (occurs-check). This is the same solved-form notion
/// AY's `VariableSubstitution` pass (`Tactic::SolveEqs`) eliminates.
///
/// OUTPUT CONTRACT (documented; Z3's own C-API contract here is
/// under-specified): on return, `variables` holds EXACTLY the solved variables
/// (queried variables with no direct solution are removed), `terms[i]` is the
/// solution for `variables[i]`, and `guards[i]` is literally `true` — every
/// reported triple `(v, t, true)` is a top-level equality ENTAILED by the
/// assertions, never an unverified/derived solution. Z3's fuller behavior
/// (triangular multi-step solutions, conditional guards) stays an honest
/// unsolved-variable removal — a sound subset, no fabricated solved form.
///
/// # Safety
/// `c` must be a valid context pointer; `s`, when non-null, a valid solver
/// handle; the three ast_vectors must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_solver_solve_for(
    c: Z3_context,
    s: Z3_solver,
    variables: Z3_ast_vector,
    terms: Z3_ast_vector,
    guards: Z3_ast_vector,
) {
    // SAFETY: `s`, when non-null, is a live handle; `as_ref` null-checks.
    let assertions: Vec<Term> = unsafe { s.as_ref() }
        .map(|h| h.assertions.clone())
        .unwrap_or_default();
    // SAFETY: `ffi_guard_void` guards `c`; the vector handles are separate live
    // allocations owned by the context arena, null-checked below.
    unsafe {
        ffi_guard_void(c, |ctx| {
            if variables.is_null() || terms.is_null() || guards.is_null() {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg = Some("Z3_solver_solve_for: null ast_vector".to_string());
                return;
            }
            // Flatten the assertion set's top-level conjunctions.
            let mut conjuncts: Vec<Term> = Vec::new();
            for &a in &assertions {
                flatten_top_conjuncts(ctx, a, &mut conjuncts);
            }
            let queried: Vec<Z3_ast> = (*variables).asts.clone();
            let mut queried_terms: Vec<Option<Term>> = Vec::with_capacity(queried.len());
            for &var_ast in &queried {
                if var_ast == 0 {
                    queried_terms.push(None);
                    continue;
                }
                let Some(term) =
                    require_term_ast(ctx, var_ast, "Z3_solver_solve_for", "queried variable")
                else {
                    return;
                };
                queried_terms.push(Some(term));
            }
            let mut solved_vars: Vec<Z3_ast> = Vec::new();
            let mut solved_terms: Vec<Z3_ast> = Vec::new();
            let mut solved_guards: Vec<Z3_ast> = Vec::new();
            for (&var_ast, v) in queried.iter().zip(queried_terms) {
                let Some(v) = v else {
                    continue;
                };
                if !matches!(ctx.solver.term_kind(v), TermKind::Var { .. }) {
                    continue; // not a variable: honestly unsolved, dropped
                }
                let mut solution: Option<Term> = None;
                for &conj in &conjuncts {
                    let TermKind::App { name, num_args } = ctx.solver.term_kind(conj) else {
                        continue;
                    };
                    if name != "=" || num_args != 2 {
                        continue;
                    }
                    let children = ctx.solver.term_children(conj);
                    let (lhs, rhs) = (children[0], children[1]);
                    let candidate = if lhs == v {
                        rhs
                    } else if rhs == v {
                        lhs
                    } else {
                        continue;
                    };
                    // Occurs-check: `t` must be free of `v` (else not a
                    // solved form).
                    if !term_contains_var(ctx, candidate, v) {
                        solution = Some(candidate);
                        break;
                    }
                }
                if let Some(t) = solution {
                    let sort = ctx.solver.sort_of(t);
                    let t_ast = term_to_ast(ctx, t);
                    record_ast_sort(ctx, t_ast, sort);
                    let tru = ctx.solver.bool_const(true);
                    let tru_ast = term_to_ast(ctx, tru);
                    record_ast_sort(ctx, tru_ast, Sort::Bool);
                    solved_vars.push(var_ast);
                    solved_terms.push(t_ast);
                    solved_guards.push(tru_ast);
                }
            }
            (*variables).asts = solved_vars;
            (*terms).asts = solved_terms;
            (*guards).asts = solved_guards;
        })
    }
}

// ============================================================================
// User-propagator registration — REAL (final-check loop architecture).
// ============================================================================

/// Mutate the handle's propagator through a scoped handle borrow; `set` on a
/// handle with NO propagator reports `Z3_INVALID_USAGE` honestly (Z3 requires
/// `Z3_solver_propagate_init` first).
///
/// # Safety
/// `c` must be a valid context pointer; `s`, when non-null, a live handle.
unsafe fn with_propagator(
    c: Z3_context,
    s: Z3_solver,
    who: &str,
    set: impl FnOnce(&mut UserPropagator),
) {
    // SAFETY: `s` null-checked by `as_mut`; the handle is its own allocation
    // (no aliasing with the context borrow below, which starts afterwards).
    let ok = match unsafe { s.as_mut() } {
        Some(handle) => match handle.propagator.as_mut() {
            Some(prop) => {
                set(prop);
                prop.revision = prop.revision.wrapping_add(1);
                handle.clear_check_artifacts();
                true
            }
            None => false,
        },
        None => false,
    };
    let who = who.to_string();
    // SAFETY: `ffi_guard_void` guards `c`; the handle borrow above has ended.
    unsafe {
        ffi_guard_void(c, move |ctx| {
            if ok {
                ctx.last_error = Z3_OK;
            } else {
                ctx.last_error = Z3_INVALID_USAGE;
                ctx.error_msg = Some(format!(
                    "{who}: no user propagator on this solver (call Z3_solver_propagate_init \
                     first) or null solver handle"
                ));
            }
        })
    }
}

/// Register a user-propagator with the solver (Z3's `Z3_solver_propagate_init`).
///
/// REAL: stores the user context and the `push`/`pop`/`fresh` callbacks on the
/// solver handle and switches `Z3_solver_check`/`_check_assumptions` for this
/// handle to the SOUND FINAL-CHECK LOOP ([`user_propagator_check`]) — SAT is
/// only ever returned once the user's final check raises no objection, and
/// every user consequence is asserted before re-solving (see module docs for
/// the full soundness argument). A second `init` replaces the propagator
/// (fresh registration state).
///
/// `fresh_eh` is stored but never fired (AY spawns no nested propagator
/// solvers) — documented divergence, observer-only.
///
/// # Safety
/// `c` must be a valid context pointer; `s`, when non-null, a live solver
/// handle; the callbacks (if non-null) must be valid `extern "C"` function
/// pointers that follow Z3's callback contract.
#[no_mangle]
pub unsafe extern "C" fn Z3_solver_propagate_init(
    c: Z3_context,
    s: Z3_solver,
    user_context: *mut c_void,
    push_eh: Z3_push_eh,
    pop_eh: Z3_pop_eh,
    fresh_eh: Z3_fresh_eh,
) {
    // SAFETY: `s` null-checked by `as_mut`; scoped handle borrow.
    let ok = match unsafe { s.as_mut() } {
        Some(handle) => {
            let revision = handle
                .propagator
                .as_ref()
                .map_or(1, |prop| prop.revision.wrapping_add(1));
            handle.propagator = Some(UserPropagator {
                revision,
                user_context,
                push_eh,
                pop_eh,
                fresh_eh,
                fixed_eh: None,
                eq_eh: None,
                diseq_eh: None,
                final_eh: None,
                created_eh: None,
                decide_eh: None,
                on_binding_eh: None,
                registered: Vec::new(),
                pending: Vec::new(),
            });
            handle.clear_check_artifacts();
            true
        }
        None => false,
    };
    // SAFETY: `ffi_guard_void` guards `c`; the handle borrow above has ended.
    unsafe {
        ffi_guard_void(c, |ctx| {
            if ok {
                ctx.last_error = Z3_OK;
            } else {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg = Some("Z3_solver_propagate_init: null Z3_solver handle".to_string());
            }
        })
    }
}

/// Register the "value fixed" callback (Z3's `Z3_solver_propagate_fixed`).
///
/// REAL: fires once per registered term with a ground (numeral/Boolean) value
/// in every final-check round, carrying the candidate model's value. `NULL`
/// unregisters (Z3 convention).
///
/// # Safety
/// `c` must be a valid context pointer; `fixed_eh` (if non-null) must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_solver_propagate_fixed(
    c: Z3_context,
    s: Z3_solver,
    fixed_eh: Z3_fixed_eh,
) {
    // SAFETY: see `with_propagator`.
    unsafe {
        with_propagator(c, s, "Z3_solver_propagate_fixed", |prop| {
            prop.fixed_eh = fixed_eh;
        })
    }
}

/// Register the equality callback (Z3's `Z3_solver_propagate_eq`).
///
/// REAL (best-effort): fires per final-check round for same-sort registered
/// pairs whose ground model values coincide (value-term identity is exact for
/// interned numeral/Boolean literals). Z3 fires on e-graph merges instead; in
/// both engines `final_eh` is the completeness point. Documented divergence.
///
/// # Safety
/// `c` must be a valid context pointer; `eq_eh` (if non-null) must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_solver_propagate_eq(c: Z3_context, s: Z3_solver, eq_eh: Z3_eq_eh) {
    // SAFETY: see `with_propagator`.
    unsafe {
        with_propagator(c, s, "Z3_solver_propagate_eq", |prop| {
            prop.eq_eh = eq_eh;
        })
    }
}

/// Register the dis-equality callback (Z3's `Z3_solver_propagate_diseq`;
/// also typed `Z3_eq_eh`).
///
/// REAL (best-effort): fires per final-check round for same-sort registered
/// pairs whose ground model values differ. See [`Z3_solver_propagate_eq`].
///
/// # Safety
/// `c` must be a valid context pointer; `eq_eh` (if non-null) must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_solver_propagate_diseq(c: Z3_context, s: Z3_solver, eq_eh: Z3_eq_eh) {
    // SAFETY: see `with_propagator`.
    unsafe {
        with_propagator(c, s, "Z3_solver_propagate_diseq", |prop| {
            prop.diseq_eh = eq_eh;
        })
    }
}

/// Register the final-check callback (Z3's `Z3_solver_propagate_final`).
///
/// REAL: fires once per final-check round, after all `fixed`/`eq`/`diseq`
/// notifications. A SAT verdict is only ever returned when this callback (and
/// the rest of the round) recorded no consequence and registered no new term —
/// exactly Z3's acceptance contract.
///
/// # Safety
/// `c` must be a valid context pointer; `final_eh` (if non-null) must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_solver_propagate_final(
    c: Z3_context,
    s: Z3_solver,
    final_eh: Z3_final_eh,
) {
    // SAFETY: see `with_propagator`.
    unsafe {
        with_propagator(c, s, "Z3_solver_propagate_final", |prop| {
            prop.final_eh = final_eh;
        })
    }
}

/// Register the "term created" callback (Z3's `Z3_solver_propagate_created`).
///
/// REAL (adapted timing): AY fires `created_eh` when a term is REGISTERED with
/// the propagator (`Z3_solver_propagate_register`/`_register_cb`) — the moment
/// the term enters the propagator's watch set — rather than on internalization
/// of terms over propagator-declared functions (AY's engine has no
/// internalization event stream). Documented divergence; the notification is
/// informational, so the adapted timing cannot change any verdict.
///
/// # Safety
/// `c` must be a valid context pointer; `created_eh` (if non-null) must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_solver_propagate_created(
    c: Z3_context,
    s: Z3_solver,
    created_eh: Z3_created_eh,
) {
    // SAFETY: see `with_propagator`.
    unsafe {
        with_propagator(c, s, "Z3_solver_propagate_created", |prop| {
            prop.created_eh = created_eh;
        })
    }
}

/// Register the branching-override callback (Z3's `Z3_solver_propagate_decide`).
///
/// Registered but never fired: AY exposes no in-search decision events, so this
/// heuristic override is not consulted — AY keeps its own decision heuristic.
/// SOUND: a decide hook only reorders the search; ignoring it can never change
/// SAT/UNSAT or model correctness. Documented divergence.
///
/// # Safety
/// `c` must be a valid context pointer; `decide_eh` (if non-null) must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_solver_propagate_decide(
    c: Z3_context,
    s: Z3_solver,
    decide_eh: Z3_decide_eh,
) {
    // SAFETY: see `with_propagator`.
    unsafe {
        with_propagator(c, s, "Z3_solver_propagate_decide", |prop| {
            prop.decide_eh = decide_eh;
        })
    }
}

/// Register the quantifier-instantiation binding callback (Z3's
/// `Z3_solver_propagate_on_binding`).
///
/// Registered but never fired: AY exposes no quantifier-instantiation binding
/// event stream. SOUND: not firing never *blocks* an instantiation, and every
/// instantiation is a sound instance of an asserted quantifier, so verdicts are
/// unaffected. Documented divergence.
///
/// # Safety
/// `c` must be a valid context pointer; `on_binding_eh` (if non-null) must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_solver_propagate_on_binding(
    c: Z3_context,
    s: Z3_solver,
    on_binding_eh: Z3_on_binding_eh,
) {
    // SAFETY: see `with_propagator`.
    unsafe {
        with_propagator(c, s, "Z3_solver_propagate_on_binding", |prop| {
            prop.on_binding_eh = on_binding_eh;
        })
    }
}

/// Register expression `e` for the user propagator to be notified about (Z3's
/// `Z3_solver_propagate_register`).
///
/// REAL: adds `e` to the propagator's watch set (dedup) and fires `created_eh`
/// for a genuinely-new term (registration-time creation announcement — see
/// [`Z3_solver_propagate_created`]). Watched terms receive `fixed_eh` (and
/// participate in `eq`/`diseq` pairing) in every final-check round.
///
/// # Safety
/// `c` must be a valid context pointer; `s`, when non-null, a live handle with
/// a registered propagator.
#[no_mangle]
pub unsafe extern "C" fn Z3_solver_propagate_register(c: Z3_context, s: Z3_solver, e: Z3_ast) {
    // Validate through a scoped guard first (error reporting), then register +
    // fire `created_eh` with NO context borrow live (the callback may re-enter
    // the C API).
    let mut valid = false;
    // SAFETY: `ffi_guard_void` guards `c`; `s` is only null-checked here.
    unsafe {
        ffi_guard_void(c, |ctx| {
            // SAFETY: scoped read-only null-check of the handle.
            let has_prop = s.as_ref().is_some_and(|h| h.propagator.is_some());
            if !has_prop {
                ctx.last_error = Z3_INVALID_USAGE;
                ctx.error_msg = Some(
                    "Z3_solver_propagate_register: no user propagator on this solver (call \
                     Z3_solver_propagate_init first)"
                        .to_string(),
                );
                return;
            }
            let _term = require_term_ast_or_return!(
                ctx,
                e,
                "Z3_solver_propagate_register",
                "registered term",
            );
            ctx.last_error = Z3_OK;
            valid = true;
        });
        if valid {
            // SAFETY: no outstanding context borrow (the guard above returned).
            register_terms_and_fire_created(c, s, vec![e]);
        }
    }
}

/// In-callback variant of `propagate_register` (Z3's
/// `Z3_solver_propagate_register_cb`).
///
/// REAL: records `e` on the live callback object; the final-check loop merges
/// it into the watch set (firing `created_eh`) when the callback returns, and
/// runs another notification round before any SAT can be reported. A null `cb`
/// (called outside a callback) is refused with `Z3_INVALID_USAGE`.
///
/// # Safety
/// `c` must be a valid context pointer; `cb`, when non-null, the live callback
/// object passed into the current user callback.
#[no_mangle]
pub unsafe extern "C" fn Z3_solver_propagate_register_cb(
    c: Z3_context,
    cb: Z3_solver_callback,
    e: Z3_ast,
) {
    if cb.is_null() {
        // Outside a callback: honest usage error (no live round to record on).
        // SAFETY: no callback is running (null `cb`), so the context borrow
        // cannot alias a caller's.
        unsafe {
            ffi_guard_void(c, |ctx| {
                ctx.last_error = Z3_INVALID_USAGE;
                ctx.error_msg = Some(
                    "Z3_solver_propagate_register_cb: only callable from inside a user-\
                     propagator callback (null Z3_solver_callback)"
                        .to_string(),
                );
            });
        }
        return;
    }
    if e == 0 {
        return;
    }
    // SAFETY: a non-null `cb` is the loop's live stack object for the current
    // round (caller contract); recording on it takes no context borrow, so the
    // in-callback aliasing discipline is preserved.
    let cbo = unsafe { &mut *cb };
    cbo.new_registrations.push(e);
}

/// Push a propagated consequence or conflict into the search from within a user
/// callback (Z3's `Z3_solver_propagate_consequence`).
///
/// REAL: RECORDS the lemma `(∧ fixed_i = value(fixed_i)) ∧ (∧ eq_j) ⇒ conseq`
/// on the live callback object; after the callbacks return, the final-check
/// loop asserts it and re-solves, so the propagation genuinely constrains the
/// search. Returns `true` only when the record was accepted. Honest refusals
/// (`false`, nothing recorded):
///   * null `cb` (outside a callback) — plus `Z3_INVALID_USAGE`;
///   * null `conseq` / null justification entries;
///   * a `fixed` justification term with no recorded model value this round
///     (its fixed-value literal cannot be represented faithfully).
///
/// # Safety
/// `c` must be a valid context pointer; `cb`, when non-null, the live callback
/// object; the fixed/eq arrays (if non-null) must point to `num_fixed` /
/// `num_eqs` valid `Z3_ast` elements.
#[no_mangle]
#[allow(clippy::too_many_arguments)]
pub unsafe extern "C" fn Z3_solver_propagate_consequence(
    c: Z3_context,
    cb: Z3_solver_callback,
    num_fixed: c_uint,
    fixed: *const Z3_ast,
    num_eqs: c_uint,
    eq_lhs: *const Z3_ast,
    eq_rhs: *const Z3_ast,
    conseq: Z3_ast,
) -> bool {
    // Equality justifications traverse two arrays (lhs and rhs), so account
    // for both rather than counting each pair as one element.
    // SAFETY: this public entry point requires `c` to be null or a live,
    // exclusively borrowed context; the bound checker only updates its error state.
    if !unsafe {
        ffi_counts_within_limit(
            c,
            "Z3_solver_propagate_consequence justifications",
            &[num_fixed, num_eqs, num_eqs],
        )
    } {
        return false;
    }
    if cb.is_null() {
        // Outside a callback: honest usage error, consequence NOT accepted.
        // SAFETY: no callback is running (null `cb`), so the context borrow
        // cannot alias a caller's.
        return unsafe {
            ffi_guard_int(c, 0, |ctx| {
                ctx.last_error = Z3_INVALID_USAGE;
                ctx.error_msg = Some(
                    "Z3_solver_propagate_consequence: only callable from inside a user-\
                     propagator callback (null Z3_solver_callback); consequence not accepted"
                        .to_string(),
                );
                0
            }) != 0
        };
    }
    if conseq == 0 {
        return false;
    }
    if (num_fixed > 0 && fixed.is_null()) || (num_eqs > 0 && (eq_lhs.is_null() || eq_rhs.is_null()))
    {
        return false;
    }
    // SAFETY: caller contract — the arrays hold the declared element counts.
    let fixed_terms: Vec<Z3_ast> = (0..num_fixed as usize)
        .map(|i| unsafe { *fixed.add(i) })
        .collect();
    // SAFETY: caller contract as above.
    let eq_pairs: Vec<(Z3_ast, Z3_ast)> = (0..num_eqs as usize)
        .map(|i| unsafe { (*eq_lhs.add(i), *eq_rhs.add(i)) })
        .collect();
    // SAFETY: a non-null `cb` is the loop's live stack object for the current
    // round; recording takes no context borrow (aliasing discipline).
    let cbo = unsafe { &mut *cb };
    if fixed_terms
        .iter()
        .any(|f| *f == 0 || !cbo.values.contains_key(f))
    {
        // A justification term that was never reported fixed this round: the
        // lemma cannot be represented faithfully — refuse, never guess.
        return false;
    }
    if eq_pairs.iter().any(|&(l, r)| l == 0 || r == 0) {
        return false;
    }
    cbo.consequences.push(RecordedConsequence {
        fixed: fixed_terms,
        eqs: eq_pairs,
        conseq,
    });
    true
}

/// Request `(t, idx, phase)` as the next split from within a user callback (Z3's
/// `Z3_solver_next_split`).
///
/// Reachable (callbacks now run) but the hint is NOT applied: AY exposes no
/// in-search decision override, so it keeps its own heuristic and returns
/// `false` ("split hint not applied" — Z3's own signal for an unusable hint).
/// SOUND: a split hint only reorders the search; ignoring it cannot change any
/// verdict. Documented divergence; no error is raised.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_solver_next_split(
    _c: Z3_context,
    _cb: Z3_solver_callback,
    _t: Z3_ast,
    _idx: c_uint,
    _phase: c_int,
) -> bool {
    // No context borrow: this may run inside a user callback while the loop's
    // guarded sections are released; touching `_c` is unnecessary (no error to
    // report) and keeping hands off preserves the aliasing discipline.
    false
}

/// Register an observer callback for asserted/inferred/deleted clauses (Z3's
/// `Z3_solver_register_on_clause`; used for proof logging / DRAT-style
/// tracing). REGISTRATION-ACCEPTED, NEVER FIRES — behavior-parity-proven
/// against libz3 4.16.0 (probed 2026-07-09):
///
///   * libz3 accepts the registration silently (no error) and its callback
///     granularity is EXPLICITLY undocumented/experimental — probed counts:
///     0 callbacks on an empty solver, 0 on `p ∧ ¬p`, 1 `assumption` event on
///     `x > 0`, 3 mixed `assumption`/`smt` events on an LIA conflict. ZERO
///     invocations are therefore inside libz3's observable contract, and a
///     consumer cannot rely on any particular event stream.
///   * AY accepts the registration identically (no error, `Z3_OK` untouched)
///     and fires nothing: suppressing pure observer notifications never
///     changes SAT/UNSAT, models, cores, or proofs — the same observable
///     class as a libz3 run whose pipeline emits no tracked clauses.
///
/// RESIDUAL (documented, not hidden): AY's SAT core does derive learned
/// clauses (the DRAT/LRAT proof stream in `ay-sat`), but no per-clause hook is
/// plumbed through `ay_dpll::api::Solver` to this FFI — surfacing real
/// `assumption`/`smt` events would need engine-side observer plumbing across
/// the per-solve construction sites. Until then callbacks simply never fire.
///
/// # Safety
/// `c` must be a valid context pointer; `on_clause_eh` (if non-null) must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_solver_register_on_clause(
    _c: Z3_context,
    _s: Z3_solver,
    _user_context: *mut c_void,
    _on_clause_eh: Z3_on_clause_eh,
) {
}

#[cfg(test)]
#[path = "propagate_tests.rs"]
mod propagate_tests;
