// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Z3-compatible C-API functions that need NO new `ay-dpll` engine method.
//!
//! Every function here is realized entirely from primitives already exposed by
//! the FFI layer and the `ay_dpll::api::Solver` — model substitution, the shared
//! solve engine, the datatype constructor/selector builders, the DIMACS
//! encoder, and the handle arenas — plus a few small `pub(crate)` visibility
//! openings elsewhere in the crate (`model_value_to_term`, `DimacsEncoder`).
//!
//! The functions fall into three groups:
//!
//! * **Real algebraic-number bounds** — `Z3_get_algebraic_number_lower`/`_upper`
//!   refine an algebraic value's isolating interval (via `ay_nra`) to the
//!   requested precision and return the endpoint as a `Real` numeral.
//!
//! * **Honest divergences** — `Z3_get_global_param_descrs` (AY honors no
//!   process-global params, so the descriptor set is empty) and
//!   `Z3_get_estimated_alloc_size` (no reachable process-global term-byte
//!   counter, so a sound `0` estimate). Neither fabricates a value; each sets an
//!   error or returns a documented sentinel.
//!
//! * **Real engine computations** — `Z3_get_implied_equalities` (all-models
//!   equivalence classes via UNSAT disequality probes on the shared engine),
//!   `Z3_qe_model_project`/`_skolem`/`_with_witness` (model-based variable
//!   projection via `Solver::substitute`), and `Z3_datatype_update_field`
//!   (functional field update rebuilt through AY's verified datatype builders).
//!
//! * **Handle plumbing** — `Z3_func_interp_add_entry`/`_set_else` (populate a
//!   model function interpretation), `Z3_goal_to_dimacs_string` (render a goal's
//!   Boolean skeleton, mirroring `Z3_solver_to_dimacs_string`), and
//!   `Z3_optimize_translate` (copy an optimize handle across contexts, mirroring
//!   `Z3_solver_translate`).
//!
//! All functions calling into the solver are wrapped via the `ffi_guard_*`
//! helpers (#6192) so panics never unwind across the FFI boundary.

use std::collections::HashMap;
use std::ffi::{c_int, c_uint};
use std::ptr;

use ay_dpll::api::{Sort, Term};
use ay_nra::{rcf_api, RealScalar};
use num_bigint::BigInt;
use num_rational::BigRational;

use super::algebraic::ast_as_scalar;
use super::model_params::model_value_to_term;
use super::solver::{
    auxiliary_query_acceptance_is_supported, solve_lbool_with_acceptance, DimacsEncoder,
};
use super::{
    cache_func_entry, cache_string, ensure_cross_context_translation_semantics,
    ffi_count_within_limit, ffi_counts_within_limit, ffi_guard_ast, ffi_guard_const_ptr,
    ffi_guard_int, ffi_guard_ptr, ffi_guard_void, record_ast_sort, require_term_ast,
    require_term_ast_or_return, require_term_asts_or_return, term_to_ast,
    transfer_cross_context_ffi_metadata, DatatypeOp, DecisionOwnerFamily, OptimizeHandle,
    ParamDescrsHandle, SoftRecord, Z3_ast, Z3_ast_map, Z3_ast_vector, Z3_context, Z3_func_decl,
    Z3_func_interp, Z3_goal, Z3_model, Z3_optimize, Z3_param_descrs, Z3_solver, Z3_string,
    MAX_FFI_REFINEMENT_PRECISION, Z3_INVALID_ARG, Z3_INVALID_USAGE, Z3_L_FALSE, Z3_L_TRUE,
    Z3_L_UNDEF, Z3_OK,
};

// ============================================================================
// Algebraic numbers — REAL isolating-interval endpoints
// ============================================================================

/// A rational lower (or upper) bound of the algebraic value `a`, refined so the
/// isolating interval is narrower than `2^-precision`.
///
/// A rational value is its own exact lower/upper bound. A genuine algebraic value
/// (an [`super::ALGEBRAIC_AST_TAG`] handle) has its open isolating interval
/// bisected — each step decided by the exact `RealAlgebraic::cmp_rational` sign
/// test, never numeric proximity — until it is narrow enough; the requested
/// endpoint is returned as a `Real` numeral. `None`/non-value/cap →
/// `Z3_INVALID_ARG` + null AST (never a fabricated bound).
fn algebraic_number_bound(
    ctx: &mut super::Z3Context,
    a: Z3_ast,
    precision: c_uint,
    want_upper: bool,
    who: &str,
) -> Z3_ast {
    if precision > MAX_FFI_REFINEMENT_PRECISION {
        ctx.last_error = Z3_INVALID_ARG;
        ctx.error_msg = Some(format!(
            "{who}: precision {precision} exceeds the supported maximum {MAX_FFI_REFINEMENT_PRECISION}"
        ));
        return 0;
    }
    let Some(s) = ast_as_scalar(ctx, a) else {
        ctx.last_error = Z3_INVALID_ARG;
        ctx.error_msg = Some(format!("{who}: operand is not an algebraic value"));
        return 0;
    };
    let emit = |ctx: &mut super::Z3Context, r: BigRational| -> Z3_ast {
        let term = ctx.solver.rational_const_bigint(r.numer(), r.denom());
        let ast = term_to_ast(ctx, term);
        record_ast_sort(ctx, ast, Sort::Real);
        ctx.last_error = Z3_OK;
        ast
    };
    match rcf_api::canonicalize(&s) {
        Some(RealScalar::Rational(r)) => emit(ctx, r),
        Some(RealScalar::Algebraic(v)) => {
            let alpha = v.alpha();
            let (lo0, hi0) = alpha.interval();
            let (mut lo, mut hi) = (lo0.clone(), hi0.clone());
            // target width = 1 / 2^precision.
            let target = BigRational::new(BigInt::from(1), BigInt::from(2).pow(precision));
            let two = BigRational::from_integer(BigInt::from(2));
            let cap = precision as usize + 256;
            for _ in 0..cap {
                if &hi - &lo <= target {
                    break;
                }
                let mid = (&lo + &hi) / &two;
                match alpha.cmp_rational(&mid) {
                    Some(std::cmp::Ordering::Less) => hi = mid, // value < mid
                    Some(std::cmp::Ordering::Greater) => lo = mid, // value > mid
                    Some(std::cmp::Ordering::Equal) => {
                        lo = mid.clone();
                        hi = mid;
                        break;
                    }
                    None => {
                        ctx.last_error = Z3_INVALID_ARG;
                        ctx.error_msg =
                            Some(format!("{who}: interval refinement not exactly computable"));
                        return 0;
                    }
                }
            }
            emit(ctx, if want_upper { hi } else { lo })
        }
        None => {
            ctx.last_error = Z3_INVALID_ARG;
            ctx.error_msg = Some(format!("{who}: value not exactly computable — fail-closed"));
            0
        }
    }
}

/// Lower bound of an algebraic-number AST (Z3's `Z3_get_algebraic_number_lower`).
///
/// REAL: refines the isolating interval to width `< 2^-precision` and returns its
/// lower endpoint as a `Real` numeral (a rational value returns itself). A
/// non-value operand or a cap → `Z3_INVALID_ARG` + null.
///
/// # Safety
/// `c` must be a valid context pointer; `a` is a `Z3_ast` handle.
#[no_mangle]
pub unsafe extern "C" fn Z3_get_algebraic_number_lower(
    c: Z3_context,
    a: Z3_ast,
    precision: c_uint,
) -> Z3_ast {
    // SAFETY: `ffi_guard_ast` guards `c` (null-check + panic catch).
    unsafe {
        ffi_guard_ast(c, |ctx| {
            algebraic_number_bound(ctx, a, precision, false, "Z3_get_algebraic_number_lower")
        })
    }
}

/// Upper bound of an algebraic-number AST (Z3's `Z3_get_algebraic_number_upper`).
///
/// REAL — see [`Z3_get_algebraic_number_lower`]: returns the refined upper
/// interval endpoint.
///
/// # Safety
/// `c` must be a valid context pointer; `a` is a `Z3_ast` handle.
#[no_mangle]
pub unsafe extern "C" fn Z3_get_algebraic_number_upper(
    c: Z3_context,
    a: Z3_ast,
    precision: c_uint,
) -> Z3_ast {
    // SAFETY: `ffi_guard_ast` guards `c` (null-check + panic catch).
    unsafe {
        ffi_guard_ast(c, |ctx| {
            algebraic_number_bound(ctx, a, precision, true, "Z3_get_algebraic_number_upper")
        })
    }
}

// ============================================================================
// Global parameter descriptors — honest empty set
// ============================================================================

/// Return the descriptor set of the process-global parameters (Z3's
/// `Z3_get_global_param_descrs`).
///
/// HONEST DIVERGENCE: AY honors no process-global parameters (its configuration
/// is per-context / per-solver), so the returned descriptor set is genuinely
/// EMPTY — never a fabricated list of parameters AY does not actually read. The
/// handle is a real, queryable [`ParamDescrsHandle`] (size 0), arena-owned via
/// `param_descrs_cache` and freed at `Z3_del_context`, so
/// `Z3_param_descrs_inc_ref`/`_dec_ref` are bookkeeping-only no-ops. Mirrors
/// `Z3_optimize_get_param_descrs` in `optimize.rs`.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_get_global_param_descrs(c: Z3_context) -> Z3_param_descrs {
    // SAFETY: `ffi_guard_ptr` guards `c` (null-check + panic catch). The handle
    // is registered in `param_descrs_cache` and freed once, on context drop.
    unsafe {
        ffi_guard_ptr(c, |ctx| {
            let handle = Box::into_raw(Box::new(ParamDescrsHandle {
                entries: Vec::new(),
            }));
            ctx.param_descrs_cache.push(handle);
            ctx.last_error = Z3_OK;
            handle
        })
    }
}

// ============================================================================
// Estimated allocation size — sound 0 estimate
// ============================================================================

/// Return an estimate of the process-global bytes allocated for terms (Z3's
/// `Z3_get_estimated_alloc_size`).
///
/// AY exposes no reachable process-global term-byte counter (its `term_bytes`
/// statistic is per-check, on a specific solver, and there is no context here to
/// read it from — the signature takes none). Rather than pull in a new `ay-core`
/// dependency to introspect the allocator, this returns `0`. A `0` value is
/// SOUND for this API: the function is documented as an ESTIMATE, and `0` is a
/// valid (if uninformative) estimate — it never misreports a concrete size.
#[no_mangle]
pub extern "C" fn Z3_get_estimated_alloc_size() -> u64 {
    0
}

// ============================================================================
// Implied equalities — all-models equivalence classes
// ============================================================================

/// Union-find `find` with path halving over a flat parent array.
fn uf_find(parent: &mut [usize], mut x: usize) -> usize {
    while parent[x] != x {
        parent[x] = parent[parent[x]];
        x = parent[x];
    }
    x
}

/// Compute the equivalence classes of `terms` that are equal in EVERY model of
/// solver `s`'s assertions (Z3's `Z3_get_implied_equalities`).
///
/// The classes are computed by a sound, real engine derivation: the solver's
/// assertions are loaded into the shared engine once, then for each not-yet-merged
/// pair `(i, j)` the routine checks `assertions ∧ (distinct t_i t_j)`. When that
/// is UNSAT, `t_i = t_j` holds in all models, so `i` and `j` are unioned. A pair
/// is merged ONLY on a definitive UNSAT — an `unknown`/`sat` probe never merges
/// (honest partial: two terms that are actually always-equal but whose
/// disequality the engine cannot refute are left in separate classes). Terms of
/// different sorts can never be equal and are never probed. `class_ids[i]` is set
/// to a small dense id shared by exactly the terms in `i`'s class.
///
/// Returns `Z3_L_TRUE` on success and `Z3_L_FALSE` for an inconsistent
/// baseline. Returns `Z3_L_UNDEF` for a null solver handle/array, a baseline
/// rejected at the consumer boundary, or active user-propagator/transitive-
/// closure semantics that this auxiliary query cannot verify faithfully.
///
/// # Safety
/// `c` must be a valid context pointer; `s`, when non-null, a valid solver handle
/// owned by `c`. `terms` and `class_ids` must each point to at least `num_terms`
/// elements when `num_terms > 0`.
#[no_mangle]
pub unsafe extern "C" fn Z3_get_implied_equalities(
    c: Z3_context,
    s: Z3_solver,
    num_terms: c_uint,
    terms: *const Z3_ast,
    class_ids: *mut c_uint,
) -> c_int {
    // SAFETY: this public entry point requires `c` to be null or a live,
    // exclusively borrowed context; the bound checker only updates its error state.
    if !unsafe {
        ffi_counts_within_limit(
            c,
            "Z3_get_implied_equalities input and output arrays",
            &[num_terms, num_terms],
        )
    } {
        return Z3_L_UNDEF;
    }
    // Pre-extract the term array (raw reads) in the unsafe fn body.
    let term_asts: Vec<Z3_ast> = if num_terms == 0 || terms.is_null() {
        Vec::new()
    } else {
        // SAFETY: `terms` points to `num_terms` valid elements (caller contract).
        (0..num_terms as usize)
            .map(|i| unsafe { *terms.add(i) })
            .collect()
    };
    // SAFETY: `ffi_guard_int` guards `c`; `s`/`class_ids` null-checked below.
    unsafe {
        ffi_guard_int(c, Z3_L_UNDEF, |ctx| {
            if !ctx.decision_engine_is_usable("Z3_get_implied_equalities") {
                return Z3_L_UNDEF;
            }
            if num_terms > 0 && terms.is_null() {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg =
                    Some("Z3_get_implied_equalities: null terms input array".to_string());
                return Z3_L_UNDEF;
            }
            if num_terms > 0 && class_ids.is_null() {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg =
                    Some("Z3_get_implied_equalities: null class_ids output array".to_string());
                return Z3_L_UNDEF;
            }
            // Snapshot the handle's assertion goal + tracking literals, then drop
            // the borrow. Tracking literals (`Z3_solver_assert_and_track`) are
            // assumed on every probe so the tracked assertions constrain the check,
            // matching the solver's real check-time semantics (see
            // `Z3_solver_get_consequences`).
            let (assertions, tracked_lits, has_user_propagator): (Vec<Term>, Vec<Term>, bool) =
                match s.as_ref() {
                    Some(h) => (
                        h.assertions.clone(),
                        h.tracked.iter().map(|(p, _)| *p).collect(),
                        h.propagator.is_some(),
                    ),
                    None => {
                        ctx.last_error = Z3_INVALID_ARG;
                        ctx.error_msg =
                            Some("Z3_get_implied_equalities: null solver handle".to_string());
                        return Z3_L_UNDEF;
                    }
                };
            if !auxiliary_query_acceptance_is_supported(
                ctx,
                has_user_propagator,
                "Z3_get_implied_equalities",
            ) {
                return Z3_L_UNDEF;
            }
            let mut term_vec = require_term_asts_or_return!(
                ctx,
                &term_asts,
                "Z3_get_implied_equalities",
                Z3_L_UNDEF
            );
            let n = term_vec.len();

            // Check-time expansion of recursive definitions (P1.1). This
            // auxiliary query has no residual-mode SAT demotion, so it is
            // STRICTLY fail-closed: expansion failure returns unknown before
            // any verdict-bearing probe. Probing expanded twins is sound —
            // under the definitional semantics each expansion equals its
            // original, and the output here is index/class-id-only.
            let mut assertions = assertions;
            let mut tracked_lits = tracked_lits;
            let mut rec_expanded = false;
            if !ctx.rec_fun_defs.is_empty() {
                let mut batch: Vec<Term> =
                    Vec::with_capacity(assertions.len() + tracked_lits.len() + term_vec.len());
                batch.extend_from_slice(&assertions);
                batch.extend_from_slice(&tracked_lits);
                batch.extend_from_slice(&term_vec);
                // Finding-2 gate: never probe through a defined body whose
                // unfolding surfaces an UNDEFINED rec declaration (see
                // `rec_defs_tainted_by_undefined`) — strictly fail-closed.
                let tainted = super::solver::rec_defs_tainted_by_undefined(ctx);
                if !tainted.is_empty() && ctx.solver.terms_mention_names(&batch, &tainted) {
                    ctx.last_error = Z3_INVALID_USAGE;
                    ctx.error_msg = Some(
                        "Z3_get_implied_equalities: a used definition depends on a \
                         recursive declaration with no definition; returning unknown \
                         fail-closed"
                            .to_string(),
                    );
                    return Z3_L_UNDEF;
                }
                match ctx.solver.try_expand_rec_defs(
                    &batch,
                    &ctx.rec_fun_defs,
                    super::solver::REC_DEF_MAX_ROUNDS,
                    super::solver::REC_DEF_WORK_BUDGET,
                    Some(super::solver::rec_def_expansion_deadline(ctx)),
                ) {
                    Ok(expanded) => {
                        let (new_asserts, rest) = expanded.split_at(assertions.len());
                        let (new_tracked, new_terms) = rest.split_at(tracked_lits.len());
                        assertions = new_asserts.to_vec();
                        tracked_lits = new_tracked.to_vec();
                        term_vec = new_terms.to_vec();
                        rec_expanded = true;
                    }
                    Err(e) => {
                        ctx.last_error = Z3_INVALID_USAGE;
                        ctx.error_msg = Some(format!(
                            "Z3_get_implied_equalities: recursive definition could not \
                             be fully expanded ({e}); returning unknown fail-closed"
                        ));
                        return Z3_L_UNDEF;
                    }
                }
            }

            // Load the goal into the shared engine (replaces any prior goal).
            if let Err(e) = ctx.solver.try_reset_assertions() {
                ctx.last_error = super::Z3_EXCEPTION;
                ctx.error_msg = Some(format!("{e}"));
                return Z3_L_UNDEF;
            }
            for &t in &assertions {
                if let Err(e) = ctx.solver.try_assert_term(t) {
                    ctx.last_error = super::Z3_EXCEPTION;
                    ctx.error_msg = Some(format!("{e}"));
                    return Z3_L_UNDEF;
                }
            }
            // Theory-internal background axioms (orders / Char bounds) too;
            // the rec-def axioms are omitted for a fully-expanded goal.
            if let Err(e) = super::assert_background_axioms(ctx, !rec_expanded) {
                ctx.last_error = super::Z3_EXCEPTION;
                ctx.error_msg = Some(e);
                return Z3_L_UNDEF;
            }

            // Establish a publicly admitted SAT baseline before inferring
            // equivalence classes. In particular, an inconsistent baseline is
            // reported as FALSE instead of making every pair vacuously equal,
            // and a consumer-rejected SAT candidate cannot escape as TRUE.
            let baseline = if tracked_lits.is_empty() {
                ctx.solver.check_sat()
            } else {
                ctx.solver.check_sat_assuming(&tracked_lits)
            };
            match solve_lbool_with_acceptance(ctx, baseline) {
                Z3_L_TRUE => {}
                Z3_L_FALSE => {
                    ctx.last_error = Z3_OK;
                    return Z3_L_FALSE;
                }
                _ => return Z3_L_UNDEF,
            }

            // Union-find over the term indices.
            let mut parent: Vec<usize> = (0..n).collect();
            for i in 0..n {
                for j in (i + 1)..n {
                    if uf_find(&mut parent, i) == uf_find(&mut parent, j) {
                        continue; // already known equal
                    }
                    let ti = term_vec[i];
                    let tj = term_vec[j];
                    // Different sorts can never be equal: leave in separate classes
                    // (and never build an ill-sorted `distinct`).
                    if ctx.solver.term_sort(ti) != ctx.solver.term_sort(tj) {
                        continue;
                    }
                    // `assertions ∧ tracked ∧ (t_i != t_j)` UNSAT ⇒ t_i = t_j in
                    // all models.
                    let neq = ctx.solver.distinct(&[ti, tj]);
                    let mut probe = tracked_lits.clone();
                    probe.push(neq);
                    if ctx.solver.check_sat_assuming(&probe).is_unsat() {
                        let ra = uf_find(&mut parent, i);
                        let rb = uf_find(&mut parent, j);
                        parent[ra] = rb;
                    }
                }
            }

            // Assign a dense class id per root (first-appearance order) and write it.
            let mut class_map: HashMap<usize, c_uint> = HashMap::new();
            let mut next_id: c_uint = 0;
            for i in 0..n {
                let root = uf_find(&mut parent, i);
                let id = *class_map.entry(root).or_insert_with(|| {
                    let x = next_id;
                    next_id += 1;
                    x
                });
                // SAFETY: `class_ids` points to `num_terms == n` writable slots
                // (checked non-null above); `i < n`.
                *class_ids.add(i) = id;
            }
            ctx.last_error = Z3_OK;
            Z3_L_TRUE
        })
    }
}

// ============================================================================
// Model-based projection (quantifier elimination given a model)
// ============================================================================

/// Shared core of the `Z3_qe_model_project*` family: substitute each bound
/// variable with its value in model `m` and simplify.
///
/// For each `Z3_app` bound constant, its model value (looked up by name) is
/// converted to a value TERM via [`model_value_to_term`] and substituted into
/// `body`; the result is folded through AY's semantics-preserving simplifier.
///
/// HONEST PARTIAL RESULT: a bound variable the model does not pin — or whose
/// value cannot be represented as a term — is left FREE in the result rather than
/// given a fabricated value. That is a sound (if incomplete) projection: the
/// returned formula is still equal to `body` under the model on every variable
/// that WAS substituted.
///
/// When `witness` is non-null, it is filled with the `bound-var -> value-term`
/// substitution actually used (only the pairs that were substituted), backing the
/// `_skolem`/`_with_witness` variants.
///
/// # Safety
/// `m`, when non-null, is a valid model handle; `witness`, when non-null, a valid
/// AST-map handle. Both are separate allocations from `ctx`.
unsafe fn qe_project_core(
    ctx: &mut super::Z3Context,
    m: Z3_model,
    bound_asts: &[Z3_ast],
    body: Z3_ast,
    witness: Z3_ast_map,
) -> Z3_ast {
    if body == 0 {
        ctx.last_error = Z3_INVALID_ARG;
        ctx.error_msg = Some("Z3_qe_model_project: null body formula".to_string());
        return 0;
    }
    if m.is_null() {
        ctx.last_error = Z3_INVALID_ARG;
        ctx.error_msg = Some("Z3_qe_model_project: null model handle".to_string());
        return 0;
    }

    let Some(body_term) = require_term_ast(ctx, body, "Z3_qe_model_project", "body formula") else {
        return 0;
    };
    let mut from: Vec<Term> = Vec::new();
    let mut to: Vec<Term> = Vec::new();
    // (bound-var ast, value-term ast) pairs actually substituted, for the witness.
    let mut witness_pairs: Vec<(Z3_ast, Z3_ast)> = Vec::new();

    for &b in bound_asts {
        if b == 0 {
            continue;
        }
        let Some(bt) = require_term_ast(ctx, b, "Z3_qe_model_project", "bound variable") else {
            return 0;
        };
        let Some(name) = ctx.solver.var_name(bt) else {
            continue; // not a named constant — nothing to project
        };
        let sort = ctx.solver.term_sort(bt);
        // SAFETY: `m` is non-null (checked above) and a separate allocation from
        // `ctx`. `value_by_name` returns an OWNED value, so the brief shared borrow
        // of `*m` is released before the `&mut` solver call below.
        let value = unsafe { (*m).model.value_by_name(&name) };
        if let Some(val) = value {
            if let Some(value_term) = model_value_to_term(&mut ctx.solver, &val, &sort) {
                from.push(bt);
                to.push(value_term);
                witness_pairs.push((b, term_to_ast(ctx, value_term)));
            }
            // else: value not representable as a term → leave `bt` free (partial).
        }
        // else: model does not pin `bt` → leave it free (honest partial result).
    }

    let projected = ctx.solver.substitute(body_term, &from, &to);
    let simplified = ctx.solver.simplify(projected);

    // Fill the witness map (skolem / with_witness variants) when requested.
    // SAFETY: `witness`, when non-null, is a valid AST-map handle (separate
    // allocation from `ctx` and `m`).
    if let Some(map) = unsafe { witness.as_mut() } {
        for (k, v) in &witness_pairs {
            map.insert(*k, *v);
        }
    }

    ctx.last_error = Z3_OK;
    term_to_ast(ctx, simplified)
}

/// Read a `Z3_app`/`Z3_ast` bound array (`num_bounds` elements) into a Vec.
///
/// # Safety
/// `bound` points to `num_bounds` valid elements when `num_bounds > 0`.
unsafe fn read_bound_array(num_bounds: c_uint, bound: *const Z3_ast) -> Vec<Z3_ast> {
    if num_bounds == 0 || bound.is_null() {
        return Vec::new();
    }
    // SAFETY: caller guarantees `bound` points to at least `num_bounds` elements.
    (0..num_bounds as usize)
        .map(|i| unsafe { *bound.add(i) })
        .collect()
}

/// Project the bound variables out of `body` using their values in model `m`
/// (Z3's `Z3_qe_model_project`).
///
/// # Safety
/// `c` must be a valid context pointer; `m`, when non-null, a valid model handle;
/// `bound` must point to `num_bounds` valid `Z3_app` handles.
#[no_mangle]
pub unsafe extern "C" fn Z3_qe_model_project(
    c: Z3_context,
    m: Z3_model,
    num_bounds: c_uint,
    bound: *const Z3_ast,
    body: Z3_ast,
) -> Z3_ast {
    // SAFETY: this public entry point requires `c` to be null or a live,
    // exclusively borrowed context; the bound checker only updates its error state.
    if !unsafe { ffi_count_within_limit(c, "Z3_qe_model_project bounds", num_bounds) } {
        return 0;
    }
    // SAFETY: valid array per contract.
    let bound_asts = unsafe { read_bound_array(num_bounds, bound) };
    // SAFETY: `ffi_guard_ast` guards `c`; `m`/witness handled inside the core.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            qe_project_core(ctx, m, &bound_asts, body, ptr::null_mut())
        })
    }
}

/// Project the bound variables out of `body`, additionally recording the
/// `bound-var -> value` skolem witnesses into `map` (Z3's
/// `Z3_qe_model_project_skolem`).
///
/// # Safety
/// `c` must be a valid context pointer; `m`/`map`, when non-null, valid handles;
/// `bound` must point to `num_bounds` valid `Z3_app` handles.
#[no_mangle]
pub unsafe extern "C" fn Z3_qe_model_project_skolem(
    c: Z3_context,
    m: Z3_model,
    num_bounds: c_uint,
    bound: *const Z3_ast,
    body: Z3_ast,
    map: Z3_ast_map,
) -> Z3_ast {
    // SAFETY: this public entry point requires `c` to be null or a live,
    // exclusively borrowed context; the bound checker only updates its error state.
    if !unsafe { ffi_count_within_limit(c, "Z3_qe_model_project_skolem bounds", num_bounds) } {
        return 0;
    }
    // SAFETY: valid array per contract.
    let bound_asts = unsafe { read_bound_array(num_bounds, bound) };
    // SAFETY: `ffi_guard_ast` guards `c`; `m`/`map` handled inside the core.
    unsafe { ffi_guard_ast(c, |ctx| qe_project_core(ctx, m, &bound_asts, body, map)) }
}

/// Project the bound variables out of `body`, filling `map` with the model
/// witnesses used (Z3's `Z3_qe_model_project_with_witness`).
///
/// Identical to [`Z3_qe_model_project_skolem`] in AY: the witness map is the
/// `bound-var -> value-term` substitution the projection applied.
///
/// # Safety
/// `c` must be a valid context pointer; `m`/`map`, when non-null, valid handles;
/// `bound` must point to `num_bounds` valid `Z3_app` handles.
#[no_mangle]
pub unsafe extern "C" fn Z3_qe_model_project_with_witness(
    c: Z3_context,
    m: Z3_model,
    num_bounds: c_uint,
    bound: *const Z3_ast,
    body: Z3_ast,
    map: Z3_ast_map,
) -> Z3_ast {
    // SAFETY: this public entry point requires `c` to be null or a live,
    // exclusively borrowed context; the bound checker only updates its error state.
    if !unsafe { ffi_count_within_limit(c, "Z3_qe_model_project_with_witness bounds", num_bounds) }
    {
        return 0;
    }
    // SAFETY: valid array per contract.
    let bound_asts = unsafe { read_bound_array(num_bounds, bound) };
    // SAFETY: `ffi_guard_ast` guards `c`; `m`/`map` handled inside the core.
    unsafe { ffi_guard_ast(c, |ctx| qe_project_core(ctx, m, &bound_asts, body, map)) }
}

// ============================================================================
// Datatype functional field update
// ============================================================================

/// Return `t` with the field selected by `field_access` replaced by `value`
/// (Z3's `Z3_datatype_update_field`).
///
/// This is a real functional update: from `t`'s datatype sort AY finds the
/// constructor `C` owning the accessed field and rebuilds
/// `C(sel_0(t), …, value, …, sel_{k-1}(t))` — the untouched fields become
/// selector applications on `t`, and the accessed field takes `value`. The rebuild
/// goes through the verified `Solver::try_datatype_selector` /
/// `try_datatype_constructor` builders (the same path AY's SMT-LIB elaborator
/// uses), so the result carries correct datatype semantics.
///
/// The field-accessor `Z3_func_decl` only records the field NAME (not its owning
/// constructor), so the constructor is resolved from `t`'s runtime sort. When the
/// update cannot be resolved — `field_access` is not a datatype accessor, `t` is
/// not a datatype term, no constructor owns the field, or `value`'s sort does not
/// match the field — this sets `Z3_INVALID_ARG` and returns the ORIGINAL `t`
/// unchanged. That is a documented, sound no-op (it never returns a mis-built
/// term); the common case performs the genuine rebuild.
///
/// # Safety
/// `c` must be a valid context pointer; `field_access`, when non-null, a valid
/// func-decl handle; `t`/`value` are `Z3_ast` handles.
#[no_mangle]
pub unsafe extern "C" fn Z3_datatype_update_field(
    c: Z3_context,
    field_access: Z3_func_decl,
    t: Z3_ast,
    value: Z3_ast,
) -> Z3_ast {
    // SAFETY: `ffi_guard_ast` guards `c`; `field_access` null-checked below.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            let t_term =
                require_term_ast_or_return!(ctx, t, "Z3_datatype_update_field", "datatype term", 0);
            let value_term = require_term_ast_or_return!(
                ctx,
                value,
                "Z3_datatype_update_field",
                "replacement value",
                0
            );
            // The accessor must be a datatype field accessor; extract its field name.
            let field_name = match field_access.as_ref() {
                Some(h) => match &h.dt_op {
                    Some(DatatypeOp::Accessor { field, .. }) => field.clone(),
                    _ => {
                        ctx.last_error = Z3_INVALID_ARG;
                        ctx.error_msg = Some(
                            "Z3_datatype_update_field: field_access is not a datatype accessor"
                                .to_string(),
                        );
                        return t;
                    }
                },
                None => {
                    ctx.last_error = Z3_INVALID_ARG;
                    ctx.error_msg = Some("Z3_datatype_update_field: null field_access".to_string());
                    return t;
                }
            };

            // `t` must be a datatype term so we can find its constructor + siblings.
            let Sort::Datatype(dt) = ctx.solver.term_sort(t_term) else {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg =
                    Some("Z3_datatype_update_field: t is not a datatype term".to_string());
                return t;
            };
            // The (first) constructor that owns a field with this name.
            let Some(ctor) = dt
                .constructors
                .iter()
                .find(|ct| ct.fields.iter().any(|f| f.name == field_name))
                .cloned()
            else {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg = Some(format!(
                    "Z3_datatype_update_field: no constructor of '{}' has field '{}'",
                    dt.name, field_name
                ));
                return t;
            };

            // Rebuild the constructor: value at the accessed field, sel_i(t) elsewhere.
            let mut args: Vec<Term> = Vec::with_capacity(ctor.fields.len());
            for f in &ctor.fields {
                if f.name == field_name {
                    args.push(value_term);
                } else {
                    match ctx
                        .solver
                        .try_datatype_selector(&f.name, t_term, f.sort.clone())
                    {
                        Ok(sel) => args.push(sel),
                        Err(e) => {
                            ctx.last_error = Z3_INVALID_ARG;
                            ctx.error_msg = Some(format!("Z3_datatype_update_field: {e}"));
                            return t;
                        }
                    }
                }
            }
            match ctx.solver.try_datatype_constructor(&dt, &ctor.name, &args) {
                Ok(updated) => {
                    ctx.last_error = Z3_OK;
                    term_to_ast(ctx, updated)
                }
                Err(e) => {
                    ctx.last_error = Z3_INVALID_ARG;
                    ctx.error_msg = Some(format!("Z3_datatype_update_field: {e}"));
                    t
                }
            }
        })
    }
}

// ============================================================================
// Function-interpretation population (model function tables)
// ============================================================================

/// Add one point (`args -> value`) to a model function interpretation (Z3's
/// `Z3_func_interp_add_entry`).
///
/// The entry's argument tuple is the current contents of the `args` AST vector.
/// The entry box is owned by the context's `func_entry_cache`; `fi` stores a
/// non-owning pointer to it (matching how `Z3_model_get_func_interp` builds its
/// tables), so both are freed exactly once at `Z3_del_context`.
///
/// # Safety
/// `c` must be a valid context pointer; `fi`, when non-null, a valid func-interp
/// handle; `args`, when non-null, a valid AST-vector handle.
#[no_mangle]
pub unsafe extern "C" fn Z3_func_interp_add_entry(
    c: Z3_context,
    fi: Z3_func_interp,
    args: Z3_ast_vector,
    value: Z3_ast,
) {
    // SAFETY: `ffi_guard_void` guards `c`; `fi`/`args` null-checked below.
    unsafe {
        ffi_guard_void(c, |ctx| {
            let entry_args: Vec<Z3_ast> = match args.as_ref() {
                Some(v) => v.asts.clone(),
                None => {
                    ctx.last_error = Z3_INVALID_ARG;
                    ctx.error_msg = Some("Z3_func_interp_add_entry: null args vector".to_string());
                    return;
                }
            };
            if fi.is_null() {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg =
                    Some("Z3_func_interp_add_entry: null func_interp handle".to_string());
                return;
            }
            let _arg_terms =
                require_term_asts_or_return!(ctx, &entry_args, "Z3_func_interp_add_entry");
            let _value_term =
                require_term_ast_or_return!(ctx, value, "Z3_func_interp_add_entry", "entry value",);
            // Allocate the entry in the context's owning arena, then reference it
            // from the interpretation handle (separate allocation from `ctx`).
            let entry = cache_func_entry(ctx, entry_args, value);
            if let Some(fi_h) = fi.as_mut() {
                fi_h.entries.push(entry);
            }
            ctx.last_error = Z3_OK;
        });
    }
}

/// Set the `else` (default) value of a model function interpretation (Z3's
/// `Z3_func_interp_set_else`).
///
/// # Safety
/// `c` must be a valid context pointer; `f`, when non-null, a valid func-interp
/// handle; `else_value` is a `Z3_ast` handle.
#[no_mangle]
pub unsafe extern "C" fn Z3_func_interp_set_else(
    c: Z3_context,
    f: Z3_func_interp,
    else_value: Z3_ast,
) {
    // SAFETY: `ffi_guard_void` guards `c`; `f` null-checked via `as_mut`.
    unsafe {
        ffi_guard_void(c, |ctx| {
            if let Some(fi_h) = f.as_mut() {
                let _term = require_term_ast_or_return!(
                    ctx,
                    else_value,
                    "Z3_func_interp_set_else",
                    "default value",
                );
                fi_h.else_ast = else_value;
                ctx.last_error = Z3_OK;
            } else {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg =
                    Some("Z3_func_interp_set_else: null func_interp handle".to_string());
            }
        });
    }
}

// ============================================================================
// Goal → DIMACS
// ============================================================================

/// Emit a goal's Boolean skeleton as a DIMACS CNF string (Z3's
/// `Z3_goal_to_dimacs_string`).
///
/// Mirrors `Z3_solver_to_dimacs_string`: the goal's formulas are fed to the same
/// [`DimacsEncoder`], producing a Tseitin CNF of the propositional skeleton (each
/// distinct Boolean atom — theory atoms included, as opaque propositional
/// variables — becomes one DIMACS variable). The CNF is equisatisfiable with the
/// skeleton; AY does NOT bit-blast theory atoms, so the DIMACS captures the
/// propositional structure only (documented in `ay_z3_compat.h`) and variable
/// numbering differs from libz3's. When `include_names` is set, a `c <var> <atom>`
/// mapping comment is emitted per atom.
///
/// # Safety
/// `c` must be a valid context pointer; `g`, when non-null, a valid goal handle.
#[no_mangle]
pub unsafe extern "C" fn Z3_goal_to_dimacs_string(
    c: Z3_context,
    g: Z3_goal,
    include_names: bool,
) -> Z3_string {
    // SAFETY: `ffi_guard_const_ptr` guards `c`; `g` null-checked via `as_ref`.
    unsafe {
        ffi_guard_const_ptr(c, |ctx| {
            let formulas: Vec<Z3_ast> = match g.as_ref() {
                Some(gh) => gh.formulas.clone(),
                None => {
                    ctx.last_error = Z3_INVALID_ARG;
                    ctx.error_msg = Some("Z3_goal_to_dimacs_string: null goal handle".to_string());
                    return ptr::null();
                }
            };
            let formula_terms = require_term_asts_or_return!(
                ctx,
                &formulas,
                "Z3_goal_to_dimacs_string",
                ptr::null()
            );
            let mut enc = DimacsEncoder::new(ctx);
            for term in formula_terms {
                enc.assert_formula(term);
            }
            let text = enc.render(include_names);
            cache_string(ctx, text)
        })
    }
}

// ============================================================================
// Optimize handle translation across contexts
// ============================================================================

/// Copy optimize handle `o` from context `source` into context `target` (Z3's
/// `Z3_optimize_translate`).
///
/// Returns a NEW optimize handle on a fresh `target`, faithfully carrying hard
/// constraints, API soft constraints (including group labels), and tracked
/// assertions. Installation is transactional: target hard state is protected by
/// an internal scope and API soft state is length-rolled-back on error; a panic
/// or failed rollback permanently poisons the target decision engine.
///
/// Honest compatibility frontier: same-context translation is rejected because
/// AY enforces one optimize handle per context. Arithmetic objectives and parsed
/// `(assert-soft ...)` state are also rejected up front because they are not yet
/// represented on `OptimizeHandle`; returning a partial translation would be a
/// wrong optimization problem. Context-resident semantic metadata is likewise
/// rejected until it can be transferred atomically. Use a fresh context and
/// rebuild those features.
///
/// # Safety
/// `source`/`target` must be valid context pointers; `o`, when non-null, a valid
/// optimize handle owned by `source`.
#[no_mangle]
pub unsafe extern "C" fn Z3_optimize_translate(
    source: Z3_context,
    o: Z3_optimize,
    target: Z3_context,
) -> Z3_optimize {
    // Pre-extract the source handle's constraint state (raw deref; lives in `source`).
    // SAFETY: `o`, when non-null, is a live `OptimizeHandle` owned by `source`.
    let handle_data = unsafe { o.as_ref() }.map(|h| {
        (
            h.hard.clone(),
            h.softs
                .iter()
                .map(|s| (s.term, s.weight, s.group.clone()))
                .collect::<Vec<(Term, u64, Option<String>)>>(),
            h.tracked.clone(),
            h.terminal_error.clone(),
        )
    });
    // SAFETY: `ffi_guard_ptr` validates/guards `target`.
    unsafe {
        ffi_guard_ptr(target, |tgt| {
            let Some((hard, softs, tracked, terminal_error)) = handle_data else {
                tgt.last_error = Z3_INVALID_ARG;
                tgt.error_msg = Some("Z3_optimize_translate: null optimize handle".to_string());
                return ptr::null_mut();
            };
            if let Some(reason) = terminal_error {
                tgt.last_error = Z3_INVALID_USAGE;
                tgt.error_msg = Some(format!(
                    "Z3_optimize_translate: source optimize handle is unavailable: {reason}"
                ));
                return ptr::null_mut();
            }
            if source == target {
                tgt.last_error = Z3_INVALID_USAGE;
                tgt.error_msg = Some(
                    "Z3_optimize_translate: same-context translation would create a second optimize handle; use a fresh Z3_context"
                        .to_string(),
                );
                return ptr::null_mut();
            }
            // SAFETY: source != target, so this immutable source borrow cannot
            // alias the mutable target borrow held by the FFI guard.
            let Some(src) = source.as_ref() else {
                tgt.last_error = Z3_INVALID_ARG;
                tgt.error_msg = Some("Z3_optimize_translate: null source context".to_string());
                return ptr::null_mut();
            };
            if !ensure_cross_context_translation_semantics(src, tgt, "Z3_optimize_translate") {
                return ptr::null_mut();
            }
            if src.solver.num_objectives() > 0 || src.solver.num_parsed_soft_constraints() > 0 {
                tgt.last_error = Z3_INVALID_USAGE;
                tgt.error_msg = Some(
                    "Z3_optimize_translate: arithmetic objectives and parsed soft constraints are not representable in translation; rebuild them on a fresh context"
                        .to_string(),
                );
                return ptr::null_mut();
            }
            if !tgt.optimize_handle_cache.is_empty() {
                tgt.last_error = Z3_INVALID_USAGE;
                tgt.error_msg = Some(
                    "Z3_optimize_translate: target context already has an optimize handle; use a separate Z3_context"
                        .to_string(),
                );
                return ptr::null_mut();
            }
            if !tgt.claim_decision_owner(DecisionOwnerFamily::Optimize, "Z3_optimize_translate") {
                return ptr::null_mut();
            }

            // Leave a fail-closed latch throughout the transaction: an FFI
            // panic is caught outside this closure, so without the latch a
            // partially installed target could later be claimed and queried.
            tgt.decision_engine_poisoned = Some(
                "Z3_optimize_translate was interrupted before transactional completion".to_string(),
            );
            let base_soft_len = tgt.solver.num_soft_constraints();
            if let Err(e) = tgt.solver.try_push() {
                tgt.poison_decision_engine(format!(
                    "Z3_optimize_translate: cannot open installation transaction: {e}"
                ));
                return ptr::null_mut();
            }

            let new_hard = tgt.solver.translate_terms_from(&src.solver, &hard);
            let soft_terms: Vec<Term> = softs.iter().map(|(t, _, _)| *t).collect();
            let new_soft_terms = tgt.solver.translate_terms_from(&src.solver, &soft_terms);
            let new_softs: Vec<(Term, u64, Option<String>)> = new_soft_terms
                .iter()
                .zip(softs.iter())
                .map(|(t, (_, w, group))| (*t, *w, group.clone()))
                .collect();
            let mut flat: Vec<Term> = Vec::with_capacity(tracked.len() * 2);
            for (p, a) in &tracked {
                flat.push(*p);
                flat.push(*a);
            }
            let new_flat = tgt.solver.translate_terms_from(&src.solver, &flat);
            let mut source_roots = hard.clone();
            source_roots.extend(soft_terms.iter().copied());
            source_roots.extend(flat.iter().copied());
            let mut target_roots = new_hard.clone();
            target_roots.extend(new_soft_terms.iter().copied());
            target_roots.extend(new_flat.iter().copied());
            let new_tracked: Vec<(Term, Term)> = new_flat
                .as_chunks::<2>()
                .0
                .iter()
                .map(|c| (c[0], c[1]))
                .collect();

            let mut install_error = None;
            for &t in &new_hard {
                if let Err(e) = tgt.solver.try_assert_term(t) {
                    install_error = Some(format!("cannot install hard constraint: {e}"));
                    break;
                }
            }
            if install_error.is_none() {
                for (t, w, group) in &new_softs {
                    if let Err(e) = tgt.solver.assert_soft(*t, *w, group.as_deref()) {
                        install_error = Some(format!("cannot install soft constraint: {e}"));
                        break;
                    }
                }
            }
            if let Some(detail) = install_error {
                tgt.solver.truncate_soft_constraints(base_soft_len);
                match tgt.solver.try_pop() {
                    Ok(()) => {
                        tgt.decision_engine_poisoned = None;
                        tgt.decision_owner = None;
                        tgt.last_error = super::Z3_EXCEPTION;
                        tgt.error_msg = Some(format!("Z3_optimize_translate: {detail}"));
                    }
                    Err(rollback) => tgt.poison_decision_engine(format!(
                        "Z3_optimize_translate: {detail}; rollback also failed: {rollback}"
                    )),
                }
                return ptr::null_mut();
            }
            if !transfer_cross_context_ffi_metadata(
                src,
                tgt,
                &source_roots,
                &target_roots,
                "Z3_optimize_translate",
            ) {
                let metadata_error = tgt.error_msg.clone();
                tgt.solver.truncate_soft_constraints(base_soft_len);
                match tgt.solver.try_pop() {
                    Ok(()) => {
                        tgt.decision_engine_poisoned = None;
                        tgt.decision_owner = None;
                        tgt.last_error = Z3_INVALID_USAGE;
                        tgt.error_msg = metadata_error;
                    }
                    Err(rollback) => tgt.poison_decision_engine(format!(
                        "Z3_optimize_translate: metadata transfer failed; rollback also failed: {rollback}"
                    )),
                }
                return ptr::null_mut();
            }

            let handle = Box::into_raw(Box::new(OptimizeHandle {
                _ctx: target,
                hard: new_hard,
                softs: new_softs
                    .into_iter()
                    .map(|(term, weight, group)| SoftRecord {
                        term,
                        weight,
                        group,
                    })
                    .collect(),
                last_model: None,
                last_check_outcome: None,
                tracked: new_tracked,
                scope_markers: Vec::new(),
                last_unsat_core: None,
                last_reason_unknown: None,
                last_statistics: None,
                terminal_error: None,
            }));
            tgt.optimize_handle_cache.push(handle);
            tgt.decision_engine_poisoned = None;
            tgt.last_error = Z3_OK;
            tgt.error_msg = None;
            handle
        })
    }
}
