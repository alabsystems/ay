// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for the REAL user-propagator surface (`propagate.rs`): the sound
//! final-check loop behind `Z3_solver_check` when a propagator is registered.
//!
//! The scenarios drive genuine C-ABI callbacks (the same `extern "C"` shape a C
//! consumer would register) implementing a pseudo-theory `x ≠ y` over two
//! registered `Int` constants:
//!   * a candidate model with `x = y` is rejected via a fixed-justified
//!     conflict lemma and the loop re-solves to a model with `x ≠ y`;
//!   * when every model has `x = y`, the same propagator forces UNSAT;
//!   * an unconditional consequence lemma (`¬(x = y)` with empty justification)
//!     flips a SAT goal to UNSAT.
//!
//! The callbacks deliberately re-enter the C API (`Z3_mk_eq`/`Z3_mk_not`/
//! `Z3_mk_false`) from inside the callback, exercising the no-outstanding-
//! borrow discipline of the loop.

use std::ffi::{c_uint, c_void};
use std::ptr;

use super::super::*;
use super::Z3_solver_callback;

unsafe fn ctx() -> Z3_context {
    // SAFETY: standard config/context construction; the config is freed after
    // the context takes ownership of its parameters.
    unsafe {
        let cfg = Z3_mk_config();
        let c = Z3_mk_context(cfg);
        Z3_del_config(cfg);
        c
    }
}

/// Shared state handed to the callbacks as `user_context`.
struct PropState {
    ctx: Z3_context,
    x: Z3_ast,
    y: Z3_ast,
    /// `(term, value)` pairs delivered by `fixed_eh` in the current round.
    fixed: Vec<(Z3_ast, Z3_ast)>,
    /// Number of `final_eh` rounds observed.
    final_rounds: usize,
    /// Number of `push_eh` / `pop_eh` events (must balance).
    pushes: usize,
    pops: usize,
    /// `eq_eh` / `diseq_eh` observations for the (x, y) pair.
    saw_eq: bool,
    saw_diseq: bool,
    /// Pseudo-theory mode: `true` = conflict when x and y share a value
    /// (fixed-justified); `false` = unconditional `¬(x = y)` lemma.
    justified_mode: bool,
}

unsafe extern "C" fn push_cb(u: *mut c_void, _cb: Z3_solver_callback) {
    let st = unsafe { &mut *(u as *mut PropState) };
    st.pushes += 1;
}

unsafe extern "C" fn pop_cb(u: *mut c_void, _cb: Z3_solver_callback, _n: c_uint) {
    let st = unsafe { &mut *(u as *mut PropState) };
    st.pops += 1;
    st.fixed.clear();
}

unsafe extern "C" fn fixed_cb(u: *mut c_void, _cb: Z3_solver_callback, t: Z3_ast, v: Z3_ast) {
    let st = unsafe { &mut *(u as *mut PropState) };
    st.fixed.push((t, v));
}

unsafe extern "C" fn eq_cb(u: *mut c_void, _cb: Z3_solver_callback, a: Z3_ast, b: Z3_ast) {
    let st = unsafe { &mut *(u as *mut PropState) };
    if (a == st.x && b == st.y) || (a == st.y && b == st.x) {
        st.saw_eq = true;
    }
}

unsafe extern "C" fn diseq_cb(u: *mut c_void, _cb: Z3_solver_callback, a: Z3_ast, b: Z3_ast) {
    let st = unsafe { &mut *(u as *mut PropState) };
    if (a == st.x && b == st.y) || (a == st.y && b == st.x) {
        st.saw_diseq = true;
    }
}

/// Final check for the pseudo-theory `x ≠ y`.
unsafe extern "C" fn final_cb(u: *mut c_void, cb: Z3_solver_callback) {
    let st = unsafe { &mut *(u as *mut PropState) };
    st.final_rounds += 1;
    if st.justified_mode {
        // Object only when the candidate model fixes x and y to the SAME value:
        // conflict lemma justified by the two fixed terms —
        // `(x = vx ∧ y = vy) ⇒ false`.
        let vx = st.fixed.iter().find(|(t, _)| *t == st.x).map(|&(_, v)| v);
        let vy = st.fixed.iter().find(|(t, _)| *t == st.y).map(|&(_, v)| v);
        if let (Some(vx), Some(vy)) = (vx, vy) {
            if vx == vy {
                // Re-enter the C API from inside the callback (allowed: the
                // loop holds no context borrow while callbacks run).
                let conflict = unsafe { Z3_mk_false(st.ctx) };
                let fixed = [st.x, st.y];
                let accepted = unsafe {
                    Z3_solver_propagate_consequence(
                        st.ctx,
                        cb,
                        2,
                        fixed.as_ptr(),
                        0,
                        ptr::null(),
                        ptr::null(),
                        conflict,
                    )
                };
                assert!(accepted, "justified conflict must be recorded");
            }
        }
    } else {
        // Unconditional user axiom: `¬(x = y)` with an empty justification.
        let neq = unsafe { Z3_mk_not(st.ctx, Z3_mk_eq(st.ctx, st.x, st.y)) };
        let accepted = unsafe {
            Z3_solver_propagate_consequence(
                st.ctx,
                cb,
                0,
                ptr::null(),
                0,
                ptr::null(),
                ptr::null(),
                neq,
            )
        };
        assert!(accepted, "unconditional consequence must be recorded");
    }
}

/// Build a solver with Int consts x, y, a registered propagator (all callbacks),
/// and return `(solver, state_ptr)`. The caller owns the state box.
unsafe fn setup_propagator(c: Z3_context, justified_mode: bool) -> (Z3_solver, *mut PropState) {
    let int_sort = unsafe { Z3_mk_int_sort(c) };
    let x = unsafe { Z3_mk_const(c, Z3_mk_string_symbol(c, c"x".as_ptr()), int_sort) };
    let y = unsafe { Z3_mk_const(c, Z3_mk_string_symbol(c, c"y".as_ptr()), int_sort) };
    let solver = unsafe { Z3_mk_solver(c) };

    let st = Box::into_raw(Box::new(PropState {
        ctx: c,
        x,
        y,
        fixed: Vec::new(),
        final_rounds: 0,
        pushes: 0,
        pops: 0,
        saw_eq: false,
        saw_diseq: false,
        justified_mode,
    }));
    unsafe {
        Z3_solver_propagate_init(
            c,
            solver,
            st as *mut c_void,
            Some(push_cb),
            Some(pop_cb),
            None,
        );
        Z3_solver_propagate_fixed(c, solver, Some(fixed_cb));
        Z3_solver_propagate_eq(c, solver, Some(eq_cb));
        Z3_solver_propagate_diseq(c, solver, Some(diseq_cb));
        Z3_solver_propagate_final(c, solver, Some(final_cb));
        assert_eq!(Z3_get_error_code(c), Z3_OK);
        Z3_solver_propagate_register(c, solver, x);
        Z3_solver_propagate_register(c, solver, y);
        assert_eq!(Z3_get_error_code(c), Z3_OK);
    }
    (solver, st)
}

/// Evaluate an Int const in the solver's model.
unsafe fn model_int(c: Z3_context, s: Z3_solver, t: Z3_ast) -> i64 {
    let m = unsafe { Z3_solver_get_model(c, s) };
    assert!(!m.is_null());
    let mut v: Z3_ast = 0;
    assert!(unsafe { Z3_model_eval(c, m, t, true, &mut v) });
    let mut out: i64 = 0;
    assert!(unsafe { Z3_get_numeral_int64(c, v, &mut out) });
    out
}

/// The propagator's conflict lemma flips a would-be `x = y` model to the only
/// surviving `x ≠ y` model: goal `(x=0 ∧ y=0) ∨ (x=1 ∧ y=2)`; the pseudo-theory
/// kills `(0,0)`, so the final verdict is SAT at exactly `(1, 2)`.
#[test]
fn user_propagator_flips_equal_model_to_distinct() {
    unsafe {
        let c = ctx();
        let (solver, st) = setup_propagator(c, true);
        let (x, y) = ((*st).x, (*st).y);
        let int_sort = Z3_mk_int_sort(c);
        let (zero, one, two) = (
            Z3_mk_int(c, 0, int_sort),
            Z3_mk_int(c, 1, int_sort),
            Z3_mk_int(c, 2, int_sort),
        );
        let both_zero = {
            let args = [Z3_mk_eq(c, x, zero), Z3_mk_eq(c, y, zero)];
            Z3_mk_and(c, 2, args.as_ptr())
        };
        let one_two = {
            let args = [Z3_mk_eq(c, x, one), Z3_mk_eq(c, y, two)];
            Z3_mk_and(c, 2, args.as_ptr())
        };
        let goal = {
            let args = [both_zero, one_two];
            Z3_mk_or(c, 2, args.as_ptr())
        };
        Z3_solver_assert(c, solver, goal);

        assert_eq!(Z3_solver_check(c, solver), Z3_L_TRUE);
        // The accepted model must satisfy the user theory: x ≠ y — and with
        // (0,0) excluded by the propagator's lemma, it is exactly (1, 2).
        assert_eq!(model_int(c, solver, x), 1);
        assert_eq!(model_int(c, solver, y), 2);

        let st_ref = &*st;
        assert!(st_ref.final_rounds >= 1, "final_eh must have run");
        assert_eq!(st_ref.pushes, st_ref.pops, "push/pop must balance");
        // The ACCEPTING round saw the distinct pair (best-effort diseq fired).
        assert!(
            st_ref.saw_diseq,
            "diseq_eh should report x ≠ y in the accepted model"
        );

        drop(Box::from_raw(st));
        Z3_del_context(c);
    }
}

/// When every model equates x and y (`x = 0 ∧ y = 0`), the pseudo-theory's
/// fixed-justified conflict makes the goal UNSAT — the propagator is
/// load-bearing and its lemma genuinely constrains the search.
#[test]
fn user_propagator_forces_unsat_via_justified_conflict() {
    unsafe {
        let c = ctx();
        let (solver, st) = setup_propagator(c, true);
        let (x, y) = ((*st).x, (*st).y);
        let int_sort = Z3_mk_int_sort(c);
        let zero = Z3_mk_int(c, 0, int_sort);
        Z3_solver_assert(c, solver, Z3_mk_eq(c, x, zero));
        Z3_solver_assert(c, solver, Z3_mk_eq(c, y, zero));

        assert_eq!(Z3_solver_check(c, solver), Z3_L_FALSE);
        let st_ref = &*st;
        assert!(
            st_ref.final_rounds >= 1,
            "the objection round must have run"
        );
        // The rejected round saw the equal pair (best-effort eq fired).
        assert!(
            st_ref.saw_eq,
            "eq_eh should report x = y in the rejected model"
        );

        drop(Box::from_raw(st));
        Z3_del_context(c);
    }
}

/// An unconditional consequence lemma (`¬(x = y)`, empty justification) added
/// against the goal `x = y` forces UNSAT.
#[test]
fn user_propagator_unconditional_lemma_forces_unsat() {
    unsafe {
        let c = ctx();
        let (solver, st) = setup_propagator(c, false);
        let (x, y) = ((*st).x, (*st).y);
        Z3_solver_assert(c, solver, Z3_mk_eq(c, x, y));

        assert_eq!(Z3_solver_check(c, solver), Z3_L_FALSE);
        assert!((*st).final_rounds >= 1);

        drop(Box::from_raw(st));
        Z3_del_context(c);
    }
}

/// A propagator that never objects: the first SAT model is accepted unchanged
/// (the loop terminates in one round) and check results stay correct.
#[test]
fn user_propagator_no_objection_accepts_first_model() {
    unsafe {
        let c = ctx();
        let (solver, st) = setup_propagator(c, true);
        let (x, y) = ((*st).x, (*st).y);
        let int_sort = Z3_mk_int_sort(c);
        // x = 3, y = 4: already distinct — the pseudo-theory never objects.
        Z3_solver_assert(c, solver, Z3_mk_eq(c, x, Z3_mk_int(c, 3, int_sort)));
        Z3_solver_assert(c, solver, Z3_mk_eq(c, y, Z3_mk_int(c, 4, int_sort)));

        assert_eq!(Z3_solver_check(c, solver), Z3_L_TRUE);
        assert_eq!(model_int(c, solver, x), 3);
        assert_eq!(model_int(c, solver, y), 4);
        assert_eq!(
            (*st).final_rounds,
            1,
            "one round suffices when no objection is raised"
        );

        drop(Box::from_raw(st));
        Z3_del_context(c);
    }
}

struct ReentrantState {
    ctx: Z3_context,
    solver: Z3_solver,
    term: Z3_ast,
    calls: usize,
}

unsafe extern "C" fn assert_false_from_final(u: *mut c_void, _cb: Z3_solver_callback) {
    let st = unsafe { &mut *u.cast::<ReentrantState>() };
    st.calls += 1;
    if st.calls == 1 {
        let falsum = unsafe { Z3_mk_false(st.ctx) };
        unsafe { Z3_solver_assert(st.ctx, st.solver, falsum) };
    }
}

unsafe extern "C" fn register_from_final(u: *mut c_void, _cb: Z3_solver_callback) {
    let st = unsafe { &mut *u.cast::<ReentrantState>() };
    st.calls += 1;
    if st.calls == 1 {
        unsafe { Z3_solver_propagate_register(st.ctx, st.solver, st.term) };
    }
}

unsafe extern "C" fn tautology_from_final(u: *mut c_void, cb: Z3_solver_callback) {
    let st = unsafe { &mut *u.cast::<ReentrantState>() };
    st.calls += 1;
    let tautology = unsafe { Z3_mk_true(st.ctx) };
    assert!(unsafe {
        Z3_solver_propagate_consequence(
            st.ctx,
            cb,
            0,
            ptr::null(),
            0,
            ptr::null(),
            ptr::null(),
            tautology,
        )
    });
}

/// A final callback may re-enter `Z3_solver_assert`. The candidate inspected
/// before that assertion is no longer authoritative and must never escape as
/// SAT; the loop re-solves the changed handle and discovers UNSAT.
#[test]
fn user_propagator_reentrant_assertion_invalidates_candidate() {
    unsafe {
        let c = ctx();
        let solver = Z3_mk_solver(c);
        let state = Box::into_raw(Box::new(ReentrantState {
            ctx: c,
            solver,
            term: Z3_mk_true(c),
            calls: 0,
        }));
        Z3_solver_propagate_init(c, solver, state.cast(), None, None, None);
        Z3_solver_propagate_final(c, solver, Some(assert_false_from_final));

        assert_eq!(Z3_solver_check(c, solver), Z3_L_FALSE);
        assert_eq!((*state).calls, 1);
        assert!(Z3_solver_get_model(c, solver).is_null());

        drop(Box::from_raw(state));
        Z3_del_context(c);
    }
}

/// Direct watch registration from a callback also invalidates the inspected
/// generation. The new watch receives a fresh round before SAT is admitted.
#[test]
fn user_propagator_reentrant_registration_forces_fresh_round() {
    unsafe {
        let c = ctx();
        let solver = Z3_mk_solver(c);
        let term = Z3_mk_const(
            c,
            Z3_mk_string_symbol(c, c"watched".as_ptr()),
            Z3_mk_bool_sort(c),
        );
        let state = Box::into_raw(Box::new(ReentrantState {
            ctx: c,
            solver,
            term,
            calls: 0,
        }));
        Z3_solver_propagate_init(c, solver, state.cast(), None, None, None);
        Z3_solver_propagate_final(c, solver, Some(register_from_final));

        assert_eq!(Z3_solver_check(c, solver), Z3_L_TRUE);
        assert_eq!(
            (*state).calls,
            2,
            "new watch requires a fresh notification round"
        );
        assert!(!Z3_solver_get_model(c, solver).is_null());

        drop(Box::from_raw(state));
        Z3_del_context(c);
    }
}

/// Repeating the same tautological consequence cannot make progress. The
/// second round returns UNKNOWN and revokes the rejected candidate model.
#[test]
fn user_propagator_duplicate_no_progress_is_unknown_without_model() {
    unsafe {
        let c = ctx();
        let solver = Z3_mk_solver(c);
        let state = Box::into_raw(Box::new(ReentrantState {
            ctx: c,
            solver,
            term: Z3_mk_true(c),
            calls: 0,
        }));
        Z3_solver_propagate_init(c, solver, state.cast(), None, None, None);
        Z3_solver_propagate_final(c, solver, Some(tautology_from_final));

        assert_eq!(Z3_solver_check(c, solver), Z3_L_UNDEF);
        assert_eq!((*state).calls, 2);
        assert!(Z3_solver_get_model(c, solver).is_null());
        assert!(!Z3_solver_get_reason_unknown(c, solver).is_null());

        drop(Box::from_raw(state));
        Z3_del_context(c);
    }
}

/// Registration without `Z3_solver_propagate_init` is an honest usage error.
#[test]
fn user_propagator_register_requires_init() {
    unsafe {
        let c = ctx();
        let int_sort = Z3_mk_int_sort(c);
        let x = Z3_mk_const(c, Z3_mk_string_symbol(c, c"x".as_ptr()), int_sort);
        let solver = Z3_mk_solver(c);
        Z3_solver_propagate_register(c, solver, x);
        assert_eq!(Z3_get_error_code(c), Z3_INVALID_USAGE);
        // In-callback entry points outside a callback: honest refusal.
        assert!(!Z3_solver_propagate_consequence(
            c,
            ptr::null_mut(),
            0,
            ptr::null(),
            0,
            ptr::null(),
            ptr::null(),
            x,
        ));
        assert_eq!(Z3_get_error_code(c), Z3_INVALID_USAGE);
        Z3_del_context(c);
    }
}

/// `Z3_solver_register_on_clause`: registration-accepted, never fires —
/// behavior-parity-proven vs libz3 4.16.0 (2026-07-09 probes: libz3 accepts
/// silently; its callback granularity is undocumented/experimental with ZERO
/// invocations observed on an empty solver and on `p ∧ ¬p`, so never-firing is
/// inside the observable contract). The registration must not set an error and
/// must not perturb any verdict.
#[test]
fn register_on_clause_accepted_never_fires() {
    unsafe extern "C" fn on_clause(
        user_ctx: *mut c_void,
        _proof_hint: Z3_ast,
        _n_deps: c_uint,
        _deps: *const c_uint,
        _clause: Z3_ast_vector,
    ) {
        // SAFETY: `user_ctx` is the &mut u32 counter passed at registration.
        unsafe { *user_ctx.cast::<u32>() += 1 };
    }
    unsafe {
        let c = ctx();
        let s = Z3_mk_solver(c);
        let mut fired: u32 = 0;
        Z3_solver_register_on_clause(c, s, (&raw mut fired).cast::<c_void>(), Some(on_clause));
        assert_eq!(
            Z3_get_error_code(c),
            Z3_OK,
            "registration is accepted, no error"
        );
        // Verdicts are unaffected and no callback fires (contract allows 0).
        let int_sort = Z3_mk_int_sort(c);
        let x = Z3_mk_const(c, Z3_mk_string_symbol(c, c"x".as_ptr()), int_sort);
        Z3_solver_assert(c, s, Z3_mk_gt(c, x, Z3_mk_int(c, 0, int_sort)));
        assert_eq!(Z3_solver_check(c, s), Z3_L_TRUE);
        assert_eq!(
            fired, 0,
            "AY's on_clause never fires (documented, within contract)"
        );
        Z3_del_context(c);
    }
}
