// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use std::{ffi::c_void, ptr};

use super::ctx;
use crate::z3_compat::{
    Z3_ast, Z3_context, Z3_del_context, Z3_mk_bool_sort, Z3_mk_const, Z3_mk_false, Z3_mk_solver,
    Z3_mk_string_symbol, Z3_mk_true, Z3_solver, Z3_solver_assert, Z3_solver_callback,
    Z3_solver_check, Z3_solver_get_model, Z3_solver_get_reason_unknown,
    Z3_solver_propagate_consequence, Z3_solver_propagate_final, Z3_solver_propagate_init,
    Z3_solver_propagate_register, Z3_L_FALSE, Z3_L_TRUE, Z3_L_UNDEF,
};

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
