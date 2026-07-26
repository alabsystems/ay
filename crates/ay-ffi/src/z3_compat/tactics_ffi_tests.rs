// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for the Z3-compatible tactic C API (`tactics.rs`).
//!
//! Coverage:
//! - `Z3_mk_tactic("elim-and")` builds a non-null handle.
//! - An UNKNOWN tactic name (and the Z3-nonexistent "flatten-and") returns NULL
//!   and sets `Z3_INVALID_ARG` (honest).
//! - `Z3_tactic_and_then` / `Z3_tactic_or_else` compose; null operands error.
//! - SOUNDNESS / EQUIVALENCE: a tactic-solver gives the SAME verdict as a plain
//!   solver on sat and unsat goals with nested ANDs, and produces a valid model.
//! - The tactic actually flattens the goal before solving.

use super::super::*;
use std::ffi::{CStr, CString};
use std::os::raw::c_uint;
use std::ptr::{addr_of_mut, null, null_mut};

/// Build the nested-AND goal `(and (and a b) c)` (all Bool consts) and assert it
/// on the given solver via the context. Returns the three const ASTs.
///
/// # Safety
/// `ctx`/`s` must be valid handles allocated by this test module.
unsafe fn assert_nested_and_sat(ctx: Z3_context, s: Z3_solver) -> (Z3_ast, Z3_ast, Z3_ast) {
    // SAFETY: forwarded under the caller's contract; all handles are valid and
    // owned by the calling test.
    unsafe {
        let bs = Z3_mk_bool_sort(ctx);
        let a = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, c"a".as_ptr()), bs);
        let b = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, c"b".as_ptr()), bs);
        let c = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, c"c".as_ptr()), bs);
        let inner_args = [a, b];
        let inner = Z3_mk_and(ctx, 2, inner_args.as_ptr());
        let outer_args = [inner, c];
        let outer = Z3_mk_and(ctx, 2, outer_args.as_ptr());
        Z3_solver_assert(ctx, s, outer);
        (a, b, c)
    }
}

/// `Z3_mk_tactic("elim-and")` yields a non-null handle with Z3_OK.
#[test]
fn test_tactic_mk_elim_and_ok() {
    // SAFETY: all handles allocated/freed within this block; single-threaded.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let t = Z3_mk_tactic(ctx, c"elim-and".as_ptr());
        assert!(!t.is_null(), "elim-and tactic should be non-null");
        assert_eq!(Z3_get_error_code(ctx), Z3_OK);

        Z3_del_context(ctx);
    }
}

/// The full shared real-Z3 name set builds; `flatten-and` (not a Z3 tactic) and
/// unknown names are honestly rejected with NULL + Z3_INVALID_ARG.
#[test]
fn test_tactic_shared_name_set_matches_z3() {
    // SAFETY: all handles allocated/freed within this block; single-threaded.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        for name in [
            c"skip".as_ptr(),
            c"simplify".as_ptr(),
            c"solve-eqs".as_ptr(),
            c"propagate-values".as_ptr(),
            c"elim-and".as_ptr(),
            c"qe-light".as_ptr(),
            c"nnf".as_ptr(),
            c"tseitin-cnf".as_ptr(),
            c"bit-blast".as_ptr(),
        ] {
            let t = Z3_mk_tactic(ctx, name);
            assert!(!t.is_null(), "real z3 tactic name should build");
            assert_eq!(Z3_get_error_code(ctx), Z3_OK);
        }

        // `flatten-and` is NOT a real z3 tactic; reject it exactly like z3 does.
        let bad = Z3_mk_tactic(ctx, c"flatten-and".as_ptr());
        assert!(
            bad.is_null(),
            "flatten-and is not a z3 tactic; must be NULL"
        );
        assert_eq!(Z3_get_error_code(ctx), Z3_INVALID_ARG);

        // `cnf` is not a Z3 5.0.0 tactic (the real name is `tseitin-cnf`).
        let bad = Z3_mk_tactic(ctx, c"cnf".as_ptr());
        assert!(bad.is_null(), "cnf is not a Z3 5.0.0 tactic");
        assert_eq!(Z3_get_error_code(ctx), Z3_INVALID_ARG);

        Z3_del_context(ctx);
    }
}

/// An unknown tactic name returns NULL and sets Z3_INVALID_ARG (HONEST: never a
/// silent no-op pretending to be the requested tactic).
#[test]
fn test_tactic_unknown_name_is_honest_error() {
    // SAFETY: see above.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let t = Z3_mk_tactic(ctx, c"definitely-not-a-real-tactic".as_ptr());
        assert!(t.is_null(), "unknown tactic name must return NULL");
        assert_eq!(
            Z3_get_error_code(ctx),
            Z3_INVALID_ARG,
            "unknown tactic name must set Z3_INVALID_ARG"
        );

        // A null name is likewise rejected.
        let t2 = Z3_mk_tactic(ctx, null());
        assert!(t2.is_null());
        assert_eq!(Z3_get_error_code(ctx), Z3_INVALID_ARG);

        Z3_del_context(ctx);
    }
}

/// `Z3_tactic_and_then` / `Z3_tactic_or_else` compose; null operands error.
#[test]
fn test_tactic_combinators() {
    // SAFETY: see above.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let t1 = Z3_mk_tactic(ctx, c"elim-and".as_ptr());
        let t2 = Z3_mk_tactic(ctx, c"elim-and".as_ptr());
        assert!(!t1.is_null() && !t2.is_null());

        let andthen = Z3_tactic_and_then(ctx, t1, t2);
        assert!(!andthen.is_null(), "and_then should compose");
        assert_eq!(Z3_get_error_code(ctx), Z3_OK);

        let orelse = Z3_tactic_or_else(ctx, t1, t2);
        assert!(!orelse.is_null(), "or_else should compose");
        assert_eq!(Z3_get_error_code(ctx), Z3_OK);

        // Nested composition is also fine.
        let nested = Z3_tactic_and_then(ctx, andthen, orelse);
        assert!(!nested.is_null());

        // Null operand -> NULL + Z3_INVALID_ARG.
        let bad = Z3_tactic_and_then(ctx, t1, null_mut());
        assert!(bad.is_null());
        assert_eq!(Z3_get_error_code(ctx), Z3_INVALID_ARG);

        Z3_del_context(ctx);
    }
}

/// inc_ref/dec_ref are bookkeeping no-ops and never crash.
#[test]
fn test_tactic_inc_dec_ref_noop() {
    // SAFETY: see above.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let t = Z3_mk_tactic(ctx, c"elim-and".as_ptr());
        Z3_tactic_inc_ref(ctx, t);
        Z3_tactic_inc_ref(ctx, t);
        Z3_tactic_dec_ref(ctx, t);
        Z3_tactic_dec_ref(ctx, t);
        // Extra dec is still a no-op (no early free, no error fabrication).
        Z3_tactic_dec_ref(ctx, t);
        assert_eq!(Z3_get_error_code(ctx), Z3_OK);

        Z3_del_context(ctx);
    }
}

/// SOUNDNESS: an elim-and solver and a plain solver give the SAME SAT verdict
/// on a nested-AND goal, and the tactic-solver yields a usable model.
#[test]
fn test_tactic_solver_matches_plain_solver_sat() {
    // SAFETY: see above.
    unsafe {
        // Plain baseline.
        let cfg_b = Z3_mk_config();
        let ctx_b = Z3_mk_context(cfg_b);
        Z3_del_config(cfg_b);
        let s_b = Z3_mk_solver(ctx_b);
        let _ = assert_nested_and_sat(ctx_b, s_b);
        let base = Z3_solver_check(ctx_b, s_b);
        assert_eq!(base, Z3_L_TRUE);
        Z3_del_context(ctx_b);

        // Tactic path.
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);
        let t = Z3_mk_tactic(ctx, c"elim-and".as_ptr());
        let s = Z3_mk_solver_from_tactic(ctx, t);
        assert!(!s.is_null());
        let (a, _b, _c) = assert_nested_and_sat(ctx, s);
        let res = Z3_solver_check(ctx, s);
        assert_eq!(res, base, "tactic verdict must equal baseline verdict");

        // Model is usable and valid: a must evaluate to true (the only model of
        // (and (and a b) c) sets all three true).
        let model = Z3_solver_get_model(ctx, s);
        assert!(
            !model.is_null(),
            "tactic-solver must produce a model on SAT"
        );
        let mut va: Z3_ast = 0;
        let ok = Z3_model_eval(ctx, model, a, true, addr_of_mut!(va));
        assert!(ok);
        assert_eq!(Z3_get_bool_value(ctx, va), Z3_L_TRUE);

        Z3_del_context(ctx);
    }
}

/// SOUNDNESS: an elim-and solver and a plain solver give the SAME UNSAT
/// verdict on a contradictory nested-AND goal.
#[test]
fn test_tactic_solver_matches_plain_solver_unsat() {
    // SAFETY: see above.
    unsafe {
        // (and (and a (not a)) b) — UNSAT.
        let build = |ctx: Z3_context, s: Z3_solver| {
            let bs = Z3_mk_bool_sort(ctx);
            let a = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, c"a".as_ptr()), bs);
            let b = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, c"b".as_ptr()), bs);
            let na = Z3_mk_not(ctx, a);
            let inner_args = [a, na];
            let inner = Z3_mk_and(ctx, 2, inner_args.as_ptr());
            let outer_args = [inner, b];
            let outer = Z3_mk_and(ctx, 2, outer_args.as_ptr());
            Z3_solver_assert(ctx, s, outer);
        };

        let cfg_b = Z3_mk_config();
        let ctx_b = Z3_mk_context(cfg_b);
        Z3_del_config(cfg_b);
        let s_b = Z3_mk_solver(ctx_b);
        build(ctx_b, s_b);
        let base = Z3_solver_check(ctx_b, s_b);
        assert_eq!(base, Z3_L_FALSE);
        Z3_del_context(ctx_b);

        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);
        let t = Z3_mk_tactic(ctx, c"elim-and".as_ptr());
        let s = Z3_mk_solver_from_tactic(ctx, t);
        build(ctx, s);
        let res = Z3_solver_check(ctx, s);
        assert_eq!(
            res, base,
            "tactic verdict must equal baseline UNSAT verdict"
        );

        Z3_del_context(ctx);
    }
}

/// SOUNDNESS: `Z3_mk_solver_from_tactic("propagate-values")` runs the goal-mode
/// value-propagation pass (`apply_goal`) on the LIVE check-sat path — it must
/// give the SAME verdicts as a plain solver, and on SAT its model must satisfy
/// the ORIGINAL assertions (apply_goal drops true-folded conjuncts, so this
/// holds only because the transform is equivalence-preserving, not merely
/// equisatisfiable).
#[test]
fn test_propagate_values_solver_from_tactic_matches_plain_verdicts() {
    // SAFETY: all handles allocated/freed within this block; single-threaded.
    unsafe {
        // SAT: p ∧ (¬p ∨ q). propagate-values harvests p ↦ true, folds the
        // clause to q, and drops nothing it should not: the only model sets
        // p = q = true.
        let build_sat = |ctx: Z3_context, s: Z3_solver| {
            let bs = Z3_mk_bool_sort(ctx);
            let p = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, c"p".as_ptr()), bs);
            let q = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, c"q".as_ptr()), bs);
            let np = Z3_mk_not(ctx, p);
            let or_args = [np, q];
            let clause = Z3_mk_or(ctx, 2, or_args.as_ptr());
            Z3_solver_assert(ctx, s, p);
            Z3_solver_assert(ctx, s, clause);
            (p, q)
        };
        // UNSAT: p ∧ (¬p ∨ q) ∧ ¬q — the goal-mode pass folds this to false.
        let build_unsat = |ctx: Z3_context, s: Z3_solver| {
            let (_p, q) = build_sat(ctx, s);
            let nq = Z3_mk_not(ctx, q);
            Z3_solver_assert(ctx, s, nq);
        };

        // SAT case: baseline vs tactic solver.
        let cfg_b = Z3_mk_config();
        let ctx_b = Z3_mk_context(cfg_b);
        Z3_del_config(cfg_b);
        let s_b = Z3_mk_solver(ctx_b);
        let _ = build_sat(ctx_b, s_b);
        assert_eq!(Z3_solver_check(ctx_b, s_b), Z3_L_TRUE);
        Z3_del_context(ctx_b);

        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);
        let t = Z3_mk_tactic(ctx, c"propagate-values".as_ptr());
        let s = Z3_mk_solver_from_tactic(ctx, t);
        assert!(!s.is_null());
        let (p, q) = build_sat(ctx, s);
        assert_eq!(
            Z3_solver_check(ctx, s),
            Z3_L_TRUE,
            "propagate-values tactic-solver must preserve the SAT verdict"
        );
        // MODEL VALIDITY against the ORIGINAL assertions: p and q must both be
        // true (the sole model of p ∧ (¬p ∨ q) restricted to {p, q}).
        let model = Z3_solver_get_model(ctx, s);
        assert!(
            !model.is_null(),
            "tactic-solver must produce a model on SAT"
        );
        for (name, ast) in [("p", p), ("q", q)] {
            let mut v: Z3_ast = 0;
            let ok = Z3_model_eval(ctx, model, ast, true, addr_of_mut!(v));
            assert!(ok, "model_eval({name}) must succeed");
            assert_eq!(
                Z3_get_bool_value(ctx, v),
                Z3_L_TRUE,
                "the model must satisfy the ORIGINAL assertions: {name} = true"
            );
        }
        Z3_del_context(ctx);

        // UNSAT case: baseline vs tactic solver.
        let cfg_b = Z3_mk_config();
        let ctx_b = Z3_mk_context(cfg_b);
        Z3_del_config(cfg_b);
        let s_b = Z3_mk_solver(ctx_b);
        build_unsat(ctx_b, s_b);
        assert_eq!(Z3_solver_check(ctx_b, s_b), Z3_L_FALSE);
        Z3_del_context(ctx_b);

        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);
        let t = Z3_mk_tactic(ctx, c"propagate-values".as_ptr());
        let s = Z3_mk_solver_from_tactic(ctx, t);
        build_unsat(ctx, s);
        assert_eq!(
            Z3_solver_check(ctx, s),
            Z3_L_FALSE,
            "propagate-values tactic-solver must preserve the UNSAT verdict"
        );
        Z3_del_context(ctx);
    }
}

/// SOUNDNESS: a `tseitin-cnf` tactic-solver gives the SAME verdict as a plain
/// solver on a non-CNF (DNF) SAT goal and on an iff-based UNSAT goal, even though
/// the CNF introduces fresh aux variables (equisatisfiable, not equivalent).
#[test]
fn test_tseitin_cnf_solver_matches_plain_solver_verdicts() {
    // SAFETY: all handles allocated/freed within this block; single-threaded.
    unsafe {
        // (or (and a b) c) — SAT (non-CNF: a conjunction under a disjunction).
        let build_sat = |ctx: Z3_context, s: Z3_solver| {
            let bs = Z3_mk_bool_sort(ctx);
            let a = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, c"a".as_ptr()), bs);
            let b = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, c"b".as_ptr()), bs);
            let c = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, c"c".as_ptr()), bs);
            let and_args = [a, b];
            let ab = Z3_mk_and(ctx, 2, and_args.as_ptr());
            let or_args = [ab, c];
            let f = Z3_mk_or(ctx, 2, or_args.as_ptr());
            Z3_solver_assert(ctx, s, f);
        };
        // (= (or a b) (and (not a) (not b))) — an iff between complements, UNSAT.
        // Genuinely exercises tseitin's iff + and + or gates (no pre-simplify).
        let build_unsat = |ctx: Z3_context, s: Z3_solver| {
            let bs = Z3_mk_bool_sort(ctx);
            let a = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, c"a".as_ptr()), bs);
            let b = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, c"b".as_ptr()), bs);
            let or_args = [a, b];
            let ab = Z3_mk_or(ctx, 2, or_args.as_ptr());
            let na = Z3_mk_not(ctx, a);
            let nb = Z3_mk_not(ctx, b);
            let nand_args = [na, nb];
            let nanb = Z3_mk_and(ctx, 2, nand_args.as_ptr());
            let f = Z3_mk_eq(ctx, ab, nanb);
            Z3_solver_assert(ctx, s, f);
        };

        for (build, expected) in [
            (&build_sat as &dyn Fn(Z3_context, Z3_solver), Z3_L_TRUE),
            (&build_unsat as &dyn Fn(Z3_context, Z3_solver), Z3_L_FALSE),
        ] {
            // Baseline: plain solver.
            let cfg_b = Z3_mk_config();
            let ctx_b = Z3_mk_context(cfg_b);
            Z3_del_config(cfg_b);
            let s_b = Z3_mk_solver(ctx_b);
            build(ctx_b, s_b);
            let base = Z3_solver_check(ctx_b, s_b);
            assert_eq!(base, expected, "baseline verdict");
            Z3_del_context(ctx_b);

            // tseitin-cnf tactic solver.
            let cfg = Z3_mk_config();
            let ctx = Z3_mk_context(cfg);
            Z3_del_config(cfg);
            let t = Z3_mk_tactic(ctx, c"tseitin-cnf".as_ptr());
            assert!(!t.is_null(), "tseitin-cnf tactic must build");
            let s = Z3_mk_solver_from_tactic(ctx, t);
            build(ctx, s);
            let res = Z3_solver_check(ctx, s);
            assert_eq!(
                res, base,
                "tseitin-cnf tactic verdict must equal the baseline verdict"
            );
            Z3_del_context(ctx);
        }
    }
}

/// SOUNDNESS: a `bit-blast` solver-from-tactic gives the SAME verdict as a plain
/// solver on a QF_BV goal — the tactic rewrites the bit-vector goal to a pure
/// Boolean one and solves THAT, so agreement is a genuine equisatisfiability
/// check over the C API (`ayz3` Tactic('bit-blast')).
#[test]
fn test_bit_blast_tactic_solver_matches_plain_solver_qf_bv() {
    // SAFETY: all handles allocated/freed within this block; single-threaded.
    unsafe {
        // x = x + 1 over BitVec 4 — UNSAT (increment has no fixpoint).
        let build_unsat = |ctx: Z3_context, s: Z3_solver| {
            let bv = Z3_mk_bv_sort(ctx, 4);
            let x = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, c"x".as_ptr()), bv);
            let one = Z3_mk_int64(ctx, 1, bv);
            let inc = Z3_mk_bvadd(ctx, x, one);
            let eq = Z3_mk_eq(ctx, x, inc);
            Z3_solver_assert(ctx, s, eq);
        };
        // x < y — SAT.
        let build_sat = |ctx: Z3_context, s: Z3_solver| {
            let bv = Z3_mk_bv_sort(ctx, 4);
            let x = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, c"x".as_ptr()), bv);
            let y = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, c"y".as_ptr()), bv);
            let lt = Z3_mk_bvult(ctx, x, y);
            Z3_solver_assert(ctx, s, lt);
        };

        let cases: [(&dyn Fn(Z3_context, Z3_solver), _); 2] =
            [(&build_unsat, Z3_L_FALSE), (&build_sat, Z3_L_TRUE)];
        for (build, expected) in cases {
            // Plain baseline.
            let cfg_b = Z3_mk_config();
            let ctx_b = Z3_mk_context(cfg_b);
            Z3_del_config(cfg_b);
            let s_b = Z3_mk_solver(ctx_b);
            build(ctx_b, s_b);
            let base = Z3_solver_check(ctx_b, s_b);
            assert_eq!(base, expected, "baseline verdict");
            Z3_del_context(ctx_b);

            // bit-blast tactic path.
            let cfg = Z3_mk_config();
            let ctx = Z3_mk_context(cfg);
            Z3_del_config(cfg);
            let t = Z3_mk_tactic(ctx, c"bit-blast".as_ptr());
            assert!(!t.is_null(), "bit-blast tactic should build");
            let s = Z3_mk_solver_from_tactic(ctx, t);
            build(ctx, s);
            let res = Z3_solver_check(ctx, s);
            assert_eq!(res, base, "bit-blast verdict must equal baseline verdict");
            Z3_del_context(ctx);
        }
    }
}

/// HONESTY: a `bit-blast` solver-from-tactic on an OUT-OF-FRAGMENT goal
/// (`bvudiv`) signals failure at check time — it returns `Z3_L_UNDEF` and sets a
/// non-OK error code — rather than silently solving the untransformed goal and
/// returning a definite verdict for a goal the tactic never blasted (matching
/// z3, whose `bit-blast` errors on `bvudiv`). This is the `ayz3` Tactic('bit-blast')
/// path: `Tactic('bit-blast').solver()` + `check()` raises.
#[test]
fn test_bit_blast_solver_from_tactic_fails_on_out_of_fragment() {
    // SAFETY: all handles allocated/freed within this block; single-threaded.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let t = Z3_mk_tactic(ctx, c"bit-blast".as_ptr());
        assert!(!t.is_null(), "bit-blast tactic should build");
        let s = Z3_mk_solver_from_tactic(ctx, t);
        assert!(!s.is_null());

        // (= (bvudiv x y) #b0001) — bvudiv is outside AY's bit-blast fragment.
        let bv = Z3_mk_bv_sort(ctx, 4);
        let x = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, c"x".as_ptr()), bv);
        let y = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, c"y".as_ptr()), bv);
        let div = Z3_mk_bvudiv(ctx, x, y);
        let one = Z3_mk_int64(ctx, 1, bv);
        let eq = Z3_mk_eq(ctx, div, one);
        Z3_solver_assert(ctx, s, eq);

        // The check must NOT return a definite verdict: the tactic honestly failed.
        let res = Z3_solver_check(ctx, s);
        assert_eq!(
            res, Z3_L_UNDEF,
            "bit-blast on an out-of-fragment goal must not return a definite verdict"
        );
        assert_ne!(
            Z3_get_error_code(ctx),
            Z3_OK,
            "an honest tactic failure must set a non-OK error code (ayz3 check() raises)"
        );

        Z3_del_context(ctx);
    }
}

/// The tactic actually flattens the goal: after a check, the solver's assertion
/// list holds the flattened conjuncts (3), not the single nested AND.
#[test]
fn test_tactic_solver_flattens_goal_before_solving() {
    // SAFETY: see above.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let t = Z3_mk_tactic(ctx, c"elim-and".as_ptr());
        let s = Z3_mk_solver_from_tactic(ctx, t);
        let _ = assert_nested_and_sat(ctx, s);

        // Before the check: one nested AND assertion.
        let before = Z3_solver_get_assertions(ctx, s);
        assert_eq!(
            Z3_ast_vector_size(ctx, before),
            1,
            "one AND goal before check"
        );

        let res = Z3_solver_check(ctx, s);
        assert_eq!(res, Z3_L_TRUE);

        // After the check: flattened into 3 conjuncts.
        let after = Z3_solver_get_assertions(ctx, s);
        assert_eq!(
            Z3_ast_vector_size(ctx, after),
            3,
            "AND flattened into 3 assertions after the tactic ran"
        );

        Z3_del_context(ctx);
    }
}

/// `Z3_tactic_get_help` returns a non-null string naming the real z3 tactics.
#[test]
fn test_tactic_get_help() {
    // SAFETY: see above.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let help = Z3_tactic_get_help(ctx);
        assert!(!help.is_null());
        let s = CStr::from_ptr(help).to_string_lossy();
        assert!(s.contains("elim-and"), "help should name elim-and: {s}");
        assert!(s.contains("qe-light"), "help should name qe-light: {s}");
        // Never advertise the Z3-nonexistent alias.
        assert!(
            !s.contains("flatten-and"),
            "help must not advertise the non-z3 name flatten-and: {s}"
        );

        Z3_del_context(ctx);
    }
}

/// `Z3_mk_tactic("qe-light")` yields a non-null handle with Z3_OK.
#[test]
fn test_tactic_mk_qe_light_ok() {
    // SAFETY: all handles allocated/freed within this block; single-threaded.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let t = Z3_mk_tactic(ctx, c"qe-light".as_ptr());
        assert!(!t.is_null(), "qe-light tactic should be non-null");
        assert_eq!(Z3_get_error_code(ctx), Z3_OK);

        Z3_del_context(ctx);
    }
}

/// Build `(exists ((x Int)) (and (x > y) (x < y + 10)))` on the given solver via
/// the context. Returns nothing; the goal is SAT (e.g. x = y+1).
///
/// # Safety
/// `ctx`/`s` must be valid handles allocated by this test module.
unsafe fn assert_eliminable_exists(ctx: Z3_context, s: Z3_solver) {
    // SAFETY: forwarded under the caller's contract; all handles owned by the
    // calling test.
    unsafe {
        let is = Z3_mk_int_sort(ctx);
        let x = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, c"x".as_ptr()), is);
        let y = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, c"y".as_ptr()), is);
        let ten = Z3_mk_numeral(ctx, c"10".as_ptr(), is);
        let add_args = [y, ten];
        let yp10 = Z3_mk_add(ctx, 2, add_args.as_ptr());
        let l1 = Z3_mk_gt(ctx, x, y);
        let l2 = Z3_mk_lt(ctx, x, yp10);
        let and_args = [l1, l2];
        let body = Z3_mk_and(ctx, 2, and_args.as_ptr());
        let bound = [x];
        let ex = Z3_mk_exists_const(ctx, 0, 1, bound.as_ptr(), 0, null(), body);
        assert!(ex != 0, "should build the existential");
        Z3_solver_assert(ctx, s, ex);
    }
}

/// The new bare tactic names (`fail`, `split-clause`) build via `Z3_mk_tactic`,
/// matching z3 (which has both).
#[test]
fn test_tactic_fail_and_split_clause_build() {
    // SAFETY: all handles allocated/freed within this block; single-threaded.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        for name in [c"fail".as_ptr(), c"split-clause".as_ptr()] {
            let t = Z3_mk_tactic(ctx, name);
            assert!(!t.is_null(), "bare z3 tactic name should build");
            assert_eq!(Z3_get_error_code(ctx), Z3_OK);
        }

        Z3_del_context(ctx);
    }
}

/// `Z3_tactic_repeat` composes; a null body errors. SOUNDNESS: a repeat(elim-and)
/// solver reproduces the plain verdict on a nested-AND goal.
#[test]
fn test_tactic_repeat_composes_and_matches_plain_solver() {
    // SAFETY: see above.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let inner = Z3_mk_tactic(ctx, c"elim-and".as_ptr());
        let rep = Z3_tactic_repeat(ctx, inner, 4);
        assert!(!rep.is_null(), "repeat should compose");
        assert_eq!(Z3_get_error_code(ctx), Z3_OK);

        // Null body -> NULL + Z3_INVALID_ARG.
        let bad = Z3_tactic_repeat(ctx, null_mut(), 4);
        assert!(bad.is_null());
        assert_eq!(Z3_get_error_code(ctx), Z3_INVALID_ARG);

        // SOUNDNESS: repeat(elim-and).solver() agrees with the plain verdict.
        let s = Z3_mk_solver_from_tactic(ctx, rep);
        assert!(!s.is_null());
        let _ = assert_nested_and_sat(ctx, s);
        assert_eq!(Z3_solver_check(ctx, s), Z3_L_TRUE);

        Z3_del_context(ctx);
    }
}

/// `Z3_tactic_using_params` / `Z3_tactic_with` return an equivalence-preserving
/// tactic (AY ignores shape-only params); a null body errors.
#[test]
fn test_tactic_using_params_is_equivalence_preserving() {
    // SAFETY: see above.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let inner = Z3_mk_tactic(ctx, c"simplify".as_ptr());
        let params = Z3_mk_params(ctx);
        let with = Z3_tactic_using_params(ctx, inner, params);
        assert!(!with.is_null(), "using-params should compose");
        assert_eq!(Z3_get_error_code(ctx), Z3_OK);

        // The alias behaves identically.
        let with2 = Z3_tactic_with(ctx, inner, params);
        assert!(!with2.is_null());

        // Null body -> NULL + Z3_INVALID_ARG.
        let bad = Z3_tactic_using_params(ctx, null_mut(), params);
        assert!(bad.is_null());
        assert_eq!(Z3_get_error_code(ctx), Z3_INVALID_ARG);

        // SOUNDNESS: the with-solver reproduces the plain verdict.
        let s = Z3_mk_solver_from_tactic(ctx, with);
        let _ = assert_nested_and_sat(ctx, s);
        assert_eq!(Z3_solver_check(ctx, s), Z3_L_TRUE);

        Z3_del_context(ctx);
    }
}

/// SOUNDNESS / EQUIVALENCE: a `qe-light` solver and a plain solver give the SAME
/// verdict on an in-fragment eliminable existential.
#[test]
fn test_tactic_qe_light_matches_plain_solver() {
    // SAFETY: see above.
    unsafe {
        // Plain baseline (quantified LIA decides the existential directly).
        let cfg_b = Z3_mk_config();
        let ctx_b = Z3_mk_context(cfg_b);
        Z3_del_config(cfg_b);
        let s_b = Z3_mk_solver(ctx_b);
        assert_eliminable_exists(ctx_b, s_b);
        let base = Z3_solver_check(ctx_b, s_b);
        assert_eq!(base, Z3_L_TRUE, "baseline existential should be SAT");
        Z3_del_context(ctx_b);

        // qe-light tactic path.
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);
        let t = Z3_mk_tactic(ctx, c"qe-light".as_ptr());
        let s = Z3_mk_solver_from_tactic(ctx, t);
        assert!(!s.is_null());
        assert_eliminable_exists(ctx, s);
        let res = Z3_solver_check(ctx, s);
        assert_eq!(res, base, "qe-light verdict must equal baseline verdict");

        Z3_del_context(ctx);
    }
}

// ===========================================================================
// Tactic-combinator completion: Z3_tactic_skip/_fail/_fail_if/
// _fail_if_not_decided/_when/_cond/_try_for/_par_and_then/_par_or/_get_descr/
// _get_param_descrs + Z3_tactic_apply_ex.
// ===========================================================================

/// Build a single-formula LIA goal `{(< 0 x)}` (undecided, is-qflia = true).
///
/// # Safety
/// `ctx` must be a valid context handle.
unsafe fn lia_goal(ctx: Z3_context) -> Z3_goal {
    // SAFETY: forwarded under the caller's contract.
    unsafe {
        let is = Z3_mk_int_sort(ctx);
        let x = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, c"x".as_ptr()), is);
        let zero = Z3_mk_int(ctx, 0, is);
        let lt = Z3_mk_lt(ctx, zero, x);
        let g = Z3_mk_goal(ctx, false, false, false);
        Z3_goal_assert(ctx, g, lt);
        g
    }
}

/// Build a clause goal `{(or a b)}` (size 1, split-clause yields 2 subgoals).
///
/// # Safety
/// `ctx` must be a valid context handle.
unsafe fn clause_goal(ctx: Z3_context) -> Z3_goal {
    // SAFETY: forwarded under the caller's contract.
    unsafe {
        let bs = Z3_mk_bool_sort(ctx);
        let a = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, c"a".as_ptr()), bs);
        let b = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, c"b".as_ptr()), bs);
        let args = [a, b];
        let or = Z3_mk_or(ctx, 2, args.as_ptr());
        let g = Z3_mk_goal(ctx, false, false, false);
        Z3_goal_assert(ctx, g, or);
        g
    }
}

/// Apply `t` to `g`; return `Some(num_subgoals)` on success, `None` on an honest
/// tactic failure (apply returns NULL + non-OK error).
///
/// # Safety
/// `ctx`/`t`/`g` must be valid handles.
unsafe fn apply_nsub(ctx: Z3_context, t: Z3_tactic, g: Z3_goal) -> Option<c_uint> {
    // SAFETY: forwarded under the caller's contract.
    unsafe {
        let r = Z3_tactic_apply(ctx, t, g);
        if r.is_null() || Z3_get_error_code(ctx) != Z3_OK {
            return None;
        }
        Some(Z3_apply_result_get_num_subgoals(ctx, r))
    }
}

/// `Z3_tactic_skip` is the identity and `Z3_tactic_fail` always fails when RUN.
#[test]
fn test_tactic_skip_and_fail_apply() {
    // SAFETY: all handles allocated/freed within this block; single-threaded.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let g = lia_goal(ctx);
        let skip = Z3_tactic_skip(ctx);
        assert!(!skip.is_null());
        assert_eq!(
            apply_nsub(ctx, skip, g),
            Some(1),
            "skip = one identity subgoal"
        );

        let fail = Z3_tactic_fail(ctx);
        assert!(!fail.is_null());
        assert_eq!(
            apply_nsub(ctx, fail, g),
            None,
            "fail must fail when applied"
        );
        assert_ne!(Z3_get_error_code(ctx), Z3_OK, "fail sets a non-OK error");

        Z3_del_context(ctx);
    }
}

/// `Z3_tactic_fail_if(p)` fails iff the probe HOLDS (libz3's real behavior).
#[test]
fn test_tactic_fail_if_gates_on_probe() {
    // SAFETY: see above.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let g = lia_goal(ctx);
        let qflia = Z3_mk_probe(ctx, c"is-qflia".as_ptr()); // TRUE on g
        let qfbv = Z3_mk_probe(ctx, c"is-qfbv".as_ptr()); // FALSE on g

        // probe TRUE -> fail.
        assert_eq!(apply_nsub(ctx, Z3_tactic_fail_if(ctx, qflia), g), None);
        // probe FALSE -> skip (identity).
        assert_eq!(apply_nsub(ctx, Z3_tactic_fail_if(ctx, qfbv), g), Some(1));

        // Null probe -> NULL + Z3_INVALID_ARG.
        let bad = Z3_tactic_fail_if(ctx, null_mut());
        assert!(bad.is_null());
        assert_eq!(Z3_get_error_code(ctx), Z3_INVALID_ARG);

        Z3_del_context(ctx);
    }
}

/// P3 batch N+1, review-pinned test (the silent-Skip hazard): on the C-API
/// path, `Z3_mk_tactic("diff-neq")` must BUILD (real z3 name), applying it
/// must FAIL honestly (NULL + non-OK error — z3 raises here too), and
/// `or-else(diff-neq, skip)` must fall through to the identity exactly like
/// z3's measured or-else routing. A `_ => Skip` regression in
/// `Tactic::from_apply` would turn the failure into a silent success and
/// break this test (and it is now a compile error as well).
#[test]
fn test_class_f_tactic_fails_and_or_else_falls_through_on_the_c_api_path() {
    // SAFETY: all handles allocated/freed within this block; single-threaded.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let g = lia_goal(ctx);
        let diff_neq = Z3_mk_tactic(ctx, c"diff-neq".as_ptr());
        assert!(
            !diff_neq.is_null(),
            "diff-neq is a real z3 tactic: must build"
        );
        assert_eq!(Z3_get_error_code(ctx), Z3_OK);
        assert_eq!(
            apply_nsub(ctx, diff_neq, g),
            None,
            "diff-neq must FAIL honestly on a generic goal (never a silent identity)"
        );
        assert_ne!(Z3_get_error_code(ctx), Z3_OK);

        // or-else falls through the honest failure to skip (identity).
        let skip = Z3_tactic_skip(ctx);
        let routed = Z3_tactic_or_else(ctx, diff_neq, skip);
        assert_eq!(
            apply_nsub(ctx, routed, g),
            Some(1),
            "(or-else diff-neq skip) must fall through to the identity like z3"
        );

        Z3_del_context(ctx);
    }
}

/// P3 batch N+1: `bv1-blast` on the C-API path is the identity on a BV-free
/// goal (z3 measured: SUCCESS, depth 1) and fails on a BV goal — so
/// `or-else(bv1-blast, X)` keeps branch 1 on BV-free goals exactly like z3.
#[test]
fn test_bv1_blast_conditional_realization_on_the_c_api_path() {
    // SAFETY: all handles allocated/freed within this block; single-threaded.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let bv1 = Z3_mk_tactic(ctx, c"bv1-blast".as_ptr());
        assert!(!bv1.is_null());

        // BV-free goal: success (one identity subgoal), like z3.
        let g = lia_goal(ctx);
        assert_eq!(apply_nsub(ctx, bv1, g), Some(1));

        // BV goal: honest failure, like z3's 'bv1 blaster cannot be applied'.
        let bvs = Z3_mk_bv_sort(ctx, 8);
        let b = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, c"b".as_ptr()), bvs);
        let one = Z3_mk_numeral(ctx, c"1".as_ptr(), bvs);
        let three = Z3_mk_numeral(ctx, c"3".as_ptr(), bvs);
        let sum = Z3_mk_bvadd(ctx, b, one);
        let eq = Z3_mk_eq(ctx, sum, three);
        let gb = Z3_mk_goal(ctx, false, false, false);
        Z3_goal_assert(ctx, gb, eq);
        assert_eq!(apply_nsub(ctx, bv1, gb), None);
        assert_ne!(Z3_get_error_code(ctx), Z3_OK);

        Z3_del_context(ctx);
    }
}

/// P3 batch N+1: every newly registered class has buildable names on the
/// C-API path, with honest per-name descriptions (registry lock-step is
/// enforced separately by `test_tactic_registry_enumeration` /
/// `test_tactic_get_descr`, which iterate the FULL registry).
#[test]
fn test_batch_names_build_and_describe_on_the_c_api_path() {
    // SAFETY: all handles allocated/freed within this block; single-threaded.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        for name in [
            c"qflia".as_ptr(),              // S
            c"smtfd".as_ptr(),              // S (timeout divergence documented)
            c"qe2".as_ptr(),                // A
            c"ctx-simplify".as_ptr(),       // A
            c"fpa2bv".as_ptr(),             // N
            c"subpaving".as_ptr(),          // N (measured divergence documented)
            c"collect-statistics".as_ptr(), // N (no stats block — documented)
            c"pb2bv".as_ptr(),              // F
            c"fail-if-undecided".as_ptr(),  // C
        ] {
            let t = Z3_mk_tactic(ctx, name);
            assert!(!t.is_null(), "batch tactic must build");
            assert_eq!(Z3_get_error_code(ctx), Z3_OK);
            let d = Z3_tactic_get_descr(ctx, name);
            assert!(!d.is_null(), "batch tactic must be described");
            let s = CStr::from_ptr(d).to_string_lossy();
            assert!(!s.is_empty());
        }

        // A solver built from a CLASS S tactic runs the REAL engine: sat/unsat
        // twins both decide (never a fabricated or stuck verdict).
        let qflia = Z3_mk_tactic(ctx, c"qflia".as_ptr());
        let s = Z3_mk_solver_from_tactic(ctx, qflia);
        assert!(!s.is_null());
        let is = Z3_mk_int_sort(ctx);
        let x = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, c"x".as_ptr()), is);
        let five = Z3_mk_int(ctx, 5, is);
        let three = Z3_mk_int(ctx, 3, is);
        Z3_solver_assert(ctx, s, Z3_mk_gt(ctx, x, five));
        assert_eq!(
            Z3_solver_check(ctx, s),
            Z3_L_TRUE,
            "sat twin must decide sat"
        );
        Z3_solver_assert(ctx, s, Z3_mk_lt(ctx, x, three));
        assert_eq!(
            Z3_solver_check(ctx, s),
            Z3_L_FALSE,
            "unsat twin must decide unsat"
        );

        Z3_del_context(ctx);
    }
}

/// `Z3_tactic_fail_if_not_decided` is the identity only on a trivially decided
/// goal (empty or containing `false`); it fails on an undecided goal.
#[test]
fn test_tactic_fail_if_not_decided() {
    // SAFETY: see above.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        // Undecided goal -> fail.
        let g = lia_goal(ctx);
        assert_eq!(apply_nsub(ctx, Z3_tactic_fail_if_not_decided(ctx), g), None);

        // Empty goal (decided-sat) -> identity.
        let ge = Z3_mk_goal(ctx, false, false, false);
        assert_eq!(
            apply_nsub(ctx, Z3_tactic_fail_if_not_decided(ctx), ge),
            Some(1)
        );

        // {false} (decided-unsat) -> identity.
        let gf = Z3_mk_goal(ctx, false, false, false);
        Z3_goal_assert(ctx, gf, Z3_mk_false(ctx));
        assert_eq!(
            apply_nsub(ctx, Z3_tactic_fail_if_not_decided(ctx), gf),
            Some(1)
        );

        Z3_del_context(ctx);
    }
}

/// `Z3_tactic_when` applies its body iff the probe holds; `Z3_tactic_cond` picks
/// the branch and PROPAGATES a chosen-branch failure (no fall-through).
#[test]
fn test_tactic_when_and_cond_run_the_right_branch() {
    // SAFETY: see above.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let gor = clause_goal(ctx);
        let qflia = Z3_mk_probe(ctx, c"is-qflia".as_ptr()); // TRUE on gor (prop subset)
                                                            // A probe that is FALSE on gor: has-quantifiers.
        let hasq = Z3_mk_probe(ctx, c"has-quantifiers".as_ptr()); // FALSE on gor

        let split = Z3_mk_tactic(ctx, c"split-clause".as_ptr());
        let skip = Z3_tactic_skip(ctx);
        let fail = Z3_tactic_fail(ctx);

        // when(TRUE, split) -> split runs (2 subgoals).
        assert_eq!(
            apply_nsub(ctx, Z3_tactic_when(ctx, qflia, split), gor),
            Some(2)
        );
        // when(FALSE, fail) -> skip (identity), NOT fail.
        assert_eq!(
            apply_nsub(ctx, Z3_tactic_when(ctx, hasq, fail), gor),
            Some(1)
        );

        // cond(TRUE, split, fail) -> split (2 subgoals).
        assert_eq!(
            apply_nsub(ctx, Z3_tactic_cond(ctx, qflia, split, fail), gor),
            Some(2)
        );
        // cond(FALSE, split, fail) -> fail branch, which PROPAGATES (no fallback).
        assert_eq!(
            apply_nsub(ctx, Z3_tactic_cond(ctx, hasq, fail, skip), gor),
            Some(1),
            "cond(false,...) runs the else branch (skip)"
        );
        // cond(TRUE, fail, skip) genuinely fails (does not fall through to skip).
        assert_eq!(
            apply_nsub(ctx, Z3_tactic_cond(ctx, qflia, fail, skip), gor),
            None,
            "cond(true, fail, skip) must propagate the fail branch"
        );

        // Null operands -> NULL + Z3_INVALID_ARG.
        assert!(Z3_tactic_when(ctx, qflia, null_mut()).is_null());
        assert_eq!(Z3_get_error_code(ctx), Z3_INVALID_ARG);
        assert!(Z3_tactic_cond(ctx, null_mut(), skip, skip).is_null());
        assert_eq!(Z3_get_error_code(ctx), Z3_INVALID_ARG);

        Z3_del_context(ctx);
    }
}

/// `Z3_tactic_try_for` behaves like its body (ay's passes always terminate), and
/// `Z3_tactic_par_and_then` / `Z3_tactic_par_or` compose sequentially with the
/// same result set as the parallel variants.
#[test]
fn test_tactic_try_for_and_parallel_variants() {
    // SAFETY: see above.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let gor = clause_goal(ctx);
        let split = Z3_mk_tactic(ctx, c"split-clause".as_ptr());
        let skip = Z3_tactic_skip(ctx);
        let fail = Z3_tactic_fail(ctx);

        // try_for(split, ms) runs split (2 subgoals).
        assert_eq!(
            apply_nsub(ctx, Z3_tactic_try_for(ctx, split, 5000), gor),
            Some(2)
        );

        // par_and_then(split, skip): split then skip on each subgoal -> 2 subgoals.
        assert_eq!(
            apply_nsub(ctx, Z3_tactic_par_and_then(ctx, split, skip), gor),
            Some(2)
        );

        // par_or: first success wins.
        let ts_fs = [fail, skip];
        assert_eq!(
            apply_nsub(ctx, Z3_tactic_par_or(ctx, 2, ts_fs.as_ptr()), gor),
            Some(1),
            "par_or(fail, skip) = skip"
        );
        let ts_ff = [fail, fail];
        assert_eq!(
            apply_nsub(ctx, Z3_tactic_par_or(ctx, 2, ts_ff.as_ptr()), gor),
            None,
            "par_or(fail, fail) fails"
        );

        // Honest errors: null operands / empty par_or.
        assert!(Z3_tactic_try_for(ctx, null_mut(), 1).is_null());
        assert_eq!(Z3_get_error_code(ctx), Z3_INVALID_ARG);
        assert!(Z3_tactic_par_and_then(ctx, skip, null_mut()).is_null());
        assert_eq!(Z3_get_error_code(ctx), Z3_INVALID_ARG);
        assert!(Z3_tactic_par_or(ctx, 0, null()).is_null());
        assert_eq!(Z3_get_error_code(ctx), Z3_INVALID_ARG);
        // Null element inside a non-empty array is also rejected.
        let ts_null = [skip, null_mut()];
        assert!(Z3_tactic_par_or(ctx, 2, ts_null.as_ptr()).is_null());
        assert_eq!(Z3_get_error_code(ctx), Z3_INVALID_ARG);

        Z3_del_context(ctx);
    }
}

/// `Z3_tactic_apply_ex` returns the SAME apply-result as `Z3_tactic_apply`
/// (params honestly ignored) and fails honestly on `fail`.
#[test]
fn test_tactic_apply_ex_matches_apply() {
    // SAFETY: see above.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let gor = clause_goal(ctx);
        let split = Z3_mk_tactic(ctx, c"split-clause".as_ptr());
        let params = Z3_mk_params(ctx);

        let r = Z3_tactic_apply_ex(ctx, split, gor, params);
        assert!(!r.is_null(), "apply_ex must produce a result");
        assert_eq!(Z3_get_error_code(ctx), Z3_OK);
        assert_eq!(
            Z3_apply_result_get_num_subgoals(ctx, r),
            2,
            "apply_ex(split-clause) yields the same 2 subgoals as apply"
        );

        // fail via apply_ex is still an honest failure.
        let fail = Z3_tactic_fail(ctx);
        let rf = Z3_tactic_apply_ex(ctx, fail, gor, params);
        assert!(rf.is_null(), "apply_ex(fail) must be NULL");
        assert_ne!(Z3_get_error_code(ctx), Z3_OK);

        Z3_del_context(ctx);
    }
}

/// `Z3_tactic_get_descr` returns a real per-name string; unknown -> NULL + error.
#[test]
fn test_tactic_get_descr() {
    // SAFETY: see above.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        for name in [
            c"skip".as_ptr(),
            c"fail".as_ptr(),
            c"simplify".as_ptr(),
            c"elim-and".as_ptr(),
            c"bit-blast".as_ptr(),
            c"split-clause".as_ptr(),
            // The transform batch (incl. the `cofactor-term-ite` alias).
            c"elim-term-ite".as_ptr(),
            c"blast-term-ite".as_ptr(),
            c"cofactor-term-ite".as_ptr(),
            c"der".as_ptr(),
            c"distribute-forall".as_ptr(),
            c"reduce-args".as_ptr(),
        ] {
            let d = Z3_tactic_get_descr(ctx, name);
            assert!(!d.is_null(), "known tactic name must have a description");
            let s = CStr::from_ptr(d).to_string_lossy();
            assert!(!s.is_empty(), "description must be a non-empty real string");
            assert_eq!(Z3_get_error_code(ctx), Z3_OK);
        }

        // Every buildable registry name must ALSO have a non-null description
        // (the two surfaces cannot drift): `Z3_mk_tactic` accepts it ⇒
        // `Z3_tactic_get_descr` describes it.
        for want in ay_frontend::SUPPORTED_TACTIC_NAMES {
            let cname = CString::new(*want)
                .expect("registered tactic name must not contain an interior NUL");
            let d = Z3_tactic_get_descr(ctx, cname.as_ptr());
            assert!(
                !d.is_null(),
                "registry tactic {want:?} must have a description"
            );
        }
        // The `cofactor-term-ite` alias is documented too.
        let cof = Z3_tactic_get_descr(ctx, c"cofactor-term-ite".as_ptr());
        assert!(!cof.is_null(), "cofactor-term-ite alias must be described");

        // Unknown name -> NULL + Z3_INVALID_ARG (honest).
        let bad = Z3_tactic_get_descr(ctx, c"not-a-real-tactic".as_ptr());
        assert!(bad.is_null());
        assert_eq!(Z3_get_error_code(ctx), Z3_INVALID_ARG);
        // `lift-if` is not a z3 tactic; no description (honest NULL).
        let lift_if = Z3_tactic_get_descr(ctx, c"lift-if".as_ptr());
        assert!(lift_if.is_null(), "lift-if is not a z3 tactic");
        let cnf = Z3_tactic_get_descr(ctx, c"cnf".as_ptr());
        assert!(cnf.is_null(), "cnf is not a Z3 5.0.0 tactic");

        Z3_del_context(ctx);
    }
}

/// `Z3_tactic_get_param_descrs` returns a REAL, queryable, HONEST-EMPTY descriptor
/// set (size 0) — never a fabricated parameter set. Null tactic -> NULL + error.
#[test]
fn test_tactic_get_param_descrs_honest_empty() {
    // SAFETY: see above.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let skip = Z3_tactic_skip(ctx);
        let pd = Z3_tactic_get_param_descrs(ctx, skip);
        assert!(
            !pd.is_null(),
            "param descrs handle must be a real (non-null) set"
        );
        assert_eq!(Z3_get_error_code(ctx), Z3_OK);
        assert_eq!(
            Z3_param_descrs_size(ctx, pd),
            0,
            "ay tactics expose no per-tactic params (honest empty)"
        );

        // Null tactic -> NULL + Z3_INVALID_ARG.
        let bad = Z3_tactic_get_param_descrs(ctx, null_mut());
        assert!(bad.is_null());
        assert_eq!(Z3_get_error_code(ctx), Z3_INVALID_ARG);

        Z3_del_context(ctx);
    }
}

/// Registry enumeration: `Z3_get_num_tactics` / `Z3_get_tactic_name` list
/// exactly AY's real registry ([`ay_frontend::SUPPORTED_TACTIC_NAMES`]), every
/// enumerated name is buildable via `Z3_mk_tactic`, and an out-of-range index
/// is an honest NULL + `Z3_INVALID_ARG`.
#[test]
fn test_tactic_registry_enumeration() {
    // SAFETY: all handles are allocated and freed within this test.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let n = Z3_get_num_tactics(ctx);
        assert_eq!(
            n as usize,
            ay_frontend::SUPPORTED_TACTIC_NAMES.len(),
            "enumerator must expose exactly the real registry"
        );
        for (i, want) in ay_frontend::SUPPORTED_TACTIC_NAMES.iter().enumerate() {
            let name = Z3_get_tactic_name(ctx, i as c_uint);
            assert!(!name.is_null(), "tactic name {i} must be non-null");
            let got = CStr::from_ptr(name)
                .to_str()
                .expect("enumerated tactic name must be valid UTF-8");
            assert_eq!(got, *want, "name {i} must match the registry");
            // Every enumerated name is REAL: Z3_mk_tactic accepts it.
            let cname = CString::new(*want)
                .expect("registered tactic name must not contain an interior NUL");
            let t = Z3_mk_tactic(ctx, cname.as_ptr());
            assert!(!t.is_null(), "enumerated tactic {got} must be buildable");
        }
        // Out of range: honest NULL + INVALID_ARG.
        assert!(Z3_get_tactic_name(ctx, n).is_null());
        assert_eq!(Z3_get_error_code(ctx), Z3_INVALID_ARG);

        Z3_del_context(ctx);
    }
}
