// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Battery for the P3 C-API stub completion (wavec-p3-capi-stubs):
//!
//! * GAP 1 — `Z3_sort_to_ast` / `Z3_func_decl_to_ast` tagged, value-canonical
//!   handles; the `ast_to_term` poison guard (a tagged handle in a
//!   term-consuming entry point must FAIL CLOSED, never alias a real term —
//!   the wrong-verdict channel this work closes).
//! * GAP 2 — `Z3_global_param_set/get/reset_all` measured z3 4.15.4 parity.
//! * GAP 3 — `Z3_get_error_msg` canonical strings + override-all semantics.
//! * GAP 4 hardening — `Z3_mk_map` sort gate + name-signature registry.
//!
//! Every parity claim below was measured against real z3 4.15.4
//! (`/opt/homebrew/lib/libz3.dylib`) on 2026-07-18.

use std::ffi::{c_char, CStr};
use std::ptr;

use super::super::*;

unsafe fn ctx() -> Z3_context {
    unsafe {
        let cfg = Z3_mk_config();
        let c = Z3_mk_context(cfg);
        Z3_del_config(cfg);
        c
    }
}

unsafe fn cstr<'a>(p: *const c_char) -> &'a str {
    assert!(!p.is_null(), "expected a non-null string");
    unsafe { CStr::from_ptr(p) }.to_str().unwrap()
}

// ============================================================================
// GAP 1: sort/decl AST handles
// ============================================================================

#[test]
fn sort_to_ast_is_canonical_and_introspectable() {
    unsafe {
        let c = ctx();
        let int1 = Z3_mk_int_sort(c);
        let int2 = Z3_mk_int_sort(c);
        let a1 = Z3_sort_to_ast(c, int1);
        let a2 = Z3_sort_to_ast(c, int2);
        assert_ne!(a1, 0);
        // Value-canonical: two handles of the SAME semantic sort mint the
        // SAME ast (z3 parity: hash-consed sorts, Z3_is_eq_ast true).
        assert_eq!(a1, a2);
        assert!(Z3_is_eq_ast(c, a1, a2));
        assert_eq!(Z3_get_ast_id(c, a1), Z3_get_ast_id(c, a2));
        assert_eq!(Z3_get_ast_hash(c, a1), Z3_get_ast_hash(c, a2));
        // z3 bands sort-ast ids with the high bit (measured 0x8000000B for
        // Int); AY mirrors the banding.
        assert_eq!(Z3_get_ast_id(c, a1) & 0x8000_0000, 0x8000_0000);
        // Kind 4 = Z3_SORT_AST (measured).
        assert_eq!(Z3_get_ast_kind(c, a1), Z3_SORT_AST);
        // Exact z3 4.15.4 renderings.
        assert_eq!(cstr(Z3_ast_to_string(c, a1)), "Int");
        let bv8 = Z3_mk_bv_sort(c, 8);
        assert_eq!(
            cstr(Z3_ast_to_string(c, Z3_sort_to_ast(c, bv8))),
            "(_ BitVec 8)"
        );
        let arr = Z3_mk_array_sort(c, Z3_mk_int_sort(c), Z3_mk_int_sort(c));
        assert_eq!(
            cstr(Z3_ast_to_string(c, Z3_sort_to_ast(c, arr))),
            "(Array Int Int)"
        );
        // Distinct sorts → distinct asts.
        assert_ne!(Z3_sort_to_ast(c, bv8), a1);
        // Null sort → null ast (pre-existing pin).
        assert_eq!(Z3_sort_to_ast(c, ptr::null_mut()), 0);
        Z3_del_context(c);
    }
}

#[test]
fn func_decl_to_ast_is_canonical_and_round_trips() {
    unsafe {
        let c = ctx();
        let int = Z3_mk_int_sort(c);
        let arr = Z3_mk_array_sort(c, int, int);
        let bv8 = Z3_mk_bv_sort(c, 8);
        let sym = Z3_mk_string_symbol(c, c"f".as_ptr());
        let mut dom = [int, arr];
        let f1 = Z3_mk_func_decl(c, sym, 2, dom.as_mut_ptr(), bv8);
        let f2 = Z3_mk_func_decl(c, sym, 2, dom.as_mut_ptr(), bv8);
        assert_ne!(f1, f2, "AY does not hash-cons decl handles (precondition)");
        let a1 = Z3_func_decl_to_ast(c, f1);
        let a2 = Z3_func_decl_to_ast(c, f2);
        assert_ne!(a1, 0);
        // Same name/signature through DIFFERENT pointers → same canonical ast
        // (z3 parity: z3 hash-conses mk_func_decl, so its asts are eq too).
        assert_eq!(a1, a2);
        assert!(Z3_is_eq_ast(c, a1, a2));
        // Kind 5 = Z3_FUNC_DECL_AST; id banded (measured).
        assert_eq!(Z3_get_ast_kind(c, a1), Z3_FUNC_DECL_AST);
        assert_eq!(Z3_get_ast_id(c, a1) & 0xC000_0000, 0xC000_0000);
        // Exact z3 4.15.4 rendering.
        assert_eq!(
            cstr(Z3_ast_to_string(c, a1)),
            "(declare-fun f (Int (Array Int Int)) (_ BitVec 8))"
        );
        // Nullary decl rendering (measured).
        let c0 = Z3_mk_func_decl(
            c,
            Z3_mk_string_symbol(c, c"c".as_ptr()),
            0,
            ptr::null_mut(),
            int,
        );
        assert_eq!(
            cstr(Z3_ast_to_string(c, Z3_func_decl_to_ast(c, c0))),
            "(declare-fun c () Int)"
        );
        // Round trip: Z3_to_func_decl returns the CANONICAL handle (may be a
        // different pointer — documented divergence, value-equal).
        let back = Z3_to_func_decl(c, a1);
        assert!(!back.is_null());
        assert!(Z3_is_eq_func_decl(c, back, f1));
        // The round-tripped decl BUILDS and SOLVES like the original.
        let g_sym = Z3_mk_string_symbol(c, c"g".as_ptr());
        let mut gdom = [int];
        let g = Z3_mk_func_decl(c, g_sym, 1, gdom.as_mut_ptr(), int);
        let g_back = Z3_to_func_decl(c, Z3_func_decl_to_ast(c, g));
        let x = Z3_mk_const(c, Z3_mk_string_symbol(c, c"x".as_ptr()), int);
        let mut app_args = [x];
        let gx_orig = Z3_mk_app(c, g, 1, app_args.as_mut_ptr());
        let gx_back = Z3_mk_app(c, g_back, 1, app_args.as_mut_ptr());
        assert_eq!(gx_orig, gx_back, "same term through either decl handle");
        // UNSAT twin through the round-tripped decl: g(x)=1 ∧ g(x)=2.
        let s = Z3_mk_solver(c);
        let one = Z3_mk_int(c, 1, int);
        let two = Z3_mk_int(c, 2, int);
        Z3_solver_assert(c, s, Z3_mk_eq(c, gx_back, one));
        Z3_solver_assert(c, s, Z3_mk_eq(c, gx_back, two));
        assert_eq!(Z3_solver_check(c, s), Z3_L_FALSE);
        // Null decl → null ast (pre-existing pin).
        assert_eq!(Z3_func_decl_to_ast(c, ptr::null_mut()), 0);
        Z3_del_context(c);
    }
}

#[test]
fn indexed_decls_do_not_conflate_in_decl_ast_interning() {
    unsafe {
        let c = ctx();
        // (_ extract 7 4) vs (_ extract 3 0): same name, same domain/range
        // widths would even be possible — the DeclAstKey params field must
        // keep them distinct.
        let bv8 = Z3_mk_bv_sort(c, 8);
        let x = Z3_mk_const(c, Z3_mk_string_symbol(c, c"x".as_ptr()), bv8);
        let e1 = Z3_mk_extract(c, 7, 4, x);
        let e2 = Z3_mk_extract(c, 3, 0, x);
        let d1 = Z3_get_app_decl(c, e1);
        let d2 = Z3_get_app_decl(c, e2);
        if !d1.is_null() && !d2.is_null() {
            let a1 = Z3_func_decl_to_ast(c, d1);
            let a2 = Z3_func_decl_to_ast(c, d2);
            if a1 != 0 && a2 != 0 {
                assert_ne!(a1, a2, "(_ extract 7 4) must not alias (_ extract 3 0)");
            }
        }
        Z3_del_context(c);
    }
}

// ============================================================================
// GAP 1: the poison guard — wrong-fact / fail-close probes
// ============================================================================

#[test]
fn tagged_handle_in_term_position_fails_closed_never_decides() {
    unsafe {
        let c = ctx();
        let int = Z3_mk_int_sort(c);
        let sort_ast = Z3_sort_to_ast(c, int);
        // (a) Assert the sort-ast into a solver: the poison id panics at the
        // first arena access INSIDE the guard → the assert ERRORS and stores
        // nothing. (Before the poison guard this u32-truncated onto an
        // arbitrary real term — asserting an unrelated formula silently.)
        let s = Z3_mk_solver(c);
        Z3_solver_assert(c, s, sort_ast);
        assert_ne!(
            Z3_get_error_code(c),
            Z3_OK,
            "asserting a tagged handle must set an error"
        );
        // Same-solver contract (measured, matches real z3): the failed assert
        // added NOTHING, so a check now sees the empty assertion set → sat.
        // The verdict is derived from the remaining (empty) assertions, never
        // from the poison — z3py/ayz3 raise at the assert and never get here.
        assert_eq!(Z3_solver_check(c, s), Z3_L_TRUE);
        // The SAME solver then still decides a well-formed UNSAT twin
        // x>0 ∧ x<0 correctly — the poison was not silently retained and the
        // engine is not damaged.
        let x = Z3_mk_const(c, Z3_mk_string_symbol(c, c"x".as_ptr()), int);
        let zero = Z3_mk_int(c, 0, int);
        Z3_solver_assert(c, s, Z3_mk_gt(c, x, zero));
        Z3_solver_assert(c, s, Z3_mk_lt(c, x, zero));
        assert_eq!(Z3_solver_check(c, s), Z3_L_FALSE);
        // And a FRESH solver on the same context works too.
        let s2 = Z3_mk_solver(c);
        Z3_solver_assert(c, s2, Z3_mk_gt(c, x, zero));
        Z3_solver_assert(c, s2, Z3_mk_lt(c, x, zero));
        assert_eq!(Z3_solver_check(c, s2), Z3_L_FALSE);
        Z3_del_context(c);
    }
}

#[test]
fn crafted_tagged_alias_of_live_term_errors_in_mk_eq() {
    unsafe {
        let c = ctx();
        let int = Z3_mk_int_sort(c);
        let x = Z3_mk_const(c, Z3_mk_string_symbol(c, c"x".as_ptr()), int);
        // Craft SORT_AST_TAG | k where k aliases the LIVE term behind x under
        // u32 truncation — exactly the wrong-verdict channel: without the
        // poison guard this would silently build (= x x)-shaped terms from a
        // non-term handle.
        let crafted = SORT_AST_TAG | x;
        let eq = Z3_mk_eq(c, crafted, x);
        assert_eq!(eq, 0, "mk_eq over a tagged handle must fail, not evaluate");
        assert_ne!(Z3_get_error_code(c), Z3_OK);
        Z3_del_context(c);
    }
}

#[test]
fn tagged_refcounting_is_balanced_noop_on_rc_context() {
    unsafe {
        let cfg = Z3_mk_config();
        let c = Z3_mk_context_rc(cfg);
        Z3_del_config(cfg);
        let int = Z3_mk_int_sort(c);
        let sort_ast = Z3_sort_to_ast(c, int);
        // z3py inc/dec-refs as_ast() of every SortRef/FuncDeclRef; must be
        // balanced no-ops — dec_ref×N must never report Z3_DEC_REF_ERROR.
        Z3_inc_ref(c, sort_ast);
        for _ in 0..4 {
            Z3_dec_ref(c, sort_ast);
            assert_eq!(
                Z3_get_error_code(c),
                Z3_OK,
                "no DEC_REF_ERROR on tagged handles"
            );
        }
        Z3_del_context(c);
    }
}

#[test]
fn tagged_handles_fail_closed_in_to_app_and_translate() {
    unsafe {
        let c = ctx();
        let int = Z3_mk_int_sort(c);
        let sort_ast = Z3_sort_to_ast(c, int);
        assert_eq!(Z3_to_app(c, sort_ast), 0);
        assert_ne!(Z3_get_error_code(c), Z3_OK);
        let c2 = ctx();
        assert_eq!(Z3_translate(c, sort_ast, c2), 0);
        assert_ne!(Z3_get_error_code(c2), Z3_OK);
        Z3_del_context(c2);
        Z3_del_context(c);
    }
}

#[test]
fn parser_context_accepts_tagged_sort_and_decl_asts() {
    unsafe {
        let c = ctx();
        // Simulate stock z3py, which passes sort.as_ast()/decl.as_ast() (a
        // TAGGED u64) into the Z3_sort/Z3_func_decl-typed parameters
        // (z3.py:9531/9534). Must decode — never a garbage-pointer deref.
        let pc = Z3_mk_parser_context(c);
        let usort = Z3_mk_uninterpreted_sort(c, Z3_mk_string_symbol(c, c"S".as_ptr()));
        let tagged_sort = Z3_sort_to_ast(c, usort);
        Z3_parser_context_add_sort(c, pc, tagged_sort as Z3_sort);
        assert_eq!(Z3_get_error_code(c), Z3_OK, "tagged sort must decode");
        let int = Z3_mk_int_sort(c);
        let mut dom = [int];
        let f = Z3_mk_func_decl(
            c,
            Z3_mk_string_symbol(c, c"pf".as_ptr()),
            1,
            dom.as_mut_ptr(),
            int,
        );
        let tagged_decl = Z3_func_decl_to_ast(c, f);
        Z3_parser_context_add_decl(c, pc, tagged_decl as Z3_func_decl);
        assert_eq!(Z3_get_error_code(c), Z3_OK, "tagged decl must decode");
        // Re-adding the same handle is idempotent; it must not create two
        // indistinguishable overload candidates and make the parse ambiguous.
        Z3_parser_context_add_decl(c, pc, tagged_decl as Z3_func_decl);
        assert_eq!(
            Z3_get_error_code(c),
            Z3_OK,
            "repeated add_decl is idempotent"
        );
        // The injected symbols are actually usable in a subsequent parse.
        let av = Z3_parser_context_from_string(
            c,
            pc,
            c"(declare-const s S)(assert (= (pf 1) 2))".as_ptr(),
        );
        assert_eq!(Z3_get_error_code(c), Z3_OK, "parse after tagged injection");
        assert!(!av.is_null());
        Z3_del_context(c);
    }
}

// ============================================================================
// GAP 2: global params (measured z3 4.15.4 parity)
// ============================================================================

/// One test for the whole store: the store is PROCESS-GLOBAL, so parallel
/// test functions would race each other's set/reset. Sequential sections
/// inside one test keep it deterministic.
#[test]
fn global_params_store_measured_z3_parity() {
    unsafe {
        // -- defaults (never set): registry values, measured verbatim.
        Z3_global_param_reset_all();
        let mut out: Z3_string = ptr::null();
        assert!(Z3_global_param_get(c"timeout".as_ptr(), &mut out));
        assert_eq!(cstr(out), "4294967295");
        assert!(Z3_global_param_get(c"verbose".as_ptr(), &mut out));
        assert_eq!(cstr(out), "0");
        assert!(Z3_global_param_get(c"pp.decimal".as_ptr(), &mut out));
        assert_eq!(cstr(out), "false");
        assert!(Z3_global_param_get(c"pp.max_depth".as_ptr(), &mut out));
        assert_eq!(cstr(out), "5");

        // -- set/get round trip + case/dash normalization (measured:
        // 'pp.MAX-WIDTH' ≡ 'pp.max_width', 'VERBOSE' readable as 'verbose').
        Z3_global_param_set(c"VERBOSE".as_ptr(), c"3".as_ptr());
        assert!(Z3_global_param_get(c"verbose".as_ptr(), &mut out));
        assert_eq!(cstr(out), "3");
        Z3_global_param_set(c"pp.MAX-WIDTH".as_ptr(), c"70".as_ptr());
        assert!(Z3_global_param_get(c"pp.max_width".as_ptr(), &mut out));
        assert_eq!(cstr(out), "70");

        // -- unknown key: false + NULLED out-buffer (measured: z3 overwrites
        // a preloaded sentinel with NULL). Never a fabricated value.
        let mut sentinel: Z3_string = c"SENTINEL".as_ptr();
        assert!(!Z3_global_param_get(
            c"definitely_not_a_param".as_ptr(),
            &mut sentinel
        ));
        assert!(sentinel.is_null(), "out-buffer must be nulled on failure");
        // -- unknown module: set refused, get false (measured).
        Z3_global_param_set(c"nomod.foo".as_ptr(), c"bar".as_ptr());
        let mut sentinel2: Z3_string = c"SENTINEL".as_ptr();
        assert!(!Z3_global_param_get(c"nomod.foo".as_ptr(), &mut sentinel2));
        assert!(sentinel2.is_null());
        // -- unknown param in the KNOWN pp module: refused too (measured).
        Z3_global_param_set(c"pp.not_a_param".as_ptr(), c"7".as_ptr());
        let mut sentinel3: Z3_string = c"SENTINEL".as_ptr();
        assert!(!Z3_global_param_get(
            c"pp.not_a_param".as_ptr(),
            &mut sentinel3
        ));
        assert!(sentinel3.is_null());

        // -- invalid value for the registered type: refused, prior value kept
        // (measured: verbose=notanum keeps 3; pp.max_depth=notanum keeps set).
        Z3_global_param_set(c"verbose".as_ptr(), c"notanum".as_ptr());
        assert!(Z3_global_param_get(c"verbose".as_ptr(), &mut out));
        assert_eq!(cstr(out), "3");

        // -- reset_all restores defaults (measured).
        Z3_global_param_reset_all();
        assert!(Z3_global_param_get(c"verbose".as_ptr(), &mut out));
        assert_eq!(cstr(out), "0");
        assert!(Z3_global_param_get(c"pp.max_width".as_ptr(), &mut out));
        assert_eq!(cstr(out), "80");
    }
}

// ============================================================================
// GAP 3: error message canonical strings
// ============================================================================

#[test]
fn error_msg_canonical_strings_byte_identical_to_z3() {
    unsafe {
        let c = ctx();
        // Measured z3 4.15.4 table; >12 → "unknown".
        let expected = [
            (0u32, "ok"),
            (1, "type error"),
            (2, "index out of bounds"),
            (3, "invalid argument"),
            (4, "parser error"),
            (5, "parser (data) is not available"),
            (6, "invalid pattern"),
            (7, "out of memory"),
            (8, "file access error"),
            (9, "internal error"),
            (10, "invalid usage"),
            (11, "invalid dec_ref command"),
            (12, "Z3 exception"),
            (13, "unknown"),
            (100, "unknown"),
        ];
        for (code, want) in expected {
            assert_eq!(
                cstr(Z3_get_error_msg(c, code)),
                want,
                "canonical string for code {code}"
            );
        }
        Z3_del_context(c);
    }
}

#[test]
fn pending_detailed_message_overrides_every_code_argument() {
    unsafe {
        let c = ctx();
        // Induce an error that records a DETAILED message.
        let bad = Z3_to_func_decl(c, 12345);
        assert!(bad.is_null());
        assert_ne!(Z3_get_error_code(c), Z3_OK);
        let detailed = cstr(Z3_get_error_msg(c, Z3_get_error_code(c))).to_string();
        assert!(
            detailed.contains("Z3_to_func_decl"),
            "detailed message expected, got: {detailed}"
        );
        // Measured z3 semantics: the pending message is returned regardless
        // of the code argument — even 0.
        assert_eq!(cstr(Z3_get_error_msg(c, 0)), detailed);
        assert_eq!(cstr(Z3_get_error_msg(c, 4)), detailed);
        Z3_del_context(c);
    }
}

// ============================================================================
// GAP 4 hardening: Z3_mk_map sort gate + name-signature registry
// ============================================================================

#[test]
fn mk_map_sort_gate_and_name_signature_registry() {
    unsafe {
        let c = ctx();
        let int = Z3_mk_int_sort(c);
        let bool_s = Z3_mk_bool_sort(c);
        let arr_ii = Z3_mk_array_sort(c, int, int);
        let arr_ib = Z3_mk_array_sort(c, int, bool_s);
        let a = Z3_mk_const(c, Z3_mk_string_symbol(c, c"a".as_ptr()), arr_ii);
        let ab = Z3_mk_const(c, Z3_mk_string_symbol(c, c"ab".as_ptr()), arr_ib);
        let mut dom_i = [int];
        let f_ii = Z3_mk_func_decl(
            c,
            Z3_mk_string_symbol(c, c"f".as_ptr()),
            1,
            dom_i.as_mut_ptr(),
            int,
        );
        // Well-sorted map: works.
        let mut margs = [a];
        let m = Z3_mk_map(c, f_ii, 1, margs.as_mut_ptr());
        assert_ne!(m, 0);
        assert_eq!(Z3_get_error_code(c), Z3_OK);
        // Element-sort mismatch: f expects Int, array holds Bool → SORT_ERROR.
        let mut margs_bad = [ab];
        assert_eq!(Z3_mk_map(c, f_ii, 1, margs_bad.as_mut_ptr()), 0);
        assert_eq!(Z3_get_error_code(c), Z3_SORT_ERROR);
        // Arity mismatch → SORT_ERROR.
        let mut margs2 = [a, a];
        assert_eq!(Z3_mk_map(c, f_ii, 2, margs2.as_mut_ptr()), 0);
        assert_eq!(Z3_get_error_code(c), Z3_SORT_ERROR);
        // A second public decl also named "f" with a DIFFERENT signature
        // (Bool→Bool) has its own collision-proof native identity. Array-map
        // records that identity, so the formerly necessary same-display-name
        // refusal is no longer needed and the maps remain disjoint.
        let mut dom_b = [bool_s];
        let f_bb = Z3_mk_func_decl(
            c,
            Z3_mk_string_symbol(c, c"f".as_ptr()),
            1,
            dom_b.as_mut_ptr(),
            bool_s,
        );
        let bb = Z3_mk_const(
            c,
            Z3_mk_string_symbol(c, c"bb".as_ptr()),
            Z3_mk_array_sort(c, int, bool_s),
        );
        let mut margs3 = [bb];
        let mb = Z3_mk_map(c, f_bb, 1, margs3.as_mut_ptr());
        assert_ne!(
            mb, 0,
            "signature overload must remain independently mappable"
        );
        assert_ne!(
            mb, m,
            "different function identities must produce distinct maps"
        );
        assert!(Z3_is_eq_sort(c, Z3_get_sort(c, mb), arr_ib));
        // The SAME signature through a different handle still works.
        let f_ii2 = Z3_mk_func_decl(
            c,
            Z3_mk_string_symbol(c, c"f".as_ptr()),
            1,
            dom_i.as_mut_ptr(),
            int,
        );
        let m2 = Z3_mk_map(c, f_ii2, 1, margs.as_mut_ptr());
        assert_ne!(m2, 0);
        assert_eq!(Z3_get_error_code(c), Z3_OK);
        assert_eq!(m, m2, "same map through value-equal decls is the same term");
        Z3_del_context(c);
    }
}

// ============================================================================
// Repair battery (#wavec-p3-capi-stubs skeptic round): recursive-datatype
// sort-ast identity, cross-context fail-close, reserved-name capture guard.
// ============================================================================

/// Skeptic-2 F1: a self-recursive datatype's constructor domain / accessor
/// range must intern to the SAME sort-ast as the datatype sort itself
/// (z3 4.15.4 measured: `cons.domain(1).as_ast() == IL.as_ast()`, kind 6),
/// and the constructor must actually apply (z3py raised 'Sort mismatch'
/// before the repair).
#[test]
fn recursive_datatype_sort_ast_is_canonical_and_constructs() {
    unsafe {
        let c = ctx();
        let int = Z3_mk_int_sort(c);
        let dt_name = Z3_mk_string_symbol(c, c"IList".as_ptr());
        // cons(car: Int, cdr: <self>)
        let cons_name = Z3_mk_string_symbol(c, c"cons".as_ptr());
        let is_cons = Z3_mk_string_symbol(c, c"is-cons".as_ptr());
        let fnames = [
            Z3_mk_string_symbol(c, c"car".as_ptr()),
            Z3_mk_string_symbol(c, c"cdr".as_ptr()),
        ];
        let fsorts = [int, ptr::null_mut()];
        let frefs = [0u32, 0u32];
        let cons_ctor = Z3_mk_constructor(
            c,
            cons_name,
            is_cons,
            2,
            fnames.as_ptr(),
            fsorts.as_ptr(),
            frefs.as_ptr(),
        );
        // nil
        let nil_name = Z3_mk_string_symbol(c, c"nil".as_ptr());
        let is_nil = Z3_mk_string_symbol(c, c"is-nil".as_ptr());
        let nil_ctor = Z3_mk_constructor(
            c,
            nil_name,
            is_nil,
            0,
            ptr::null(),
            ptr::null(),
            ptr::null(),
        );
        let mut ctors = [cons_ctor, nil_ctor];
        let il = Z3_mk_datatype(c, dt_name, 2, ctors.as_mut_ptr());
        assert!(!il.is_null(), "datatype creation must succeed");

        let mut cons_decl: Z3_func_decl = ptr::null_mut();
        let mut tester: Z3_func_decl = ptr::null_mut();
        let mut accessors: [Z3_func_decl; 2] = [ptr::null_mut(); 2];
        Z3_query_constructor(
            c,
            cons_ctor,
            2,
            &mut cons_decl,
            &mut tester,
            accessors.as_mut_ptr(),
        );
        let mut nil_decl: Z3_func_decl = ptr::null_mut();
        Z3_query_constructor(
            c,
            nil_ctor,
            0,
            &mut nil_decl,
            ptr::null_mut(),
            ptr::null_mut(),
        );
        assert!(!cons_decl.is_null() && !nil_decl.is_null());

        // The recursive domain and the datatype sort must be the SAME
        // semantic sort: same sort-ast handle, datatype kind — z3py's
        // SortRef.eq (Z3_is_eq_ast over as_ast) depends on it.
        let il_ast = Z3_sort_to_ast(c, il);
        let dom1 = Z3_get_domain(c, cons_decl, 1);
        assert!(!dom1.is_null());
        let dom1_ast = Z3_sort_to_ast(c, dom1);
        assert_eq!(dom1_ast, il_ast, "cons.domain(1) must BE the datatype sort");
        assert_eq!(Z3_get_sort_kind(c, dom1), Z3_DATATYPE_SORT);
        // Accessor range (cdr: IL -> IL) and constructor range likewise.
        let cdr_range = Z3_get_range(c, accessors[1]);
        assert_eq!(
            Z3_sort_to_ast(c, cdr_range),
            il_ast,
            "cdr.range() must BE the datatype sort"
        );
        assert_eq!(Z3_sort_to_ast(c, Z3_get_range(c, cons_decl)), il_ast);

        // The z3py flow that regressed: cons(5, nil()) must construct, and
        // both polarities of car(cons(5,nil)) must decide correctly.
        let nil_t = Z3_mk_app(c, nil_decl, 0, ptr::null());
        assert_ne!(nil_t, 0, "nil() must construct");
        let five = Z3_mk_int(c, 5, int);
        let args = [five, nil_t];
        let cons_t = Z3_mk_app(c, cons_decl, 2, args.as_ptr());
        assert_ne!(cons_t, 0, "cons(5, nil) must construct (raised pre-repair)");
        assert_eq!(Z3_get_error_code(c), Z3_OK);
        let car_of = Z3_mk_app(c, accessors[0], 1, &cons_t);
        assert_ne!(car_of, 0);

        // wrong-fact must be unsat
        let s = Z3_mk_solver(c);
        Z3_solver_assert(c, s, Z3_mk_not(c, Z3_mk_eq(c, car_of, five)));
        assert_eq!(
            Z3_solver_check(c, s),
            Z3_L_FALSE,
            "car(cons(5,nil)) != 5 must be unsat"
        );
        // true-fact must be sat
        let s2 = Z3_mk_solver(c);
        Z3_solver_assert(c, s2, Z3_mk_eq(c, car_of, five));
        assert_eq!(
            Z3_solver_check(c, s2),
            Z3_L_TRUE,
            "car(cons(5,nil)) == 5 must be sat"
        );

        Z3_del_constructor(c, cons_ctor);
        Z3_del_constructor(c, nil_ctor);
        Z3_del_context(c);
    }
}

/// Skeptic-1 F1: a sort/decl ast minted in one context must NEVER decode to
/// a different object in another context — the salt check fails it closed
/// (null render / null decl, never a wrong sort).
#[test]
fn foreign_context_tagged_handles_fail_closed() {
    unsafe {
        let c1 = ctx();
        let c2 = ctx();
        let int1 = Z3_mk_int_sort(c1);
        // Make c2's sort-id space non-empty and DIFFERENT at the same index.
        let bv8 = Z3_mk_bv_sort(c2, 8);
        let _ = Z3_sort_to_ast(c2, bv8);
        let sa = Z3_sort_to_ast(c1, int1);
        // In-context: renders "Int".
        assert_eq!(cstr(Z3_ast_to_string(c1, sa)), "Int");
        // Foreign context: must fail closed (null), never render c2's sort.
        assert!(
            Z3_ast_to_string(c2, sa).is_null(),
            "foreign-context sort ast must not decode"
        );
        // Same for decl asts through Z3_to_func_decl.
        let f = Z3_mk_func_decl(c1, Z3_mk_string_symbol(c1, c"f".as_ptr()), 1, &int1, int1);
        let fa = Z3_func_decl_to_ast(c1, f);
        assert!(
            !Z3_to_func_decl(c1, fa).is_null(),
            "in-context decode works"
        );
        assert!(
            Z3_to_func_decl(c2, fa).is_null(),
            "foreign-context decl ast must not decode"
        );
        // Bare-forged tags (salt 0) never decode in ANY context.
        assert!(Z3_ast_to_string(c1, SORT_AST_TAG | 1).is_null());
        assert!(Z3_to_func_decl(c1, FUNC_DECL_AST_TAG).is_null());
        Z3_del_context(c1);
        Z3_del_context(c2);
    }
}

/// Skeptic-1 F2: a user declaration named `map[f]` is captured BY NAME by the
/// core array-map rewriter (`select(map[f](a),i) -> f(a[i])`) — a measured
/// silent wrong verdict (z3 sat / AY unsat). Every FFI decl-creation path and
/// the SMT-LIB text bridges must refuse the reserved namespaces, fail-closed.
#[test]
fn reserved_map_and_internal_names_are_refused() {
    unsafe {
        let c = ctx();
        let int = Z3_mk_int_sort(c);
        // Z3_mk_func_decl: `map[f]` refused with a detailed message.
        let d = Z3_mk_func_decl(c, Z3_mk_string_symbol(c, c"map[f]".as_ptr()), 1, &int, int);
        assert!(d.is_null(), "map[f] decl must be refused");
        assert_eq!(Z3_get_error_code(c), Z3_INVALID_ARG);
        assert!(cstr(Z3_get_error_msg(c, Z3_INVALID_ARG)).contains("reserved"));
        // Z3_mk_const: `!ay.array-ext!0` (internal witness namespace) refused.
        let k = Z3_mk_const(c, Z3_mk_string_symbol(c, c"!ay.array-ext!0".as_ptr()), int);
        assert_eq!(k, 0, "!ay.* const must be refused");
        // Control: ordinary names still work.
        let ok = Z3_mk_func_decl(c, Z3_mk_string_symbol(c, c"mapf".as_ptr()), 1, &int, int);
        assert!(!ok.is_null(), "non-reserved name must still declare");
        // SMT-LIB text bridge: quoted `|map[f]|` declaration fails closed…
        let bad = c"(declare-fun |map[f]| ((Array Int Int)) (Array Int Int)) (declare-const a (Array Int Int)) (assert (= (select (|map[f]| a) 3) 7)) (check-sat)";
        let out = cstr(Z3_eval_smtlib2_string(c, bad.as_ptr()));
        assert!(
            out.contains("error"),
            "reserved smtlib2 decl must error, got {out}"
        );
        assert_eq!(Z3_get_error_code(c), Z3_INVALID_ARG);
        // …and the same shape with a clean name still answers (sat, as z3).
        let good = c"(declare-fun mapf ((Array Int Int)) (Array Int Int)) (declare-const a (Array Int Int)) (assert (= (select (mapf a) 3) 7)) (check-sat)";
        let out2 = cstr(Z3_eval_smtlib2_string(c, good.as_ptr()));
        assert_eq!(out2, "sat", "clean-name control must still decide");
        Z3_del_context(c);
    }
}

/// FloatingPoint-theory sort names are already declarations in every Z3
/// context.  Treating `RoundingMode` as an ordinary uninterpreted sort aliases
/// AY's five-element rounding-mode carrier and can turn a six-element
/// datatype/pigeonhole into a spurious UNSAT.
#[test]
fn builtin_fpa_sort_names_cannot_be_uninterpreted_sorts() {
    unsafe {
        let c = ctx();
        for name in [
            c"RoundingMode",
            c"Float16",
            c"Float32",
            c"Float64",
            c"Float128",
        ] {
            let sort = Z3_mk_uninterpreted_sort(c, Z3_mk_string_symbol(c, name.as_ptr()));
            assert!(sort.is_null(), "builtin sort {name:?} must be reserved");
            assert_eq!(Z3_get_error_code(c), Z3_INVALID_ARG);
        }
        assert!(
            !Z3_mk_fpa_rounding_mode_sort(c).is_null(),
            "the real builtin RoundingMode sort remains available"
        );
        Z3_del_context(c);
    }
}

/// Integer symbols and same-spelled string symbols are different Z3 symbols;
/// constants also overload a string symbol by sort.  Both distinctions must
/// survive term construction, solving, app-decl introspection, and model
/// enumeration instead of being collapsed by AY's name-only variable table.
#[test]
fn symbol_kind_and_constant_sort_overloads_keep_distinct_identities() {
    unsafe {
        let c = ctx();
        let int = Z3_mk_int_sort(c);
        let bool_sort = Z3_mk_bool_sort(c);

        let int_symbol = Z3_mk_int_symbol(c, 23);
        let string_symbol = Z3_mk_string_symbol(c, c"s!23".as_ptr());
        assert_eq!(Z3_get_symbol_kind(c, int_symbol), 0);
        assert_eq!(Z3_get_symbol_kind(c, string_symbol), 1);
        assert_eq!(Z3_get_symbol_int(c, int_symbol), 23);
        assert_eq!(Z3_get_symbol_int(c, string_symbol), -1);
        assert_eq!(cstr(Z3_get_symbol_string(c, int_symbol)), "s!23");
        assert_eq!(cstr(Z3_get_symbol_string(c, string_symbol)), "s!23");

        let int_named = Z3_mk_const(c, int_symbol, int);
        let string_named = Z3_mk_const(c, string_symbol, int);
        assert_ne!(int_named, string_named, "symbol kind is part of identity");

        let overloaded_symbol = Z3_mk_string_symbol(c, c"overloaded".as_ptr());
        let overloaded_int = Z3_mk_const(c, overloaded_symbol, int);
        let overloaded_bool = Z3_mk_const(c, overloaded_symbol, bool_sort);
        assert_ne!(
            overloaded_int, overloaded_bool,
            "constant sort is part of identity"
        );
        assert!(Z3_is_eq_sort(c, Z3_get_sort(c, overloaded_int), int));
        assert!(Z3_is_eq_sort(c, Z3_get_sort(c, overloaded_bool), bool_sort));

        // App-decl introspection preserves the original symbol kind.
        let int_decl = Z3_get_app_decl(c, int_named);
        let string_decl = Z3_get_app_decl(c, string_named);
        assert_eq!(Z3_get_symbol_kind(c, Z3_get_decl_name(c, int_decl)), 0);
        assert_eq!(Z3_get_symbol_kind(c, Z3_get_decl_name(c, string_decl)), 1);

        let solver = Z3_mk_solver(c);
        Z3_solver_assert(c, solver, Z3_mk_eq(c, int_named, Z3_mk_int(c, 1, int)));
        Z3_solver_assert(c, solver, Z3_mk_eq(c, string_named, Z3_mk_int(c, 2, int)));
        Z3_solver_assert(c, solver, Z3_mk_eq(c, overloaded_int, Z3_mk_int(c, 3, int)));
        Z3_solver_assert(c, solver, overloaded_bool);
        assert_eq!(Z3_solver_check(c, solver), Z3_L_TRUE);

        let model = Z3_solver_get_model(c, solver);
        assert!(!model.is_null());
        let mut same_spelling_kinds = Vec::new();
        let mut overloaded_ranges = Vec::new();
        for i in 0..Z3_model_get_num_consts(c, model) {
            let decl = Z3_model_get_const_decl(c, model, i);
            assert!(!decl.is_null());
            assert_ne!(Z3_model_get_const_interp(c, model, decl), 0);
            let name_symbol = Z3_get_decl_name(c, decl);
            match cstr(Z3_get_symbol_string(c, name_symbol)) {
                "s!23" => same_spelling_kinds.push(Z3_get_symbol_kind(c, name_symbol)),
                "overloaded" => {
                    overloaded_ranges.push(Z3_get_sort_kind(c, Z3_get_range(c, decl)));
                }
                _ => {}
            }
        }
        same_spelling_kinds.sort_unstable();
        overloaded_ranges.sort_unstable();
        assert_eq!(same_spelling_kinds, vec![0, 1]);
        assert_eq!(overloaded_ranges, vec![Z3_BOOL_SORT, Z3_INT_SORT]);

        Z3_del_context(c);
    }
}

/// Function declarations use `(symbol kind/value, domain, range)` identity,
/// while fresh declarations have a private identity and skip already-used
/// display names.  These constraints would be UNSAT if either pair aliased.
#[test]
fn function_overloads_and_fresh_declarations_do_not_alias_named_ones() {
    unsafe {
        let c = ctx();
        let int = Z3_mk_int_sort(c);
        let bool_sort = Z3_mk_bool_sort(c);
        let arg = Z3_mk_int(c, 0, int);

        let int_symbol = Z3_mk_int_symbol(c, 9);
        let string_symbol = Z3_mk_string_symbol(c, c"s!9".as_ptr());
        let int_symbol_fun = Z3_mk_func_decl(c, int_symbol, 1, &int, int);
        let string_symbol_fun = Z3_mk_func_decl(c, string_symbol, 1, &int, int);
        let int_app = Z3_mk_app(c, int_symbol_fun, 1, &arg);
        let string_app = Z3_mk_app(c, string_symbol_fun, 1, &arg);
        assert_ne!(int_app, string_app);

        // Same string symbol, different signature: both declarations remain
        // usable with their own range sort.
        let overload = Z3_mk_string_symbol(c, c"ovf".as_ptr());
        let ovf_int = Z3_mk_func_decl(c, overload, 1, &int, int);
        let ovf_bool = Z3_mk_func_decl(c, overload, 1, &int, bool_sort);
        let ovf_int_app = Z3_mk_app(c, ovf_int, 1, &arg);
        let ovf_bool_app = Z3_mk_app(c, ovf_bool, 1, &arg);
        assert!(Z3_is_eq_sort(c, Z3_get_sort(c, ovf_int_app), int));
        assert!(Z3_is_eq_sort(c, Z3_get_sort(c, ovf_bool_app), bool_sort));

        // These names collide with the old ast_sorts/next_decl_id-derived
        // generators after the named declaration is cached.
        let named_const = Z3_mk_const(c, Z3_mk_string_symbol(c, c"p!2".as_ptr()), int);
        let fresh_const = Z3_mk_fresh_const(c, c"p".as_ptr(), int);
        assert_ne!(named_const, fresh_const);
        let named_fun = Z3_mk_func_decl(c, Z3_mk_string_symbol(c, c"f!2".as_ptr()), 1, &int, int);
        let fresh_fun = Z3_mk_fresh_func_decl(c, c"f".as_ptr(), 1, &int, int);
        assert!(!Z3_is_eq_func_decl(c, named_fun, fresh_fun));
        let named_fun_app = Z3_mk_app(c, named_fun, 1, &arg);
        let fresh_fun_app = Z3_mk_app(c, fresh_fun, 1, &arg);

        let solver = Z3_mk_solver(c);
        for (term, value) in [
            (int_app, 1),
            (string_app, 2),
            (ovf_int_app, 3),
            (named_const, 4),
            (fresh_const, 5),
            (named_fun_app, 6),
            (fresh_fun_app, 7),
        ] {
            Z3_solver_assert(c, solver, Z3_mk_eq(c, term, Z3_mk_int(c, value, int)));
        }
        Z3_solver_assert(c, solver, ovf_bool_app);
        assert_eq!(Z3_solver_check(c, solver), Z3_L_TRUE);

        Z3_del_context(c);
    }
}
