// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for the Z3-compatible incremental parser context (`parser_context.rs`)
//! and the curated datatype/decl-parameter getters
//! (`Z3_get_datatype_sort_*`, `Z3_get_decl_parameter_kind`).
//!
//! Every expected value is the value libz3 4.15.4 reports for the same input
//! (pinned by `tests/capi_parser_context_consumer.c`, which runs the identical
//! assertions against both ay-ffi and libz3). Coverage:
//! - parser context: inc_ref/dec_ref refcount bookkeeping (saturating);
//!   incremental parse where a second `from_string` resolves symbols declared by
//!   the first; returned assertions are REAL terms, inspectable and SAT-solvable
//!   in the parent context.
//! - datatype introspection: constructor count / names / arities / range kinds,
//!   recognizer arity+range (name is AY's `is-<ctor>`), accessor names + range
//!   kinds; out-of-range → null; non-datatype → 0/null.
//! - decl parameter kind: `(_ extract 5 2)` reports two `Z3_PARAMETER_INT`
//!   parameters; out-of-range sets `Z3_IOB`.

use super::super::*;
use std::ffi::CStr;
use std::ptr;

/// Build a fresh context.
///
/// # Safety
/// The returned context must be freed by the caller with `Z3_del_context`.
unsafe fn mk_ctx() -> Z3_context {
    // SAFETY: standard context construction; single-threaded test.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);
        ctx
    }
}

/// Read a func_decl's name as an owned String.
///
/// # Safety
/// `ctx`/`d` must be valid handles.
unsafe fn decl_name(ctx: Z3_context, d: Z3_func_decl) -> String {
    // SAFETY: forwarded under the caller's contract; the returned C string is
    // context-owned and copied out immediately.
    unsafe {
        let sym = Z3_get_decl_name(ctx, d);
        CStr::from_ptr(Z3_get_symbol_string(ctx, sym))
            .to_str()
            .expect("declaration name must be valid UTF-8")
            .to_string()
    }
}

#[test]
fn test_parser_context_refcount_bookkeeping() {
    // SAFETY: all handles allocated/freed within this block; single-threaded.
    unsafe {
        let ctx = mk_ctx();
        let pc = Z3_mk_parser_context(ctx);
        assert!(!pc.is_null(), "mk_parser_context non-null");
        assert_eq!((*pc).refcount, 0, "fresh handle refcount 0");

        Z3_parser_context_inc_ref(ctx, pc);
        Z3_parser_context_inc_ref(ctx, pc);
        assert_eq!((*pc).refcount, 2, "two inc_refs -> 2");
        Z3_parser_context_dec_ref(ctx, pc);
        assert_eq!((*pc).refcount, 1, "one dec_ref -> 1");
        Z3_parser_context_dec_ref(ctx, pc);
        assert_eq!((*pc).refcount, 0, "balanced -> 0");
        // Unbalanced dec_ref saturates at 0 and never frees the arena handle.
        Z3_parser_context_dec_ref(ctx, pc);
        assert_eq!((*pc).refcount, 0, "dec below 0 saturates");

        Z3_del_context(ctx);
    }
}

#[test]
fn test_parser_context_incremental_parse_and_solve() {
    // SAFETY: all handles allocated/freed within this block; single-threaded.
    unsafe {
        let ctx = mk_ctx();
        let pc = Z3_mk_parser_context(ctx);
        Z3_parser_context_inc_ref(ctx, pc);

        // Inject an uninterpreted sort U and a decl f: Int -> Int.
        let u = Z3_mk_uninterpreted_sort(ctx, Z3_mk_string_symbol(ctx, c"U".as_ptr()));
        Z3_parser_context_add_sort(ctx, pc, u);
        let int_s = Z3_mk_int_sort(ctx);
        let dom = [int_s];
        let f = Z3_mk_func_decl(
            ctx,
            Z3_mk_string_symbol(ctx, c"f".as_ptr()),
            1,
            dom.as_ptr(),
            int_s,
        );
        Z3_parser_context_add_decl(ctx, pc, f);
        assert_eq!((*pc).added_sorts.len(), 1, "one sort recorded");
        assert_eq!((*pc).added_decls.len(), 1, "one decl recorded");

        // First parse: declares a,b of sort U; uses f (both from add_*).
        let v1 = Z3_parser_context_from_string(
            ctx,
            pc,
            c"(declare-const a U)(declare-const b U)(assert (distinct a b))(assert (= (f 0) 5))"
                .as_ptr(),
        );
        assert_eq!(Z3_get_error_code(ctx), Z3_OK, "first parse ok");
        assert!(!v1.is_null(), "v1 non-null");
        assert_eq!(Z3_ast_vector_size(ctx, v1), 2, "v1 has two assertions");
        // The returned assertion is a real, inspectable term in this context.
        let a0 = Z3_ast_vector_get(ctx, v1, 0);
        assert_ne!(a0, 0, "assertion term non-null");
        assert_eq!(Z3_get_ast_kind(ctx, a0), Z3_APP_AST, "assertion is an app");

        // Second parse references a,b declared by the FIRST parse (incremental
        // symbol table). Its own new symbol cc is declared here.
        let v2 = Z3_parser_context_from_string(
            ctx,
            pc,
            c"(declare-const cc U)(assert (or (= cc a) (= cc b)))".as_ptr(),
        );
        assert_eq!(
            Z3_get_error_code(ctx),
            Z3_OK,
            "second parse resolves a,b from the first"
        );
        assert_eq!(Z3_ast_vector_size(ctx, v2), 1, "v2 has one assertion");

        // All collected assertions are jointly satisfiable.
        let s = Z3_mk_solver(ctx);
        Z3_solver_inc_ref(ctx, s);
        for i in 0..Z3_ast_vector_size(ctx, v1) {
            Z3_solver_assert(ctx, s, Z3_ast_vector_get(ctx, v1, i));
        }
        for i in 0..Z3_ast_vector_size(ctx, v2) {
            Z3_solver_assert(ctx, s, Z3_ast_vector_get(ctx, v2, i));
        }
        assert_eq!(
            Z3_solver_check(ctx, s),
            Z3_L_TRUE,
            "collected parser-context assertions are SAT"
        );

        Z3_del_context(ctx);
    }
}

#[test]
fn test_parser_context_rejects_unrepresentable_sort_transactionally() {
    unsafe {
        let ctx = mk_ctx();
        let pc = Z3_mk_parser_context(ctx);
        let bad = Z3_mk_uninterpreted_sort(ctx, Z3_mk_string_symbol(ctx, c"bad|sort".as_ptr()));
        Z3_parser_context_add_sort(ctx, pc, bad);
        assert_eq!(Z3_get_error_code(ctx), Z3_EXCEPTION);
        assert!(
            (*pc).added_sorts.is_empty(),
            "an unthreadable declaration must not be recorded on the parser handle"
        );

        // The failed declaration did not poison or claim the decision engine.
        assert!(!Z3_mk_optimize(ctx).is_null());
        Z3_del_context(ctx);
    }
}

#[test]
fn test_parser_context_optimization_commands_fail_preflight_without_owner_claim() {
    unsafe {
        let ctx = mk_ctx();
        let pc = Z3_mk_parser_context(ctx);
        let out = Z3_parser_context_from_string(ctx, pc, c"(assert true)(minimize 0)".as_ptr());
        assert_eq!(Z3_get_error_code(ctx), Z3_INVALID_USAGE);
        assert_eq!(Z3_ast_vector_size(ctx, out), 0);
        assert!(!Z3_mk_optimize(ctx).is_null());
        Z3_del_context(ctx);
    }
}

#[test]
fn test_parser_context_null_and_error_paths() {
    // SAFETY: all handles allocated/freed within this block; single-threaded.
    unsafe {
        let ctx = mk_ctx();
        let pc = Z3_mk_parser_context(ctx);

        // Null input string -> INVALID_ARG, empty vector (never fabricated).
        let v = Z3_parser_context_from_string(ctx, pc, ptr::null());
        assert_eq!(Z3_get_error_code(ctx), Z3_INVALID_ARG, "null input errors");
        assert_eq!(Z3_ast_vector_size(ctx, v), 0, "null input -> empty vector");

        // A genuine parse error (malformed s-expression: unbalanced parens) ->
        // error + empty vector (never a fabricated assertion).
        let v2 = Z3_parser_context_from_string(ctx, pc, c"(assert (and true false".as_ptr());
        assert_ne!(Z3_get_error_code(ctx), Z3_OK, "malformed input is an error");
        assert_eq!(
            Z3_ast_vector_size(ctx, v2),
            0,
            "parse error -> empty vector"
        );

        Z3_del_context(ctx);
    }
}

#[test]
fn test_parser_context_late_semantic_error_poison_is_fail_closed() {
    // SAFETY: all handles allocated/freed within this block; single-threaded.
    unsafe {
        let ctx = mk_ctx();
        let pc = Z3_mk_parser_context(ctx);
        let solver = Z3_mk_solver(ctx);
        assert_eq!(Z3_solver_check(ctx, solver), Z3_L_TRUE);
        assert!(!Z3_solver_get_model(ctx, solver).is_null());

        let v = Z3_parser_context_from_string(
            ctx,
            pc,
            c"(declare-const y Int)(assert (= y 0))(assert 1)".as_ptr(),
        );
        assert_eq!(Z3_get_error_code(ctx), Z3_EXCEPTION);
        assert_eq!(Z3_ast_vector_size(ctx, v), 0);
        assert!(Z3_solver_get_model(ctx, solver).is_null());
        assert_eq!(Z3_solver_check(ctx, solver), Z3_L_UNDEF);
        assert_eq!(Z3_get_error_code(ctx), Z3_INVALID_USAGE);

        Z3_del_context(ctx);
    }
}

#[test]
fn test_datatype_sort_introspection_enum_and_struct() {
    // SAFETY: all handles allocated/freed within this block; single-threaded.
    unsafe {
        let ctx = mk_ctx();
        let int_s = Z3_mk_int_sort(ctx);

        // enum Color = red | green | blue (three nullary constructors).
        let names = [c"red", c"green", c"blue"];
        let recognizer_names = [c"r-red", c"r-green", c"r-blue"];
        let mut ctors: [Z3_constructor; 3] = [ptr::null_mut(); 3];
        for (i, nm) in names.iter().enumerate() {
            ctors[i] = Z3_mk_constructor(
                ctx,
                Z3_mk_string_symbol(ctx, nm.as_ptr()),
                Z3_mk_string_symbol(ctx, recognizer_names[i].as_ptr()),
                0,
                ptr::null(),
                ptr::null(),
                ptr::null(),
            );
        }
        let color = Z3_mk_datatype(
            ctx,
            Z3_mk_string_symbol(ctx, c"Color".as_ptr()),
            3,
            ctors.as_mut_ptr(),
        );
        assert!(!color.is_null(), "Color datatype created");
        assert_eq!(
            Z3_get_sort_kind(ctx, color),
            Z3_DATATYPE_SORT,
            "Color is a datatype sort"
        );
        assert_eq!(
            Z3_get_datatype_sort_num_constructors(ctx, color),
            3,
            "Color has 3 constructors"
        );
        for (i, nm) in names.iter().enumerate() {
            let cd = Z3_get_datatype_sort_constructor(ctx, color, i as u32);
            assert!(!cd.is_null(), "constructor decl non-null");
            assert_eq!(
                decl_name(ctx, cd),
                nm.to_str().expect("constructor name must be valid UTF-8"),
                "constructor name"
            );
            assert_eq!(Z3_get_arity(ctx, cd), 0, "enum constructor arity 0");
            assert_eq!(
                Z3_get_sort_kind(ctx, Z3_get_range(ctx, cd)),
                Z3_DATATYPE_SORT,
                "constructor range is the datatype"
            );
            let rd = Z3_get_datatype_sort_recognizer(ctx, color, i as u32);
            assert!(!rd.is_null(), "recognizer decl non-null");
            assert_eq!(Z3_get_arity(ctx, rd), 1, "recognizer arity 1");
            assert_eq!(
                Z3_get_sort_kind(ctx, Z3_get_range(ctx, rd)),
                Z3_BOOL_SORT,
                "recognizer range Bool"
            );
            // The C API preserves the caller-supplied recognizer symbol; it
            // does not replace it with AY's canonical SMT-LIB tester name.
            assert_eq!(
                decl_name(ctx, rd),
                recognizer_names[i]
                    .to_str()
                    .expect("recognizer name must be valid UTF-8"),
                "caller-supplied recognizer name"
            );
        }

        // struct IntPair = mk(fst: Int, snd: Int).
        let fnames = [
            Z3_mk_string_symbol(ctx, c"fst".as_ptr()),
            Z3_mk_string_symbol(ctx, c"snd".as_ptr()),
        ];
        let fsorts = [int_s, int_s];
        let srefs = [0u32, 0u32];
        let mk = Z3_mk_constructor(
            ctx,
            Z3_mk_string_symbol(ctx, c"mk".as_ptr()),
            Z3_mk_string_symbol(ctx, c"is_mk".as_ptr()),
            2,
            fnames.as_ptr(),
            fsorts.as_ptr(),
            srefs.as_ptr(),
        );
        let mut arr = [mk];
        let pair = Z3_mk_datatype(
            ctx,
            Z3_mk_string_symbol(ctx, c"IntPair".as_ptr()),
            1,
            arr.as_mut_ptr(),
        );
        assert_eq!(
            Z3_get_datatype_sort_num_constructors(ctx, pair),
            1,
            "IntPair has 1 constructor"
        );
        let cd = Z3_get_datatype_sort_constructor(ctx, pair, 0);
        assert_eq!(decl_name(ctx, cd), "mk", "struct constructor name");
        assert_eq!(Z3_get_arity(ctx, cd), 2, "struct constructor arity 2");
        let rd = Z3_get_datatype_sort_recognizer(ctx, pair, 0);
        assert_eq!(decl_name(ctx, rd), "is_mk", "struct recognizer name");
        let acc0 = Z3_get_datatype_sort_constructor_accessor(ctx, pair, 0, 0);
        let acc1 = Z3_get_datatype_sort_constructor_accessor(ctx, pair, 0, 1);
        assert_eq!(decl_name(ctx, acc0), "fst", "accessor 0 name");
        assert_eq!(decl_name(ctx, acc1), "snd", "accessor 1 name");
        assert_eq!(
            Z3_get_sort_kind(ctx, Z3_get_range(ctx, acc0)),
            Z3_INT_SORT,
            "accessor 0 range Int"
        );
        assert_eq!(
            Z3_get_sort_kind(ctx, Z3_get_range(ctx, acc1)),
            Z3_INT_SORT,
            "accessor 1 range Int"
        );

        // Out-of-range and non-datatype: honest null/0 (never fabricated).
        assert!(
            Z3_get_datatype_sort_constructor(ctx, pair, 5).is_null(),
            "OOB constructor -> null"
        );
        assert!(
            Z3_get_datatype_sort_constructor_accessor(ctx, pair, 0, 9).is_null(),
            "OOB accessor -> null"
        );
        assert_eq!(
            Z3_get_datatype_sort_num_constructors(ctx, int_s),
            0,
            "non-datatype -> 0 constructors"
        );
        assert!(
            Z3_get_datatype_sort_constructor(ctx, int_s, 0).is_null(),
            "non-datatype constructor -> null"
        );

        Z3_del_context(ctx);
    }
}

#[test]
fn test_datatype_constructor_decl_is_usable() {
    // The constructor func_decl returned by the getter is REAL: applying it via
    // Z3_mk_app builds a constructor term the recognizer accepts.
    // SAFETY: all handles allocated/freed within this block; single-threaded.
    unsafe {
        let ctx = mk_ctx();
        let names = [c"red", c"green"];
        let mut ctors: [Z3_constructor; 2] = [ptr::null_mut(); 2];
        for (i, nm) in names.iter().enumerate() {
            ctors[i] = Z3_mk_constructor(
                ctx,
                Z3_mk_string_symbol(ctx, nm.as_ptr()),
                Z3_mk_string_symbol(ctx, c"r".as_ptr()),
                0,
                ptr::null(),
                ptr::null(),
                ptr::null(),
            );
        }
        let color = Z3_mk_datatype(
            ctx,
            Z3_mk_string_symbol(ctx, c"Hue".as_ptr()),
            2,
            ctors.as_mut_ptr(),
        );
        let red_ctor = Z3_get_datatype_sort_constructor(ctx, color, 0);
        let is_red = Z3_get_datatype_sort_recognizer(ctx, color, 0);
        // red := red() ; assert (is-red red) -> SAT (a real constructor term).
        let red_term = Z3_mk_app(ctx, red_ctor, 0, ptr::null());
        assert_ne!(red_term, 0, "constructor application non-null");
        let args = [red_term];
        let is_red_app = Z3_mk_app(ctx, is_red, 1, args.as_ptr());
        assert_ne!(is_red_app, 0, "recognizer application non-null");
        let s = Z3_mk_solver(ctx);
        Z3_solver_inc_ref(ctx, s);
        Z3_solver_assert(ctx, s, is_red_app);
        assert_eq!(
            Z3_solver_check(ctx, s),
            Z3_L_TRUE,
            "(is-red red) is satisfiable"
        );
        Z3_del_context(ctx);
    }
}

#[test]
fn test_decl_parameter_kind_extract() {
    // SAFETY: all handles allocated/freed within this block; single-threaded.
    unsafe {
        let ctx = mk_ctx();
        let bv8 = Z3_mk_bv_sort(ctx, 8);
        let x = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, c"bx".as_ptr()), bv8);
        // (_ extract 5 2) bx : a 4-bit slice.
        let ext = Z3_mk_extract(ctx, 5, 2, x);
        let app = Z3_to_app(ctx, ext);
        let d = Z3_get_app_decl(ctx, app);
        assert!(!d.is_null(), "extract app decl non-null");
        assert_eq!(
            Z3_get_decl_num_parameters(ctx, d),
            2,
            "extract has 2 parameters"
        );
        assert_eq!(
            Z3_get_decl_parameter_kind(ctx, d, 0),
            Z3_PARAMETER_INT,
            "param 0 kind INT"
        );
        assert_eq!(
            Z3_get_decl_parameter_kind(ctx, d, 1),
            Z3_PARAMETER_INT,
            "param 1 kind INT"
        );
        assert_eq!(Z3_get_decl_int_parameter(ctx, d, 0), 5, "param 0 == 5");
        assert_eq!(Z3_get_decl_int_parameter(ctx, d, 1), 2, "param 1 == 2");

        // Out-of-range parameter index -> Z3_IOB (honest error).
        let _ = Z3_get_decl_parameter_kind(ctx, d, 2);
        assert_eq!(
            Z3_get_error_code(ctx),
            Z3_IOB,
            "out-of-range parameter index sets IOB"
        );
        Z3_del_context(ctx);
    }
}
