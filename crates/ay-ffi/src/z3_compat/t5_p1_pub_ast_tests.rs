// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! T5 P1: a `Z3_ast` names a public node, interned by (engine term, public
//! sort). Two public objects AY stores as one engine term (a finite-domain
//! value and the integer of the same value, a character and its code point)
//! are two ASTs, each keeping its own sort, as in z3. Every expectation below
//! is libz3 5.1.0's answer (measured through z3py, `~/ay-bench/t5p1/probes`).

use std::ffi::{c_uint, CStr};
use std::ptr;

use crate::z3_compat::*;

/// Fresh context; caller frees via `Z3_del_context`.
unsafe fn ctx() -> Z3_context {
    // SAFETY: standard config/context construction; config freed immediately.
    unsafe {
        let cfg = Z3_mk_config();
        let c = Z3_mk_context(cfg);
        Z3_del_config(cfg);
        c
    }
}

unsafe fn sort_kind(c: Z3_context, a: Z3_ast) -> c_uint {
    // SAFETY: `a` is a live AST of `c`.
    unsafe { Z3_get_sort_kind(c, Z3_get_sort(c, a)) }
}

/// z3: `FiniteDomainVal(3, S).eq(IntVal(3))` is False, the value's sort stays
/// `S`, and building finite-domain values never changes `IntVal(3).sort()`.
#[test]
fn finite_domain_value_and_int_numeral_are_distinct_asts() {
    // SAFETY: every handle lives in one context.
    unsafe {
        let c = ctx();
        let int = Z3_mk_int_sort(c);
        let three = Z3_mk_int(c, 3, int);
        let s = Z3_mk_finite_domain_sort(c, Z3_mk_string_symbol(c, c"S".as_ptr()), 5);
        let fd_three = Z3_mk_int(c, 3, s);
        assert_ne!(fd_three, 0);
        assert_ne!(fd_three, three);
        assert!(!Z3_is_eq_ast(c, fd_three, three));
        assert_eq!(sort_kind(c, fd_three), Z3_FINITE_DOMAIN_SORT);
        assert_eq!(sort_kind(c, three), Z3_INT_SORT);
        // Hash-consing still holds within each sort.
        assert_eq!(Z3_mk_int(c, 3, s), fd_three);
        assert_eq!(Z3_mk_int(c, 3, int), three);
        assert_eq!(sort_kind(c, three), Z3_INT_SORT);
        Z3_del_context(c);
    }
}

/// z3: `c.to_int()` is its own Int AST (`c.to_int().eq(c)` is False) and `c`
/// keeps sort Char; `CharVal('a').eq(IntVal(97))` is False.
#[test]
fn character_and_its_code_point_are_distinct_asts() {
    // SAFETY: every handle lives in one context.
    unsafe {
        let c = ctx();
        let ch_sort = Z3_mk_char_sort(c);
        let ch = Z3_mk_const(c, Z3_mk_string_symbol(c, c"ch".as_ptr()), ch_sort);
        let code = Z3_mk_char_to_int(c, ch);
        assert_ne!(code, ch);
        assert_eq!(sort_kind(c, code), Z3_INT_SORT);
        assert_eq!(sort_kind(c, ch), Z3_CHAR_SORT);
        let a = Z3_mk_char(c, 97);
        let n97 = Z3_mk_int(c, 97, Z3_mk_int_sort(c));
        assert_ne!(a, n97);
        assert_eq!(sort_kind(c, a), Z3_CHAR_SORT);
        assert_eq!(sort_kind(c, n97), Z3_INT_SORT);
        Z3_del_context(c);
    }
}

/// z3: `CharVal('a').decl().params()` is `[97]`, one `Z3_PARAMETER_INT`
/// (z3py prints a character value from it).
#[test]
fn character_value_decl_carries_its_code_point() {
    // SAFETY: every handle lives in one context.
    unsafe {
        let c = ctx();
        let a = Z3_mk_char(c, 97);
        let d = Z3_get_app_decl(c, a);
        assert!(!d.is_null());
        assert_eq!(Z3_get_decl_kind(c, d), Z3_OP_CHAR_CONST);
        assert_eq!(Z3_get_decl_num_parameters(c, d), 1);
        assert_eq!(Z3_get_decl_parameter_kind(c, d, 0), Z3_PARAMETER_INT);
        assert_eq!(Z3_get_decl_int_parameter(c, d, 0), 97);
        Z3_del_context(c);
    }
}

/// z3: `FiniteDomainVal(3, S).decl().params()` is `['3', S]`, a
/// `Z3_PARAMETER_RATIONAL` and a `Z3_PARAMETER_SORT`.
#[test]
fn finite_domain_value_decl_carries_value_and_sort() {
    // SAFETY: every handle lives in one context.
    unsafe {
        let c = ctx();
        let s = Z3_mk_finite_domain_sort(c, Z3_mk_string_symbol(c, c"S".as_ptr()), 5);
        let three = Z3_mk_int(c, 3, s);
        let d = Z3_get_app_decl(c, three);
        assert!(!d.is_null());
        assert_eq!(Z3_get_decl_kind(c, d), Z3_OP_FD_CONSTANT);
        assert_eq!(Z3_get_decl_num_parameters(c, d), 2);
        assert_eq!(Z3_get_decl_parameter_kind(c, d, 0), Z3_PARAMETER_RATIONAL);
        assert_eq!(Z3_get_decl_parameter_kind(c, d, 1), Z3_PARAMETER_SORT);
        let value = Z3_get_decl_rational_parameter(c, d, 0);
        assert!(!value.is_null());
        assert_eq!(CStr::from_ptr(value).to_str(), Ok("3"));
        assert_eq!(Z3_get_decl_sort_parameter(c, d, 1), s);
        Z3_del_context(c);
    }
}

/// The store: a node minted with no sort takes the first stated sort in
/// place; a second sort mints a second node, which the term then reads as;
/// stating the first sort again finds the first node.
#[test]
fn store_interns_by_term_and_public_sort() {
    use super::pub_ast::{NodeData, PubStore};
    use ay_dpll::api::{Logic, Solver, Sort};

    let mut solver = Solver::new(Logic::All);
    let three = solver.int_const(3);
    let mut store = PubStore::default();
    let unsorted = store.engine_node(three);
    assert!(unsorted.is_some());
    assert_eq!(store.engine_node(three), unsorted);
    let unsorted = unsorted.expect("a node for the term");
    let int = store.intern_sort(&Sort::Int).expect("Int interned");
    let fd = store
        .intern_sort(&Sort::FiniteDomain("S".to_string(), 5))
        .expect("finite domain interned");
    assert_eq!(store.sorted_node(three, int), Some((unsorted, None)));
    let (fd_node, previous) = store.sorted_node(three, fd).expect("a second node");
    assert_ne!(fd_node, unsorted);
    assert_eq!(previous, Some(int));
    assert_eq!(store.engine_node(three), Some(fd_node));
    assert_eq!(store.sorted_node(three, int), Some((unsorted, Some(fd))));
    assert_eq!(store.engine_node(three), Some(unsorted));
    assert_eq!(
        store.node(fd_node),
        Some(NodeData::Engine {
            term: three,
            sort: Some(fd)
        })
    );
    assert_eq!(store.len(), 2);
}

/// A unary predicate `name : domain -> Bool` applied to `arg`.
unsafe fn pred(c: Z3_context, name: &CStr, domain: Z3_sort, arg: Z3_ast) -> Z3_ast {
    // SAFETY: `domain` and `arg` are live handles of `c`.
    unsafe {
        let decl = Z3_mk_func_decl(
            c,
            Z3_mk_string_symbol(c, name.as_ptr()),
            1,
            ptr::from_ref(&domain),
            Z3_mk_bool_sort(c),
        );
        Z3_mk_app(c, decl, 1, ptr::from_ref(&arg))
    }
}

/// `Z3_substitute(target, [from] -> [to])`.
unsafe fn substitute1(c: Z3_context, target: Z3_ast, from: Z3_ast, to: Z3_ast) -> Z3_ast {
    // SAFETY: every handle is a live AST of `c`; the arrays have one element.
    unsafe { Z3_substitute(c, target, 1, ptr::from_ref(&from), ptr::from_ref(&to)) }
}

/// z3 substitutes by AST: `3 -> y` in `And(f(FD 3), g(3))` gives
/// `And(f(3), g(y))` and `FD 3 -> FD 4` gives `And(f(4), g(3))` (libz3
/// 5.1.0). AY matches by engine term, where both 3s are one term, so it would
/// replace both: a pattern whose term stands for two public objects is
/// refused. A pattern whose term has one public object still substitutes.
#[test]
fn substitute_refuses_a_pattern_shared_by_two_public_objects() {
    // SAFETY: every handle lives in one context.
    unsafe {
        let c = ctx();
        let int = Z3_mk_int_sort(c);
        let s = Z3_mk_finite_domain_sort(c, Z3_mk_string_symbol(c, c"S".as_ptr()), 5);
        let y = Z3_mk_const(c, Z3_mk_string_symbol(c, c"y".as_ptr()), int);
        let three = Z3_mk_int(c, 3, int);
        let g3 = pred(c, c"g", int, three);
        // Before any finite-domain 3 exists, the integer 3 is one object.
        let g_y = substitute1(c, g3, three, y);
        assert_ne!(g_y, 0);
        assert_eq!(Z3_get_error_code(c), Z3_OK);
        assert_eq!(g_y, pred(c, c"g", int, y));
        let fd_three = Z3_mk_int(c, 3, s);
        let f3 = pred(c, c"f", s, fd_three);
        let args = [f3, g3];
        let target = Z3_mk_and(c, 2, args.as_ptr());
        assert_ne!(target, 0);
        assert_eq!(substitute1(c, target, three, y), 0);
        assert_eq!(Z3_get_error_code(c), Z3_INVALID_ARG);
        let fd_four = Z3_mk_int(c, 4, s);
        assert_eq!(substitute1(c, target, fd_three, fd_four), 0);
        assert_eq!(Z3_get_error_code(c), Z3_INVALID_ARG);
        // A constant pattern is still substituted.
        let x = Z3_mk_const(c, Z3_mk_string_symbol(c, c"x".as_ptr()), int);
        let gx = pred(c, c"g", int, x);
        assert_eq!(substitute1(c, gx, x, y), g_y);
        assert_eq!(Z3_get_error_code(c), Z3_OK);
        Z3_del_context(c);
    }
}

/// A character literal is AY's engine term of its code point: substituting
/// either must not rewrite the other (libz3 5.1.0: `97 -> y` in
/// `And(h('a'), g(97))` gives `And(h('a'), g(y))`, and `'a' -> 'b'` gives
/// `And(h('b'), g(97))`), so both patterns are refused.
#[test]
fn substitute_refuses_a_character_or_its_code_point_as_pattern() {
    // SAFETY: every handle lives in one context.
    unsafe {
        let c = ctx();
        let int = Z3_mk_int_sort(c);
        let ch_sort = Z3_mk_char_sort(c);
        let a = Z3_mk_char(c, 97);
        let n97 = Z3_mk_int(c, 97, int);
        let h = pred(c, c"h", ch_sort, a);
        let g = pred(c, c"g", int, n97);
        let args = [h, g];
        let target = Z3_mk_and(c, 2, args.as_ptr());
        assert_ne!(target, 0);
        let y = Z3_mk_const(c, Z3_mk_string_symbol(c, c"y".as_ptr()), int);
        assert_eq!(substitute1(c, target, n97, y), 0);
        assert_eq!(Z3_get_error_code(c), Z3_INVALID_ARG);
        let b = Z3_mk_char(c, 98);
        assert_eq!(substitute1(c, target, a, b), 0);
        assert_eq!(Z3_get_error_code(c), Z3_INVALID_ARG);
        Z3_del_context(c);
    }
}

/// Construction evidence is kept per public node: `ite(p, a, b)` over two
/// characters is built faithfully by `Z3_mk_ite`, while its code point
/// `CharToInt(ite(p, a, b))` (AY's engine term of the `ite` itself) is not an
/// `ite` to z3. Updating the `ite` keeps z3's operator; updating the code
/// point would return an `ite` where z3 has `char.to_int`, so it is refused.
#[test]
fn update_term_reads_construction_evidence_of_the_callers_node() {
    // SAFETY: every handle lives in one context.
    unsafe {
        let c = ctx();
        let ch_sort = Z3_mk_char_sort(c);
        let bool_sort = Z3_mk_bool_sort(c);
        let a = Z3_mk_const(c, Z3_mk_string_symbol(c, c"a".as_ptr()), ch_sort);
        let b = Z3_mk_const(c, Z3_mk_string_symbol(c, c"b".as_ptr()), ch_sort);
        let p = Z3_mk_const(c, Z3_mk_string_symbol(c, c"p".as_ptr()), bool_sort);
        let q = Z3_mk_const(c, Z3_mk_string_symbol(c, c"q".as_ptr()), bool_sort);
        let ite = Z3_mk_ite(c, p, a, b);
        let code = Z3_mk_char_to_int(c, ite);
        assert_ne!(code, ite);
        let args = [q, a, b];
        let updated = Z3_update_term(c, ite, 3, args.as_ptr());
        assert_ne!(updated, 0);
        assert_eq!(Z3_get_error_code(c), Z3_OK);
        assert_eq!(Z3_get_app_num_args(c, updated), 3);
        assert_eq!(Z3_get_app_arg(c, updated, 0), q);
        assert_eq!(Z3_update_term(c, code, 3, args.as_ptr()), 0);
        assert_eq!(Z3_get_error_code(c), Z3_INVALID_ARG);
        Z3_del_context(c);
    }
}
