// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use ay_core::term::Symbol;
use ay_core::{Sort, TermId, TermStore};
use num_bigint::BigInt;

fn mk_eq(terms: &mut TermStore, a: TermId, b: TermId) -> TermId {
    terms.mk_app(Symbol::named("="), vec![a, b], Sort::Bool)
}

fn mk_and(terms: &mut TermStore, a: TermId, b: TermId) -> TermId {
    terms.mk_app(Symbol::named("and"), vec![a, b], Sort::Bool)
}

fn mk_or(terms: &mut TermStore, a: TermId, b: TermId) -> TermId {
    terms.mk_app(Symbol::named("or"), vec![a, b], Sort::Bool)
}

#[test]
fn arithmetic_term_classifiers_handle_basic_cases() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let five = terms.mk_int(BigInt::from(5));

    let add = terms.mk_app(Symbol::named("+"), vec![x, five], Sort::Int);
    let f_x = terms.mk_app(Symbol::named("f"), vec![x], Sort::Int);

    assert!(is_pure_arithmetic_term(&terms, x));
    assert!(is_pure_arithmetic_term(&terms, add));
    assert!(!is_pure_arithmetic_term(&terms, f_x));

    let lt = terms.mk_app(Symbol::named("<"), vec![x, five], Sort::Bool);
    assert!(contains_arithmetic_ops(&terms, lt));
    assert!(contains_arithmetic_ops(&terms, add));

    let eq_xy = mk_eq(&mut terms, x, y);
    assert!(contains_arithmetic_ops(&terms, eq_xy));

    let eq_fx_5 = mk_eq(&mut terms, f_x, five);
    assert!(!contains_arithmetic_ops(&terms, eq_fx_5));
}

#[test]
fn involves_int_and_real_arithmetic_routes_equalities_only_when_pure() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let r = terms.mk_var("r", Sort::Real);
    let five = terms.mk_int(BigInt::from(5));
    let f_x = terms.mk_app(Symbol::named("f"), vec![x], Sort::Int);

    let eq_x_5 = mk_eq(&mut terms, x, five);
    assert!(involves_int_arithmetic(&terms, eq_x_5));

    let eq_fx_5 = mk_eq(&mut terms, f_x, five);
    assert!(!involves_int_arithmetic(&terms, eq_fx_5));

    let plus_int = terms.mk_app(Symbol::named("+"), vec![x, five], Sort::Int);
    assert!(involves_int_arithmetic(&terms, plus_int));
    assert!(!involves_real_arithmetic(&terms, plus_int));

    let plus_real = terms.mk_app(Symbol::named("+"), vec![r, r], Sort::Real);
    assert!(involves_real_arithmetic(&terms, plus_real));
    assert!(!involves_int_arithmetic(&terms, plus_real));

    let arr = terms.mk_var("a", Sort::array(Sort::Int, Sort::Int));
    let idx = terms.mk_var("i", Sort::Int);
    let sel = terms.mk_select(arr, idx);
    let eq_sel_5 = mk_eq(&mut terms, sel, five);
    assert!(involves_int_arithmetic(&terms, eq_sel_5));

    assert!(!involves_int_arithmetic(&terms, eq_fx_5));

    let sel2 = terms.mk_select(arr, five);
    let distinct_sel = terms.mk_app(Symbol::named("distinct"), vec![sel, sel2], Sort::Bool);
    assert!(involves_int_arithmetic(&terms, distinct_sel));
    assert!(contains_arithmetic_ops(&terms, eq_sel_5));
}

#[test]
fn decode_helpers_recognize_non_bool_equalities_and_chains() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Int);
    let b = terms.mk_var("b", Sort::Int);
    let c = terms.mk_var("c", Sort::Int);
    let d = terms.mk_var("d", Sort::Int);

    let eq_ab = mk_eq(&mut terms, a, b);
    assert_eq!(decode_non_bool_eq(&terms, eq_ab), Some((a, b)));

    let bool_a = terms.mk_var("p", Sort::Bool);
    let bool_b = terms.mk_var("q", Sort::Bool);
    let eq_bool = mk_eq(&mut terms, bool_a, bool_b);
    assert_eq!(decode_non_bool_eq(&terms, eq_bool), None);

    let eq_bc = mk_eq(&mut terms, b, c);
    assert_eq!(chain_endpoints((a, b), (b, c)), Some((a, c)));
    assert_eq!(chain_endpoints((a, b), (c, d)), None);

    let and_two = mk_and(&mut terms, eq_ab, eq_bc);
    assert_eq!(decode_and_two_eqs(&terms, and_two), Some(((a, b), (b, c))));
}

#[test]
fn or_implies_eq_endpoints_detects_transitivity_pattern() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Int);
    let b = terms.mk_var("b", Sort::Int);
    let m = terms.mk_var("m", Sort::Int);
    let n = terms.mk_var("n", Sort::Int);

    let eq_am = mk_eq(&mut terms, a, m);
    let eq_mb = mk_eq(&mut terms, m, b);
    let and1 = mk_and(&mut terms, eq_am, eq_mb);

    let eq_an = mk_eq(&mut terms, a, n);
    let eq_nb = mk_eq(&mut terms, n, b);
    let and2 = mk_and(&mut terms, eq_an, eq_nb);
    let term = mk_or(&mut terms, and1, and2);

    assert_eq!(or_implies_eq_endpoints(&terms, term), Some((a, b)));
}

#[test]
fn extract_interface_arith_term_identifies_mixed_equalities() {
    let mut terms = TermStore::new();
    let c = terms.mk_var("c", Sort::Int);
    let two = terms.mk_int(BigInt::from(2));
    let ten = terms.mk_int(BigInt::from(10));

    let c_times_2 = terms.mk_app(Symbol::named("*"), vec![c, two], Sort::Int);
    let f_c = terms.mk_app(Symbol::named("f"), vec![c], Sort::Int);

    let eq_fc_c2 = mk_eq(&mut terms, f_c, c_times_2);
    assert_eq!(
        extract_interface_arith_term(&terms, eq_fc_c2),
        Some(c_times_2)
    );

    let eq_fc_10 = mk_eq(&mut terms, f_c, ten);
    assert_eq!(extract_interface_arith_term(&terms, eq_fc_10), Some(ten));

    let five = terms.mk_int(BigInt::from(5));
    let eq_c_5 = mk_eq(&mut terms, c, five);
    assert_eq!(extract_interface_arith_term(&terms, eq_c_5), None);

    let g_c = terms.mk_app(Symbol::named("g"), vec![c], Sort::Int);
    let eq_fc_gc = mk_eq(&mut terms, f_c, g_c);
    assert_eq!(extract_interface_arith_term(&terms, eq_fc_gc), None);
}

#[test]
fn involves_uninterpreted_function_detects_uf() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let two = terms.mk_int(BigInt::from(2));

    assert!(!involves_uninterpreted_function(&terms, x));
    assert!(!involves_uninterpreted_function(&terms, two));

    let x_times_2 = terms.mk_app(Symbol::named("*"), vec![x, two], Sort::Int);
    assert!(!involves_uninterpreted_function(&terms, x_times_2));

    let x_plus_y = terms.mk_app(Symbol::named("+"), vec![x, y], Sort::Int);
    assert!(!involves_uninterpreted_function(&terms, x_plus_y));

    let f_x = terms.mk_app(Symbol::named("f"), vec![x], Sort::Int);
    assert!(involves_uninterpreted_function(&terms, f_x));

    let f_x_plus_2 = terms.mk_app(Symbol::named("+"), vec![f_x, two], Sort::Int);
    assert!(involves_uninterpreted_function(&terms, f_x_plus_2));

    let eq_x_fy = terms.mk_app(Symbol::named("="), vec![x, f_x], Sort::Bool);
    assert!(involves_uninterpreted_function(&terms, eq_x_fy));
}

#[test]
fn contains_string_ops_detects_codepoint_bridge_ops() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::String);
    let code = terms.mk_app(Symbol::named("str.to_code"), vec![x], Sort::Int);
    let codepoint = terms.mk_int(BigInt::from(97));
    let eq_code = mk_eq(&mut terms, code, codepoint);
    assert!(contains_string_ops(&terms, eq_code));

    let n = terms.mk_var("n", Sort::Int);
    let from_code = terms.mk_app(Symbol::named("str.from_code"), vec![n], Sort::String);
    let a = terms.mk_string("a".to_string());
    let eq_from_code = mk_eq(&mut terms, from_code, a);
    assert!(contains_string_ops(&terms, eq_from_code));
}

#[test]
fn is_absorbing_concat_eq_detects_self_reference() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::String);
    let y = terms.mk_var("y", Sort::String);

    let concat_yx = terms.mk_app(Symbol::named("str.++"), vec![y, x], Sort::String);
    assert!(is_absorbing_concat_eq(&terms, x, concat_yx));

    let concat_xy = terms.mk_app(Symbol::named("str.++"), vec![x, y], Sort::String);
    assert!(is_absorbing_concat_eq(&terms, x, concat_xy));
}

#[test]
fn is_absorbing_concat_eq_non_absorbing() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::String);
    let y = terms.mk_var("y", Sort::String);
    let z = terms.mk_var("z", Sort::String);

    let concat_yz = terms.mk_app(Symbol::named("str.++"), vec![y, z], Sort::String);
    assert!(!is_absorbing_concat_eq(&terms, x, concat_yz));
    assert!(!is_absorbing_concat_eq(&terms, x, y));
}

#[test]
fn is_absorbing_concat_eq_nested() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::String);
    let y = terms.mk_var("y", Sort::String);
    let z = terms.mk_var("z", Sort::String);

    let inner = terms.mk_app(Symbol::named("str.++"), vec![z, x], Sort::String);
    let outer = terms.mk_app(Symbol::named("str.++"), vec![y, inner], Sort::String);
    assert!(is_absorbing_concat_eq(&terms, x, outer));
}

#[test]
fn contains_string_ops_detects_absorbing_concat_eq() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::String);
    let y = terms.mk_var("y", Sort::String);

    let concat_yx = terms.mk_app(Symbol::named("str.++"), vec![y, x], Sort::String);
    let eq = mk_eq(&mut terms, x, concat_yx);
    assert!(contains_string_ops(&terms, eq));

    let hello = terms.mk_string("hello".to_string());
    let concat_yh = terms.mk_app(Symbol::named("str.++"), vec![y, hello], Sort::String);
    let eq2 = mk_eq(&mut terms, x, concat_yh);
    assert!(!contains_string_ops(&terms, eq2));

    let a = terms.mk_string("a".to_string());
    let concat_xa = terms.mk_app(Symbol::named("str.++"), vec![x, a], Sort::String);
    let eq3 = mk_eq(&mut terms, concat_xa, a);
    assert!(!contains_string_ops(&terms, eq3));
}

#[test]
fn is_absorbing_concat_eq_constant_not_absorbing() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::String);
    let a = terms.mk_string("a".to_string());

    let concat_xa = terms.mk_app(Symbol::named("str.++"), vec![x, a], Sort::String);
    assert!(!is_absorbing_concat_eq(&terms, a, concat_xa));
    assert!(!is_absorbing_concat_eq(&terms, concat_xa, a));
}

#[test]
fn is_uf_int_equality_detects_mixed_uf_arith() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let five = terms.mk_int(BigInt::from(5));
    let six = terms.mk_int(BigInt::from(6));
    let one = terms.mk_int(BigInt::from(1));
    let g_x = terms.mk_app(Symbol::named("g"), vec![x], Sort::Int);

    let eq_gx_5 = mk_eq(&mut terms, g_x, five);
    assert!(is_uf_int_equality(&terms, eq_gx_5).is_some());

    let gx_plus_1 = terms.mk_app(Symbol::named("+"), vec![g_x, one], Sort::Int);
    let eq_gxp1_6 = mk_eq(&mut terms, gx_plus_1, six);
    assert!(is_uf_int_equality(&terms, eq_gxp1_6).is_some());

    let eq_x_5 = mk_eq(&mut terms, x, five);
    assert!(is_uf_int_equality(&terms, eq_x_5).is_none());

    let not_eq_gx_5 = terms.mk_not(eq_gx_5);
    assert!(is_uf_int_equality(&terms, not_eq_gx_5).is_some());
}

#[test]
fn is_uf_real_equality_detects_mixed_uf_arith() {
    use num_rational::BigRational;

    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let five = terms.mk_rational(BigRational::from(BigInt::from(5)));
    let one = terms.mk_rational(BigRational::from(BigInt::from(1)));
    let six = terms.mk_rational(BigRational::from(BigInt::from(6)));
    let f_x = terms.mk_app(Symbol::named("f"), vec![x], Sort::Real);

    let eq_fx_5 = mk_eq(&mut terms, f_x, five);
    assert!(is_uf_real_equality(&terms, eq_fx_5).is_some());

    let fx_plus_1 = terms.mk_app(Symbol::named("+"), vec![f_x, one], Sort::Real);
    let eq_fxp1_6 = mk_eq(&mut terms, fx_plus_1, six);
    assert!(is_uf_real_equality(&terms, eq_fxp1_6).is_some());

    let eq_x_5 = mk_eq(&mut terms, x, five);
    assert!(is_uf_real_equality(&terms, eq_x_5).is_none());

    let not_eq_fx_5 = terms.mk_not(eq_fx_5);
    assert!(is_uf_real_equality(&terms, not_eq_fx_5).is_some());

    let y = terms.mk_var("y", Sort::Int);
    let g_y = terms.mk_app(Symbol::named("g"), vec![y], Sort::Int);
    let int_five = terms.mk_int(BigInt::from(5));
    let eq_gy_5 = mk_eq(&mut terms, g_y, int_five);
    assert!(is_uf_real_equality(&terms, eq_gy_5).is_none());
}

#[test]
fn involves_array_classifies_quiescence_relevant_literals() {
    use ay_core::ArraySort;

    let mut terms = TermStore::new();
    let arr_sort = Sort::Array(Box::new(ArraySort::new(Sort::Int, Sort::Int)));

    let a = terms.mk_var("a", arr_sort.clone());
    let b = terms.mk_var("b", arr_sort);
    let arr_eq = mk_eq(&mut terms, a, b);
    assert!(involves_array(&terms, arr_eq));

    let idx = terms.mk_var("i", Sort::Int);
    let val = terms.mk_var("v", Sort::Int);
    let sel = terms.mk_select(a, idx);
    let store = terms.mk_app(
        Symbol::named("store"),
        vec![a, idx, val],
        Sort::array(Sort::Int, Sort::Int),
    );
    assert!(involves_array(&terms, sel));
    assert!(involves_array(&terms, store));

    let j = terms.mk_var("j", Sort::Int);
    let int_eq = mk_eq(&mut terms, idx, j);
    assert!(involves_array(&terms, int_eq));

    let int_distinct = terms.mk_app(Symbol::named("distinct"), vec![idx, j], Sort::Bool);
    assert!(involves_array(&terms, int_distinct));

    let not_int_eq = terms.mk_not(int_eq);
    assert!(involves_array(&terms, not_int_eq));

    let bool_var = terms.mk_var("p", Sort::Bool);
    assert!(!involves_array(&terms, bool_var));

    let five = terms.mk_int(BigInt::from(5));
    let lt = terms.mk_app(Symbol::named("<"), vec![idx, five], Sort::Bool);
    assert!(!involves_array(&terms, lt));

    let not_lt = terms.mk_not(lt);
    assert!(!involves_array(&terms, not_lt));

    let f_i = terms.mk_app(Symbol::named("f"), vec![idx], Sort::Int);
    assert!(!involves_array(&terms, f_i));

    let g_a = terms.mk_app(Symbol::named("g"), vec![a], Sort::Bool);
    assert!(involves_array(&terms, g_a));
}
