// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use ay_core::{ArraySort, BitVecSort};

#[test]
fn test_is_bv_theory_atom_detects_bv_comparisons_and_equalities() {
    let mut terms = TermStore::new();
    let bv8 = Sort::BitVec(BitVecSort::new(8));
    let x = terms.mk_var("x", bv8.clone());
    let y = terms.mk_var("y", bv8);
    let ult = terms.mk_bvult(x, y);
    let eq = terms.mk_eq(x, y);
    let int_eq = {
        let i = terms.mk_var("i", Sort::Int);
        let j = terms.mk_var("j", Sort::Int);
        terms.mk_eq(i, j)
    };

    assert!(SmtContext::is_bv_theory_atom(&terms, ult));
    assert!(SmtContext::is_bv_theory_atom(&terms, eq));
    assert!(!SmtContext::is_bv_theory_atom(&terms, int_eq));
}

#[test]
fn test_is_array_theory_atom_detects_array_ops_and_equalities() {
    let mut terms = TermStore::new();
    let arr_sort = Sort::Array(Box::new(ArraySort::new(Sort::Int, Sort::Int)));
    let array = terms.mk_var("a", arr_sort.clone());
    let other_array = terms.mk_var("b", arr_sort);
    let index = terms.mk_var("i", Sort::Int);
    let value = terms.mk_var("v", Sort::Int);
    let select = terms.mk_select(array, index);
    let store = terms.mk_store(other_array, index, value);
    let array_eq = terms.mk_eq(array, other_array);
    let int_eq = {
        let lhs = terms.mk_var("lhs", Sort::Int);
        let rhs = terms.mk_var("rhs", Sort::Int);
        terms.mk_eq(lhs, rhs)
    };

    assert!(SmtContext::is_array_theory_atom(&terms, select));
    assert!(SmtContext::is_array_theory_atom(&terms, store));
    assert!(SmtContext::is_array_theory_atom(&terms, array_eq));
    assert!(!SmtContext::is_array_theory_atom(&terms, int_eq));
}
