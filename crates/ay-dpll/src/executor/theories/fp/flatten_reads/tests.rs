// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

fn bv_array(index_w: u32, elem_w: u32) -> Sort {
    Sort::array(Sort::bitvec(index_w), Sort::bitvec(elem_w))
}

#[test]
fn collapses_equal_index_values_into_one_cell() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", bv_array(32, 8));
    // Two spellings of index 4 at the same width must map to ONE cell; a
    // second numeric index must get its own.
    let i1 = terms.mk_bitvec(BigInt::from(4), 32);
    let i2 = terms.mk_bitvec(BigInt::from(4u64), 32);
    let j = terms.mk_bitvec(BigInt::from(5), 32);
    let s1 = terms.mk_select(a, i1);
    let s2 = terms.mk_select(a, i2);
    let s3 = terms.mk_select(a, j);
    let eq = terms.mk_eq(s1, s2);
    let eq2 = terms.mk_eq(s1, s3);
    let ne = terms.mk_not(eq2);
    let plan = plan(&mut terms, &[eq, ne]).expect("plan should fire");
    assert_eq!(plan.cells.len(), 2, "cells: {:?}", plan.cells);
    assert!(is_array_free(&terms, &plan.assertions));
}

#[test]
fn distinct_arrays_never_share_a_cell_constant() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", bv_array(32, 8));
    let b = terms.mk_var("b", bv_array(32, 8));
    let i = terms.mk_bitvec(BigInt::from(0), 32);
    let sa = terms.mk_select(a, i);
    let sb = terms.mk_select(b, i);
    let eq = terms.mk_eq(sa, sb);
    let plan = plan(&mut terms, &[eq]).expect("plan should fire");
    assert_eq!(plan.cells.len(), 2);
    assert_ne!(plan.cells[0].fresh, plan.cells[1].fresh);
}

#[test]
fn abstains_on_store() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", bv_array(32, 8));
    let i = terms.mk_bitvec(BigInt::from(0), 32);
    let v = terms.mk_bitvec(BigInt::from(7), 8);
    let st = terms.mk_store(a, i, v);
    let rd = terms.mk_select(st, i);
    let lit = terms.mk_bitvec(BigInt::from(9), 8);
    let eq = terms.mk_eq(rd, lit);
    assert!(matches!(
        plan(&mut terms, &[eq]),
        Err(FlattenAbstain::Store | FlattenAbstain::NoArrays)
    ));
}

#[test]
fn abstains_on_symbolic_index() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", bv_array(32, 8));
    let i = terms.mk_var("i", Sort::bitvec(32));
    let rd = terms.mk_select(a, i);
    let lit = terms.mk_bitvec(BigInt::from(7), 8);
    let eq = terms.mk_eq(rd, lit);
    assert!(matches!(
        plan(&mut terms, &[eq]),
        Err(FlattenAbstain::SymbolicIndex)
    ));
}

#[test]
fn abstains_on_array_equality() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", bv_array(32, 8));
    let b = terms.mk_var("b", bv_array(32, 8));
    let eq = terms.mk_eq(a, b);
    assert!(matches!(
        plan(&mut terms, &[eq]),
        Err(FlattenAbstain::ArrayNotOnlySelected)
    ));
}

#[test]
fn abstains_on_non_bv_array_sort() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::array(Sort::Int, Sort::bitvec(8)));
    let i = terms.mk_int(BigInt::from(0));
    let rd = terms.mk_select(a, i);
    let lit = terms.mk_bitvec(BigInt::from(7), 8);
    let eq = terms.mk_eq(rd, lit);
    assert!(matches!(
        plan(&mut terms, &[eq]),
        Err(FlattenAbstain::ArraySortUnsupported)
    ));
}

#[test]
fn abstains_when_no_array_present() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::bitvec(8));
    let lit = terms.mk_bitvec(BigInt::from(7), 8);
    let eq = terms.mk_eq(x, lit);
    assert!(matches!(
        plan(&mut terms, &[eq]),
        Err(FlattenAbstain::NoArrays)
    ));
}
