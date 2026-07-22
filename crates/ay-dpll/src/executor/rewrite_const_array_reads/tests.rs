// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use ay_core::term::TermStore;
use ay_core::Sort;

fn bv32(terms: &mut TermStore, v: u64) -> TermId {
    terms.mk_bitvec(num_bigint::BigInt::from(v), 32)
}

/// `select(V, k)` where `V = const-array(false)` is a ground unit assertion is
/// rewritten to `false`, collapsing an enclosing `ite`-condition to a concrete
/// integer.
#[test]
fn rewrites_read_through_ground_const_array() {
    let mut terms = TermStore::new();
    let arr_sort = Sort::array(Sort::bitvec(32), Sort::Bool);
    let v = terms.mk_var("__EMPTY", arr_sort);
    let false_t = terms.mk_bool(false);
    let ca = terms.mk_const_array(Sort::bitvec(32), false_t);
    let eq = terms.mk_eq(v, ca); // V = const-array(false)  [ground fact]

    let k = bv32(&mut terms, 1);
    let sel = terms.mk_select(v, k); // select(V, 1) — opaque (V is a var)
                                     // len = (ite (select V 1) 0 1)
    let zero = terms.mk_int(num_bigint::BigInt::from(0));
    let one = terms.mk_int(num_bigint::BigInt::from(1));
    let ite = terms.mk_ite(sel, zero, one);
    let len = terms.mk_var("len", Sort::Int);
    let len_def = terms.mk_eq(len, ite);

    let mut assertions = vec![eq, len_def];
    let changed = rewrite_const_array_reads(&mut terms, &mut assertions);

    assert!(
        changed,
        "read through ground const-array should be rewritten"
    );
    // len_def should now be (= len 1): the select folded to false, ite -> else (1).
    let TermData::App(Symbol::Named(n), args) = terms.get(assertions[1]).clone() else {
        panic!("len_def not an application");
    };
    assert_eq!(n, "=");
    // mk_eq may normalize operand order, so accept the folded constant on either
    // side: the equality must now be `(= len 1)` with the ite over the rewritten
    // read collapsed to the concrete integer 1.
    let one_bi = num_bigint::BigInt::from(1);
    let folded = args
        .iter()
        .any(|&a| terms.extract_integer_constant(a) == Some(one_bi.clone()));
    assert!(
        folded,
        "ite over the rewritten read must fold to the concrete integer 1; got {:?}",
        args.iter()
            .map(|&a| terms.get(a).clone())
            .collect::<Vec<_>>()
    );
}

/// With no ground const-array equality, a `select(V, k)` read is left untouched.
#[test]
fn leaves_read_untouched_without_ground_eq() {
    let mut terms = TermStore::new();
    let arr_sort = Sort::array(Sort::bitvec(32), Sort::Bool);
    let v = terms.mk_var("s", arr_sort);
    let k = bv32(&mut terms, 1);
    let sel = terms.mk_select(v, k);
    let mut assertions = vec![sel];

    let changed = rewrite_const_array_reads(&mut terms, &mut assertions);
    assert!(
        !changed,
        "no ground const-array equality: nothing to rewrite"
    );
    assert_eq!(assertions[0], sel);
}

/// A `V` bound to two distinct const-array defaults is dropped — no read is
/// rewritten (its models are contradictory; the equalities preserve UNSAT).
#[test]
fn drops_conflicting_defaults() {
    let mut terms = TermStore::new();
    let arr_sort = Sort::array(Sort::bitvec(32), Sort::Bool);
    let v = terms.mk_var("__EMPTY", arr_sort);
    let false_t = terms.mk_bool(false);
    let true_t = terms.mk_bool(true);
    let ca_f = terms.mk_const_array(Sort::bitvec(32), false_t);
    let ca_t = terms.mk_const_array(Sort::bitvec(32), true_t);
    let eq_f = terms.mk_eq(v, ca_f);
    let eq_t = terms.mk_eq(v, ca_t);
    let k = bv32(&mut terms, 1);
    let sel = terms.mk_select(v, k);

    let mut assertions = vec![eq_f, eq_t, sel];
    let changed = rewrite_const_array_reads(&mut terms, &mut assertions);
    assert!(
        !changed,
        "conflicting const-array defaults must not be propagated"
    );
}
