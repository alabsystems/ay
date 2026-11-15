// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::super::{closed_bv_in, EvalValue};
use super::*;

#[test]
fn a_closed_term_folds_and_a_variable_does_not() {
    let mut terms = TermStore::new();
    let ones = bv(&mut terms, 0xff, 8);
    let one = app(&mut terms, "bvneg", &[ones], Sort::bitvec(8));
    assert_eq!(closed_bv_in(&terms, one, &[]), Some(1));
    let x = terms.mk_var("x", Sort::bitvec(8));
    let open = app(&mut terms, "bvneg", &[x], Sort::bitvec(8));
    assert_eq!(closed_bv_in(&terms, open, &[]), None);
    // A variable a hypothesis or case fixes is read as its value.
    let fixed = [(
        x,
        EvalValue::BitVec {
            value: 0xff,
            width: 8,
        },
    )];
    assert_eq!(closed_bv_in(&terms, open, &fixed), Some(1));
}

#[test]
fn a_division_by_a_closed_power_of_two_is_exact_and_any_other_is_not() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::bitvec(8));
    let divided_by = |terms: &mut TermStore, negated: u64| {
        let constant = bv(terms, negated, 8);
        let divisor = app(terms, "bvneg", &[constant], Sort::bitvec(8));
        app(terms, "bvudiv", &[x, divisor], Sort::bitvec(8))
    };
    // (bvudiv x (bvneg #xff)) = x: the divisor is 1.
    let by_one = divided_by(&mut terms, 0xff);
    let identity = app(&mut terms, "=", &[by_one, x], Sort::Bool);
    assert!(crate::recognize_bv_bitblast(&terms, &[identity]));
    // (bvudiv x (bvneg #xfe)) = x is false (the divisor is 2), and stays so.
    let by_two = divided_by(&mut terms, 0xfe);
    let false_identity = app(&mut terms, "=", &[by_two, x], Sort::Bool);
    assert!(!crate::recognize_bv_bitblast(&terms, &[false_identity]));
}
