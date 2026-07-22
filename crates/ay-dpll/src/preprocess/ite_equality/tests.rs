// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use ay_core::Sort;
use num_bigint::BigInt;

#[test]
fn test_ite_equality_derivation() {
    let mut terms = TermStore::new();

    // Create: (ite (= opcode #x88) (= x #b1) (= x #b0))
    //         (ite (= opcode #x88) (= y #b1) (= y #b0))
    let opcode = terms.mk_var("opcode", Sort::bitvec(8));
    let x = terms.mk_var("x", Sort::bitvec(1));
    let y = terms.mk_var("y", Sort::bitvec(1));

    let const_88 = terms.mk_bitvec(BigInt::from(0x88), 8);
    let const_1 = terms.mk_bitvec(BigInt::from(1), 1);
    let const_0 = terms.mk_bitvec(BigInt::from(0), 1);

    let cond = terms.mk_eq(opcode, const_88);
    let x_eq_1 = terms.mk_eq(x, const_1);
    let x_eq_0 = terms.mk_eq(x, const_0);
    let y_eq_1 = terms.mk_eq(y, const_1);
    let y_eq_0 = terms.mk_eq(y, const_0);

    let ite_x = terms.mk_ite(cond, x_eq_1, x_eq_0);
    let ite_y = terms.mk_ite(cond, y_eq_1, y_eq_0);

    let mut assertions = vec![ite_x, ite_y];
    let mut pass = IteEquality::new();

    let modified = pass.apply(&mut terms, &mut assertions);
    assert!(modified, "Should have added equality assertion");

    // Should have added (= x y)
    assert_eq!(assertions.len(), 3);
    let eq_xy = terms.mk_eq(x, y);
    assert!(
        assertions.contains(&eq_xy),
        "Should contain equality between x and y"
    );
}

#[test]
fn test_no_equality_for_different_conditions() {
    let mut terms = TermStore::new();

    // Create ITEs with DIFFERENT conditions - no equality should be derived
    let cond1 = terms.mk_var("cond1", Sort::Bool);
    let cond2 = terms.mk_var("cond2", Sort::Bool);
    let x = terms.mk_var("x", Sort::bitvec(1));
    let y = terms.mk_var("y", Sort::bitvec(1));

    let const_1 = terms.mk_bitvec(BigInt::from(1), 1);
    let const_0 = terms.mk_bitvec(BigInt::from(0), 1);

    let x_eq_1 = terms.mk_eq(x, const_1);
    let x_eq_0 = terms.mk_eq(x, const_0);
    let y_eq_1 = terms.mk_eq(y, const_1);
    let y_eq_0 = terms.mk_eq(y, const_0);

    let ite_x = terms.mk_ite(cond1, x_eq_1, x_eq_0);
    let ite_y = terms.mk_ite(cond2, y_eq_1, y_eq_0);

    let mut assertions = vec![ite_x, ite_y];
    let mut pass = IteEquality::new();

    let modified = pass.apply(&mut terms, &mut assertions);
    assert!(
        !modified,
        "Should not add equality for different conditions"
    );
    assert_eq!(assertions.len(), 2);
}

#[test]
fn test_no_equality_for_different_values() {
    let mut terms = TermStore::new();

    // Create ITEs with same condition but DIFFERENT values
    let cond = terms.mk_var("cond", Sort::Bool);
    let x = terms.mk_var("x", Sort::bitvec(2));
    let y = terms.mk_var("y", Sort::bitvec(2));

    let const_1 = terms.mk_bitvec(BigInt::from(1), 2);
    let const_2 = terms.mk_bitvec(BigInt::from(2), 2);
    let const_0 = terms.mk_bitvec(BigInt::from(0), 2);

    let x_eq_1 = terms.mk_eq(x, const_1);
    let x_eq_0 = terms.mk_eq(x, const_0);
    let y_eq_2 = terms.mk_eq(y, const_2); // Different!
    let y_eq_0 = terms.mk_eq(y, const_0);

    let ite_x = terms.mk_ite(cond, x_eq_1, x_eq_0);
    let ite_y = terms.mk_ite(cond, y_eq_2, y_eq_0);

    let mut assertions = vec![ite_x, ite_y];
    let mut pass = IteEquality::new();

    let modified = pass.apply(&mut terms, &mut assertions);
    assert!(!modified, "Should not add equality for different values");
}

#[test]
fn test_multiple_variables_in_group() {
    let mut terms = TermStore::new();

    // Create ITEs with 3 variables all constrained the same way
    let cond = terms.mk_var("cond", Sort::Bool);
    let x = terms.mk_var("x", Sort::bitvec(1));
    let y = terms.mk_var("y", Sort::bitvec(1));
    let z = terms.mk_var("z", Sort::bitvec(1));

    let const_1 = terms.mk_bitvec(BigInt::from(1), 1);
    let const_0 = terms.mk_bitvec(BigInt::from(0), 1);

    let x_eq_1 = terms.mk_eq(x, const_1);
    let x_eq_0 = terms.mk_eq(x, const_0);
    let y_eq_1 = terms.mk_eq(y, const_1);
    let y_eq_0 = terms.mk_eq(y, const_0);
    let z_eq_1 = terms.mk_eq(z, const_1);
    let z_eq_0 = terms.mk_eq(z, const_0);

    let ite_x = terms.mk_ite(cond, x_eq_1, x_eq_0);
    let ite_y = terms.mk_ite(cond, y_eq_1, y_eq_0);
    let ite_z = terms.mk_ite(cond, z_eq_1, z_eq_0);

    let mut assertions = vec![ite_x, ite_y, ite_z];
    let mut pass = IteEquality::new();

    let modified = pass.apply(&mut terms, &mut assertions);
    assert!(modified);

    // Should have added 2 equalities (x=y, y=z) to chain them
    assert_eq!(assertions.len(), 5);
}

#[test]
fn test_no_equality_for_nested_ite_structure() {
    let mut terms = TermStore::new();

    // Nested ITE counterexample (see #1791):
    //
    // (ite c1
    //   (and (= x 10) (= y 10))
    //   (ite c2
    //     (and (= x 20) (= y 20))
    //     (and (= x 30) (= y 40))))
    //
    // The nested structure does not imply x = y (c1=false,c2=false gives x=30,y=40),
    // so the preprocessing pass must not derive x=y here.
    let c1 = terms.mk_var("c1", Sort::Bool);
    let c2 = terms.mk_var("c2", Sort::Bool);
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);

    let ten = terms.mk_int(BigInt::from(10));
    let twenty = terms.mk_int(BigInt::from(20));
    let thirty = terms.mk_int(BigInt::from(30));
    let forty = terms.mk_int(BigInt::from(40));

    let x_eq_10 = terms.mk_eq(x, ten);
    let y_eq_10 = terms.mk_eq(y, ten);
    let x_eq_20 = terms.mk_eq(x, twenty);
    let y_eq_20 = terms.mk_eq(y, twenty);
    let x_eq_30 = terms.mk_eq(x, thirty);
    let y_eq_40 = terms.mk_eq(y, forty);

    let branch1 = terms.mk_and(vec![x_eq_10, y_eq_10]);
    let branch2 = terms.mk_and(vec![x_eq_20, y_eq_20]);
    let branch3 = terms.mk_and(vec![x_eq_30, y_eq_40]);
    let nested = terms.mk_ite(c2, branch2, branch3);
    let ite = terms.mk_ite(c1, branch1, nested);

    let mut assertions = vec![ite];
    let mut pass = IteEquality::new();

    let modified = pass.apply(&mut terms, &mut assertions);
    assert!(
        !modified,
        "Nested ITE structure should not trigger ITE-equality derivation"
    );
    assert_eq!(assertions.len(), 1);
}
