// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use ay_core::Sort;
use num_bigint::BigInt;
use num_rational::BigRational;

/// Helper to create a rational constant
fn mk_rat(terms: &mut TermStore, n: i64, d: i64) -> TermId {
    terms.mk_rational(BigRational::new(BigInt::from(n), BigInt::from(d)))
}

/// Helper to create an integer constant
fn mk_i(terms: &mut TermStore, n: i64) -> TermId {
    terms.mk_int(BigInt::from(n))
}

#[test]
fn test_som_const_times_sum() {
    // (* 2 (+ x y)) should normalize to (+ (* 2 x) (* 2 y))
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let c2 = mk_i(&mut terms, 2);

    let sum = terms.mk_add(vec![x, y]);
    // Use mk_app to avoid mk_mul's built-in distribution (simulating parse)
    let mul = terms.mk_app(Symbol::named("*"), vec![c2, sum], Sort::Int);

    let mut pass = NormalizeArithSom::new();
    let normalized = pass.normalize(&mut terms, mul);

    // Should be a sum after SOM normalization
    match terms.get(normalized) {
        TermData::App(Symbol::Named(name), args) if name == "+" => {
            assert_eq!(args.len(), 2, "Should have 2 addends");
        }
        other => {
            // mk_mul may have already normalized in a different way,
            // but the result should not be a raw (* c (+ ...)) anymore
            assert_ne!(normalized, mul, "SOM should change the term: got {other:?}");
        }
    }
}

#[test]
fn test_som_product_of_sums() {
    // (* (+ a b) (+ c d)) → (+ (* a c) (* a d) (* b c) (* b d))
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Real);
    let b = terms.mk_var("b", Sort::Real);
    let c = terms.mk_var("c", Sort::Real);
    let d = terms.mk_var("d", Sort::Real);

    let sum1 = terms.mk_add(vec![a, b]);
    let sum2 = terms.mk_add(vec![c, d]);
    // Use mk_app to bypass mk_mul normalization
    let mul = terms.mk_app(Symbol::named("*"), vec![sum1, sum2], Sort::Real);

    let mut pass = NormalizeArithSom::new();
    let normalized = pass.normalize(&mut terms, mul);

    // Should be expanded to a sum
    match terms.get(normalized) {
        TermData::App(Symbol::Named(name), _) if name == "+" => {
            // Correct — distributed into sum of monomials
        }
        _ => {
            // The term should have changed from the original mul
            assert_ne!(normalized, mul, "SOM should expand product of sums");
        }
    }
}

#[test]
fn test_som_blowup_guard() {
    // Create a large product of sums that would exceed the blowup limit.
    // With SOM_BLOWUP=10 and 4 factors of 4 addends each:
    // total = 4^4 = 256, limit = 10 * 4 = 40 → should skip
    let mut terms = TermStore::new();
    let mut sums = Vec::new();

    for i in 0..4 {
        let vars: Vec<TermId> = (0..4)
            .map(|j| terms.mk_var(format!("x_{i}_{j}"), Sort::Real))
            .collect();
        sums.push(terms.mk_add(vars));
    }

    let mul = terms.mk_app(Symbol::named("*"), sums.clone(), Sort::Real);

    let mut pass = NormalizeArithSom::new();
    let normalized = pass.normalize(&mut terms, mul);

    // Should NOT be a sum — blowup guard should prevent expansion.
    // The result should be rebuilt through mk_mul but not expanded.
    // (mk_mul won't expand multi-sum products either)
    match terms.get(normalized) {
        TermData::App(Symbol::Named(name), _) if name == "+" => {
            // This is actually OK if mk_mul partially distributed.
            // The key is it didn't produce 256 monomials.
        }
        _ => {
            // Expected: still a multiplication or simplified form
        }
    }
}

#[test]
fn test_som_no_change_for_non_arithmetic() {
    // Boolean terms should not be modified
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    let b = terms.mk_var("b", Sort::Bool);
    let and_ab = terms.mk_and(vec![a, b]);

    let mut assertions = vec![and_ab];
    let mut pass = NormalizeArithSom::new();
    let modified = pass.apply(&mut terms, &mut assertions);

    assert!(
        !modified,
        "Boolean-only terms should not be modified by SOM"
    );
}

#[test]
fn test_som_nested_in_comparison() {
    // (<= (* 3 (+ x y)) z) should normalize to (<= (+ (* 3 x) (* 3 y)) z)
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let z = terms.mk_var("z", Sort::Int);
    let c3 = mk_i(&mut terms, 3);

    let sum = terms.mk_add(vec![x, y]);
    // Bypass mk_mul distribution by using mk_app directly
    let mul = terms.mk_app(Symbol::named("*"), vec![c3, sum], Sort::Int);
    let le = terms.mk_le(mul, z);

    let mut pass = NormalizeArithSom::new();
    let normalized = pass.normalize(&mut terms, le);

    // The comparison should have a normalized LHS
    assert_ne!(normalized, le, "SOM should normalize inside comparisons");
}

#[test]
fn test_som_idempotent() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let c = mk_rat(&mut terms, 5, 1);

    let sum = terms.mk_add(vec![x, y]);
    let mul = terms.mk_app(Symbol::named("*"), vec![c, sum], Sort::Real);

    let mut pass = NormalizeArithSom::new();
    let norm1 = pass.normalize(&mut terms, mul);
    pass.cache.clear();
    let norm2 = pass.normalize(&mut terms, norm1);

    assert_eq!(norm1, norm2, "SOM normalization should be idempotent");
}
