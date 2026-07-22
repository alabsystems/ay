// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use num_bigint::BigInt;

#[test]
fn test_normalize_concat_eq_variable() {
    let mut terms = TermStore::new();

    // Create: (= (concat a b) x)
    // where a is 4-bit, b is 4-bit, x is 8-bit
    let a = terms.mk_var("a", Sort::bitvec(4));
    let b = terms.mk_var("b", Sort::bitvec(4));
    let x = terms.mk_var("x", Sort::bitvec(8));

    let concat_ab = terms.mk_bvconcat(vec![a, b]);
    let eq = terms.mk_eq(concat_ab, x);

    let mut assertions = vec![eq];
    let mut pass = NormalizeEqBvConcat::new();

    let modified = pass.apply(&mut terms, &mut assertions);
    assert!(modified, "Should have normalized the equality");
    assert_eq!(assertions.len(), 1);

    // The result should be an AND of two equalities
    match terms.get(assertions[0]) {
        TermData::App(sym, args) if sym.name() == "and" => {
            assert_eq!(args.len(), 2, "Should have two conjuncts");

            // Check that we have equalities with extracts
            for arg in args {
                match terms.get(*arg) {
                    TermData::App(sym, eq_args) if sym.name() == "=" => {
                        assert_eq!(eq_args.len(), 2);
                        // One side should be a or b, other should be an extract
                        let is_extract = |t: TermId| matches!(terms.get(t), TermData::App(s, _) if s.name() == "extract");
                        assert!(
                            is_extract(eq_args[0]) || is_extract(eq_args[1]),
                            "One side should be an extract"
                        );
                    }
                    _ => panic!("Expected equality in AND"),
                }
            }
        }
        _ => panic!("Expected AND term, got {:?}", terms.get(assertions[0])),
    }
}

#[test]
fn test_normalize_concat_eq_constant() {
    let mut terms = TermStore::new();

    // Create: (= (concat a b) #xABCD)
    // where a is 8-bit, b is 8-bit, constant is 16-bit
    // Should produce: (and (= a #xAB) (= b #xCD))
    let a = terms.mk_var("a", Sort::bitvec(8));
    let b = terms.mk_var("b", Sort::bitvec(8));
    let const_abcd = terms.mk_bitvec(BigInt::from(0xABCD_u32), 16);

    let concat_ab = terms.mk_bvconcat(vec![a, b]);
    let eq = terms.mk_eq(concat_ab, const_abcd);

    let mut assertions = vec![eq];
    let mut pass = NormalizeEqBvConcat::new();

    let modified = pass.apply(&mut terms, &mut assertions);
    assert!(modified, "Should have normalized the equality");

    // After FlattenAnd and constant folding in mk_bvextract,
    // we should end up with equalities to constants
    let args = match terms.get(assertions[0]).clone() {
        TermData::App(sym, args) if sym.name() == "and" => args,
        _ => panic!("Expected AND term"),
    };
    assert_eq!(args.len(), 2);

    // Check that the extracts are constant-folded
    // (= a (extract 15 8 #xABCD)) -> (= a #xAB)
    // (= b (extract 7 0 #xABCD))  -> (= b #xCD)
    let const_ab = terms.mk_bitvec(BigInt::from(0xAB_u32), 8);
    let const_cd = terms.mk_bitvec(BigInt::from(0xCD_u32), 8);
    let expected_a_eq = terms.mk_eq(a, const_ab);
    let expected_b_eq = terms.mk_eq(b, const_cd);

    // The AND args should be these equalities (in some order)
    assert!(
        (args[0] == expected_a_eq && args[1] == expected_b_eq)
            || (args[0] == expected_b_eq && args[1] == expected_a_eq),
        "Should have constant-folded equalities"
    );
}

#[test]
fn test_no_normalize_both_concat() {
    let mut terms = TermStore::new();

    // Create: (= (concat a b) (concat c d))
    // This should NOT be normalized (would need different handling)
    let a = terms.mk_var("a", Sort::bitvec(4));
    let b = terms.mk_var("b", Sort::bitvec(4));
    let c = terms.mk_var("c", Sort::bitvec(4));
    let d = terms.mk_var("d", Sort::bitvec(4));

    let concat_ab = terms.mk_bvconcat(vec![a, b]);
    let concat_cd = terms.mk_bvconcat(vec![c, d]);
    let eq = terms.mk_eq(concat_ab, concat_cd);

    let mut assertions = vec![eq];
    let mut pass = NormalizeEqBvConcat::new();

    let modified = pass.apply(&mut terms, &mut assertions);
    assert!(!modified, "Should not normalize when both sides are concat");
    assert_eq!(assertions.len(), 1);
    assert_eq!(assertions[0], eq);
}

#[test]
fn test_no_normalize_non_bv() {
    let mut terms = TermStore::new();

    // Create a non-BV equality - should not be touched
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let eq = terms.mk_eq(x, y);

    let mut assertions = vec![eq];
    let mut pass = NormalizeEqBvConcat::new();

    let modified = pass.apply(&mut terms, &mut assertions);
    assert!(!modified, "Should not modify non-BV equality");
}

#[test]
fn test_no_normalize_no_concat() {
    let mut terms = TermStore::new();

    // Create a BV equality without concat
    let x = terms.mk_var("x", Sort::bitvec(8));
    let y = terms.mk_var("y", Sort::bitvec(8));
    let eq = terms.mk_eq(x, y);

    let mut assertions = vec![eq];
    let mut pass = NormalizeEqBvConcat::new();

    let modified = pass.apply(&mut terms, &mut assertions);
    assert!(!modified, "Should not modify equality without concat");
}

#[test]
fn test_normalize_reversed_order() {
    let mut terms = TermStore::new();

    // Create: (= x (concat a b)) - concat on RHS
    let a = terms.mk_var("a", Sort::bitvec(4));
    let b = terms.mk_var("b", Sort::bitvec(4));
    let x = terms.mk_var("x", Sort::bitvec(8));

    let concat_ab = terms.mk_bvconcat(vec![a, b]);
    let eq = terms.mk_eq(x, concat_ab); // x on LHS, concat on RHS

    let mut assertions = vec![eq];
    let mut pass = NormalizeEqBvConcat::new();

    let modified = pass.apply(&mut terms, &mut assertions);
    assert!(modified, "Should normalize even when concat is on RHS");
}

#[test]
fn test_nested_concat_multiple_iterations() {
    let mut terms = TermStore::new();

    // Create: (= (concat (concat a b) c) x)
    // First iteration: split into (concat a b) = extract(high) and c = extract(low)
    // Second iteration: split (concat a b) = extract(high) further
    let a = terms.mk_var("a", Sort::bitvec(4));
    let b = terms.mk_var("b", Sort::bitvec(4));
    let c = terms.mk_var("c", Sort::bitvec(4));
    let x = terms.mk_var("x", Sort::bitvec(12));

    let concat_ab = terms.mk_bvconcat(vec![a, b]);
    let concat_abc = terms.mk_bvconcat(vec![concat_ab, c]);
    let eq = terms.mk_eq(concat_abc, x);

    let mut assertions = vec![eq];
    let mut pass = NormalizeEqBvConcat::new();

    // First pass
    let modified1 = pass.apply(&mut terms, &mut assertions);
    assert!(modified1, "First pass should normalize outer concat");

    // The result is an AND - flatten it manually for the test
    let mut flattened = Vec::new();
    for &assertion in &assertions {
        match terms.get(assertion) {
            TermData::App(sym, args) if sym.name() == "and" => {
                flattened.extend(args.iter().copied());
            }
            _ => flattened.push(assertion),
        }
    }
    assertions = flattened;

    // Reset for second pass (this is what preprocessor does)
    // But we should NOT reset processed set, so we need to check if there's
    // a new concat-eq that was created

    // The first split created (= (concat a b) extract_high_x) which is a new
    // concat-eq that should be normalized on the next iteration
    let modified2 = pass.apply(&mut terms, &mut assertions);
    assert!(modified2, "Second pass should normalize nested concat");

    // Due to how the pass works, the nested concat should be processed
    // in the fixed-point loop (or we may need to flatten AND first)
    // For this test, we verify the structure is correct
    assert!(
        assertions.len() >= 2,
        "Should have at least 2 assertions after first split"
    );
}

#[test]
fn test_idempotency() {
    let mut terms = TermStore::new();

    // Create: (= (concat a b) x)
    let a = terms.mk_var("a", Sort::bitvec(4));
    let b = terms.mk_var("b", Sort::bitvec(4));
    let x = terms.mk_var("x", Sort::bitvec(8));

    let concat_ab = terms.mk_bvconcat(vec![a, b]);
    let eq = terms.mk_eq(concat_ab, x);

    let mut assertions = vec![eq];
    let mut pass = NormalizeEqBvConcat::new();

    // First pass should normalize
    let modified1 = pass.apply(&mut terms, &mut assertions);
    assert!(modified1, "First pass should modify");

    let assertions_after_first = assertions.clone();

    // Second pass on same assertions should be idempotent
    let modified2 = pass.apply(&mut terms, &mut assertions);
    assert!(!modified2, "Second pass should NOT modify (idempotent)");
    assert_eq!(
        assertions, assertions_after_first,
        "Assertions should be unchanged"
    );
}

#[test]
fn test_no_normalize_negated_equality() {
    let mut terms = TermStore::new();

    // Create: (not (= (concat a b) x))
    // This should NOT be normalized - only top-level equalities are handled
    let a = terms.mk_var("a", Sort::bitvec(4));
    let b = terms.mk_var("b", Sort::bitvec(4));
    let x = terms.mk_var("x", Sort::bitvec(8));

    let concat_ab = terms.mk_bvconcat(vec![a, b]);
    let eq = terms.mk_eq(concat_ab, x);
    let negated = terms.mk_not(eq);

    let mut assertions = vec![negated];
    let mut pass = NormalizeEqBvConcat::new();

    let modified = pass.apply(&mut terms, &mut assertions);
    assert!(!modified, "Should not normalize negated equality");
    assert_eq!(assertions.len(), 1);
    assert_eq!(assertions[0], negated);
}
