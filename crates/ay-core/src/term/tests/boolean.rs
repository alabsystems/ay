// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_bool_constants() {
    let mut store = TermStore::new();

    let t1 = store.mk_bool(true);
    let t2 = store.mk_bool(true);
    let f1 = store.mk_bool(false);

    assert_eq!(t1, t2);
    assert_ne!(t1, f1);
    assert_eq!(t1, store.true_term());
    assert_eq!(f1, store.false_term());
}

#[test]
fn test_negation_simplification() {
    let mut store = TermStore::new();

    let t = store.true_term();
    let not_t = store.mk_not(t);
    let not_not_t = store.mk_not(not_t);

    // not(true) = false
    assert_eq!(not_t, store.false_term());
    // not(not(x)) = x
    assert_eq!(not_not_t, t);
}

#[test]
fn test_de_morgan_not_and() {
    let mut store = TermStore::new();

    let x = store.mk_var("x", Sort::Bool);
    let y = store.mk_var("y", Sort::Bool);

    let and_xy = store.mk_and(vec![x, y]);
    let result = store.mk_not(and_xy);

    // (not (and x y)) -> (or (not x) (not y))
    match store.get(result) {
        TermData::App(Symbol::Named(name), args) => {
            assert_eq!(name, "or");
            assert_eq!(args.len(), 2);
            assert!(args
                .iter()
                .all(|&a| matches!(store.get(a), TermData::Not(_))));
        }
        other => panic!("expected (or ...) after De Morgan, got {other:?}"),
    }
}

#[test]
fn test_de_morgan_not_or() {
    let mut store = TermStore::new();

    let x = store.mk_var("x", Sort::Bool);
    let y = store.mk_var("y", Sort::Bool);

    let or_xy = store.mk_or(vec![x, y]);
    let result = store.mk_not(or_xy);

    // (not (or x y)) -> (and (not x) (not y))
    match store.get(result) {
        TermData::App(Symbol::Named(name), args) => {
            assert_eq!(name, "and");
            assert_eq!(args.len(), 2);
            assert!(args
                .iter()
                .all(|&a| matches!(store.get(a), TermData::Not(_))));
        }
        other => panic!("expected (and ...) after De Morgan, got {other:?}"),
    }
}

#[test]
fn test_mk_not_raw_preserves_not_wrapper() {
    let mut store = TermStore::new();

    let x = store.mk_var("x", Sort::Bool);
    let y = store.mk_var("y", Sort::Bool);
    let and_xy = store.mk_and(vec![x, y]);
    let raw_not = store.mk_not_raw(and_xy);

    assert!(
        matches!(store.get(raw_not), TermData::Not(inner) if *inner == and_xy),
        "expected raw Not wrapper around (and x y)"
    );

    // mk_not still performs De Morgan on the same argument.
    let normalized = store.mk_not(and_xy);
    assert_ne!(normalized, raw_not);
}

#[test]
fn test_de_morgan_enables_complement_simplification() {
    let mut store = TermStore::new();

    let x = store.mk_var("x", Sort::Bool);
    let y = store.mk_var("y", Sort::Bool);

    // x ∧ ¬(x ∨ y) -> x ∧ (¬x ∧ ¬y) -> false
    let or_xy = store.mk_or(vec![x, y]);
    let not_or_xy = store.mk_not(or_xy);
    let result = store.mk_and(vec![x, not_or_xy]);

    assert_eq!(result, store.false_term());
}

#[test]
fn test_and_simplification() {
    let mut store = TermStore::new();

    let x = store.mk_var("x", Sort::Bool);
    let t = store.true_term();
    let f = store.false_term();

    // and(x, true) = x
    assert_eq!(store.mk_and(vec![x, t]), x);

    // and(x, false) = false
    assert_eq!(store.mk_and(vec![x, f]), f);

    // and() = true
    assert_eq!(store.mk_and(vec![]), t);
}

#[test]
fn test_or_simplification() {
    let mut store = TermStore::new();

    let x = store.mk_var("x", Sort::Bool);
    let t = store.true_term();
    let f = store.false_term();

    // or(x, false) = x
    assert_eq!(store.mk_or(vec![x, f]), x);

    // or(x, true) = true
    assert_eq!(store.mk_or(vec![x, t]), t);

    // or() = false
    assert_eq!(store.mk_or(vec![]), f);
}

#[test]
#[allow(clippy::many_single_char_names)]
fn test_ite_simplification() {
    let mut store = TermStore::new();

    let x = store.mk_var("x", Sort::Int);
    let y = store.mk_var("y", Sort::Int);
    let t = store.true_term();
    let f = store.false_term();

    // ite(true, x, y) = x
    assert_eq!(store.mk_ite(t, x, y), x);

    // ite(false, x, y) = y
    assert_eq!(store.mk_ite(f, x, y), y);

    // ite(c, x, x) = x
    let c = store.mk_var("c", Sort::Bool);
    assert_eq!(store.mk_ite(c, x, x), x);
}

#[test]
fn test_coefficient_collection_with_negation() {
    let mut store = TermStore::new();

    let a = store.mk_var("a", Sort::Int);
    let three = store.mk_int(BigInt::from(3));

    // Create (* 3 a) and (- a)
    let three_a = store.mk_mul(vec![three, a]);
    let neg_a = store.mk_neg(a);

    // (* 3 a) + (- a) = (* 2 a)
    let result = store.mk_add(vec![three_a, neg_a]);
    let two = store.mk_int(BigInt::from(2));
    let expected = store.mk_mul(vec![two, a]);
    assert_eq!(result, expected);
}

#[test]
fn test_mul_double_negation_via_minus_one() {
    let mut store = TermStore::new();

    let a = store.mk_var("a", Sort::Int);
    let neg_one = store.mk_int(BigInt::from(-1));

    // (* -1 -1 a) = (* 1 a) = a
    let result = store.mk_mul(vec![neg_one, neg_one, a]);
    assert_eq!(result, a);
}

#[test]
fn test_ite_boolean_branch_simplification() {
    let mut store = TermStore::new();

    let c = store.mk_var("c", Sort::Bool);
    let t = store.true_term();
    let f = store.false_term();

    // (ite c true false) = c
    assert_eq!(store.mk_ite(c, t, f), c);

    // (ite c false true) = (not c)
    let not_c = store.mk_not(c);
    assert_eq!(store.mk_ite(c, f, t), not_c);

    // (ite c c false) = c
    assert_eq!(store.mk_ite(c, c, f), c);

    // (ite c true c) = c
    assert_eq!(store.mk_ite(c, t, c), c);
}

#[test]
fn test_ite_to_and_or_simplification() {
    let mut store = TermStore::new();

    let c = store.mk_var("c", Sort::Bool);
    let x = store.mk_var("x", Sort::Bool);
    let t = store.true_term();
    let f = store.false_term();

    // (ite c x false) = (and c x)
    let result = store.mk_ite(c, x, f);
    let expected = store.mk_and(vec![c, x]);
    assert_eq!(result, expected);

    // (ite c true x) = (or c x)
    let result = store.mk_ite(c, t, x);
    let expected = store.mk_or(vec![c, x]);
    assert_eq!(result, expected);

    // (ite c false x) = (and (not c) x)
    let result = store.mk_ite(c, f, x);
    let not_c = store.mk_not(c);
    let expected = store.mk_and(vec![not_c, x]);
    assert_eq!(result, expected);

    // (ite c x true) = (or (not c) x)
    let result = store.mk_ite(c, x, t);
    let not_c = store.mk_not(c);
    let expected = store.mk_or(vec![not_c, x]);
    assert_eq!(result, expected);
}

#[test]
fn test_ite_nested_simplification() {
    let mut store = TermStore::new();

    let c = store.mk_var("c", Sort::Bool);
    let x = store.mk_var("x", Sort::Bool);
    let y = store.mk_var("y", Sort::Bool);
    let z = store.mk_var("z", Sort::Bool);

    // (ite c (ite c x y) z) = (ite c x z)
    let inner = store.mk_ite(c, x, y);
    let result = store.mk_ite(c, inner, z);
    let expected = store.mk_ite(c, x, z);
    assert_eq!(result, expected);

    // (ite c x (ite c y z)) = (ite c x z)
    let inner = store.mk_ite(c, y, z);
    let result = store.mk_ite(c, x, inner);
    let expected = store.mk_ite(c, x, z);
    assert_eq!(result, expected);
}

#[test]
fn test_ite_non_bool_no_simplification() {
    let mut store = TermStore::new();

    let c = store.mk_var("c", Sort::Bool);
    let x = store.mk_var("x", Sort::Int);
    let zero = store.mk_int(BigInt::from(0));

    // (ite c x 0) should NOT simplify to (and c x) since x is Int
    let result = store.mk_ite(c, x, zero);
    // The result should be an Ite term, not an And
    match store.get(result) {
        TermData::Ite(_, _, _) => {} // expected
        _ => panic!("Expected Ite term for non-Bool branches"),
    }
}

#[test]
fn test_ite_negated_condition_normalization() {
    let mut store = TermStore::new();

    let c = store.mk_var("c", Sort::Bool);
    let x = store.mk_var("x", Sort::Int);
    let y = store.mk_var("y", Sort::Int);

    // (ite (not c) a b) -> (ite c b a)
    let not_c = store.mk_not(c);
    let ite_negated = store.mk_ite(not_c, x, y);
    let ite_positive = store.mk_ite(c, y, x);
    assert_eq!(ite_negated, ite_positive);

    // Verify the condition is positive, not negated
    if let TermData::Ite(cond, then_t, else_t) = store.get(ite_negated) {
        assert_eq!(*cond, c, "Condition should be positive (c), not (not c)");
        assert_eq!(*then_t, y, "Then branch should be y (swapped)");
        assert_eq!(*else_t, x, "Else branch should be x (swapped)");
    } else {
        panic!("Expected Ite term");
    }
}

#[test]
fn test_ite_negated_condition_with_bool_branches() {
    let mut store = TermStore::new();

    let c = store.mk_var("c", Sort::Bool);
    let t = store.true_term();
    let f = store.false_term();

    // (ite (not c) true false) -> (ite c false true) -> (not c)
    // This tests that negated condition normalization composes with other simplifications
    let not_c = store.mk_not(c);
    let result = store.mk_ite(not_c, t, f);
    // After normalization: (ite c false true) = (not c)
    assert_eq!(result, not_c);
}

#[test]
fn test_ite_double_negated_condition() {
    let mut store = TermStore::new();

    let c = store.mk_var("c", Sort::Bool);
    let x = store.mk_var("x", Sort::Int);
    let y = store.mk_var("y", Sort::Int);

    // (ite (not (not c)) a b) -> (ite (not c) b a) -> (ite c a b)
    // Double negation should fully simplify
    let not_c = store.mk_not(c);
    let not_not_c = store.mk_not(not_c);
    let result = store.mk_ite(not_not_c, x, y);

    // not_not_c simplifies to c in mk_not, so this should be (ite c x y)
    let expected = store.mk_ite(c, x, y);
    assert_eq!(result, expected);
}

#[test]
fn test_eq_bool_with_true() {
    let mut store = TermStore::new();

    let x = store.mk_var("x", Sort::Bool);
    let t = store.true_term();

    // (= x true) -> x
    assert_eq!(store.mk_eq(x, t), x);
    // (= true x) -> x
    assert_eq!(store.mk_eq(t, x), x);
}

#[test]
fn test_eq_bool_with_false() {
    let mut store = TermStore::new();

    let x = store.mk_var("x", Sort::Bool);
    let f = store.false_term();
    let not_x = store.mk_not(x);

    // (= x false) -> (not x)
    assert_eq!(store.mk_eq(x, f), not_x);
    // (= false x) -> (not x)
    assert_eq!(store.mk_eq(f, x), not_x);
}

#[test]
fn test_eq_bool_nested() {
    let mut store = TermStore::new();

    let x = store.mk_var("x", Sort::Bool);
    let y = store.mk_var("y", Sort::Bool);
    let t = store.true_term();
    let f = store.false_term();

    // (= (and x y) true) -> (and x y)
    let and_xy = store.mk_and(vec![x, y]);
    assert_eq!(store.mk_eq(and_xy, t), and_xy);

    // (= (or x y) false) -> (not (or x y)) (which mk_not may normalize via De Morgan)
    let or_xy = store.mk_or(vec![x, y]);
    let not_or = store.mk_not(or_xy);
    assert_eq!(store.mk_eq(or_xy, f), not_or);
}

#[test]
#[cfg_attr(debug_assertions, should_panic(expected = "mk_eq expects same sort"))]
fn test_eq_bool_not_applied_to_non_bool() {
    let mut store = TermStore::new();

    let x = store.mk_var("x", Sort::Int);
    let t = store.true_term();

    // (= x true) where x is Int is ill-sorted.
    // In debug builds, this should panic with a debug_assert.
    // In release builds, it produces an = term (no crash, but semantically wrong).
    let eq = store.mk_eq(x, t);

    // Release-only: Should be an = term, not simplified
    match store.get(eq) {
        TermData::App(Symbol::Named(name), _) => assert_eq!(name, "="),
        _ => panic!("Expected App term"),
    }
}

#[test]
fn test_eq_negation_lifting() {
    let mut store = TermStore::new();

    let x = store.mk_var("x", Sort::Bool);
    let y = store.mk_var("y", Sort::Bool);
    let not_x = store.mk_not(x);
    let not_y = store.mk_not(y);

    // (= (not x) (not y)) -> (= x y)
    let eq_not_not = store.mk_eq(not_x, not_y);
    let eq_xy = store.mk_eq(x, y);
    assert_eq!(eq_not_not, eq_xy);
}

#[test]
fn test_eq_negation_lifting_complex() {
    let mut store = TermStore::new();

    let a = store.mk_var("a", Sort::Bool);
    let b = store.mk_var("b", Sort::Bool);
    let c = store.mk_var("c", Sort::Bool);
    let d = store.mk_var("d", Sort::Bool);

    let and_ab = store.mk_and(vec![a, b]);
    let or_cd = store.mk_or(vec![c, d]);
    let not_and = store.mk_not(and_ab);
    let not_or = store.mk_not(or_cd);

    // (= (not (and a b)) (not (or c d)))
    // De Morgan transforms not(and(a,b)) -> or(!a, !b) and not(or(c,d)) -> and(!c, !d),
    // so negation lifting in mk_eq cannot fire (operands are no longer Not-wrapped).
    // The result is a biconditional encoding (ITE) of the De Morgan forms (#3421).
    let eq_negations = store.mk_eq(not_and, not_or);

    // #6869: Bool equalities are now kept as App("=", ...) for EUF congruence
    // closure visibility. The ITE normalization from #3421 was removed because
    // it prevented EUF from seeing alias chains. Tseitin encoding handles
    // the biconditional semantics via encode_eq.
    assert!(
        matches!(store.get(eq_negations), TermData::App(_, _)),
        "Bool eq should stay as App(\"=\", ...) for EUF visibility (#6869), got {:?}",
        store.get(eq_negations)
    );
}

#[test]
fn test_eq_reflexive_negation() {
    let mut store = TermStore::new();

    let x = store.mk_var("x", Sort::Bool);
    let not_x = store.mk_not(x);

    // (= (not x) (not x)) -> true (by reflexivity before negation lifting)
    assert_eq!(store.mk_eq(not_x, not_x), store.true_term());
}

#[test]
fn test_eq_ite_then_branch() {
    let mut store = TermStore::new();

    let c = store.mk_var("c", Sort::Bool);
    let a = store.mk_var("a", Sort::Bool);
    let b = store.mk_var("b", Sort::Bool);

    // (= (ite c a b) a) -> (or c (= b a))
    let ite = store.mk_ite(c, a, b);
    let result = store.mk_eq(ite, a);

    let eq_ba = store.mk_eq(b, a);
    let expected = store.mk_or(vec![c, eq_ba]);

    assert_eq!(result, expected);
}

#[test]
fn test_eq_ite_else_branch() {
    let mut store = TermStore::new();

    let c = store.mk_var("c", Sort::Bool);
    let a = store.mk_var("a", Sort::Bool);
    let b = store.mk_var("b", Sort::Bool);

    // (= (ite c a b) b) -> (or (not c) (= a b))
    let ite = store.mk_ite(c, a, b);
    let result = store.mk_eq(ite, b);

    let not_c = store.mk_not(c);
    let eq_ab = store.mk_eq(a, b);
    let expected = store.mk_or(vec![not_c, eq_ab]);

    assert_eq!(result, expected);
}

#[test]
fn test_eq_ite_then_branch_symmetric() {
    let mut store = TermStore::new();

    let c = store.mk_var("c", Sort::Bool);
    let a = store.mk_var("a", Sort::Bool);
    let b = store.mk_var("b", Sort::Bool);

    // (= a (ite c a b)) -> (or c (= b a))
    let ite = store.mk_ite(c, a, b);
    let result = store.mk_eq(a, ite);

    let eq_ba = store.mk_eq(b, a);
    let expected = store.mk_or(vec![c, eq_ba]);

    assert_eq!(result, expected);
}

#[test]
fn test_eq_ite_else_branch_symmetric() {
    let mut store = TermStore::new();

    let c = store.mk_var("c", Sort::Bool);
    let a = store.mk_var("a", Sort::Bool);
    let b = store.mk_var("b", Sort::Bool);

    // (= b (ite c a b)) -> (or (not c) (= a b))
    let ite = store.mk_ite(c, a, b);
    let result = store.mk_eq(b, ite);

    let not_c = store.mk_not(c);
    let eq_ab = store.mk_eq(a, b);
    let expected = store.mk_or(vec![not_c, eq_ab]);

    assert_eq!(result, expected);
}

#[test]
#[allow(clippy::many_single_char_names)]
fn test_eq_ite_same_condition() {
    let mut store = TermStore::new();

    let c = store.mk_var("c", Sort::Bool);
    let a = store.mk_var("a", Sort::Bool);
    let b = store.mk_var("b", Sort::Bool);
    let x = store.mk_var("x", Sort::Bool);
    let y = store.mk_var("y", Sort::Bool);

    // (= (ite c a b) (ite c x y)) -> (ite c (= a x) (= b y))
    let ite1 = store.mk_ite(c, a, b);
    let ite2 = store.mk_ite(c, x, y);
    let result = store.mk_eq(ite1, ite2);

    let eq_ax = store.mk_eq(a, x);
    let eq_by = store.mk_eq(b, y);
    let expected = store.mk_ite(c, eq_ax, eq_by);

    assert_eq!(result, expected);
}

#[test]
fn test_eq_ite_same_branches() {
    let mut store = TermStore::new();

    let c = store.mk_var("c", Sort::Bool);
    let a = store.mk_var("a", Sort::Bool);

    // (= (ite c a a) a) should simplify via same-branch rule first to (= a a) = true
    // The ite simplifies: (ite c a a) -> a
    let ite = store.mk_ite(c, a, a);
    assert_eq!(ite, a); // Same-branch simplification in mk_ite

    // So (= (ite c a a) a) = (= a a) = true
    let result = store.mk_eq(ite, a);
    assert_eq!(result, store.true_term());
}

#[test]
fn test_and_flattening() {
    let mut store = TermStore::new();

    let a = store.mk_var("a", Sort::Bool);
    let b = store.mk_var("b", Sort::Bool);
    let c = store.mk_var("c", Sort::Bool);

    // Create (and b c) first
    let and_bc = store.mk_and(vec![b, c]);

    // (and a (and b c)) should flatten to (and a b c)
    let result = store.mk_and(vec![a, and_bc]);

    // Verify it's a flat and with all three arguments
    if let TermData::App(Symbol::Named(name), args) = store.get(result) {
        assert_eq!(name, "and");
        assert_eq!(args.len(), 3);
        assert!(args.contains(&a));
        assert!(args.contains(&b));
        assert!(args.contains(&c));
    } else {
        panic!("Expected and App term");
    }
}

#[test]
fn test_or_flattening() {
    let mut store = TermStore::new();

    let a = store.mk_var("a", Sort::Bool);
    let b = store.mk_var("b", Sort::Bool);
    let c = store.mk_var("c", Sort::Bool);

    // Create (or b c) first
    let or_bc = store.mk_or(vec![b, c]);

    // (or a (or b c)) should flatten to (or a b c)
    let result = store.mk_or(vec![a, or_bc]);

    // Verify it's a flat or with all three arguments
    if let TermData::App(Symbol::Named(name), args) = store.get(result) {
        assert_eq!(name, "or");
        assert_eq!(args.len(), 3);
        assert!(args.contains(&a));
        assert!(args.contains(&b));
        assert!(args.contains(&c));
    } else {
        panic!("Expected or App term");
    }
}

#[test]
fn test_and_flattening_multiple_nested() {
    let mut store = TermStore::new();

    let a = store.mk_var("a", Sort::Bool);
    let b = store.mk_var("b", Sort::Bool);
    let c = store.mk_var("c", Sort::Bool);
    let d = store.mk_var("d", Sort::Bool);

    // Create (and a b) and (and c d)
    let and_ab = store.mk_and(vec![a, b]);
    let and_cd = store.mk_and(vec![c, d]);

    // (and (and a b) (and c d)) should flatten to (and a b c d)
    let result = store.mk_and(vec![and_ab, and_cd]);

    // Verify it's a flat and with all four arguments
    if let TermData::App(Symbol::Named(name), args) = store.get(result) {
        assert_eq!(name, "and");
        assert_eq!(args.len(), 4);
        assert!(args.contains(&a));
        assert!(args.contains(&b));
        assert!(args.contains(&c));
        assert!(args.contains(&d));
    } else {
        panic!("Expected and App term");
    }
}

#[test]
fn test_or_flattening_multiple_nested() {
    let mut store = TermStore::new();

    let a = store.mk_var("a", Sort::Bool);
    let b = store.mk_var("b", Sort::Bool);
    let c = store.mk_var("c", Sort::Bool);
    let d = store.mk_var("d", Sort::Bool);

    // Create (or a b) and (or c d)
    let or_ab = store.mk_or(vec![a, b]);
    let or_cd = store.mk_or(vec![c, d]);

    // (or (or a b) (or c d)) should flatten to (or a b c d)
    let result = store.mk_or(vec![or_ab, or_cd]);

    // Verify it's a flat or with all four arguments
    if let TermData::App(Symbol::Named(name), args) = store.get(result) {
        assert_eq!(name, "or");
        assert_eq!(args.len(), 4);
        assert!(args.contains(&a));
        assert!(args.contains(&b));
        assert!(args.contains(&c));
        assert!(args.contains(&d));
    } else {
        panic!("Expected or App term");
    }
}

#[test]
fn test_and_flattening_with_constant() {
    let mut store = TermStore::new();

    let a = store.mk_var("a", Sort::Bool);
    let b = store.mk_var("b", Sort::Bool);
    let t = store.true_term();

    // Create (and a b)
    let and_ab = store.mk_and(vec![a, b]);

    // (and true (and a b)) should flatten and simplify to (and a b)
    let result = store.mk_and(vec![t, and_ab]);
    assert_eq!(result, and_ab);
}

#[test]
fn test_and_flattening_to_false() {
    let mut store = TermStore::new();

    let a = store.mk_var("a", Sort::Bool);
    let b = store.mk_var("b", Sort::Bool);
    let f = store.false_term();

    // Create (and a b)
    let and_ab = store.mk_and(vec![a, b]);

    // (and false (and a b)) should simplify to false
    let result = store.mk_and(vec![f, and_ab]);
    assert_eq!(result, f);
}

#[test]
fn test_or_flattening_with_constant() {
    let mut store = TermStore::new();

    let a = store.mk_var("a", Sort::Bool);
    let b = store.mk_var("b", Sort::Bool);
    let f = store.false_term();

    // Create (or a b)
    let or_ab = store.mk_or(vec![a, b]);

    // (or false (or a b)) should flatten and simplify to (or a b)
    let result = store.mk_or(vec![f, or_ab]);
    assert_eq!(result, or_ab);
}

#[test]
fn test_or_flattening_to_true() {
    let mut store = TermStore::new();

    let a = store.mk_var("a", Sort::Bool);
    let b = store.mk_var("b", Sort::Bool);
    let t = store.true_term();

    // Create (or a b)
    let or_ab = store.mk_or(vec![a, b]);

    // (or true (or a b)) should simplify to true
    let result = store.mk_or(vec![t, or_ab]);
    assert_eq!(result, t);
}

#[test]
fn test_and_flattening_dedup() {
    let mut store = TermStore::new();

    let a = store.mk_var("a", Sort::Bool);
    let b = store.mk_var("b", Sort::Bool);

    // Create (and a b)
    let and_ab = store.mk_and(vec![a, b]);

    // (and a (and a b)) should flatten and dedup to (and a b)
    let result = store.mk_and(vec![a, and_ab]);
    assert_eq!(result, and_ab);
}

#[test]
fn test_or_flattening_dedup() {
    let mut store = TermStore::new();

    let a = store.mk_var("a", Sort::Bool);
    let b = store.mk_var("b", Sort::Bool);

    // Create (or a b)
    let or_ab = store.mk_or(vec![a, b]);

    // (or a (or a b)) should flatten and dedup to (or a b)
    let result = store.mk_or(vec![a, or_ab]);
    assert_eq!(result, or_ab);
}

#[test]
fn test_and_complement_detection() {
    let mut store = TermStore::new();

    let x = store.mk_var("x", Sort::Bool);
    let not_x = store.mk_not(x);
    let f = store.false_term();

    // (and x (not x)) = false
    assert_eq!(store.mk_and(vec![x, not_x]), f);
    // (and (not x) x) = false (order shouldn't matter)
    assert_eq!(store.mk_and(vec![not_x, x]), f);
}

#[test]
fn test_or_complement_detection() {
    let mut store = TermStore::new();

    let x = store.mk_var("x", Sort::Bool);
    let not_x = store.mk_not(x);
    let t = store.true_term();

    // (or x (not x)) = true
    assert_eq!(store.mk_or(vec![x, not_x]), t);
    // (or (not x) x) = true (order shouldn't matter)
    assert_eq!(store.mk_or(vec![not_x, x]), t);
}

#[test]
fn test_and_complement_with_other_terms() {
    let mut store = TermStore::new();

    let x = store.mk_var("x", Sort::Bool);
    let y = store.mk_var("y", Sort::Bool);
    let z = store.mk_var("z", Sort::Bool);
    let not_x = store.mk_not(x);
    let f = store.false_term();

    // (and x y (not x) z) = false
    assert_eq!(store.mk_and(vec![x, y, not_x, z]), f);
    // (and y z x (not x)) = false
    assert_eq!(store.mk_and(vec![y, z, x, not_x]), f);
}

#[test]
fn test_or_complement_with_other_terms() {
    let mut store = TermStore::new();

    let x = store.mk_var("x", Sort::Bool);
    let y = store.mk_var("y", Sort::Bool);
    let z = store.mk_var("z", Sort::Bool);
    let not_x = store.mk_not(x);
    let t = store.true_term();

    // (or x y (not x) z) = true
    assert_eq!(store.mk_or(vec![x, y, not_x, z]), t);
    // (or y z x (not x)) = true
    assert_eq!(store.mk_or(vec![y, z, x, not_x]), t);
}

#[test]
fn test_and_complement_nested() {
    let mut store = TermStore::new();

    let a = store.mk_var("a", Sort::Bool);
    let b = store.mk_var("b", Sort::Bool);
    let not_a = store.mk_not(a);
    let f = store.false_term();

    // Create (and a b) and then (and (and a b) (not a))
    // After flattening: (and a b (not a)) = false
    let and_ab = store.mk_and(vec![a, b]);
    let result = store.mk_and(vec![and_ab, not_a]);
    assert_eq!(result, f);
}

#[test]
fn test_and_complement_before_flattening_raw_not() {
    let mut store = TermStore::new();

    let x = store.mk_var("x", Sort::Bool);
    let y = store.mk_var("y", Sort::Bool);
    let f = store.false_term();

    let and_xy = store.mk_and(vec![x, y]);
    let not_and_xy = store.mk_not_raw(and_xy);

    assert_eq!(store.mk_and(vec![and_xy, not_and_xy]), f);
    assert_eq!(store.mk_and(vec![not_and_xy, and_xy]), f);
}

#[test]
fn test_or_complement_nested() {
    let mut store = TermStore::new();

    let a = store.mk_var("a", Sort::Bool);
    let b = store.mk_var("b", Sort::Bool);
    let not_a = store.mk_not(a);
    let t = store.true_term();

    // Create (or a b) and then (or (or a b) (not a))
    // After flattening: (or a b (not a)) = true
    let or_ab = store.mk_or(vec![a, b]);
    let result = store.mk_or(vec![or_ab, not_a]);
    assert_eq!(result, t);
}

#[test]
fn test_or_complement_before_flattening_raw_not() {
    let mut store = TermStore::new();

    let x = store.mk_var("x", Sort::Bool);
    let y = store.mk_var("y", Sort::Bool);
    let t = store.true_term();

    let or_xy = store.mk_or(vec![x, y]);
    let not_or_xy = store.mk_not_raw(or_xy);

    assert_eq!(store.mk_or(vec![or_xy, not_or_xy]), t);
    assert_eq!(store.mk_or(vec![not_or_xy, or_xy]), t);
}

#[test]
fn test_and_no_false_complement() {
    let mut store = TermStore::new();

    let x = store.mk_var("x", Sort::Bool);
    let y = store.mk_var("y", Sort::Bool);
    let not_y = store.mk_not(y);

    // (and x (not y)) should NOT simplify to false (no complement)
    let result = store.mk_and(vec![x, not_y]);
    // The result should be an and term, not false
    match store.get(result) {
        TermData::App(Symbol::Named(name), args) => {
            assert_eq!(name, "and");
            assert_eq!(args.len(), 2);
        }
        _ => panic!("Expected and App term"),
    }
}

#[test]
fn test_or_no_true_complement() {
    let mut store = TermStore::new();

    let x = store.mk_var("x", Sort::Bool);
    let y = store.mk_var("y", Sort::Bool);
    let not_y = store.mk_not(y);

    // (or x (not y)) should NOT simplify to true (no complement)
    let result = store.mk_or(vec![x, not_y]);
    // The result should be an or term, not true
    match store.get(result) {
        TermData::App(Symbol::Named(name), args) => {
            assert_eq!(name, "or");
            assert_eq!(args.len(), 2);
        }
        _ => panic!("Expected or App term"),
    }
}

#[test]
fn test_and_complement_complex_term() {
    let mut store = TermStore::new();

    let x = store.mk_var("x", Sort::Bool);
    let y = store.mk_var("y", Sort::Bool);
    let f = store.false_term();

    // Create (and x y) and (not (and x y))
    let and_xy = store.mk_and(vec![x, y]);
    let not_and_xy = store.mk_not(and_xy);

    // (and (and x y) (not (and x y))) = false
    assert_eq!(store.mk_and(vec![and_xy, not_and_xy]), f);
}

#[test]
fn test_or_complement_complex_term() {
    let mut store = TermStore::new();

    let x = store.mk_var("x", Sort::Bool);
    let y = store.mk_var("y", Sort::Bool);
    let t = store.true_term();

    // Create (or x y) and (not (or x y))
    let or_xy = store.mk_or(vec![x, y]);
    let not_or_xy = store.mk_not(or_xy);

    // (or (or x y) (not (or x y))) = true
    assert_eq!(store.mk_or(vec![or_xy, not_or_xy]), t);
}

#[test]
fn test_and_absorption_basic() {
    let mut store = TermStore::new();

    let x = store.mk_var("x", Sort::Bool);
    let y = store.mk_var("y", Sort::Bool);

    // Create (or x y)
    let or_xy = store.mk_or(vec![x, y]);

    // (and x (or x y)) = x
    let result = store.mk_and(vec![x, or_xy]);
    assert_eq!(result, x);
}

#[test]
fn test_or_absorption_basic() {
    let mut store = TermStore::new();

    let x = store.mk_var("x", Sort::Bool);
    let y = store.mk_var("y", Sort::Bool);

    // Create (and x y)
    let and_xy = store.mk_and(vec![x, y]);

    // (or x (and x y)) = x
    let result = store.mk_or(vec![x, and_xy]);
    assert_eq!(result, x);
}

#[test]
fn test_and_absorption_order_independent() {
    let mut store = TermStore::new();

    let x = store.mk_var("x", Sort::Bool);
    let y = store.mk_var("y", Sort::Bool);

    // Create (or x y)
    let or_xy = store.mk_or(vec![x, y]);

    // (and (or x y) x) = x (order shouldn't matter)
    let result = store.mk_and(vec![or_xy, x]);
    assert_eq!(result, x);
}

#[test]
fn test_or_absorption_order_independent() {
    let mut store = TermStore::new();

    let x = store.mk_var("x", Sort::Bool);
    let y = store.mk_var("y", Sort::Bool);

    // Create (and x y)
    let and_xy = store.mk_and(vec![x, y]);

    // (or (and x y) x) = x (order shouldn't matter)
    let result = store.mk_or(vec![and_xy, x]);
    assert_eq!(result, x);
}

#[test]
fn test_and_absorption_multiple_vars() {
    let mut store = TermStore::new();

    let x = store.mk_var("x", Sort::Bool);
    let y = store.mk_var("y", Sort::Bool);
    let z = store.mk_var("z", Sort::Bool);

    // Create (or x y z)
    let or_xyz = store.mk_or(vec![x, y, z]);

    // (and x (or x y z)) = x
    let result = store.mk_and(vec![x, or_xyz]);
    assert_eq!(result, x);

    // (and y (or x y z)) = y
    let result = store.mk_and(vec![y, or_xyz]);
    assert_eq!(result, y);
}

#[test]
fn test_or_absorption_multiple_vars() {
    let mut store = TermStore::new();

    let x = store.mk_var("x", Sort::Bool);
    let y = store.mk_var("y", Sort::Bool);
    let z = store.mk_var("z", Sort::Bool);

    // Create (and x y z)
    let and_xyz = store.mk_and(vec![x, y, z]);

    // (or x (and x y z)) = x
    let result = store.mk_or(vec![x, and_xyz]);
    assert_eq!(result, x);

    // (or y (and x y z)) = y
    let result = store.mk_or(vec![y, and_xyz]);
    assert_eq!(result, y);
}

#[test]
fn test_and_absorption_with_extra_terms() {
    let mut store = TermStore::new();

    let a = store.mk_var("a", Sort::Bool);
    let b = store.mk_var("b", Sort::Bool);
    let c = store.mk_var("c", Sort::Bool);

    // Create (or a b)
    let or_ab = store.mk_or(vec![a, b]);

    // (and a c (or a b)) should simplify to (and a c) because (or a b) is absorbed by a
    let result = store.mk_and(vec![a, c, or_ab]);

    // Should be (and a c) - the or is absorbed
    if let TermData::App(Symbol::Named(name), args) = store.get(result) {
        assert_eq!(name, "and");
        assert_eq!(args.len(), 2);
        assert!(args.contains(&a));
        assert!(args.contains(&c));
        assert!(!args.contains(&or_ab));
    } else {
        panic!("Expected and App term");
    }
}

#[test]
fn test_or_absorption_with_extra_terms() {
    let mut store = TermStore::new();

    let a = store.mk_var("a", Sort::Bool);
    let b = store.mk_var("b", Sort::Bool);
    let c = store.mk_var("c", Sort::Bool);

    // Create (and a b)
    let and_ab = store.mk_and(vec![a, b]);

    // (or a c (and a b)) should simplify to (or a c) because (and a b) is absorbed by a
    let result = store.mk_or(vec![a, c, and_ab]);

    // Should be (or a c) - the and is absorbed
    if let TermData::App(Symbol::Named(name), args) = store.get(result) {
        assert_eq!(name, "or");
        assert_eq!(args.len(), 2);
        assert!(args.contains(&a));
        assert!(args.contains(&c));
        assert!(!args.contains(&and_ab));
    } else {
        panic!("Expected or App term");
    }
}

#[test]
fn test_and_no_absorption_without_match() {
    let mut store = TermStore::new();

    let x = store.mk_var("x", Sort::Bool);
    let y = store.mk_var("y", Sort::Bool);
    let z = store.mk_var("z", Sort::Bool);

    // Create (or y z)
    let or_yz = store.mk_or(vec![y, z]);

    // (and x (or y z)) should NOT simplify - x is not in (or y z)
    let result = store.mk_and(vec![x, or_yz]);

    // Should still be an and with both terms
    if let TermData::App(Symbol::Named(name), args) = store.get(result) {
        assert_eq!(name, "and");
        assert_eq!(args.len(), 2);
    } else {
        panic!("Expected and App term");
    }
}

#[test]
fn test_or_no_absorption_without_match() {
    let mut store = TermStore::new();

    let x = store.mk_var("x", Sort::Bool);
    let y = store.mk_var("y", Sort::Bool);
    let z = store.mk_var("z", Sort::Bool);

    // Create (and y z)
    let and_yz = store.mk_and(vec![y, z]);

    // (or x (and y z)) should NOT simplify - x is not in (and y z)
    let result = store.mk_or(vec![x, and_yz]);

    // Should still be an or with both terms
    if let TermData::App(Symbol::Named(name), args) = store.get(result) {
        assert_eq!(name, "or");
        assert_eq!(args.len(), 2);
    } else {
        panic!("Expected or App term");
    }
}

#[test]
fn test_and_negation_through_absorption_basic() {
    let mut store = TermStore::new();

    let x = store.mk_var("x", Sort::Bool);
    let y = store.mk_var("y", Sort::Bool);

    // (and x (or (not x) y)) should simplify to (and x y)
    // because if x is true, (not x) is false, so (or false y) = y
    let not_x = store.mk_not(x);
    let or_notx_y = store.mk_or(vec![not_x, y]);
    let result = store.mk_and(vec![x, or_notx_y]);

    let expected = store.mk_and(vec![x, y]);
    assert_eq!(result, expected);
}

#[test]
fn test_or_negation_through_absorption_basic() {
    let mut store = TermStore::new();

    let x = store.mk_var("x", Sort::Bool);
    let y = store.mk_var("y", Sort::Bool);

    // (or x (and (not x) y)) should simplify to (or x y)
    // because if x is false, (not x) is true, so (and true y) = y
    let not_x = store.mk_not(x);
    let and_notx_y = store.mk_and(vec![not_x, y]);
    let result = store.mk_or(vec![x, and_notx_y]);

    let expected = store.mk_or(vec![x, y]);
    assert_eq!(result, expected);
}

#[test]
fn test_and_negation_through_absorption_multiple() {
    let mut store = TermStore::new();

    let x = store.mk_var("x", Sort::Bool);
    let y = store.mk_var("y", Sort::Bool);
    let z = store.mk_var("z", Sort::Bool);

    // (and x (or (not x) y z)) should simplify to (and x (or y z))
    let not_x = store.mk_not(x);
    let or_notx_yz = store.mk_or(vec![not_x, y, z]);
    let result = store.mk_and(vec![x, or_notx_yz]);

    let or_yz = store.mk_or(vec![y, z]);
    let expected = store.mk_and(vec![x, or_yz]);
    assert_eq!(result, expected);
}

#[test]
fn test_or_negation_through_absorption_multiple() {
    let mut store = TermStore::new();

    let x = store.mk_var("x", Sort::Bool);
    let y = store.mk_var("y", Sort::Bool);
    let z = store.mk_var("z", Sort::Bool);

    // (or x (and (not x) y z)) should simplify to (or x (and y z))
    let not_x = store.mk_not(x);
    let and_notx_yz = store.mk_and(vec![not_x, y, z]);
    let result = store.mk_or(vec![x, and_notx_yz]);

    let and_yz = store.mk_and(vec![y, z]);
    let expected = store.mk_or(vec![x, and_yz]);
    assert_eq!(result, expected);
}

#[test]
fn test_and_negation_through_absorption_removes_or() {
    let mut store = TermStore::new();

    let x = store.mk_var("x", Sort::Bool);

    // (and x (or (not x))) simplifies:
    // First, (or (not x)) = (not x) (single element)
    // Then (and x (not x)) = false (complement)
    let not_x = store.mk_not(x);
    let or_notx = store.mk_or(vec![not_x]);
    let result = store.mk_and(vec![x, or_notx]);

    let expected = store.false_term();
    assert_eq!(result, expected);
}

#[test]
fn test_or_negation_through_absorption_removes_and() {
    let mut store = TermStore::new();

    let x = store.mk_var("x", Sort::Bool);

    // (or x (and (not x))) simplifies:
    // First, (and (not x)) = (not x) (single element)
    // Then (or x (not x)) = true (complement)
    let not_x = store.mk_not(x);
    let and_notx = store.mk_and(vec![not_x]);
    let result = store.mk_or(vec![x, and_notx]);

    let expected = store.true_term();
    assert_eq!(result, expected);
}

#[test]
fn test_and_negation_through_absorption_multiple_conjuncts() {
    let mut store = TermStore::new();

    let a = store.mk_var("a", Sort::Bool);
    let b = store.mk_var("b", Sort::Bool);
    let y = store.mk_var("y", Sort::Bool);

    // (and a b (or (not a) (not b) y)) should simplify to (and a b y)
    // because (not a) and (not b) are both removed from the or
    let not_a = store.mk_not(a);
    let not_b = store.mk_not(b);
    let or_term = store.mk_or(vec![not_a, not_b, y]);
    let result = store.mk_and(vec![a, b, or_term]);

    let expected = store.mk_and(vec![a, b, y]);
    assert_eq!(result, expected);
}

#[test]
fn test_or_negation_through_absorption_multiple_disjuncts() {
    let mut store = TermStore::new();

    let a = store.mk_var("a", Sort::Bool);
    let b = store.mk_var("b", Sort::Bool);
    let y = store.mk_var("y", Sort::Bool);

    // (or a b (and (not a) (not b) y)) should simplify to (or a b y)
    // because (not a) and (not b) are both removed from the and
    let not_a = store.mk_not(a);
    let not_b = store.mk_not(b);
    let and_term = store.mk_and(vec![not_a, not_b, y]);
    let result = store.mk_or(vec![a, b, and_term]);

    let expected = store.mk_or(vec![a, b, y]);
    assert_eq!(result, expected);
}

#[test]
fn test_and_negation_through_no_false_positive() {
    let mut store = TermStore::new();

    let x = store.mk_var("x", Sort::Bool);
    let y = store.mk_var("y", Sort::Bool);
    let z = store.mk_var("z", Sort::Bool);

    // (and x (or y z)) should NOT simplify - no (not x) in the or
    let or_yz = store.mk_or(vec![y, z]);
    let result = store.mk_and(vec![x, or_yz]);

    // Should still be an and with both terms
    if let TermData::App(Symbol::Named(name), args) = store.get(result) {
        assert_eq!(name, "and");
        assert_eq!(args.len(), 2);
        assert!(args.contains(&x));
        assert!(args.contains(&or_yz));
    } else {
        panic!("Expected and App term");
    }
}

#[test]
fn test_or_negation_through_no_false_positive() {
    let mut store = TermStore::new();

    let x = store.mk_var("x", Sort::Bool);
    let y = store.mk_var("y", Sort::Bool);
    let z = store.mk_var("z", Sort::Bool);

    // (or x (and y z)) should NOT simplify - no (not x) in the and
    let and_yz = store.mk_and(vec![y, z]);
    let result = store.mk_or(vec![x, and_yz]);

    // Should still be an or with both terms
    if let TermData::App(Symbol::Named(name), args) = store.get(result) {
        assert_eq!(name, "or");
        assert_eq!(args.len(), 2);
        assert!(args.contains(&x));
        assert!(args.contains(&and_yz));
    } else {
        panic!("Expected or App term");
    }
}

#[test]
fn test_not_ite_normalization_basic() {
    let mut store = TermStore::new();

    let c = store.mk_var("c", Sort::Bool);
    let a = store.mk_var("a", Sort::Bool);
    let b = store.mk_var("b", Sort::Bool);

    // (not (ite c a b)) -> (ite c (not a) (not b))
    let ite = store.mk_ite(c, a, b);
    let not_ite = store.mk_not(ite);

    // Result should be (ite c (not a) (not b))
    let not_a = store.mk_not(a);
    let not_b = store.mk_not(b);
    let expected = store.mk_ite(c, not_a, not_b);

    assert_eq!(not_ite, expected);
}

#[test]
fn test_not_ite_with_true_false_branches() {
    let mut store = TermStore::new();

    let c = store.mk_var("c", Sort::Bool);
    let t = store.true_term();
    let f = store.false_term();

    // (not (ite c true false)) = (not c)
    // Because (ite c true false) = c, and (not c) = (not c)
    let ite = store.mk_ite(c, t, f);
    assert_eq!(ite, c); // First the ite simplifies to c
    let not_ite = store.mk_not(ite);
    let not_c = store.mk_not(c);
    assert_eq!(not_ite, not_c);
}

#[test]
fn test_not_ite_with_false_true_branches() {
    let mut store = TermStore::new();

    let c = store.mk_var("c", Sort::Bool);
    let t = store.true_term();
    let f = store.false_term();

    // (not (ite c false true)) = c
    // Because (ite c false true) = (not c), and (not (not c)) = c
    let ite = store.mk_ite(c, f, t);
    let not_c = store.mk_not(c);
    assert_eq!(ite, not_c); // First the ite simplifies to (not c)
    let not_ite = store.mk_not(ite);
    assert_eq!(not_ite, c); // Double negation elimination
}

#[test]
fn test_not_ite_with_true_branch() {
    let mut store = TermStore::new();

    let c = store.mk_var("c", Sort::Bool);
    let a = store.mk_var("a", Sort::Bool);
    let t = store.true_term();

    // (not (ite c true a)) = (ite c false (not a)) = (and (not c) (not a))
    // Because (ite c true a) = (or c a), and (not (or c a)) = (and (not c) (not a))
    let ite = store.mk_ite(c, t, a);
    let not_ite = store.mk_not(ite);

    // This should simplify via De Morgan: (not (or c a)) -> (and (not c) (not a))
    let not_c = store.mk_not(c);
    let not_a = store.mk_not(a);
    let expected = store.mk_and(vec![not_c, not_a]);
    assert_eq!(not_ite, expected);
}

#[test]
fn test_not_ite_with_false_branch() {
    let mut store = TermStore::new();

    let c = store.mk_var("c", Sort::Bool);
    let a = store.mk_var("a", Sort::Bool);
    let f = store.false_term();

    // (not (ite c a false)) = (ite c (not a) true) = (or (not c) (not a))
    // Because (ite c a false) = (and c a), and (not (and c a)) = (or (not c) (not a))
    let ite = store.mk_ite(c, a, f);
    let not_ite = store.mk_not(ite);

    // This should simplify via De Morgan: (not (and c a)) -> (or (not c) (not a))
    let not_c = store.mk_not(c);
    let not_a = store.mk_not(a);
    let expected = store.mk_or(vec![not_c, not_a]);
    assert_eq!(not_ite, expected);
}

#[test]
fn test_not_ite_same_branches() {
    let mut store = TermStore::new();

    let c = store.mk_var("c", Sort::Bool);
    let a = store.mk_var("a", Sort::Bool);

    // (not (ite c a a)) = (not a)
    // Because (ite c a a) = a, and (not a) = (not a)
    let ite = store.mk_ite(c, a, a);
    assert_eq!(ite, a); // First the ite simplifies to a
    let not_ite = store.mk_not(ite);
    let not_a = store.mk_not(a);
    assert_eq!(not_ite, not_a);
}

#[test]
fn test_not_ite_double_negation() {
    let mut store = TermStore::new();

    let c = store.mk_var("c", Sort::Bool);
    let a = store.mk_var("a", Sort::Bool);
    let b = store.mk_var("b", Sort::Bool);

    // (not (not (ite c a b))) = (ite c a b)
    let ite = store.mk_ite(c, a, b);
    let not_ite = store.mk_not(ite);
    let not_not_ite = store.mk_not(not_ite);

    // After double negation elimination, we should get the original
    // Note: the ite may be normalized differently
    assert_eq!(not_not_ite, ite);
}

#[test]
fn test_not_ite_non_bool_unchanged() {
    let mut store = TermStore::new();

    let c = store.mk_var("c", Sort::Bool);
    let x = store.mk_var("x", Sort::Int);
    let y = store.mk_var("y", Sort::Int);

    // (ite c x y) where x, y are Int cannot have (not ...) applied meaningfully
    // This test verifies the ite itself is constructed correctly
    let ite = store.mk_ite(c, x, y);
    assert!(matches!(store.get(ite), TermData::Ite(_, _, _)));
}

#[test]
fn test_not_ite_nested() {
    let mut store = TermStore::new();

    let c1 = store.mk_var("c1", Sort::Bool);
    let c2 = store.mk_var("c2", Sort::Bool);
    let a = store.mk_var("a", Sort::Bool);
    let b = store.mk_var("b", Sort::Bool);

    // (not (ite c1 (ite c2 a b) false))
    // = (not (and c1 (ite c2 a b)))           -- ite with false branch
    // = (or (not c1) (not (ite c2 a b)))     -- De Morgan
    // = (or (not c1) (ite c2 (not a) (not b))) -- ITE negation
    let inner_ite = store.mk_ite(c2, a, b);
    let f = store.false_term();
    let outer_ite = store.mk_ite(c1, inner_ite, f);
    let result = store.mk_not(outer_ite);

    // Build the expected result
    let not_c1 = store.mk_not(c1);
    let not_a = store.mk_not(a);
    let not_b = store.mk_not(b);
    let inner_neg = store.mk_ite(c2, not_a, not_b);
    let expected = store.mk_or(vec![not_c1, inner_neg]);

    assert_eq!(result, expected);
}

#[test]
fn test_xor_same_operand() {
    let mut store = TermStore::new();

    let x = store.mk_var("x", Sort::Bool);
    // (xor x x) = false
    let result = store.mk_xor(x, x);
    assert_eq!(result, store.false_term());
}

#[test]
fn test_xor_with_true() {
    let mut store = TermStore::new();

    let x = store.mk_var("x", Sort::Bool);
    let t = store.true_term();

    // (xor x true) = (not x)
    let result = store.mk_xor(x, t);
    assert_eq!(result, store.mk_not(x));

    // (xor true x) = (not x)
    let result2 = store.mk_xor(t, x);
    assert_eq!(result2, store.mk_not(x));
}

#[test]
fn test_xor_with_false() {
    let mut store = TermStore::new();

    let x = store.mk_var("x", Sort::Bool);
    let f = store.false_term();

    // (xor x false) = x
    let result = store.mk_xor(x, f);
    assert_eq!(result, x);

    // (xor false x) = x
    let result2 = store.mk_xor(f, x);
    assert_eq!(result2, x);
}

#[test]
fn test_xor_complement() {
    let mut store = TermStore::new();

    let x = store.mk_var("x", Sort::Bool);
    let not_x = store.mk_not(x);

    // (xor x (not x)) = true
    let result = store.mk_xor(x, not_x);
    assert_eq!(result, store.true_term());

    // (xor (not x) x) = true
    let result2 = store.mk_xor(not_x, x);
    assert_eq!(result2, store.true_term());
}

#[test]
fn test_xor_double_negation_lifting() {
    let mut store = TermStore::new();

    let x = store.mk_var("x", Sort::Bool);
    let y = store.mk_var("y", Sort::Bool);
    let not_x = store.mk_not(x);
    let not_y = store.mk_not(y);

    // (xor (not x) (not y)) = (xor x y)
    let result = store.mk_xor(not_x, not_y);
    let expected = store.mk_xor(x, y);
    assert_eq!(result, expected);
}

#[test]
fn test_xor_canonical_order() {
    let mut store = TermStore::new();

    let x = store.mk_var("x", Sort::Bool);
    let y = store.mk_var("y", Sort::Bool);

    // (xor x y) and (xor y x) should produce the same canonical form
    let result1 = store.mk_xor(x, y);
    let result2 = store.mk_xor(y, x);
    assert_eq!(result1, result2);
}
