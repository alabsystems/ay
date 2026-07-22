// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

mod arithmetic;
mod bitvector_array;
mod boolean;
mod memory_limit;

#[test]
fn speculative_rollback_is_store_bound_affine_and_prunes_term_sidecars() {
    let mut store = TermStore::new();
    let stable = store.mk_var("stable", Sort::Bool);
    let checkpoint = store.rollback_checkpoint();
    let scratch = store.mk_var("scratch", Sort::Bool);
    let scratch_not = store.mk_not(scratch);
    let scratch_quantifier = store.mk_forall(vec![("q".to_string(), Sort::Bool)], scratch);
    store.mark_no_mbqi(scratch_quantifier);
    store.set_quantifier_id(scratch_quantifier, "scratch-qid".to_string());
    let before_rollback = store.len();

    store.rollback_to(checkpoint);

    assert!(store.len() < before_rollback);
    assert_eq!(store.get(stable), &TermData::Var("stable".to_string(), 0));
    assert_eq!(store.true_term().index(), 0);
    assert_eq!(store.false_term().index(), 1);
    assert!(!store.has_var_name("scratch"));
    assert!(!store.is_no_mbqi(scratch_quantifier));
    assert_eq!(store.quantifier_id(scratch_quantifier), None);

    let replacement = store.mk_var("replacement", Sort::Bool);
    assert_eq!(
        replacement, scratch,
        "discarded suffix IDs should be reusable"
    );
    let replacement_not = store.mk_not(replacement);
    assert_eq!(
        store.get(replacement_not),
        &TermData::Not(replacement),
        "the discarded not-cache result {scratch_not} must not survive ID reuse"
    );
}

#[test]
#[should_panic(expected = "term rollback checkpoint belongs to a different store")]
fn speculative_rollback_rejects_checkpoint_from_cloned_store() {
    let store = TermStore::new();
    let checkpoint = store.rollback_checkpoint();
    let mut cloned = store.clone();
    cloned.rollback_to(checkpoint);
}

#[test]
#[should_panic(expected = "term rollback checkpoint is stale or out of order")]
fn speculative_rollback_rejects_older_nested_checkpoint() {
    let mut store = TermStore::new();
    let outer = store.rollback_checkpoint();
    let _scratch = store.mk_var("scratch", Sort::Bool);
    let inner = store.rollback_checkpoint();
    let _more_scratch = store.mk_var("more-scratch", Sort::Bool);
    store.rollback_to(inner);
    store.rollback_to(outer);
}

#[test]
fn speculative_rollback_preserves_preallocated_boolean_floor() {
    let mut store = TermStore::new();
    let checkpoint = store.rollback_checkpoint();
    let _scratch = store.mk_var("scratch", Sort::Bool);
    store.rollback_to(checkpoint);
    assert_eq!(store.len(), 2);
    assert_eq!(
        store.get(store.true_term()),
        &TermData::Const(Constant::Bool(true))
    );
    assert_eq!(
        store.get(store.false_term()),
        &TermData::Const(Constant::Bool(false))
    );
}

#[test]
fn test_hash_consing() {
    let mut store = TermStore::new();

    let x1 = store.mk_var("x", Sort::Int);
    let x2 = store.mk_var("x", Sort::Int);

    // Same variable should return same ID
    assert_eq!(x1, x2);
}

#[test]
fn test_equality() {
    let mut store = TermStore::new();

    let x = store.mk_var("x", Sort::Int);
    let y = store.mk_var("y", Sort::Int);

    // x = x is true
    assert_eq!(store.mk_eq(x, x), store.true_term());

    // x = y and y = x should be the same term
    let eq1 = store.mk_eq(x, y);
    let eq2 = store.mk_eq(y, x);
    assert_eq!(eq1, eq2);
}

#[test]
fn test_find_eq_returns_existing_canonical_equality_only() {
    let mut store = TermStore::new();

    let x = store.mk_var("x", Sort::Int);
    let y = store.mk_var("y", Sort::Int);
    let eq = store.mk_eq(x, y);

    assert_eq!(store.find_eq(x, y), Some(eq));
    assert_eq!(store.find_eq(y, x), Some(eq));

    let b1 = store.mk_var("b1", Sort::Bool);
    let b2 = store.mk_var("b2", Sort::Bool);
    let bool_eq = store.mk_eq(b1, b2);

    // Bool equalities are now kept as App("=", ...) for EUF visibility (#6869).
    assert_eq!(store.find_eq(b1, b2), Some(bool_eq));
    assert_ne!(bool_eq, store.true_term());
}

#[test]
fn test_sort_aware_interning_seq_empty_cross_sort() {
    // #6734: a sort-polymorphic nullary constructor (`seq.empty`) carries its
    // element sort ONLY in the requested `sort`, not in the `TermData`
    // (`App("seq.empty", [])` is identical for every element sort). Hash-consing
    // must be SORT-AWARE: the (Seq Bool) empty and the (Seq Int) empty are
    // DISTINCT values and must get DISTINCT TermIds with their correct sorts.
    let mut store = TermStore::new();

    let bool_empty = store.mk_app(
        Symbol::named("seq.empty"),
        Vec::<TermId>::new(),
        Sort::seq(Sort::Bool),
    );
    let int_empty = store.mk_app(
        Symbol::named("seq.empty"),
        Vec::<TermId>::new(),
        Sort::seq(Sort::Int),
    );

    // Different sorts => different interned identities.
    assert_ne!(
        bool_empty, int_empty,
        "cross-sort seq.empty must not be merged into one TermId"
    );
    // Each TermId carries its own correct sort.
    assert_eq!(store.sort(bool_empty), &Sort::seq(Sort::Bool));
    assert_eq!(store.sort(int_empty), &Sort::seq(Sort::Int));

    // Re-requesting the same (TermData, sort) still hash-conses (idempotent).
    let bool_empty2 = store.mk_app(
        Symbol::named("seq.empty"),
        Vec::<TermId>::new(),
        Sort::seq(Sort::Bool),
    );
    let int_empty2 = store.mk_app(
        Symbol::named("seq.empty"),
        Vec::<TermId>::new(),
        Sort::seq(Sort::Int),
    );
    assert_eq!(bool_empty, bool_empty2);
    assert_eq!(int_empty, int_empty2);
}

#[test]
fn test_sort_aware_interning_generic_nullary_app_cross_sort() {
    // The same protection applies to ANY sort-polymorphic nullary App term
    // built via the generic `(as <name> <sort>)` path (e.g. `re.none`,
    // user constants). Identical TermData + different sort => distinct ids.
    let mut store = TermStore::new();

    let a_int = store.mk_app(Symbol::named("poly.const"), Vec::<TermId>::new(), Sort::Int);
    let a_bool = store.mk_app(
        Symbol::named("poly.const"),
        Vec::<TermId>::new(),
        Sort::Bool,
    );

    assert_ne!(a_int, a_bool);
    assert_eq!(store.sort(a_int), &Sort::Int);
    assert_eq!(store.sort(a_bool), &Sort::Bool);
}

#[test]
fn test_bitvec_constants() {
    let mut store = TermStore::new();

    let bv1 = store.mk_bitvec(BigInt::from(0xFF), 8);
    let bv2 = store.mk_bitvec(BigInt::from(0xFF), 8);
    let bv3 = store.mk_bitvec(BigInt::from(0xFF), 16);

    assert_eq!(bv1, bv2);
    assert_ne!(bv1, bv3); // Different width
}

#[test]
fn test_fresh_vars() {
    let mut store = TermStore::new();

    let v1 = store.mk_fresh_var("tseitin", Sort::Bool);
    let v2 = store.mk_fresh_var("tseitin", Sort::Bool);
    let v3 = store.mk_fresh_var("tseitin", Sort::Bool);

    assert_ne!(v1, v2);
    assert_ne!(v2, v3);
}

#[test]
fn test_fresh_var_avoids_declared_name_collisions() {
    let mut store = TermStore::new();

    // Declare a global name that would collide with the first mk_fresh_var("x", ...)
    // after the mk_var increments the counter to 1.
    let _ = store.mk_var("x_1", Sort::Int);

    let fresh = store.mk_fresh_var("x", Sort::Int);
    let fresh_name = match store.get(fresh) {
        TermData::Var(name, _) => name.clone(),
        other => panic!("Expected Var from mk_fresh_var, got {other:?}"),
    };
    assert_eq!(fresh_name, "x_2");

    // Declaring the same name later should NOT reuse the fresh var.
    let declared = store.mk_var(fresh_name, Sort::Int);
    assert_ne!(fresh, declared);
}

#[test]
fn test_app_canonical_form() {
    let mut store = TermStore::new();

    let x = store.mk_var("x", Sort::Bool);
    let y = store.mk_var("y", Sort::Bool);
    let z = store.mk_var("z", Sort::Bool);

    // and(x, y, z) and and(z, y, x) should be the same
    let and1 = store.mk_and(vec![x, y, z]);
    let and2 = store.mk_and(vec![z, y, x]);
    assert_eq!(and1, and2);
}

#[test]
fn test_abs() {
    let mut store = TermStore::new();

    let neg_five = store.mk_int(BigInt::from(-5));
    let five = store.mk_int(BigInt::from(5));
    let zero = store.mk_int(BigInt::from(0));

    // |−5| = 5
    assert_eq!(store.mk_abs(neg_five), five);
    // |5| = 5
    assert_eq!(store.mk_abs(five), five);
    // |0| = 0
    assert_eq!(store.mk_abs(zero), zero);
}

/// PROVER: Verify abs ITE expansion is correct
///
/// abs(x) should expand to (ite (>= x 0) x (- x))
/// Note: mk_ge normalizes to mk_le, so (>= x 0) becomes (<= 0 x)
/// This is critical for LIA/LRA theories to reason about absolute value.
#[test]
fn prover_abs_ite_expansion() {
    let mut store = TermStore::new();
    let x = store.mk_var("x", Sort::Int);

    let result = store.mk_abs(x);

    // Result should be an ITE term
    match store.get(result) {
        TermData::Ite(cond, then_br, else_br) => {
            // Condition should be (<= 0 x) which is semantically (>= x 0)
            match store.get(*cond) {
                TermData::App(Symbol::Named(op), args) => {
                    assert_eq!(op, "<=", "Condition should be <= (normalized from >=)");
                    assert_eq!(args.len(), 2);
                    // First arg should be 0
                    assert!(
                        store.get_int(args[0]) == Some(&BigInt::from(0)),
                        "First arg should be 0"
                    );
                    // Second arg should be x
                    assert_eq!(args[1], x, "Second arg should be x");
                }
                other => panic!("Expected <= term in condition, got {other:?}"),
            }
            // Then branch should be x
            assert_eq!(*then_br, x, "Then branch should be x");
            // Else branch should be (- x) or negation of x
            match store.get(*else_br) {
                TermData::App(Symbol::Named(op), args) => {
                    assert!(
                        op == "-" || op == "*",
                        "Else branch should be negation, got op={op}"
                    );
                    // Should involve x
                    assert!(
                        args.contains(&x) || args.iter().any(|&a| {
                            matches!(store.get(a), TermData::App(_, inner) if inner.contains(&x))
                        }),
                        "Else branch should involve x"
                    );
                }
                other => panic!("Expected negation in else branch, got {other:?}"),
            }
        }
        other => panic!("Expected ITE term for abs(x), got {other:?}"),
    }
}

/// PROVER: Verify min ITE expansion is correct
///
/// min(x, y) should expand to (ite (<= x y) x y)
#[test]
fn prover_min_ite_expansion() {
    let mut store = TermStore::new();
    let x = store.mk_var("x", Sort::Int);
    let y = store.mk_var("y", Sort::Int);

    let result = store.mk_min(x, y);

    // Result should be an ITE term
    match store.get(result) {
        TermData::Ite(cond, then_br, else_br) => {
            // Condition should be (<= x y)
            match store.get(*cond) {
                TermData::App(Symbol::Named(op), args) => {
                    assert_eq!(op, "<=", "Condition should be <=");
                    assert_eq!(args.len(), 2);
                    assert_eq!(args[0], x, "First arg should be x");
                    assert_eq!(args[1], y, "Second arg should be y");
                }
                other => panic!("Expected <= term in condition, got {other:?}"),
            }
            // Then branch should be x
            assert_eq!(*then_br, x, "Then branch should be x");
            // Else branch should be y
            assert_eq!(*else_br, y, "Else branch should be y");
        }
        other => panic!("Expected ITE term for min(x, y), got {other:?}"),
    }
}

/// PROVER: Verify min constant folding
#[test]
fn prover_min_constant_folding() {
    let mut store = TermStore::new();

    let three = store.mk_int(BigInt::from(3));
    let five = store.mk_int(BigInt::from(5));
    let neg_two = store.mk_int(BigInt::from(-2));

    // min(3, 5) = 3
    assert_eq!(store.mk_min(three, five), three);
    // min(5, 3) = 3
    assert_eq!(store.mk_min(five, three), three);
    // min(-2, 5) = -2
    assert_eq!(store.mk_min(neg_two, five), neg_two);
    // min(x, x) = x
    let x = store.mk_var("x", Sort::Int);
    assert_eq!(store.mk_min(x, x), x);
}

/// PROVER: Verify max ITE expansion is correct
///
/// max(x, y) should expand to (ite (>= x y) x y)
/// Note: mk_ge normalizes to mk_le, so (>= x y) becomes (<= y x)
#[test]
fn prover_max_ite_expansion() {
    let mut store = TermStore::new();
    let x = store.mk_var("x", Sort::Int);
    let y = store.mk_var("y", Sort::Int);

    let result = store.mk_max(x, y);

    // Result should be an ITE term
    match store.get(result) {
        TermData::Ite(cond, then_br, else_br) => {
            // Condition should be (<= y x) which is semantically (>= x y)
            match store.get(*cond) {
                TermData::App(Symbol::Named(op), args) => {
                    assert_eq!(op, "<=", "Condition should be <= (normalized from >=)");
                    assert_eq!(args.len(), 2);
                    assert_eq!(args[0], y, "First arg should be y");
                    assert_eq!(args[1], x, "Second arg should be x");
                }
                other => panic!("Expected <= term in condition, got {other:?}"),
            }
            // Then branch should be x
            assert_eq!(*then_br, x, "Then branch should be x");
            // Else branch should be y
            assert_eq!(*else_br, y, "Else branch should be y");
        }
        other => panic!("Expected ITE term for max(x, y), got {other:?}"),
    }
}

/// PROVER: Verify max constant folding
#[test]
fn prover_max_constant_folding() {
    let mut store = TermStore::new();

    let three = store.mk_int(BigInt::from(3));
    let five = store.mk_int(BigInt::from(5));
    let neg_two = store.mk_int(BigInt::from(-2));

    // max(3, 5) = 5
    assert_eq!(store.mk_max(three, five), five);
    // max(5, 3) = 5
    assert_eq!(store.mk_max(five, three), five);
    // max(-2, 5) = 5
    assert_eq!(store.mk_max(neg_two, five), five);
    // max(x, x) = x
    let x = store.mk_var("x", Sort::Int);
    assert_eq!(store.mk_max(x, x), x);
}

#[test]
fn test_partial_folding() {
    let mut store = TermStore::new();

    let x = store.mk_var("x", Sort::Int);
    let two = store.mk_int(BigInt::from(2));
    let three = store.mk_int(BigInt::from(3));
    let five = store.mk_int(BigInt::from(5));

    // x + 2 + 3 should simplify to x + 5
    let result = store.mk_add(vec![x, two, three]);

    // The result should contain x and 5, not 2 and 3
    if let TermData::App(Symbol::Named(name), args) = store.get(result) {
        assert_eq!(name, "+");
        assert_eq!(args.len(), 2);
        // One should be x, one should be 5
        assert!(args.contains(&x));
        assert!(args.contains(&five));
    } else {
        panic!("Expected App term");
    }
}

#[test]
fn test_add_flattening() {
    let mut store = TermStore::new();

    let a = store.mk_var("a", Sort::Int);
    let b = store.mk_var("b", Sort::Int);
    let c = store.mk_var("c", Sort::Int);

    // Create (+ a b)
    let add_ab = store.mk_add(vec![a, b]);

    // (+ (+ a b) c) should flatten to (+ a b c)
    let result = store.mk_add(vec![add_ab, c]);

    // Verify it's a flat addition with all three arguments
    if let TermData::App(Symbol::Named(name), args) = store.get(result) {
        assert_eq!(name, "+");
        assert_eq!(args.len(), 3);
        assert!(args.contains(&a));
        assert!(args.contains(&b));
        assert!(args.contains(&c));
    } else {
        panic!("Expected + App term");
    }
}

#[test]
fn test_add_flattening_nested() {
    let mut store = TermStore::new();

    let a = store.mk_var("a", Sort::Int);
    let b = store.mk_var("b", Sort::Int);
    let c = store.mk_var("c", Sort::Int);
    let d = store.mk_var("d", Sort::Int);

    // Create (+ a b) and (+ c d)
    let add_ab = store.mk_add(vec![a, b]);
    let add_cd = store.mk_add(vec![c, d]);

    // (+ (+ a b) (+ c d)) should flatten to (+ a b c d)
    let result = store.mk_add(vec![add_ab, add_cd]);

    // Verify it's a flat addition with all four arguments
    if let TermData::App(Symbol::Named(name), args) = store.get(result) {
        assert_eq!(name, "+");
        assert_eq!(args.len(), 4);
        assert!(args.contains(&a));
        assert!(args.contains(&b));
        assert!(args.contains(&c));
        assert!(args.contains(&d));
    } else {
        panic!("Expected + App term");
    }
}

#[test]
fn test_add_flattening_with_constants() {
    let mut store = TermStore::new();

    let a = store.mk_var("a", Sort::Int);
    let two = store.mk_int(BigInt::from(2));
    let three = store.mk_int(BigInt::from(3));

    // Create (+ a 2)
    let add_a2 = store.mk_add(vec![a, two]);

    // (+ (+ a 2) 3) should flatten and fold constants to (+ a 5)
    let result = store.mk_add(vec![add_a2, three]);

    // Verify constants were folded
    if let TermData::App(Symbol::Named(name), args) = store.get(result) {
        assert_eq!(name, "+");
        assert_eq!(args.len(), 2);
        assert!(args.contains(&a));
        // One arg should be 5
        let has_five = args
            .iter()
            .any(|&arg| store.get_int(arg).is_some_and(|n| *n == BigInt::from(5)));
        assert!(has_five);
    } else {
        panic!("Expected + App term");
    }
}

#[test]
fn test_additive_inverse_detection() {
    let mut store = TermStore::new();

    let a = store.mk_var("a", Sort::Int);
    let neg_a = store.mk_neg(a);
    let zero = store.mk_int(BigInt::from(0));

    // a + (-a) = 0
    let result = store.mk_add(vec![a, neg_a]);
    assert_eq!(result, zero);
}

#[test]
fn test_additive_inverse_detection_multiple() {
    let mut store = TermStore::new();

    let a = store.mk_var("a", Sort::Int);
    let b = store.mk_var("b", Sort::Int);
    let neg_a = store.mk_neg(a);

    // a + b + (-a) = b
    let result = store.mk_add(vec![a, b, neg_a]);
    assert_eq!(result, b);
}

#[test]
fn test_additive_inverse_with_constant() {
    let mut store = TermStore::new();

    let a = store.mk_var("a", Sort::Int);
    let neg_a = store.mk_neg(a);
    let five = store.mk_int(BigInt::from(5));

    // a + (-a) + 5 = 5
    let result = store.mk_add(vec![a, neg_a, five]);
    assert_eq!(result, five);
}

#[test]
fn test_coefficient_collection_basic() {
    let mut store = TermStore::new();

    let a = store.mk_var("a", Sort::Int);
    let two = store.mk_int(BigInt::from(2));
    let three = store.mk_int(BigInt::from(3));
    let five = store.mk_int(BigInt::from(5));

    // Create (* 2 a) and (* 3 a)
    let two_a = store.mk_mul(vec![two, a]);
    let three_a = store.mk_mul(vec![three, a]);

    // (* 2 a) + (* 3 a) = (* 5 a)
    let result = store.mk_add(vec![two_a, three_a]);
    let expected = store.mk_mul(vec![five, a]);
    assert_eq!(result, expected);
}

#[test]
fn test_coefficient_collection_to_zero() {
    let mut store = TermStore::new();

    let a = store.mk_var("a", Sort::Int);
    let two = store.mk_int(BigInt::from(2));
    let neg_two = store.mk_int(BigInt::from(-2));
    let zero = store.mk_int(BigInt::from(0));

    // Create (* 2 a) and (* -2 a)
    let two_a = store.mk_mul(vec![two, a]);
    let neg_two_a = store.mk_mul(vec![neg_two, a]);

    // (* 2 a) + (* -2 a) = 0
    let result = store.mk_add(vec![two_a, neg_two_a]);
    assert_eq!(result, zero);
}

#[test]
fn test_coefficient_collection_to_single() {
    let mut store = TermStore::new();

    let a = store.mk_var("a", Sort::Int);
    let two = store.mk_int(BigInt::from(2));
    let neg_one = store.mk_int(BigInt::from(-1));

    // Create (* 2 a) and (* -1 a)
    let two_a = store.mk_mul(vec![two, a]);
    let neg_one_a = store.mk_mul(vec![neg_one, a]);

    // (* 2 a) + (* -1 a) = a
    let result = store.mk_add(vec![two_a, neg_one_a]);
    assert_eq!(result, a);
}

#[test]
fn test_coefficient_collection_mixed() {
    let mut store = TermStore::new();

    let a = store.mk_var("a", Sort::Int);
    let b = store.mk_var("b", Sort::Int);
    let two = store.mk_int(BigInt::from(2));
    let three = store.mk_int(BigInt::from(3));

    // Create (* 2 a), a, and (* 3 b)
    let two_a = store.mk_mul(vec![two, a]);
    let three_b = store.mk_mul(vec![three, b]);

    // (* 2 a) + a + (* 3 b) should combine 2a + 1a = 3a
    let result = store.mk_add(vec![two_a, a, three_b]);

    // Result should be (+ (* 3 a) (* 3 b)) - though order may vary
    if let TermData::App(Symbol::Named(name), args) = store.get(result) {
        assert_eq!(name, "+");
        assert_eq!(args.len(), 2);
        // Both should be multiplications with coefficient 3
        for &arg in args {
            if let TermData::App(Symbol::Named(op), factors) = store.get(arg) {
                assert_eq!(op, "*");
                assert_eq!(factors.len(), 2);
                // The constant can be at either position (mk_mul puts it at the end)
                let has_coeff_3 = factors
                    .iter()
                    .any(|&f| store.get_int(f) == Some(&BigInt::from(3)));
                assert!(has_coeff_3, "Expected coefficient 3 in multiplication");
            } else {
                panic!("Expected multiplication");
            }
        }
    } else {
        panic!("Expected + App term");
    }
}

#[test]
fn test_coefficient_collection_to_neg() {
    let mut store = TermStore::new();

    let a = store.mk_var("a", Sort::Int);
    let two = store.mk_int(BigInt::from(2));
    let neg_three = store.mk_int(BigInt::from(-3));

    // Create (* 2 a) and (* -3 a)
    let two_a = store.mk_mul(vec![two, a]);
    let neg_three_a = store.mk_mul(vec![neg_three, a]);

    // (* 2 a) + (* -3 a) = (- a)
    let result = store.mk_add(vec![two_a, neg_three_a]);
    let expected = store.mk_neg(a);
    assert_eq!(result, expected);
}

#[test]
fn test_coefficient_collection_deterministic_order_int() {
    let mut store = TermStore::new();

    // Create variables in a specific order - a is allocated before b
    let a = store.mk_var("a", Sort::Int);
    let b = store.mk_var("b", Sort::Int);

    // a has lower TermId than b
    assert!(a.0 < b.0, "a should have lower TermId than b");

    let two = store.mk_int(BigInt::from(2));
    let three = store.mk_int(BigInt::from(3));

    // Create terms in reverse order: 3b first, then 2a
    let three_b = store.mk_mul(vec![three, b]);
    let two_a = store.mk_mul(vec![two, a]);
    let three_b_dup = store.mk_mul(vec![three, b]);

    // Add in order: 3b, 2a, 3b (duplicates combine)
    // Input order has b before a, but output should have a before b (sorted by TermId)
    let result = store.mk_add(vec![three_b, two_a, three_b_dup]);

    // Result should be (+ (* 2 a) (* 6 b)) with a before b due to TermId sorting
    if let TermData::App(Symbol::Named(name), args) = store.get(result) {
        assert_eq!(name, "+");
        assert_eq!(args.len(), 2);

        // First arg should contain 'a' (lower TermId)
        let first_base = extract_base_from_mul(&store, args[0]);
        let second_base = extract_base_from_mul(&store, args[1]);

        assert_eq!(
            first_base,
            Some(a),
            "First term should be based on 'a' (lower TermId)"
        );
        assert_eq!(
            second_base,
            Some(b),
            "Second term should be based on 'b' (higher TermId)"
        );
    } else {
        panic!("Expected + App term");
    }
}

#[test]
fn test_coefficient_collection_deterministic_order_real() {
    let mut store = TermStore::new();

    // Create variables in a specific order - x is allocated before y
    let x = store.mk_var("x", Sort::Real);
    let y = store.mk_var("y", Sort::Real);

    // x has lower TermId than y
    assert!(x.0 < y.0, "x should have lower TermId than y");

    let two = store.mk_rational(BigRational::from(BigInt::from(2)));
    let three = store.mk_rational(BigRational::from(BigInt::from(3)));

    // Create terms in reverse order: 3y first, then 2x
    let three_y = store.mk_mul(vec![three, y]);
    let two_x = store.mk_mul(vec![two, x]);
    let three_y_dup = store.mk_mul(vec![three, y]);

    // Add in order: 3y, 2x, 3y (duplicates combine)
    // Input order has y before x, but output should have x before y (sorted by TermId)
    let result = store.mk_add(vec![three_y, two_x, three_y_dup]);

    // Result should be (+ (* 2 x) (* 6 y)) with x before y due to TermId sorting
    if let TermData::App(Symbol::Named(name), args) = store.get(result) {
        assert_eq!(name, "+");
        assert_eq!(args.len(), 2);

        // First arg should contain 'x' (lower TermId)
        let first_base = extract_base_from_mul(&store, args[0]);
        let second_base = extract_base_from_mul(&store, args[1]);

        assert_eq!(
            first_base,
            Some(x),
            "First term should be based on 'x' (lower TermId)"
        );
        assert_eq!(
            second_base,
            Some(y),
            "Second term should be based on 'y' (higher TermId)"
        );
    } else {
        panic!("Expected + App term");
    }
}

/// Helper to extract the base variable from a multiplication term like (* coeff base)
fn extract_base_from_mul(store: &TermStore, term: TermId) -> Option<TermId> {
    if let TermData::App(Symbol::Named(name), args) = store.get(term) {
        if name == "*" && args.len() == 2 {
            // One of the args is a constant, the other is the base
            for &arg in args {
                if store.get_int(arg).is_none() && store.get_rational(arg).is_none() {
                    return Some(arg);
                }
            }
        }
    }
    None
}

#[test]
fn test_mul_flattening() {
    let mut store = TermStore::new();

    let a = store.mk_var("a", Sort::Int);
    let b = store.mk_var("b", Sort::Int);
    let c = store.mk_var("c", Sort::Int);

    // Create (* a b)
    let mul_ab = store.mk_mul(vec![a, b]);

    // (* (* a b) c) should flatten to (* a b c)
    let result = store.mk_mul(vec![mul_ab, c]);

    // Verify it's a flat multiplication with all three arguments
    if let TermData::App(Symbol::Named(name), args) = store.get(result) {
        assert_eq!(name, "*");
        assert_eq!(args.len(), 3);
        assert!(args.contains(&a));
        assert!(args.contains(&b));
        assert!(args.contains(&c));
    } else {
        panic!("Expected * App term");
    }
}

#[test]
fn test_mul_flattening_nested() {
    let mut store = TermStore::new();

    let a = store.mk_var("a", Sort::Int);
    let b = store.mk_var("b", Sort::Int);
    let c = store.mk_var("c", Sort::Int);
    let d = store.mk_var("d", Sort::Int);

    // Create (* a b) and (* c d)
    let mul_ab = store.mk_mul(vec![a, b]);
    let mul_cd = store.mk_mul(vec![c, d]);

    // (* (* a b) (* c d)) should flatten to (* a b c d)
    let result = store.mk_mul(vec![mul_ab, mul_cd]);

    // Verify it's a flat multiplication with all four arguments
    if let TermData::App(Symbol::Named(name), args) = store.get(result) {
        assert_eq!(name, "*");
        assert_eq!(args.len(), 4);
        assert!(args.contains(&a));
        assert!(args.contains(&b));
        assert!(args.contains(&c));
        assert!(args.contains(&d));
    } else {
        panic!("Expected * App term");
    }
}

#[test]
fn test_mul_flattening_with_constants() {
    let mut store = TermStore::new();

    let a = store.mk_var("a", Sort::Int);
    let two = store.mk_int(BigInt::from(2));
    let three = store.mk_int(BigInt::from(3));

    // Create (* a 2)
    let mul_a2 = store.mk_mul(vec![a, two]);

    // (* (* a 2) 3) should flatten and fold constants to (* a 6)
    let result = store.mk_mul(vec![mul_a2, three]);

    // Verify constants were folded
    if let TermData::App(Symbol::Named(name), args) = store.get(result) {
        assert_eq!(name, "*");
        assert_eq!(args.len(), 2);
        assert!(args.contains(&a));
        // One arg should be 6
        let has_six = args
            .iter()
            .any(|&arg| store.get_int(arg).is_some_and(|n| *n == BigInt::from(6)));
        assert!(has_six);
    } else {
        panic!("Expected * App term");
    }
}

#[test]
fn test_mul_by_minus_one() {
    let mut store = TermStore::new();

    let a = store.mk_var("a", Sort::Int);
    let neg_one = store.mk_int(BigInt::from(-1));

    // (* -1 a) = (- a)
    let result = store.mk_mul(vec![neg_one, a]);

    // Should be a negation
    if let TermData::App(Symbol::Named(name), args) = store.get(result) {
        assert_eq!(name, "-");
        assert_eq!(args.len(), 1);
        assert_eq!(args[0], a);
    } else {
        panic!("Expected - App term (negation)");
    }
}

#[test]
fn test_mul_by_minus_one_multiple() {
    let mut store = TermStore::new();

    let a = store.mk_var("a", Sort::Int);
    let b = store.mk_var("b", Sort::Int);
    let neg_one = store.mk_int(BigInt::from(-1));

    // (* -1 a b) = (- (* a b))
    let result = store.mk_mul(vec![neg_one, a, b]);

    // Should be a negation of multiplication
    if let TermData::App(Symbol::Named(name), args) = store.get(result) {
        assert_eq!(name, "-");
        assert_eq!(args.len(), 1);
        // Inner should be (* a b)
        if let TermData::App(Symbol::Named(inner_name), inner_args) = store.get(args[0]) {
            assert_eq!(inner_name, "*");
            assert_eq!(inner_args.len(), 2);
            assert!(inner_args.contains(&a));
            assert!(inner_args.contains(&b));
        } else {
            panic!("Expected inner * App term");
        }
    } else {
        panic!("Expected - App term (negation)");
    }
}

#[test]
fn test_mul_by_minus_one_folded() {
    let mut store = TermStore::new();

    let a = store.mk_var("a", Sort::Int);
    let two = store.mk_int(BigInt::from(2));
    let neg_three = store.mk_int(BigInt::from(-3));

    // (* 2 -3 a) = (* -6 a) = (- (* 6 a)) but since -6 is not -1, it stays as (* a -6)
    // Actually: 2 * -3 = -6, so (* 2 -3 a) = (* -6 a)
    // Wait, the implementation folds to -6, not -1, so it won't become negation
    let result = store.mk_mul(vec![two, neg_three, a]);

    // Should have a and -6 as arguments
    if let TermData::App(Symbol::Named(name), args) = store.get(result) {
        assert_eq!(name, "*");
        assert_eq!(args.len(), 2);
        assert!(args.contains(&a));
        let has_neg_six = args
            .iter()
            .any(|&arg| store.get_int(arg).is_some_and(|n| *n == BigInt::from(-6)));
        assert!(has_neg_six);
    } else {
        panic!("Expected * App term");
    }
}

#[test]
fn test_comparison_reflexive_simplification() {
    let mut store = TermStore::new();

    let x = store.mk_var("x", Sort::Int);

    // x < x = false
    assert_eq!(store.mk_lt(x, x), store.false_term());
    // x <= x = true
    assert_eq!(store.mk_le(x, x), store.true_term());
    // x > x = false
    assert_eq!(store.mk_gt(x, x), store.false_term());
    // x >= x = true
    assert_eq!(store.mk_ge(x, x), store.true_term());
}

#[test]
fn test_comparison_non_constant() {
    let mut store = TermStore::new();

    let x = store.mk_var("x", Sort::Int);
    let y = store.mk_var("y", Sort::Int);

    // x < y should create an App term, not simplify
    let lt = store.mk_lt(x, y);
    if let TermData::App(Symbol::Named(name), args) = store.get(lt) {
        assert_eq!(name, "<");
        assert_eq!(args.len(), 2);
    } else {
        panic!("Expected App term for non-constant comparison");
    }
}

#[test]
fn test_eq_constant_folding() {
    let mut store = TermStore::new();

    // Integer constants
    let one = store.mk_int(BigInt::from(1));
    let two = store.mk_int(BigInt::from(2));

    // (= 1 2) = false
    assert_eq!(store.mk_eq(one, two), store.false_term());
    // (= 1 1) = true (same constant)
    assert_eq!(store.mk_eq(one, one), store.true_term());

    // Boolean constants
    let t = store.true_term();
    let f = store.false_term();

    // (= true false) = false
    assert_eq!(store.mk_eq(t, f), store.false_term());
    // (= true true) = true
    assert_eq!(store.mk_eq(t, t), store.true_term());

    // String constants
    let hello = store.mk_string("hello".to_string());
    let world = store.mk_string("world".to_string());

    // (= "hello" "world") = false
    assert_eq!(store.mk_eq(hello, world), store.false_term());
    // (= "hello" "hello") = true
    assert_eq!(store.mk_eq(hello, hello), store.true_term());
}

#[test]
fn test_distinct_duplicate_detection() {
    let mut store = TermStore::new();

    let x = store.mk_var("x", Sort::Int);
    let y = store.mk_var("y", Sort::Int);

    // (distinct x x) = false
    assert_eq!(store.mk_distinct(vec![x, x]), store.false_term());
    // (distinct x y x) = false (x appears twice)
    assert_eq!(store.mk_distinct(vec![x, y, x]), store.false_term());
    // (distinct x y) should not simplify (non-constant)
    let dist = store.mk_distinct(vec![x, y]);
    assert_ne!(dist, store.true_term());
    assert_ne!(dist, store.false_term());
}

#[test]
fn test_distinct_constant_folding() {
    let mut store = TermStore::new();

    let one = store.mk_int(BigInt::from(1));
    let two = store.mk_int(BigInt::from(2));
    let three = store.mk_int(BigInt::from(3));

    // (distinct 1 2 3) = true
    assert_eq!(store.mk_distinct(vec![one, two, three]), store.true_term());
    // (distinct 1 2 1) = false (duplicate)
    assert_eq!(store.mk_distinct(vec![one, two, one]), store.false_term());
    // (distinct 1 1) = false
    assert_eq!(store.mk_distinct(vec![one, one]), store.false_term());
}

#[test]
fn test_comparison_normalization_gt_to_lt() {
    let mut store = TermStore::new();

    let x = store.mk_var("x", Sort::Int);
    let y = store.mk_var("y", Sort::Int);

    // (> x y) should produce the same term as (< y x)
    let gt = store.mk_gt(x, y);
    let lt = store.mk_lt(y, x);
    assert_eq!(gt, lt);

    // Verify it's a < term with swapped arguments
    if let TermData::App(Symbol::Named(name), args) = store.get(gt) {
        assert_eq!(name, "<");
        assert_eq!(args[0], y);
        assert_eq!(args[1], x);
    } else {
        panic!("Expected < App term");
    }
}

#[test]
fn test_comparison_normalization_ge_to_le() {
    let mut store = TermStore::new();

    let x = store.mk_var("x", Sort::Int);
    let y = store.mk_var("y", Sort::Int);

    // (>= x y) should produce the same term as (<= y x)
    let ge = store.mk_ge(x, y);
    let le = store.mk_le(y, x);
    assert_eq!(ge, le);

    // Verify it's a <= term with swapped arguments
    if let TermData::App(Symbol::Named(name), args) = store.get(ge) {
        assert_eq!(name, "<=");
        assert_eq!(args[0], y);
        assert_eq!(args[1], x);
    } else {
        panic!("Expected <= App term");
    }
}

#[test]
fn test_comparison_normalization_term_sharing() {
    let mut store = TermStore::new();

    let a = store.mk_var("a", Sort::Real);
    let b = store.mk_var("b", Sort::Real);

    // These should all produce the same term (term sharing)
    let t1 = store.mk_gt(b, a); // (> b a) -> (< a b)
    let t2 = store.mk_lt(a, b); // (< a b)
    let t3 = store.mk_gt(b, a); // (> b a) -> (< a b)

    assert_eq!(t1, t2);
    assert_eq!(t2, t3);

    // Similarly for >= and <=
    let t4 = store.mk_ge(b, a); // (>= b a) -> (<= a b)
    let t5 = store.mk_le(a, b); // (<= a b)

    assert_eq!(t4, t5);
}

#[test]
fn test_eq_complement_detection() {
    let mut store = TermStore::new();

    let x = store.mk_var("x", Sort::Bool);
    let not_x = store.mk_not(x);

    // (= x (not x)) -> false
    assert_eq!(store.mk_eq(x, not_x), store.false_term());
    // (= (not x) x) -> false
    assert_eq!(store.mk_eq(not_x, x), store.false_term());
}

#[test]
fn test_eq_complement_with_complex_term() {
    let mut store = TermStore::new();

    // Use uninterpreted predicates to avoid De Morgan transformation
    let u = Sort::Uninterpreted("U".to_string());
    let a = store.mk_var("a", u);
    let p_a = store.mk_app(Symbol::named("p"), vec![a], Sort::Bool);
    let not_p_a = store.mk_not(p_a);

    // (= p(a) (not p(a))) -> false
    assert_eq!(store.mk_eq(p_a, not_p_a), store.false_term());
}

#[test]
fn test_absorption_complete_simplification() {
    let mut store = TermStore::new();

    let x = store.mk_var("x", Sort::Bool);
    let y = store.mk_var("y", Sort::Bool);

    // Create (or x y)
    let or_xy = store.mk_or(vec![x, y]);

    // (and x y (or x y)) - both x and y are in the or
    // The or should be absorbed, leaving just (and x y)
    let result = store.mk_and(vec![x, y, or_xy]);
    let expected = store.mk_and(vec![x, y]);
    assert_eq!(result, expected);
}

#[test]
fn test_sub_to_add_conversion_int() {
    let mut store = TermStore::new();

    let a = store.mk_var("a", Sort::Int);
    let b = store.mk_var("b", Sort::Int);

    // (a - b) → (+ a (- b))
    let result = store.mk_sub(vec![a, b]);

    // Result should be addition
    match store.get(result) {
        TermData::App(Symbol::Named(name), args) => {
            assert_eq!(name, "+");
            assert_eq!(args.len(), 2);
            assert_eq!(args[0], a);
            // Second arg should be (- b)
            match store.get(args[1]) {
                TermData::App(Symbol::Named(neg_name), neg_args) => {
                    assert_eq!(neg_name, "-");
                    assert_eq!(neg_args.len(), 1);
                    assert_eq!(neg_args[0], b);
                }
                _ => panic!("Expected negation"),
            }
        }
        _ => panic!("Expected addition"),
    }
}

#[test]
fn test_sub_to_add_conversion_real() {
    let mut store = TermStore::new();

    let x = store.mk_var("x", Sort::Real);
    let y = store.mk_var("y", Sort::Real);

    // (x - y) → (+ x (- y))
    let result = store.mk_sub(vec![x, y]);

    // Result should be addition
    match store.get(result) {
        TermData::App(Symbol::Named(name), args) => {
            assert_eq!(name, "+");
            assert_eq!(args.len(), 2);
            assert_eq!(args[0], x);
        }
        _ => panic!("Expected addition"),
    }
}

#[test]
fn test_sub_coeff_collection_int() {
    let mut store = TermStore::new();

    let a = store.mk_var("a", Sort::Int);
    let two = store.mk_int(BigInt::from(2));

    // (2a - a) → a (via coefficient collection)
    let two_a = store.mk_mul(vec![two, a]);
    let result = store.mk_sub(vec![two_a, a]);

    // Should simplify to just a (coefficient 2 - 1 = 1)
    assert_eq!(result, a);
}

#[test]
fn test_sub_coeff_collection_real() {
    let mut store = TermStore::new();

    let x = store.mk_var("x", Sort::Real);
    let three = store.mk_rational(BigRational::from(BigInt::from(3)));

    // (3x - x) → 2x (via coefficient collection)
    let three_x = store.mk_mul(vec![three, x]);
    let result = store.mk_sub(vec![three_x, x]);

    // Should simplify to 2x
    let expected_two = store.mk_rational(BigRational::from(BigInt::from(2)));
    let expected = store.mk_mul(vec![x, expected_two]);
    assert_eq!(result, expected);
}

#[test]
fn test_sub_nary_to_add() {
    let mut store = TermStore::new();

    let a = store.mk_var("a", Sort::Int);
    let b = store.mk_var("b", Sort::Int);
    let c = store.mk_var("c", Sort::Int);

    // (- a b c) → (+ a (- b) (- c))
    let result = store.mk_sub(vec![a, b, c]);

    // Result should be addition with 3 arguments
    match store.get(result) {
        TermData::App(Symbol::Named(name), args) => {
            assert_eq!(name, "+");
            assert_eq!(args.len(), 3);
            assert_eq!(args[0], a);
            // args[1] should be (- b) and args[2] should be (- c)
            for &(i, expected_inner) in &[(1usize, b), (2usize, c)] {
                match store.get(args[i]) {
                    TermData::App(Symbol::Named(neg_name), neg_args) => {
                        assert_eq!(neg_name, "-");
                        assert_eq!(neg_args.len(), 1);
                        assert_eq!(neg_args[0], expected_inner);
                    }
                    _ => panic!("Expected negation at position {i}"),
                }
            }
        }
        _ => panic!("Expected addition"),
    }
}

#[test]
fn test_sub_coeff_chain_simplification() {
    let mut store = TermStore::new();

    let x = store.mk_var("x", Sort::Int);
    let three = store.mk_int(BigInt::from(3));
    let two_const = store.mk_int(BigInt::from(2));

    // Build (3x - 2x) which should simplify to x
    let three_x = store.mk_mul(vec![three, x]);
    let two_x = store.mk_mul(vec![two_const, x]);
    let result = store.mk_sub(vec![three_x, two_x]);

    // Should simplify to x (coefficient 3 - 2 = 1)
    assert_eq!(result, x);
}

#[test]
fn test_sub_zero_coeff() {
    let mut store = TermStore::new();

    let a = store.mk_var("a", Sort::Int);
    let two = store.mk_int(BigInt::from(2));
    let zero = store.mk_int(BigInt::from(0));

    // (2a - 2a) → 0 (via coefficient collection)
    let two_a = store.mk_mul(vec![two, a]);
    let result = store.mk_sub(vec![two_a, two_a]);

    // Should simplify to 0
    assert_eq!(result, zero);
}

#[test]
fn test_sub_negative_coeff() {
    let mut store = TermStore::new();

    let a = store.mk_var("a", Sort::Int);
    let two = store.mk_int(BigInt::from(2));
    let three = store.mk_int(BigInt::from(3));

    // (2a - 3a) → -a (via coefficient collection)
    let two_a = store.mk_mul(vec![two, a]);
    let three_a = store.mk_mul(vec![three, a]);
    let result = store.mk_sub(vec![two_a, three_a]);

    // Should simplify to (- a)
    let expected = store.mk_neg(a);
    assert_eq!(result, expected);
}

#[test]
fn test_mk_eq_coerce_same_sort_delegates_to_mk_eq() {
    let mut store = TermStore::new();
    let x = store.mk_var("x", Sort::Int);
    let y = store.mk_var("y", Sort::Int);

    // Same sort: mk_eq_coerce should produce the same result as mk_eq
    let eq_coerce = store.mk_eq_coerce(x, y);
    let eq_direct = store.mk_eq(x, y);
    assert_eq!(eq_coerce, eq_direct);
}

#[test]
fn test_mk_eq_coerce_no_ite_expand_keeps_branch_equality_structural_11936() {
    let mut store = TermStore::new();
    let c = store.mk_var("c", Sort::Bool);
    let a = store.mk_var("a", Sort::bitvec(8));
    let b = store.mk_var("b", Sort::bitvec(8));
    let ite = store.mk_ite(c, a, b);

    let eq = store.mk_eq_coerce_no_ite_expand(ite, a);

    let TermData::App(Symbol::Named(name), args) = store.get(eq) else {
        panic!("expected structural equality, got {:?}", store.get(eq));
    };
    assert_eq!(name, "=");
    assert_eq!(args.len(), 2);
    assert!(args.contains(&ite));
    assert!(args.contains(&a));
}

#[test]
fn test_mk_eq_coerce_int_real_lhs_int() {
    let mut store = TermStore::new();
    let x = store.mk_var("x", Sort::Int);
    let r = store.mk_var("r", Sort::Real);

    // Int = Real: should wrap Int in to_real
    let eq = store.mk_eq_coerce(x, r);
    assert_eq!(*store.sort(eq), Sort::Bool);

    // The equality should be between to_real(x) and r
    if let TermData::App(Symbol::Named(name), args) = store.get(eq) {
        assert_eq!(name, "=");
        assert_eq!(args.len(), 2);
        // One side should be to_real(x), the other should be r
        let has_to_real = args.iter().any(|&a| {
            matches!(store.get(a), TermData::App(Symbol::Named(n), inner) if n == "to_real" && inner.len() == 1 && inner[0] == x)
        });
        assert!(has_to_real, "Expected to_real(x) in equality args");
        assert!(args.contains(&r), "Expected r in equality args");
    } else {
        panic!("Expected equality App term");
    }
}

#[test]
fn test_mk_eq_coerce_int_real_rhs_int() {
    let mut store = TermStore::new();
    let r = store.mk_var("r", Sort::Real);
    let y = store.mk_var("y", Sort::Int);

    // Real = Int: should wrap Int in to_real
    let eq = store.mk_eq_coerce(r, y);
    assert_eq!(*store.sort(eq), Sort::Bool);

    // The equality should be between r and to_real(y)
    if let TermData::App(Symbol::Named(name), args) = store.get(eq) {
        assert_eq!(name, "=");
        assert_eq!(args.len(), 2);
        let has_to_real = args.iter().any(|&a| {
            matches!(store.get(a), TermData::App(Symbol::Named(n), inner) if n == "to_real" && inner.len() == 1 && inner[0] == y)
        });
        assert!(has_to_real, "Expected to_real(y) in equality args");
        assert!(args.contains(&r), "Expected r in equality args");
    } else {
        panic!("Expected equality App term");
    }
}

#[test]
fn test_mk_eq_coerce_int_constant_to_real() {
    let mut store = TermStore::new();
    let five_int = store.mk_int(BigInt::from(5));
    let r = store.mk_var("r", Sort::Real);

    // Int constant = Real var: the Int constant should become a Rational
    let eq = store.mk_eq_coerce(five_int, r);
    assert_eq!(*store.sort(eq), Sort::Bool);
    // mk_to_real on a constant Int folds to Rational(5/1), so the equality
    // should be between 5.0 and r
}

#[test]
fn test_mk_eq_coerce_reflexive_int_real() {
    let mut store = TermStore::new();
    let x = store.mk_var("x", Sort::Int);
    let to_real_x = store.mk_to_real(x);

    // to_real(x) = to_real(x) should be true (reflexive)
    let eq = store.mk_eq_coerce(to_real_x, to_real_x);
    assert_eq!(eq, store.true_term());
}
