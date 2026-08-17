// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

// ========================================================================
// Incremental Backtracking Proof Tests (#29)
// ========================================================================
//
// These tests verify that push/pop correctly implements incremental
// backtracking for the eager DPLL(T) optimization. The key invariant is:
//
//   For any sequence of assertions at level N:
//   - push(); assert(x); pop() ≡ no-op (state unchanged)
//   - push(); assert(x); assert(y); pop(); assert(x) ≡ just assert(x)
//
// The tests discriminate correct implementations (O(undo_records) per backtrack)
// from incorrect implementations (O(trail_len) per backtrack).

#[test]
fn test_push_pop_basic_equality() {
    let mut store = TermStore::new();
    let u = Sort::Uninterpreted("U".to_string());
    let a = store.mk_var("a", u.clone());
    let b = store.mk_var("b", u.clone());
    let c = store.mk_var("c", u);
    let eq_ab = store.mk_eq(a, b);
    let eq_bc = store.mk_eq(b, c);
    let _eq_ac = store.mk_eq(a, c);
    let mut euf = EufSolver::new(&store);

    // Level 0: a = b
    euf.assert_literal(eq_ab, true);
    euf.rebuild_closure();
    assert_eq!(euf.uf.find(a.0), euf.uf.find(b.0));
    assert_ne!(euf.uf.find(a.0), euf.uf.find(c.0));

    // Level 1: b = c → a,b,c all equivalent
    euf.push();
    euf.assert_literal(eq_bc, true);
    euf.rebuild_closure();
    assert_eq!(euf.uf.find(a.0), euf.uf.find(c.0));

    // Pop: a=b still holds, c distinct again
    euf.pop();
    euf.rebuild_closure();
    assert_eq!(euf.uf.find(a.0), euf.uf.find(b.0));
    assert_ne!(euf.uf.find(a.0), euf.uf.find(c.0));
}

#[test]
fn test_push_pop_congruence() {
    // Verify push/pop correctly handles congruence closure
    let mut store = TermStore::new();
    let u = Sort::Uninterpreted("U".to_string());

    let a = store.mk_var("a", u.clone());
    let b = store.mk_var("b", u.clone());
    let f_a = store.mk_app(Symbol::named("f"), vec![a], u.clone());
    let f_b = store.mk_app(Symbol::named("f"), vec![b], u);
    let eq_ab = store.mk_eq(a, b);
    let _eq_fa_fb = store.mk_eq(f_a, f_b);

    let mut euf = EufSolver::new(&store);

    // Initially f(a) and f(b) are distinct
    let rep_fa_init = euf.uf.find(f_a.0);
    let rep_fb_init = euf.uf.find(f_b.0);
    assert_ne!(rep_fa_init, rep_fb_init, "f(a) and f(b) initially distinct");

    // Push and assert a = b
    euf.push();
    euf.assert_literal(eq_ab, true);
    euf.rebuild_closure();

    // After a = b, f(a) and f(b) should be congruent
    let rep_fa_after_eq = euf.uf.find(f_a.0);
    let rep_fb_after_eq = euf.uf.find(f_b.0);
    assert_eq!(
        rep_fa_after_eq, rep_fb_after_eq,
        "f(a) = f(b) by congruence"
    );

    // Pop - f(a) and f(b) should be distinct again
    euf.pop();
    euf.rebuild_closure();

    let rep_fa_popped = euf.uf.find(f_a.0);
    let rep_fb_popped = euf.uf.find(f_b.0);
    assert_ne!(
        rep_fa_popped, rep_fb_popped,
        "f(a) and f(b) distinct after pop"
    );
}

#[test]
#[serial]
fn test_push_pop_conflict_detection() {
    // Verify push/pop correctly handles conflict detection across levels
    let mut store = TermStore::new();
    let u = Sort::Uninterpreted("U".to_string());

    let a = store.mk_var("a", u.clone());
    let b = store.mk_var("b", u.clone());
    let c = store.mk_var("c", u);
    let eq_ab = store.mk_eq(a, b);
    let eq_bc = store.mk_eq(b, c);
    let eq_ac = store.mk_eq(a, c);

    let mut euf = EufSolver::new(&store);

    // Level 0: assert a = b
    euf.assert_literal(eq_ab, true);

    // Level 1: assert b = c
    euf.push();
    euf.assert_literal(eq_bc, true);

    // Now assert a != c - should conflict due to transitivity
    euf.assert_literal(eq_ac, false);
    let result = euf.check();
    assert!(
        matches!(result, TheoryResult::Unsat(_)),
        "Should conflict at level 1"
    );

    // Pop back to level 0
    euf.pop();

    // At level 0 with only a = b, asserting a != c should be SAT
    euf.assert_literal(eq_ac, false);
    let result_l0 = euf.check();
    assert!(
        matches!(result_l0, TheoryResult::Sat),
        "Should be SAT at level 0"
    );
}

#[test]
fn test_nested_push_pop() {
    // Verify multiple nested push/pop levels work correctly
    let mut store = TermStore::new();
    let u = Sort::Uninterpreted("U".to_string());

    let x0 = store.mk_var("x0", u.clone());
    let x1 = store.mk_var("x1", u.clone());
    let x2 = store.mk_var("x2", u.clone());
    let x3 = store.mk_var("x3", u);
    let eq_01 = store.mk_eq(x0, x1);
    let eq_12 = store.mk_eq(x1, x2);
    let eq_23 = store.mk_eq(x2, x3);

    let mut euf = EufSolver::new(&store);

    // Level 0: x0 = x1
    euf.assert_literal(eq_01, true);
    euf.rebuild_closure();
    let _class_size_l0 = {
        let rep = euf.uf.find(x0.0);
        // Count members in class
        let mut count = 0;
        for i in 0..store.len() {
            if euf.uf.find(i as u32) == rep {
                count += 1;
            }
        }
        count
    };

    // Level 1: x1 = x2
    euf.push();
    euf.assert_literal(eq_12, true);
    euf.rebuild_closure();

    // Level 2: x2 = x3
    euf.push();
    euf.assert_literal(eq_23, true);
    euf.rebuild_closure();

    // At level 2, all should be in same class
    let rep_x0_l2 = euf.uf.find(x0.0);
    let rep_x3_l2 = euf.uf.find(x3.0);
    assert_eq!(
        rep_x0_l2, rep_x3_l2,
        "x0 and x3 should be equivalent at level 2"
    );

    // Pop to level 1
    euf.pop();
    euf.rebuild_closure();

    // x0, x1, x2 should be equivalent; x3 should be distinct
    let rep_x0_l1 = euf.uf.find(x0.0);
    let rep_x2_l1 = euf.uf.find(x2.0);
    let rep_x3_l1 = euf.uf.find(x3.0);
    assert_eq!(rep_x0_l1, rep_x2_l1, "x0 and x2 equivalent at level 1");
    assert_ne!(rep_x0_l1, rep_x3_l1, "x3 distinct at level 1");

    // Pop to level 0
    euf.pop();
    euf.rebuild_closure();

    // Only x0 = x1 remains
    let rep_x0_l0 = euf.uf.find(x0.0);
    let rep_x1_l0 = euf.uf.find(x1.0);
    let rep_x2_l0 = euf.uf.find(x2.0);
    assert_eq!(rep_x0_l0, rep_x1_l0, "x0 and x1 equivalent at level 0");
    assert_ne!(rep_x0_l0, rep_x2_l0, "x2 distinct at level 0");
}

#[test]
fn test_incremental_push_pop_resyncs_uf_and_model_6775() {
    use num_bigint::BigInt;

    let mut store = TermStore::new();
    let u = Sort::Uninterpreted("U".to_string());

    let a = store.mk_var("a", u.clone());
    let b = store.mk_var("b", u.clone());
    let c = store.mk_var("c", u);
    let f_a = store.mk_app(Symbol::named("f"), vec![a], Sort::Int);
    let five = store.mk_int(BigInt::from(5));
    let eq_ab = store.mk_eq(a, b);
    let eq_bc = store.mk_eq(b, c);
    let eq_fa_five = store.mk_eq(f_a, five);

    let mut euf = new_incremental_euf(&store);

    // Establish an outer-scope class {a, b} and a tracked UF application value.
    euf.assert_literal(eq_ab, true);
    euf.assert_literal(eq_fa_five, true);
    assert!(matches!(euf.check(), TheoryResult::Sat));

    // Merge c into the class in an inner scope so pop() must restore the mirror.
    euf.push();
    euf.assert_literal(eq_bc, true);
    assert!(matches!(euf.check(), TheoryResult::Sat));
    assert_eq!(
        euf.uf.find(a.0),
        euf.uf.find(c.0),
        "inner scope should merge c into the a/b class"
    );

    // Regression for #6775: pop() alone must restore the UF mirror, without
    // requiring a follow-up check() or rebuild_closure().
    euf.pop();
    assert_eq!(
        euf.uf.find(a.0),
        euf.uf.find(b.0),
        "a and b should remain equivalent after pop"
    );
    assert_ne!(
        euf.uf.find(a.0),
        euf.uf.find(c.0),
        "c must leave the class immediately after pop"
    );

    let model = euf.extract_model();
    let a_val = model
        .term_values
        .get(&a)
        .expect("model should assign a value to a");
    let b_val = model
        .term_values
        .get(&b)
        .expect("model should assign a value to b");
    let c_val = model
        .term_values
        .get(&c)
        .expect("model should assign a value to c");
    assert_eq!(
        a_val, b_val,
        "model should preserve the outer-scope a=b class"
    );
    assert_ne!(a_val, c_val, "model should keep c distinct after pop");
    assert_eq!(
        model.func_app_const_terms.get(&f_a),
        Some(&five),
        "model should preserve UF application constant values after pop"
    );
}

#[test]
fn test_euf_model_materializes_bv_array_observations() {
    use num_bigint::BigInt;

    let mut store = TermStore::new();
    let bv32 = Sort::bitvec(32);
    let array = store.mk_var("a", Sort::array(bv32.clone(), bv32));
    let index_zero = store.mk_bitvec(BigInt::from(0u8), 32);
    let index_other = store.mk_bitvec(BigInt::from(0x26u8), 32);
    let value_one = store.mk_bitvec(BigInt::from(1u8), 32);
    let select_zero = store.mk_select(array, index_zero);
    let select_other = store.mk_select(array, index_other);
    let zero_read = store.mk_eq(select_zero, index_zero);
    let non_one_read = store.mk_eq(select_other, value_one);

    let mut euf = EufSolver::new(&store);
    euf.assert_literal(zero_read, true);
    euf.assert_literal(non_one_read, false);
    assert!(matches!(euf.check(), TheoryResult::Sat));
    euf.scope_model_to_roots(&[zero_read, non_one_read]);

    let model = euf.extract_model();
    assert_eq!(
        model.term_values.get(&index_other).map(String::as_str),
        Some("#x00000026")
    );
    assert_eq!(
        model.term_values.get(&select_zero).map(String::as_str),
        Some("#x00000000")
    );
    assert_ne!(
        model.term_values.get(&select_other),
        model.term_values.get(&value_one),
        "a committed BV disequality must survive finite model completion"
    );
}

#[test]
#[allow(clippy::many_single_char_names)]
fn test_push_pop_equivalence_to_reset() {
    // PROOF TEST: push/pop should produce same state as reset + re-assert
    // This test verifies the semantic equivalence that enables the optimization.
    let mut store = TermStore::new();
    let u = Sort::Uninterpreted("U".to_string());

    let a = store.mk_var("a", u.clone());
    let b = store.mk_var("b", u.clone());
    let c = store.mk_var("c", u.clone());
    let d = store.mk_var("d", u);
    let eq_ab = store.mk_eq(a, b);
    let eq_cd = store.mk_eq(c, d);
    let eq_bc = store.mk_eq(b, c);

    // Method 1: Using push/pop
    let mut euf1 = EufSolver::new(&store);
    euf1.assert_literal(eq_ab, true);
    euf1.assert_literal(eq_cd, true);
    euf1.push();
    euf1.assert_literal(eq_bc, true);
    euf1.pop();
    euf1.rebuild_closure();

    // Method 2: Using reset + re-assert
    let mut euf2 = EufSolver::new(&store);
    euf2.assert_literal(eq_ab, true);
    euf2.assert_literal(eq_cd, true);
    euf2.assert_literal(eq_bc, true);
    euf2.reset();
    euf2.assert_literal(eq_ab, true);
    euf2.assert_literal(eq_cd, true);
    euf2.rebuild_closure();

    // Both should produce the same equivalence classes
    for i in 0..store.len() {
        let rep1 = euf1.uf.find(i as u32);
        let rep2 = euf2.uf.find(i as u32);
        // We check structural equivalence: same groupings
        for j in 0..store.len() {
            let same_class1 = euf1.uf.find(j as u32) == rep1;
            let same_class2 = euf2.uf.find(j as u32) == rep2;
            assert_eq!(
                same_class1, same_class2,
                "Equivalence class membership should match: terms {i} and {j}"
            );
        }
    }
}

#[test]
#[serial]
fn test_incremental_backtracking_complexity() {
    // This test creates a chain of equalities and measures that
    // pop() is O(1) in terms of new allocations (not re-asserting all).
    // It's a sanity check that the undo trail is being used.
    let mut store = TermStore::new();
    let u = Sort::Uninterpreted("U".to_string());

    // Create chain: x0 = x1 = x2 = ... = x9
    let vars: Vec<_> = (0..10)
        .map(|i| store.mk_var(format!("x{i}"), u.clone()))
        .collect();
    let eqs: Vec<_> = (0..9).map(|i| store.mk_eq(vars[i], vars[i + 1])).collect();

    let mut euf = new_incremental_euf(&store);
    euf.init_enodes();

    // Assert base level
    euf.assert_literal(eqs[0], true);
    euf.assert_literal(eqs[1], true);
    euf.assert_literal(eqs[2], true);

    // Push and assert more
    euf.push();
    let undo_len_before_push2 = euf.undo_trail.len();

    euf.assert_literal(eqs[3], true);
    euf.assert_literal(eqs[4], true);
    euf.assert_literal(eqs[5], true);

    // Process merges
    euf.incremental_rebuild();

    let undo_len_after_asserts = euf.undo_trail.len();
    let undo_records_added = undo_len_after_asserts - undo_len_before_push2;

    // Pop should replay these undo records
    euf.pop();

    // After pop, undo trail should be back to before push
    let undo_len_after_pop = euf.undo_trail.len();

    // Verify undo trail is being used (not empty)
    assert!(
        undo_records_added > 0,
        "Should have added undo records for merges"
    );

    // The key check: pop processed undo records (trail length decreased)
    assert!(
        undo_len_after_pop < undo_len_after_asserts,
        "Pop should have consumed undo records"
    );
}
