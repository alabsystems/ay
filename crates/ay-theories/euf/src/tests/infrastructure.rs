// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
mod backtracking;
mod fixed_point_integrity;

#[test]
#[serial]
fn test_euf_conflict_from_implied_equality() {
    let mut store = TermStore::new();
    let u = Sort::Uninterpreted("U".to_string());

    let a = store.mk_var("a", u.clone());
    let b = store.mk_var("b", u.clone());
    let c = store.mk_var("c", u);

    let eq_ac = store.mk_eq(a, c);
    let eq_cb = store.mk_eq(c, b);
    let eq_ab = store.mk_eq(a, b);

    let mut euf = EufSolver::new(&store);
    euf.assert_literal(eq_ac, true);
    euf.assert_literal(eq_cb, true);
    euf.assert_literal(eq_ab, false);

    assert!(matches!(euf.check(), TheoryResult::Unsat(_)));
}

#[test]
fn test_euf_distinct_conflict() {
    let mut store = TermStore::new();
    let u = Sort::Uninterpreted("U".to_string());

    let a = store.mk_var("a", u.clone());
    let b = store.mk_var("b", u);

    let eq_ab = store.mk_eq(a, b);
    let distinct_ab = store.mk_distinct(vec![a, b]);

    let mut euf = EufSolver::new(&store);
    euf.assert_literal(eq_ab, true);
    euf.assert_literal(distinct_ab, true);

    assert!(matches!(euf.check(), TheoryResult::Unsat(_)));
}

#[test]
#[serial]
fn test_euf_predicate_congruence_conflict() {
    let mut store = TermStore::new();
    let u = Sort::Uninterpreted("U".to_string());

    let a = store.mk_var("a", u.clone());
    let b = store.mk_var("b", u);

    let eq_ab = store.mk_eq(a, b);
    let p_a = store.mk_app(Symbol::named("p"), vec![a], Sort::Bool);
    let p_b = store.mk_app(Symbol::named("p"), vec![b], Sort::Bool);

    let mut euf = EufSolver::new(&store);
    euf.assert_literal(eq_ab, true);
    euf.assert_literal(p_a, true);
    euf.assert_literal(p_b, false);

    assert!(matches!(euf.check(), TheoryResult::Unsat(_)));
}

#[test]
fn test_euf_predicate_congruence_sat() {
    let mut store = TermStore::new();
    let u = Sort::Uninterpreted("U".to_string());

    let a = store.mk_var("a", u.clone());
    let b = store.mk_var("b", u);

    let eq_ab = store.mk_eq(a, b);
    let p_a = store.mk_app(Symbol::named("p"), vec![a], Sort::Bool);
    let p_b = store.mk_app(Symbol::named("p"), vec![b], Sort::Bool);

    let mut euf = EufSolver::new(&store);
    euf.assert_literal(eq_ab, true);
    euf.assert_literal(p_a, true);
    euf.assert_literal(p_b, true);

    assert!(matches!(euf.check(), TheoryResult::Sat));
}

#[test]
#[serial]
fn test_euf_bool_alias_chain_conflict_via_biconditional_ite_6881() {
    let mut store = TermStore::new();
    let u = Sort::Uninterpreted("U".to_string());

    let x = store.mk_var("x", u.clone());
    let y = store.mk_var("y", u.clone());
    let z = store.mk_var("z", u.clone());
    let b_alias = store.mk_var("b_alias", Sort::Bool);
    let b_mid = store.mk_var("b_mid", Sort::Bool);
    let pred_z = store.mk_app(Symbol::named("pred"), vec![z], Sort::Bool);
    let eq_xy = store.mk_eq(x, y);
    let eq_alias_atom = store.mk_eq(b_alias, eq_xy);
    let eq_alias_mid = store.mk_eq(b_alias, b_mid);
    let eq_seed = store.mk_eq(b_mid, pred_z);
    let h_eq_xy = store.mk_app(Symbol::named("h"), vec![eq_xy], u.clone());
    let h_pred_z = store.mk_app(Symbol::named("h"), vec![pred_z], u);
    let eq_h_terms = store.mk_eq(h_eq_xy, h_pred_z);

    let mut euf = EufSolver::new(&store);
    euf.assert_literal(eq_alias_atom, true);
    euf.assert_literal(eq_alias_mid, true);
    euf.assert_literal(eq_seed, true);
    euf.assert_literal(eq_h_terms, false);

    assert!(
        matches!(euf.check(), TheoryResult::Unsat(_)),
        "Bool alias biconditionals must decode as equalities for EUF"
    );
}

#[test]
fn test_extract_model_function_table_canonicalizes_bool_args() {
    let mut store = TermStore::new();
    let u = Sort::Uninterpreted("U".to_string());

    let b = store.mk_var("b", Sort::Bool);
    let x = store.mk_var("x", u.clone());
    let _f_b_x = store.mk_app(Symbol::named("f"), vec![b, x], u);

    let mut euf = EufSolver::new(&store);
    euf.assert_literal(b, false);
    assert!(matches!(euf.check(), TheoryResult::Sat));

    let model = euf.extract_model();
    let table = model
        .function_tables
        .get("f")
        .expect("f table should be present in extracted model");
    assert!(
        table
            .iter()
            .all(|(args, _)| args.first().map(String::as_str) == Some("false")),
        "bool argument keys must be canonical true/false: {table:?}"
    );
}

#[test]
fn test_extract_model_scope_excludes_dead_predicates_6813() {
    let mut store = TermStore::new();
    let u = Sort::Uninterpreted("U".to_string());

    let a = store.mk_var("a", u.clone());
    let b = store.mk_var("b", u);
    let eq_ab = store.mk_eq(a, b);
    let _p_a = store.mk_app(Symbol::named("p"), vec![a], Sort::Bool);
    let p_b = store.mk_app(Symbol::named("p"), vec![b], Sort::Bool);

    let mut euf = EufSolver::new(&store);
    euf.assert_literal(eq_ab, true);
    euf.assert_literal(p_b, true);
    assert!(matches!(euf.check(), TheoryResult::Sat));

    euf.scope_model_to_roots(&[eq_ab, p_b]);
    let model = euf.extract_model();
    euf.clear_model_scope();

    let table = model
        .function_tables
        .get("p")
        .expect("p table should be present in extracted model");
    assert_eq!(
        table,
        &vec![(vec!["@U!0".to_string()], "true".to_string())],
        "scoped model extraction must ignore unreachable predicate terms: {table:?}"
    );
}

// Phase 1 infrastructure tests.

#[test]
fn test_enode_initialization() {
    // Test that ENode data structures initialize correctly
    let mut store = TermStore::new();
    let u = Sort::Uninterpreted("U".to_string());

    let a = store.mk_var("a", u.clone());
    let b = store.mk_var("b", u.clone());
    let f_a = store.mk_app(Symbol::named("f"), vec![a], u.clone());
    let f_b = store.mk_app(Symbol::named("f"), vec![b], u);
    let _eq_fa_fb = store.mk_eq(f_a, f_b);

    let mut euf = EufSolver::new(&store);

    // Force initialization
    euf.init_enodes();

    // Verify enodes were created for all terms
    assert_eq!(euf.enodes.len(), store.len());

    // Verify initial state: each node is its own root
    for (i, enode) in euf.enodes.iter().enumerate() {
        assert_eq!(
            enode.root, i as u32,
            "Each node should be its own root initially"
        );
        assert_eq!(
            enode.next, i as u32,
            "Each node should point to itself in circular list"
        );
        assert_eq!(
            enode.class_size, 1,
            "Each class should have size 1 initially"
        );
    }

    // Verify parent pointers: a and b should be parents of f_a and f_b respectively
    assert!(
        euf.enodes[a.0 as usize].parents.contains(&(f_a.0)),
        "a should have f(a) as parent"
    );
    assert!(
        euf.enodes[b.0 as usize].parents.contains(&(f_b.0)),
        "b should have f(b) as parent"
    );
}

#[test]
fn test_congruence_table_initialization() {
    // Test that congruence table is populated correctly
    let mut store = TermStore::new();
    let u = Sort::Uninterpreted("U".to_string());

    let a = store.mk_var("a", u.clone());
    let b = store.mk_var("b", u.clone());
    let _f_a = store.mk_app(Symbol::named("f"), vec![a], u.clone());
    let _f_b = store.mk_app(Symbol::named("f"), vec![b], u);

    let mut euf = EufSolver::new(&store);
    euf.init_enodes();

    // Congruence table should have entries for f(a) and f(b)
    // Since a != b initially, they have different signatures
    assert_eq!(
        euf.cong_table.table_len(),
        2,
        "Should have 2 distinct function applications"
    );
}

#[test]
fn test_signature_equality() {
    // Test that compact u128 signature comparison works correctly (#5575).
    // Create 5 singleton enodes so root[i] == i.
    let enodes: Vec<ENode> = (0..5).map(ENode::new).collect();
    let args123 = [1u32, 2, 3];
    let args124 = [1u32, 2, 4]; // different third argument

    let sig1 = CongruenceTable::make_signature(12345, &args123, &enodes);
    let sig2 = CongruenceTable::make_signature(12345, &args123, &enodes);
    let sig3 = CongruenceTable::make_signature(12345, &args124, &enodes);

    assert_eq!(sig1, sig2, "Same signatures should be equal");
    assert_ne!(sig1, sig3, "Different argument reps should be unequal");
}

/// Test that CongruenceTable.insert() returns matches on signature collision,
/// and that caller-side verification can distinguish true congruence from
/// hash collisions (#6153).
#[test]
fn test_congruence_table_collision_safety() {
    let mut table = CongruenceTable::new();
    let enodes: Vec<ENode> = (0..5).map(ENode::new).collect();

    // Insert term 10 with signature for f(1, 2)
    let sig_f12 = CongruenceTable::make_signature(100, &[1, 2], &enodes);
    assert!(
        table.insert(10, sig_f12).is_none(),
        "First insert should succeed"
    );

    // Insert term 20 with same signature — simulates true congruence
    let result = table.insert(20, sig_f12);
    assert_eq!(
        result,
        Some(10),
        "Second insert with same sig should return existing"
    );

    // Now simulate a collision: same u128 value but different func/args.
    // In production, the caller verifies func_hash + arg reps match before
    // trusting this result. Here we verify the table returns a match even
    // for collisions (it's the caller's job to reject).
    // Different term, same forced signature:
    let result2 = table.insert(30, sig_f12);
    assert_eq!(
        result2,
        Some(10),
        "Collision: table returns existing term for same sig"
    );

    // Verify that inserting the same term ID is a no-op
    let result3 = table.insert(10, sig_f12);
    assert!(
        result3.is_none(),
        "Re-inserting same term_id should return None"
    );
}

#[test]
fn test_enode_find_simple() {
    // Test the enode_find function
    let mut store = TermStore::new();
    let u = Sort::Uninterpreted("U".to_string());

    let a = store.mk_var("a", u.clone());
    let _b = store.mk_var("b", u);

    let mut euf = EufSolver::new(&store);
    euf.init_enodes();

    // Initially, each node is its own representative
    let rep = euf.enode_find(a.0);
    assert_eq!(rep, a.0, "Initial representative should be self");
}

#[test]
fn test_reset_clears_incremental_state() {
    // Test that reset() properly clears incremental state
    let mut store = TermStore::new();
    let u = Sort::Uninterpreted("U".to_string());

    let a = store.mk_var("a", u.clone());
    let b = store.mk_var("b", u);
    let eq_ab = store.mk_eq(a, b);

    let mut euf = EufSolver::new(&store);

    // Initialize and use
    euf.assert_literal(eq_ab, true);
    euf.init_enodes();
    assert!(euf.enodes_init);
    assert!(!euf.enodes.is_empty());

    // Reset
    euf.reset();

    // Verify state is cleared
    assert!(!euf.enodes_init, "enodes_init should be false after reset");
    assert!(euf.enodes.is_empty(), "enodes should be empty after reset");
    assert!(
        euf.cong_table.table_is_empty(),
        "cong_table should be empty after reset"
    );
    assert!(
        euf.to_merge.is_empty(),
        "to_merge should be empty after reset"
    );
    assert!(
        euf.undo_trail.is_empty(),
        "undo_trail should be empty after reset"
    );
}
