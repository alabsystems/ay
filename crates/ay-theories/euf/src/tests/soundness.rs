// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

// ========================================================================
// PROOF TEST: P0 #110 - EUF Bounds Check Vulnerability
// ========================================================================

#[test]
fn test_proof_enode_find_const_bounds_safety() {
    let mut store = TermStore::new();
    let u = Sort::Uninterpreted("U".to_string());

    let a = store.mk_var("a", u.clone());
    let b = store.mk_var("b", u);
    let _eq = store.mk_eq(a, b);

    let mut euf = EufSolver::new(&store);
    euf.init_enodes();

    assert_eq!(
        euf.enodes.len(),
        store.len(),
        "enodes should be sized to term store"
    );

    let rep_a = euf.enode_find_const(a.0);
    assert_eq!(rep_a, a.0, "Valid term should find itself initially");
}

#[test]
#[serial]
fn test_proof_pop_undo_replay_bounds_safety() {
    let mut store = TermStore::new();
    let u = Sort::Uninterpreted("U".to_string());

    let a = store.mk_var("a", u.clone());
    let b = store.mk_var("b", u.clone());
    let c = store.mk_var("c", u);
    let eq_ab = store.mk_eq(a, b);
    let eq_bc = store.mk_eq(b, c);

    let mut euf = new_incremental_euf(&store);
    euf.init_enodes();

    euf.push();
    euf.assert_literal(eq_ab, true);
    euf.assert_literal(eq_bc, true);
    euf.incremental_rebuild();

    let undo_count = euf.undo_trail.len();
    assert!(undo_count > 0, "Should have undo records after merges");

    euf.pop();

    assert!(
        euf.undo_trail.len() < undo_count,
        "Pop should consume undo records"
    );
}

#[test]
#[serial]
fn test_proof_check_diseq_bounds_safety() {
    let mut store = TermStore::new();
    let u = Sort::Uninterpreted("U".to_string());

    let a = store.mk_var("a", u.clone());
    let b = store.mk_var("b", u.clone());
    let c = store.mk_var("c", u);

    let eq_ac = store.mk_eq(a, c);
    let eq_cb = store.mk_eq(c, b);
    let eq_ab = store.mk_eq(a, b);

    let mut euf = new_incremental_euf(&store);

    euf.assert_literal(eq_ac, true);
    euf.assert_literal(eq_cb, true);
    euf.assert_literal(eq_ab, false);

    let result = euf.check();
    assert!(
        matches!(result, TheoryResult::Unsat(_)),
        "Should detect conflict from transitivity + disequality"
    );
}

// ========================================================================
// Nelson-Oppen Incremental Tests (#318)
// ========================================================================

#[test]
#[serial]
fn test_pop_clears_propagated_eqs_for_asserted_equalities() {
    let mut store = TermStore::new();
    let u = Sort::Uninterpreted("U".to_string());

    let a = store.mk_var("a", u.clone());
    let b = store.mk_var("b", u);
    let eq_ab = store.mk_eq(a, b);

    let mut euf = EufSolver::new(&store);

    euf.push();
    euf.assert_literal(eq_ab, true);
    assert!(matches!(euf.check(), TheoryResult::Sat));
    let equalities = euf.propagate_equalities().equalities;
    assert!(
        has_discovered_equality(&equalities, a, b),
        "expected asserted equality to be propagated"
    );
    euf.pop();

    euf.push();
    euf.assert_literal(eq_ab, true);
    assert!(matches!(euf.check(), TheoryResult::Sat));
    let equalities = euf.propagate_equalities().equalities;
    assert!(
        has_discovered_equality(&equalities, a, b),
        "expected asserted equality to be re-propagated after pop()"
    );
}

#[test]
#[serial]
fn test_pop_clears_propagated_eq_pairs_for_congruence_equalities() {
    let mut store = TermStore::new();

    let a = store.mk_var("a", Sort::Int);
    let b = store.mk_var("b", Sort::Int);
    let eq_ab = store.mk_eq(a, b);

    let f = Symbol::named("f");
    let f_a = store.mk_app(f.clone(), vec![a], Sort::Int);
    let f_b = store.mk_app(f, vec![b], Sort::Int);

    let mut euf = EufSolver::new(&store);

    euf.push();
    euf.assert_literal(eq_ab, true);
    assert!(matches!(euf.check(), TheoryResult::Sat));
    let equalities = euf.propagate_equalities().equalities;
    assert!(
        has_discovered_equality(&equalities, f_a, f_b),
        "expected congruence-derived equality to be propagated"
    );
    euf.pop();

    euf.push();
    euf.assert_literal(eq_ab, true);
    assert!(matches!(euf.check(), TheoryResult::Sat));
    let equalities = euf.propagate_equalities().equalities;
    assert!(
        has_discovered_equality(&equalities, f_a, f_b),
        "expected congruence-derived equality to be re-propagated after pop()"
    );
}

#[test]
fn test_pop_clears_shared_equalities() {
    let mut store = TermStore::new();
    let u = Sort::Uninterpreted("U".to_string());

    let a = store.mk_var("a", u.clone());
    let b = store.mk_var("b", u);
    let eq_ab = store.mk_eq(a, b);

    let mut euf = EufSolver::new(&store);

    euf.assert_literal(eq_ab, false);

    euf.push();
    euf.assert_shared_equality(a, b, &[]);
    assert!(matches!(euf.check(), TheoryResult::Unsat(_)));
    euf.pop();

    assert!(matches!(euf.check(), TheoryResult::Sat));
}

#[test]
fn test_pop_clears_pending_propagations() {
    let mut store = TermStore::new();
    let u = Sort::Uninterpreted("U".to_string());

    let a = store.mk_var("a", u.clone());
    let b = store.mk_var("b", u);
    let eq_ab = store.mk_eq(a, b);

    let mut euf = EufSolver::new(&store);

    euf.push();
    euf.assert_literal(eq_ab, true);
    assert!(matches!(euf.check(), TheoryResult::Sat));
    euf.pop();

    let equalities = euf.propagate_equalities().equalities;
    assert!(
        equalities.is_empty(),
        "expected pending_propagations to be cleared on pop()"
    );
}

fn assert_reflexive_equality_is_not_propagated(use_incremental: bool) {
    let mut store = TermStore::new();
    let u = Sort::Uninterpreted("U".to_string());
    let a = store.mk_var("a", u);
    let eq_aa = store.mk_app(Symbol::named("="), vec![a, a], Sort::Bool);

    let _ = use_incremental; // parameter reserved for future non-incremental path
    let mut euf = new_incremental_euf(&store);

    euf.assert_literal(eq_aa, true);
    assert!(
        matches!(euf.check(), TheoryResult::Sat),
        "asserting a raw reflexive equality atom should stay SAT"
    );

    let equalities = euf.propagate_equalities().equalities;
    assert!(
        equalities.is_empty(),
        "reflexive equality must not be forwarded via Nelson-Oppen: {equalities:?}"
    );
}

#[test]
#[serial]
fn test_legacy_reflexive_equalities_are_not_propagated() {
    assert_reflexive_equality_is_not_propagated(false);
}

#[test]
#[serial]
fn test_incremental_reflexive_equalities_are_not_propagated() {
    assert_reflexive_equality_is_not_propagated(true);
}

proptest! {
    #![proptest_config(ProptestConfig {
        cases: 64,
        max_shrink_iters: 0,
        .. ProptestConfig::default()
    })]

    #[test]
    #[serial]
    fn proptest_pop_repropagates_congruence_equalities(
        (num_vars, i, j) in (2u8..=4u8).prop_flat_map(|n| (Just(n), 0u8..n, 0u8..n))
            .prop_filter("distinct indices", |(_, i, j)| i != j)
    ) {
        let mut store = TermStore::new();
        let vars: Vec<_> = (0..num_vars)
            .map(|k| store.mk_var(format!("x{k}"), Sort::Int))
            .collect();

        let f = Symbol::named("f");
        let f_apps: Vec<_> = vars
            .iter()
            .map(|&v| store.mk_app(f.clone(), vec![v], Sort::Int))
            .collect();

        let a = vars[i as usize];
        let b = vars[j as usize];
        let f_a = f_apps[i as usize];
        let f_b = f_apps[j as usize];
        let eq_ab = store.mk_eq(a, b);

        let mut euf = EufSolver::new(&store);

        euf.push();
        euf.assert_literal(eq_ab, true);
        prop_assert!(matches!(euf.check(), TheoryResult::Sat));
        let equalities = euf.propagate_equalities().equalities;
        prop_assert!(has_discovered_equality(&equalities, a, b));
        prop_assert!(has_discovered_equality(&equalities, f_a, f_b));
        euf.pop();

        euf.push();
        euf.assert_literal(eq_ab, true);
        prop_assert!(matches!(euf.check(), TheoryResult::Sat));
        let equalities = euf.propagate_equalities().equalities;
        prop_assert!(has_discovered_equality(&equalities, a, b));
        prop_assert!(has_discovered_equality(&equalities, f_a, f_b));
    }
}

// ========================================================================
// Phase 2 Verification Tests - EUF Conflict Soundness (#298)
// ========================================================================

#[test]
fn test_euf_conflict_explanation_soundness() {
    let mut store = TermStore::new();
    let u = Sort::Uninterpreted("U".to_string());

    let a = store.mk_var("a", u.clone());
    let b = store.mk_var("b", u.clone());
    let c = store.mk_var("c", u);

    let eq_ab = store.mk_eq(a, b);
    let eq_bc = store.mk_eq(b, c);
    let eq_ac = store.mk_eq(a, c);

    let mut euf = EufSolver::new(&store);
    euf.assert_literal(eq_ab, true);
    euf.assert_literal(eq_bc, true);
    euf.assert_literal(eq_ac, false);

    let result = euf.check();
    let conflict = assert_conflict_soundness(result, EufSolver::new(&store));
    assert!(conflict.iter().any(|l| l.term == eq_ac && !l.value));
}

#[test]
fn test_euf_congruence_conflict_soundness() {
    let mut store = TermStore::new();
    let u = Sort::Uninterpreted("U".to_string());

    let a = store.mk_var("a", u.clone());
    let b = store.mk_var("b", u.clone());
    let f_a = store.mk_app(Symbol::named("f"), vec![a], u.clone());
    let f_b = store.mk_app(Symbol::named("f"), vec![b], u);

    let eq_ab = store.mk_eq(a, b);
    let eq_fa_fb = store.mk_eq(f_a, f_b);

    let mut euf = EufSolver::new(&store);
    euf.assert_literal(eq_ab, true);
    euf.assert_literal(eq_fa_fb, false);

    let result = euf.check();
    assert_conflict_soundness(result, EufSolver::new(&store));
}

#[test]
fn test_euf_no_bogus_conflict_on_sat() {
    let mut store = TermStore::new();
    let u = Sort::Uninterpreted("U".to_string());

    let a = store.mk_var("a", u.clone());
    let b = store.mk_var("b", u.clone());
    let c = store.mk_var("c", u);

    let eq_ab = store.mk_eq(a, b);
    let eq_bc = store.mk_eq(b, c);

    let mut euf = EufSolver::new(&store);
    euf.assert_literal(eq_ab, false);
    euf.assert_literal(eq_bc, false);

    assert!(matches!(euf.check(), TheoryResult::Sat));
}

#[test]
fn test_euf_long_chain_conflict_soundness() {
    let mut store = TermStore::new();
    let u = Sort::Uninterpreted("U".to_string());

    let x: Vec<_> = (0..5)
        .map(|i| store.mk_var(format!("x{i}"), u.clone()))
        .collect();
    let equalities: Vec<_> = (0..4).map(|i| store.mk_eq(x[i], x[i + 1])).collect();
    let diseq_0_4 = store.mk_eq(x[0], x[4]);

    let mut euf = EufSolver::new(&store);
    for eq in &equalities {
        euf.assert_literal(*eq, true);
    }
    euf.assert_literal(diseq_0_4, false);

    let result = euf.check();
    let conflict = assert_conflict_soundness(result, EufSolver::new(&store));
    assert!(conflict.len() <= 6, "Got {} literals", conflict.len());
}

// ========================================================================
// Shared Equality Reason Tests (#320)
// ========================================================================

#[test]
#[serial]
fn test_shared_equality_reasons_in_conflict_explanation() {
    let mut store = TermStore::new();
    let u = Sort::Uninterpreted("U".to_string());

    let a = store.mk_var("a", u.clone());
    let b = store.mk_var("b", u.clone());
    let f_a = store.mk_app(Symbol::named("f"), vec![a], u.clone());
    let f_b = store.mk_app(Symbol::named("f"), vec![b], u);

    let r1 = store.mk_var("r1", Sort::Bool);
    let r2 = store.mk_var("r2", Sort::Bool);

    let eq_fa_fb = store.mk_eq(f_a, f_b);

    let mut euf = EufSolver::new(&store);

    euf.assert_literal(r1, true);
    euf.assert_literal(r2, true);
    euf.assert_literal(eq_fa_fb, false);

    let reason = vec![TheoryLit::new(r1, true), TheoryLit::new(r2, true)];
    euf.assert_shared_equality(a, b, &reason);

    let result = euf.check();
    let TheoryResult::Unsat(conflict) = result else {
        panic!("Expected UNSAT (congruence conflict), got {result:?}");
    };

    let has_r1 = conflict.iter().any(|l| l.term == r1 && l.value);
    let has_r2 = conflict.iter().any(|l| l.term == r2 && l.value);
    let has_diseq = conflict.iter().any(|l| l.term == eq_fa_fb && !l.value);

    assert!(
        has_diseq,
        "Conflict should contain disequality f(a)!=f(b), got: {conflict:?}"
    );
    assert!(
        has_r1,
        "Conflict should contain shared reason r1=true, got: {conflict:?}"
    );
    assert!(
        has_r2,
        "Conflict should contain shared reason r2=true, got: {conflict:?}"
    );

    assert!(
        conflict.len() >= 3,
        "Conflict should have at least 3 literals: r1, r2, and disequality; got {conflict:?}"
    );
}

#[test]
#[serial]
fn test_shared_equality_reasons_cleared_on_pop() {
    let mut store = TermStore::new();
    let u = Sort::Uninterpreted("U".to_string());

    let a = store.mk_var("a", u.clone());
    let b = store.mk_var("b", u.clone());
    let f_a = store.mk_app(Symbol::named("f"), vec![a], u.clone());
    let f_b = store.mk_app(Symbol::named("f"), vec![b], u);
    let r1 = store.mk_var("r1", Sort::Bool);
    let r2 = store.mk_var("r2", Sort::Bool);

    let eq_fa_fb = store.mk_eq(f_a, f_b);

    let mut euf = EufSolver::new(&store);

    euf.assert_literal(r1, true);
    euf.assert_literal(r2, true);
    euf.assert_literal(eq_fa_fb, false);

    euf.push();
    euf.assert_shared_equality(a, b, &[TheoryLit::new(r1, true)]);
    let result = euf.check();
    assert!(matches!(result, TheoryResult::Unsat(_)));
    euf.pop();

    assert!(matches!(euf.check(), TheoryResult::Sat));

    euf.push();
    euf.assert_shared_equality(a, b, &[TheoryLit::new(r2, true)]);
    let result = euf.check();
    let TheoryResult::Unsat(conflict) = result else {
        panic!("Expected UNSAT, got {result:?}");
    };

    let has_r2 = conflict.iter().any(|l| l.term == r2 && l.value);
    let has_r1 = conflict.iter().any(|l| l.term == r1 && l.value);
    assert!(has_r2, "Conflict should contain r2 from current branch");
    assert!(!has_r1, "Conflict should NOT contain r1 from popped branch");
}

#[test]
#[serial]
fn test_shared_equality_reasons_in_transitivity() {
    let mut store = TermStore::new();
    let u = Sort::Uninterpreted("U".to_string());

    let a = store.mk_var("a", u.clone());
    let b = store.mk_var("b", u.clone());
    let c = store.mk_var("c", u);
    let r = store.mk_var("r", Sort::Bool);

    let eq_bc = store.mk_eq(b, c);
    let eq_ac = store.mk_eq(a, c);

    let mut euf = EufSolver::new(&store);

    euf.assert_literal(r, true);
    euf.assert_literal(eq_bc, true);
    euf.assert_literal(eq_ac, false);
    euf.assert_shared_equality(a, b, &[TheoryLit::new(r, true)]);

    let result = euf.check();
    let TheoryResult::Unsat(conflict) = result else {
        panic!("Expected UNSAT (transitivity conflict), got {result:?}");
    };

    let has_r = conflict.iter().any(|l| l.term == r && l.value);
    let has_bc = conflict.iter().any(|l| l.term == eq_bc && l.value);
    let has_diseq = conflict.iter().any(|l| l.term == eq_ac && !l.value);

    assert!(
        has_diseq,
        "Conflict should contain disequality a!=c, got: {conflict:?}"
    );
    assert!(has_bc, "Conflict should contain b=c, got: {conflict:?}");
    assert!(
        has_r,
        "Conflict should contain shared reason r=true, got: {conflict:?}"
    );
}

#[test]
#[serial]
fn test_shared_equality_reasons_incremental_mode() {
    let result = std::panic::catch_unwind(|| {
        let mut store = TermStore::new();
        let u = Sort::Uninterpreted("U".to_string());

        let a = store.mk_var("a", u.clone());
        let b = store.mk_var("b", u.clone());
        let f_a = store.mk_app(Symbol::named("f"), vec![a], u.clone());
        let f_b = store.mk_app(Symbol::named("f"), vec![b], u);
        let r1 = store.mk_var("r1", Sort::Bool);
        let r2 = store.mk_var("r2", Sort::Bool);

        let eq_fa_fb = store.mk_eq(f_a, f_b);

        let mut euf = new_incremental_euf(&store);

        euf.assert_literal(r1, true);
        euf.assert_literal(r2, true);
        euf.assert_literal(eq_fa_fb, false);

        let reason = vec![TheoryLit::new(r1, true), TheoryLit::new(r2, true)];
        euf.assert_shared_equality(a, b, &reason);

        let check_result = euf.check();
        let TheoryResult::Unsat(conflict) = check_result else {
            panic!("Expected UNSAT (congruence conflict), got {check_result:?}");
        };

        let has_r1 = conflict.iter().any(|l| l.term == r1 && l.value);
        let has_r2 = conflict.iter().any(|l| l.term == r2 && l.value);
        let has_diseq = conflict.iter().any(|l| l.term == eq_fa_fb && !l.value);

        assert!(
            has_diseq,
            "Conflict should contain disequality, got: {conflict:?}"
        );
        assert!(has_r1, "Conflict should contain r1=true, got: {conflict:?}");
        assert!(has_r2, "Conflict should contain r2=true, got: {conflict:?}");
    });

    if let Err(e) = result {
        std::panic::resume_unwind(e);
    }
}

// ============================================================================
// Incremental UF-mirror sync: dirty-node cover completeness (AY_EUF_INC_SYNC)
// ============================================================================

/// Random push/pop/merge sequences must leave the UF mirror (`uf.find`)
/// identical to the ground-truth E-graph partition (`are_equal`) after every
/// `check()`. The incremental dirty-node sync only refreshes nodes recorded as
/// dirty by merges and pop-undo; if that cover were ever incomplete, `uf.find`
/// would disagree with `are_equal` for some pair. This proptest hammers the
/// merge+backtrack interleaving that the static unit tests don't reach.
///
/// In debug builds the in-solver `debug_assert_eq!` self-check in
/// `sync_egraph_to_uf` also fires on every incremental sync, giving a second
/// independent witness.
#[test]
fn proptest_incremental_uf_sync_matches_full_under_push_pop() {
    let mut runner = proptest::test_runner::TestRunner::default();
    // ops: 0 = push, 1 = pop, 2 = assert next equality from the pool
    let strategy = proptest::collection::vec(0u8..3, 1..120);
    runner
        .run(&strategy, |ops| {
            let mut store = TermStore::new();
            let u = Sort::Uninterpreted("U".to_string());
            let n = 10usize;
            let vars: Vec<TermId> = (0..n)
                .map(|i| store.mk_var(format!("v{i}"), u.clone()))
                .collect();
            // A fixed pool of equalities connecting consecutive and wrap-around
            // pairs, so merges build up real chains.
            let mut eqs: Vec<TermId> = Vec::new();
            for i in 0..n {
                eqs.push(store.mk_eq(vars[i], vars[(i + 1) % n]));
                eqs.push(store.mk_eq(vars[i], vars[(i + 3) % n]));
            }

            let mut euf = new_incremental_euf(&store);
            let mut eq_cursor = 0usize;
            let mut depth = 0usize;

            for op in ops {
                match op {
                    0 => {
                        euf.push();
                        depth += 1;
                    }
                    1 => {
                        if depth > 0 {
                            euf.pop();
                            depth -= 1;
                        }
                    }
                    _ => {
                        if eq_cursor < eqs.len() {
                            euf.assert_literal(eqs[eq_cursor], true);
                            eq_cursor += 1;
                        }
                    }
                }
                // check() runs rebuild_closure → sync_egraph_to_uf (incremental).
                let _ = euf.check();
                euf.sync_egraph_to_uf();

                // Ground truth (are_equal via enode_find_const) must match the
                // UF mirror (uf.find) for every pair.
                for i in 0..n {
                    for j in (i + 1)..n {
                        let mirror_eq = euf.uf.find(vars[i].0) == euf.uf.find(vars[j].0);
                        let truth_eq = euf.are_equal(vars[i], vars[j]);
                        prop_assert_eq!(
                            mirror_eq,
                            truth_eq,
                            "UF mirror disagreed with E-graph for ({}, {})",
                            i,
                            j
                        );
                    }
                }
            }
            Ok(())
        })
        .unwrap();
}
