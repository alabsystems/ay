// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn ground_occurrences_agree_full_incremental_in_both_orders() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let f_x = terms.mk_app(Symbol::named("f"), vec![x], Sort::Int);
    let p_fx = terms.mk_app(Symbol::named("P"), vec![f_x], Sort::Bool);
    let quantified = terms.mk_forall(vec![("x".to_string(), Sort::Int)], p_fx);

    for roots in [[quantified, p_fx], [p_fx, quantified]] {
        let mut incremental = PersistentMatchState::new();
        incremental.refresh_index(&terms, &roots[..1]);
        incremental.refresh_index(&terms, &roots);
        let full = TermIndex::new(&terms, &roots);
        assert_eq!(incremental.index().get_by_symbol("f"), &[f_x]);
        assert_eq!(
            incremental.index().get_by_symbol("f"),
            full.get_by_symbol("f")
        );
        assert_eq!(
            incremental.index().get_by_symbol("P"),
            full.get_by_symbol("P")
        );
        assert_eq!(
            collect_ground_terms_by_sort(&terms, &roots)[&Sort::Int],
            vec![x, f_x]
        );
    }
    let binder_only = TermIndex::new(&terms, &[quantified]);
    assert!(binder_only.get_by_symbol("f").is_empty());
    assert!(!collect_ground_terms_by_sort(&terms, &[quantified])
        .get(&Sort::Int)
        .is_some_and(|values| values.contains(&f_x)));
}

#[test]
fn ground_occurrences_drop_retracted_free_candidate_at_epoch_reset() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let f_x = terms.mk_app(Symbol::named("f"), vec![x], Sort::Int);
    let body = terms.mk_app(Symbol::named("P"), vec![f_x], Sort::Bool);
    let quantified = terms.mk_forall(vec![("x".to_string(), Sort::Int)], body);
    let mut state = PersistentMatchState::new();

    state.refresh_index(&terms, &[quantified, body]);
    assert_eq!(state.index().get_by_symbol("f"), &[f_x]);
    state.begin_epoch(0);
    state.refresh_index(&terms, &[quantified]);
    assert!(state.index().get_by_symbol("f").is_empty());
    assert_eq!(
        state.index().get_by_symbol("f"),
        TermIndex::new(&terms, &[quantified]).get_by_symbol("f")
    );
}

#[test]
fn ground_occurrences_ignore_unasserted_quantifiers() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let f_x = terms.mk_app(Symbol::named("f"), vec![x], Sort::Int);
    let p_fx = terms.mk_app(Symbol::named("P"), vec![f_x], Sort::Bool);
    let _unasserted = terms.mk_forall(vec![("x".to_string(), Sort::Int)], p_fx);

    assert_eq!(TermIndex::new(&terms, &[p_fx]).get_by_symbol("f"), &[f_x]);
    let mut incremental = PersistentMatchState::new();
    incremental.refresh_index(&terms, &[p_fx]);
    assert_eq!(incremental.index().get_by_symbol("f"), &[f_x]);
    assert_eq!(
        collect_ground_terms_by_sort(&terms, &[p_fx])[&Sort::Int],
        vec![x, f_x]
    );
}

#[test]
fn ground_occurrences_restore_repeated_binder_names_and_visit_all_children() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let f_x = terms.mk_app(Symbol::named("f"), vec![x], Sort::Int);
    let g_y = terms.mk_app(Symbol::named("g"), vec![y], Sort::Int);
    let inner_body = terms.mk_app(Symbol::named("Inner"), vec![f_x], Sort::Bool);
    let inner = terms.mk_forall(vec![("x".to_string(), Sort::Int)], inner_body);
    let outer_body = terms.mk_app(Symbol::named("Outer"), vec![inner, f_x, g_y], Sort::Bool);
    let outer = terms.mk_forall(vec![("x".to_string(), Sort::Int)], outer_body);

    let index = TermIndex::new(&terms, &[outer]);
    assert!(
        index.get_by_symbol("f").is_empty(),
        "outer x remains bound after inner x pops"
    );
    assert_eq!(
        index.get_by_symbol("g"),
        &[g_y],
        "later free sibling is still visited"
    );
    assert_eq!(
        collect_ground_terms_by_sort(&terms, &[outer])[&Sort::Int],
        vec![y, g_y]
    );
}

#[test]
fn bool_uf_arguments_are_ground_at_their_own_occurrence() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let c = terms.mk_var("c", Sort::Bool);
    let h_c = terms.mk_app(Symbol::named("H"), vec![c], Sort::Bool);
    let bound_c = terms.mk_forall(vec![("c".to_string(), Sort::Bool)], h_c);
    let _unasserted = bound_c;
    assert_eq!(collect_bool_uf_arg_terms(&terms, &[h_c]), vec![c]);
    assert!(collect_bool_uf_arg_terms(&terms, &[bound_c]).is_empty());

    let mixed = terms.mk_app(Symbol::named("Mixed"), vec![x, c], Sort::Bool);
    let bound_x = terms.mk_forall(vec![("x".to_string(), Sort::Int)], mixed);
    assert_eq!(collect_bool_uf_arg_terms(&terms, &[bound_x]), vec![c]);
    assert_eq!(collect_bool_uf_arg_terms(&terms, &[bound_c, h_c]), vec![c]);
    assert_eq!(collect_bool_uf_arg_terms(&terms, &[h_c, bound_c]), vec![c]);
}

/// A C-API-style binder and free occurrence can share the exact same term ID.
/// This checks the E-matcher itself, so MBQI cannot mask a missing index entry.
#[test]
fn ground_occurrences_drive_ematching_for_shared_binder_and_free_term() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let f_x = terms.mk_app(Symbol::named("f"), vec![x], Sort::Int);
    let body = terms.mk_app(Symbol::named("P"), vec![f_x], Sort::Bool);
    let quantified = terms.mk_forall(vec![("x".to_string(), Sort::Int)], body);
    let free_goal = terms.mk_not(body);

    for assertions in [[quantified, free_goal], [free_goal, quantified]] {
        let result = perform_ematching(&mut terms, &assertions);
        assert!(
            result.instantiations.contains(&body),
            "the free occurrence of the shared P(f(x)) must trigger its own body instance"
        );
        assert!(
            result
                .unconditional_forall_instantiations
                .iter()
                .any(|witness| {
                    witness.quantifier == quantified
                        && witness.binding == [x]
                        && witness.instance == body
                }),
            "E-matching must record the exact shared-TermId binding and instance"
        );
    }
}

/// The round cache hands every quantifier of a round exactly the map a fresh
/// collection over the same seed builds, even after the round added terms
/// and quantifiers to the store, and recomputes for a different seed.
#[test]
fn ground_terms_round_equals_a_fresh_collection() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let c = terms.mk_var("c", Sort::Int);
    let f_x = terms.mk_app(Symbol::named("f"), vec![x], Sort::Int);
    let f_c = terms.mk_app(Symbol::named("f"), vec![c], Sort::Int);
    let p_fx = terms.mk_app(Symbol::named("P"), vec![f_x], Sort::Bool);
    let p_fc = terms.mk_app(Symbol::named("P"), vec![f_c], Sort::Bool);
    let quantified = terms.mk_forall(vec![("x".to_string(), Sort::Int)], p_fx);
    let seed = [quantified, p_fc];

    let mut round = GroundTermsRound::default();
    assert_eq!(
        round.by_sort(&terms, &seed),
        &collect_ground_terms_by_sort(&terms, &seed)
    );
    // The round adds an instance and an unasserted quantifier over `c`.
    let p_c = terms.mk_app(Symbol::named("P"), vec![c], Sort::Bool);
    let _unasserted = terms.mk_forall(vec![("c".to_string(), Sort::Int)], p_c);
    assert_eq!(
        round.by_sort(&terms, &seed),
        &collect_ground_terms_by_sort(&terms, &seed)
    );
    assert_eq!(round.by_sort(&terms, &seed)[&Sort::Int], vec![c, f_c]);
    // A different seed is recomputed, not served from the cache.
    let other = [quantified, p_fx];
    assert_eq!(
        round.by_sort(&terms, &other),
        &collect_ground_terms_by_sort(&terms, &other)
    );
    assert_eq!(round.by_sort(&terms, &other)[&Sort::Int], vec![x, f_x]);
}

/// A shared DAG with 2^40 root-to-leaf paths is collected once per node.
#[test]
fn ground_terms_walk_a_shared_dag_once_per_node() {
    let mut terms = TermStore::new();
    let mut top = terms.mk_var("leaf", Sort::Int);
    let mut nodes = vec![top];
    for _ in 0..40 {
        top = terms.mk_app(Symbol::named("g"), vec![top, top], Sort::Int);
        nodes.push(top);
    }
    let root = terms.mk_app(Symbol::named("P"), vec![top], Sort::Bool);
    let mut collected = collect_ground_terms_by_sort(&terms, &[root])[&Sort::Int].clone();
    collected.sort_unstable_by_key(|t| t.0);
    nodes.sort_unstable_by_key(|t| t.0);
    assert_eq!(collected, nodes);
}
