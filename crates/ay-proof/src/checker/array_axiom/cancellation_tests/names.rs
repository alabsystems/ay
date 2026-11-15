// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]

use super::*;

fn freshness_error(proof: &Proof, terms: &TermStore, roots: &[TermId]) {
    let result = ExtDiffRegistry::collect_with_progress(proof, terms, roots, &mut |_, _| true);
    assert!(
        matches!(result, Err(ProofCheckError::InvalidTheoryLemma { reason, .. })
        if reason.contains("NOT fresh") && reason.contains("`k`"))
    );
}

#[test]
fn authored_and_assumed_names_reject_even_distinct_term_ids_and_sorts() {
    let (mut terms, proof, k) = basic();
    let alias = terms.mk_var("k", Sort::Bool);
    assert_ne!(alias, k);
    freshness_error(&proof, &terms, &[alias]);
    every_poll(&proof, &terms, &[alias]);
    let mut assumed = proof.clone();
    assumed.steps.push(ProofStep::Assume(alias));
    freshness_error(&assumed, &terms, &[]);
    every_poll(&assumed, &terms, &[]);
}

#[test]
fn application_heads_let_and_quantifier_binders_and_triggers_stay_conservative() {
    let (mut terms, proof, k) = basic();
    let truth = terms.true_term();
    let zero = terms.mk_int(0.into());
    let named = terms.mk_app(Symbol::named("k"), vec![], Sort::Bool);
    let indexed = terms.mk_app(Symbol::indexed("k", vec![1]), vec![], Sort::Bool);
    let bound = terms.mk_let(vec![("k".to_owned(), zero)], truth);
    let forall = terms.mk_forall(vec![("k".to_owned(), Sort::Int)], truth);
    let exists = terms.mk_exists(vec![("k".to_owned(), Sort::Int)], truth);
    let trigger =
        terms.mk_forall_with_triggers(vec![("x".to_owned(), Sort::Int)], truth, vec![vec![k, k]]);
    for root in [named, indexed, bound, forall, exists, trigger] {
        freshness_error(&proof, &terms, &[root]);
        every_poll(&proof, &terms, &[root]);
    }
}

#[test]
fn duplicate_source_roots_and_dag_edges_are_each_polled_before_seen_rejection() {
    let (mut terms, proof, _) = basic();
    let p = terms.mk_var("p", Sort::Bool);
    let wide = terms.mk_app(Symbol::named("and"), vec![p; 4096], Sort::Bool);
    let roots = vec![wide; 64];
    let mut total = 0;
    let result = ExtDiffRegistry::collect_with_progress(&proof, &terms, &roots, &mut |_, _| {
        total += 1;
        true
    })
    .unwrap();
    assert_eq!(result.bindings.len(), 1);
    assert!(total >= 8192 + 64 * 2);
    for stop_at in [1, 4096, 8192, total - 1, total] {
        let mut calls = 0;
        let result = ExtDiffRegistry::collect_with_progress(&proof, &terms, &roots, &mut |_, _| {
            calls += 1;
            calls != stop_at
        });
        assert!(matches!(result, Err(ProofCheckError::ResourceLimit)));
        assert_eq!(calls, stop_at);
    }
}

#[test]
fn name_walker_preserves_not_ite_let_value_and_quantified_trigger_order() {
    let (mut terms, _, k) = basic();
    let condition = terms.mk_var("condition", Sort::Bool);
    let truth = terms.true_term();
    let negated = terms.mk_not(condition);
    let let_term = terms.mk_let(vec![("binder".to_owned(), k)], negated);
    let exists = terms.mk_exists_with_triggers(
        vec![("quantified".to_owned(), Sort::Int)],
        truth,
        vec![vec![k], vec![]],
    );
    let root = terms.mk_ite_raw(condition, let_term, exists);
    let mut names = det_hash_set_new();
    let mut seen = det_hash_set_new();
    let mut total = 0;
    collect_symbol_names(&terms, root, &mut names, &mut seen, &mut |_, _| {
        total += 1;
        true
    })
    .unwrap();
    let mut names: Vec<_> = names.into_iter().collect();
    names.sort();
    assert_eq!(names, ["binder", "condition", "k", "quantified"]);
    for stop_at in 1..=total {
        let mut calls = 0;
        let result = collect_symbol_names(
            &terms,
            root,
            &mut det_hash_set_new(),
            &mut det_hash_set_new(),
            &mut |_, _| {
                calls += 1;
                calls != stop_at
            },
        );
        assert!(matches!(result, Err(ProofCheckError::ResourceLimit)));
        assert_eq!(calls, stop_at);
    }
}

#[test]
fn empty_registry_keeps_legacy_no_freshness_scan_but_polls_final_admission() {
    let mut terms = TermStore::new();
    let k = terms.mk_var("k", Sort::Bool);
    let proof = Proof::from_steps(vec![ProofStep::Assume(k); 8]);
    every_poll(&proof, &terms, &[k; 8]);
    let mut calls = 0;
    let result = ExtDiffRegistry::collect_with_progress(&proof, &terms, &[k; 8], &mut |_, _| {
        calls += 1;
        true
    })
    .unwrap();
    assert!(result.is_empty());
    assert_eq!(
        calls,
        proof.steps.len() + 2,
        "entry, each proof step, final; no needless source walk"
    );
}
