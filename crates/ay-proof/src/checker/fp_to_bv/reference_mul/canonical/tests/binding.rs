// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn negated_complete_clause_uses_every_ordered_literal_not_a_selected_subset() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    let negative = terms.mk_not_raw(a);
    let mut live = || ControlFlow::Continue(());
    let mut work = WorkBudget::new(50_000_000, &mut live);
    let mut proof = capture_clause(&terms, &[a, negative], &limits(), &mut work)
        .expect("complete tautological clause");
    proof.replay().expect("same complete ordered negated roots");
    drop(proof);
    assert!(matches!(
        capture_clause(&terms, &[a], &limits(), &mut work),
        Err(Error::Search(ay_sat::ResolutionProofError::Satisfiable))
    ));
    assert!(capture_clause(&terms, &[], &limits(), &mut work).is_err());
}

#[test]
fn every_original_root_is_preserved_in_order_and_extra_roots_refuse_binding() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    let not_a = app(&mut terms, "not", &[a], Sort::Bool);
    let unrelated = terms.mk_var("b", Sort::Bool);
    let mut live = || ControlFlow::Continue(());
    let mut work = WorkBudget::new(50_000_000, &mut live);
    let mut proof =
        capture(&terms, &[a, not_a], &limits(), &mut work).expect("actual two-root contradiction");
    assert!(matches!(
        replay_for(
            &terms,
            &[not_a, a],
            &proof.dag,
            &proof.limits,
            &mut *proof.work
        ),
        Err(Error::Binding)
    ));
    assert!(matches!(
        replay_for(
            &terms,
            &[a, not_a, unrelated],
            &proof.dag,
            &proof.limits,
            &mut *proof.work
        ),
        Err(Error::Binding)
    ));
    assert!(matches!(
        replay_for(&terms, &[a], &proof.dag, &proof.limits, &mut *proof.work),
        Err(Error::Binding)
    ));
    proof.replay().expect("all originals still healthy");
}

#[test]
fn missing_added_changed_reordered_clause_inventory_never_replays() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    let not_a = app(&mut terms, "not", &[a], Sort::Bool);
    let mut live = || ControlFlow::Continue(());
    let mut work = WorkBudget::new(50_000_000, &mut live);
    let mut proof =
        capture(&terms, &[a, not_a], &limits(), &mut work).expect("full original contradiction");
    let mut changed = proof.dag.clone();
    changed.original_clauses.pop();
    assert!(matches!(
        replay_for(
            &terms,
            &[a, not_a],
            &changed,
            &proof.limits,
            &mut *proof.work
        ),
        Err(Error::Binding)
    ));
    let mut changed = proof.dag.clone();
    changed.original_clauses.push((999, Vec::new())); // hidden overconstraint
    assert!(matches!(
        replay_for(
            &terms,
            &[a, not_a],
            &changed,
            &proof.limits,
            &mut *proof.work
        ),
        Err(Error::Binding)
    ));
    let mut changed = proof.dag.clone();
    changed.original_clauses[0].1[0] = changed.original_clauses[0].1[0].negated();
    assert!(matches!(
        replay_for(
            &terms,
            &[a, not_a],
            &changed,
            &proof.limits,
            &mut *proof.work
        ),
        Err(Error::Binding)
    ));
    let mut changed = proof.dag.clone();
    changed.original_clauses.swap(0, 1);
    assert!(matches!(
        replay_for(
            &terms,
            &[a, not_a],
            &changed,
            &proof.limits,
            &mut *proof.work
        ),
        Err(Error::Binding)
    ));
}

#[test]
fn changed_refutation_hints_empty_clause_and_variable_namespace_refuse() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    let not_a = app(&mut terms, "not", &[a], Sort::Bool);
    let mut live = || ControlFlow::Continue(());
    let mut work = WorkBudget::new(50_000_000, &mut live);
    let mut proof = capture(&terms, &[a, not_a], &limits(), &mut work).expect("source refutation");
    let mut changed = proof.dag.clone();
    changed.num_vars += 1;
    assert!(matches!(
        replay_for(
            &terms,
            &[a, not_a],
            &changed,
            &proof.limits,
            &mut *proof.work
        ),
        Err(Error::Binding)
    ));
    let mut changed = proof.dag.clone();
    changed.empty_clause_id = u64::MAX;
    assert!(matches!(
        replay_for(
            &terms,
            &[a, not_a],
            &changed,
            &proof.limits,
            &mut *proof.work
        ),
        Err(Error::Replay(_))
    ));
    let mut changed = proof.dag.clone();
    changed
        .derived
        .last_mut()
        .expect("empty derivation")
        .rup_hints
        .clear();
    assert!(matches!(
        replay_for(
            &terms,
            &[a, not_a],
            &changed,
            &proof.limits,
            &mut *proof.work
        ),
        Err(Error::Replay(_))
    ));
}

#[test]
fn missing_cyclic_noncanonical_and_wrong_interchange_width_sources_decline() {
    let mut terms = TermStore::new();
    let word = terms.mk_var("raw", Sort::bitvec(3)); // needs4
    let wrong = raw(&mut terms, word, 2, 2);
    let root = opposite_equal(&mut terms, wrong, wrong);
    let mut live = || ControlFlow::Continue(());
    let mut work = WorkBudget::new(10_000_000, &mut live);
    assert!(capture(&terms, &[root], &limits(), &mut work).is_err());
    assert!(capture(&terms, &[TermId::SENTINEL], &limits(), &mut work).is_err());
    let mut entries = terms.entries_snapshot();
    entries[root.index()] = (TermData::Not(root), Sort::Bool);
    let cyclic = TermStore::from_entries(entries, None, None, terms.var_counter());
    assert!(capture(&cyclic, &[root], &limits(), &mut work).is_err());
    let mut entries = terms.entries_snapshot();
    entries[word.index()] = (
        TermData::Const(Constant::BitVec {
            value: (-1i8).into(),
            width: 3,
        }),
        Sort::bitvec(3),
    );
    let bad = TermStore::from_entries(entries, None, None, terms.var_counter());
    assert!(capture(&bad, &[root], &limits(), &mut work).is_err());
}

#[test]
fn false_root_does_not_skip_unsupported_division_or_unknown_boolean_app() {
    let mut terms = TermStore::new();
    let zero = terms.mk_bool(false);
    let word = terms.mk_var("raw", Sort::bitvec(4));
    let x = raw(&mut terms, word, 2, 2);
    let rm = app(
        &mut terms,
        "RNE",
        &[],
        Sort::Uninterpreted("RoundingMode".into()),
    );
    let div = app(&mut terms, "fp.div", &[rm, x, x], Sort::FloatingPoint(2, 2));
    let root = opposite_equal(&mut terms, div, div);
    let unknown = app(&mut terms, "unsupported_bool", &[zero], Sort::Bool);
    for unsupported in [root, unknown] {
        let mut live = || ControlFlow::Continue(());
        let mut work = WorkBudget::new(10_000_000, &mut live);
        assert!(capture(&terms, &[zero, unsupported], &limits(), &mut work).is_err());
    }
}
