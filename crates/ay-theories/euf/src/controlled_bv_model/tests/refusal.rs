// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn unprepared_and_poisoned_states_refuse_without_rebuild_or_scope_mutation() {
    let (terms, roots, assignments) = fixture(8, false);
    let fresh = EufSolver::new(&terms);
    assert!(matches!(
        measured(&fresh, &roots, u64::MAX, usize::MAX).0,
        Err(QueryError::Exhausted)
    ));
    assert!(!fresh.enodes_init);
    let mut source = prepare(&terms, &assignments);
    let before = source.uf.parent.clone();
    source.dirty = true;
    assert!(matches!(
        measured(&source, &roots, u64::MAX, usize::MAX).0,
        Err(QueryError::Exhausted)
    ));
    assert!(source.dirty);
    assert_eq!(source.uf.parent, before);
    source.dirty = false;
    source.poisoned = true;
    assert!(matches!(
        measured(&source, &roots, u64::MAX, usize::MAX).0,
        Err(QueryError::Exhausted)
    ));
}

#[test]
fn unsupported_unrelated_live_domains_refuse_without_legacy_fallback() {
    let end = Instant::now() + Duration::from_secs(20);
    for sort in [
        Sort::Int,
        Sort::Real,
        Sort::Uninterpreted("U".into()),
        Sort::bitvec(0),
        Sort::bitvec(129),
        Sort::array(Sort::bitvec(8), Sort::array(Sort::bitvec(8), Sort::Bool)),
    ] {
        let mut terms = TermStore::new();
        let root = terms.mk_var("accepted", Sort::bitvec(8));
        let _unrelated = terms.mk_var("unsupported", sort);
        let source = prepare(&terms, &[]);
        assert!(matches!(
            measured(&source, &[root], u64::MAX, usize::MAX).0,
            Err(QueryError::Exhausted)
        ));
        assert!(source.model_term_scope.is_none());
        assert!(Instant::now() < end);
    }
}

#[test]
fn user_functions_and_store_nodes_refuse_including_unchosen_children() {
    let mut terms = TermStore::new();
    let value = terms.mk_var("v", Sort::bitvec(8));
    let foreign = terms.mk_app(Symbol::named("foreign"), [value], Sort::bitvec(8));
    let cond = terms.mk_var("cond", Sort::Bool);
    let root = terms.mk_ite_raw(cond, value, foreign);
    let source = prepare(&terms, &[]);
    assert!(matches!(
        measured(&source, &[root], u64::MAX, usize::MAX).0,
        Err(QueryError::Exhausted)
    ));
    let mut terms = TermStore::new();
    let array = terms.mk_var(
        "a",
        Sort::array(
            Sort::bitvec(8),
            Sort::array(Sort::bitvec(8), Sort::bitvec(8)),
        ),
    );
    let value = terms.mk_bitvec(0u8.into(), 8);
    let nested = terms.mk_var("nested", Sort::array(Sort::bitvec(8), Sort::bitvec(8)));
    let store = terms.mk_app(
        Symbol::named("store"),
        [array, value, nested],
        terms.sort(array).clone(),
    );
    let source = prepare(&terms, &[]);
    assert!(matches!(
        measured(&source, &[store], u64::MAX, usize::MAX).0,
        Err(QueryError::Exhausted)
    ));
}

#[test]
fn dead_roots_and_corrupt_class_edges_refuse_before_indexing() {
    let mut terms = TermStore::new();
    let value = terms.mk_var("v", Sort::bitvec(8));
    let mut source = prepare(&terms, &[]);
    assert!(measured(&source, &[TermId(u32::MAX)], u64::MAX, usize::MAX)
        .0
        .is_err());
    source.enodes[value.0 as usize].next = u32::MAX;
    assert!(matches!(
        measured(&source, &[value], u64::MAX, usize::MAX).0,
        Err(QueryError::Exhausted)
    ));
}

#[test]
fn mismatched_uf_mirror_and_nonterminating_parent_walk_refuse() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::bitvec(8));
    let b = terms.mk_var("b", Sort::bitvec(8));
    let mut source = prepare(&terms, &[]);
    source.uf.parent[a.0 as usize] = b.0;
    assert!(matches!(
        measured(&source, &[a], u64::MAX, usize::MAX).0,
        Err(QueryError::Exhausted)
    ));
    source.uf.parent[a.0 as usize] = a.0;
    source.enodes[a.0 as usize].root = b.0;
    source.enodes[b.0 as usize].root = a.0;
    assert!(matches!(
        measured(&source, &[a], u64::MAX, usize::MAX).0,
        Err(QueryError::Exhausted)
    ));
}
