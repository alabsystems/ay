// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The nested search's session cache (M4, `session.rs`): rebuilding a known
//! quantifier term over its cached constants, seeding, and the store-epoch
//! binding that retires the cache on compaction and on any rollback below
//! what it holds. End-to-end incremental behaviour is pinned in
//! `executor_tests/quantifier/qlra/m4_incremental.rs`.

use ay_core::{Sort, TermId, TermStore};

use super::approx::NInstance;
use super::ntree::{build_nested_tree_reusing, NestedTree};
use super::session::NestedSessionCache;

fn binder(name: &str) -> Vec<(String, Sort)> {
    vec![(name.to_string(), Sort::Real)]
}

/// `∀x ∃y. y > x + c`: a universal node with one existential child.
fn nested_root(terms: &mut TermStore) -> TermId {
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let c = terms.mk_var("c", Sort::Real);
    let sum = terms.mk_add(vec![x, c]);
    let gt = terms.mk_gt(y, sum);
    let inner = terms.mk_exists(binder("y"), gt);
    terms.mk_forall(binder("x"), inner)
}

/// One fake (but well-formed) instance per node: `true`.
fn one_instance_each(terms: &mut TermStore, tree: &NestedTree) -> Vec<Vec<NInstance>> {
    let truth = terms.mk_bool(true);
    tree.nodes
        .iter()
        .map(|_| {
            vec![NInstance {
                tuple: Vec::new(),
                frozen: truth,
                round: 0,
            }]
        })
        .collect()
}

fn populated(terms: &mut TermStore, root: TermId) -> (NestedSessionCache, NestedTree) {
    let tree = build_nested_tree_reusing(terms, &[root], None).expect("tree");
    let gamma = one_instance_each(terms, &tree);
    let exact = vec![true; tree.nodes.len()];
    let mut cache = NestedSessionCache::default();
    cache.record(terms, &tree, &gamma, &exact);
    assert_eq!(cache.len(), tree.nodes.len(), "every node is cached");
    (cache, tree)
}

#[test]
fn a_rebuilt_tree_reuses_the_cached_constants_and_is_seeded() {
    let mut terms = TermStore::new();
    let root = nested_root(&mut terms);
    let (mut cache, first) = populated(&mut terms, root);
    assert!(cache.validate(&terms));

    let second = build_nested_tree_reusing(&mut terms, &[root], Some(&cache)).expect("tree");
    assert_eq!(second.nodes.len(), first.nodes.len());
    for (a, b) in first.nodes.iter().zip(&second.nodes) {
        assert_eq!(a.ce_vars, b.ce_vars, "cached constants are reused");
        assert_eq!(
            a.ce_body, b.ce_body,
            "so the bodies hash-cons to the same terms"
        );
    }
    let seed = cache.seed(&second);
    assert_eq!(seed.hits, second.nodes.len());
    assert!(seed.exact.iter().all(|&e| e));
    assert!(seed.gamma.iter().all(|g| g.len() == 1));

    // Without the cache the builder mints fresh constants: nothing matches.
    let fresh = build_nested_tree_reusing(&mut terms, &[root], None).expect("tree");
    assert_ne!(fresh.nodes[0].ce_vars, first.nodes[0].ce_vars);
    assert_eq!(cache.seed(&fresh).hits, 0, "a fresh tree is not seeded");
}

#[test]
fn compaction_retires_the_cache() {
    let mut terms = TermStore::new();
    let root = nested_root(&mut terms);
    let (mut cache, _) = populated(&mut terms, root);
    assert!(cache.validate(&terms));
    let _remap = terms.mark_and_compact(&[root]);
    assert!(
        !cache.validate(&terms),
        "a compaction epoch change must clear the cache"
    );
    assert_eq!(cache.len(), 0);
    let tree = build_nested_tree_reusing(&mut terms, &[root], Some(&cache)).expect("tree");
    assert_eq!(cache.seed(&tree).hits, 0);
}

#[test]
fn a_rollback_above_the_cache_keeps_it_and_one_below_clears_it() {
    let mut terms = TermStore::new();
    let root = nested_root(&mut terms);
    let (mut cache, tree) = populated(&mut terms, root);

    // Above: a scratch suffix minted after the cache was written.
    let checkpoint = terms.rollback_checkpoint();
    let at = terms.len();
    let _scratch = terms.mk_fresh_var("scratch", Sort::Real);
    let survives = cache.survives_rollback_to(&terms, at);
    terms.rollback_to(checkpoint);
    assert!(survives);
    assert!(
        !cache.is_valid_for(&terms),
        "any rollback advances the store generation"
    );
    cache.rebind_after_rollback(&terms, survives);
    assert!(cache.validate(&terms), "re-bound: every cached id is alive");
    assert_eq!(cache.len(), tree.nodes.len());

    // Below: a checkpoint taken before the cached constants existed.
    let mut terms = TermStore::new();
    let root = nested_root(&mut terms);
    let checkpoint = terms.rollback_checkpoint();
    let at = terms.len();
    let (mut cache, _) = populated(&mut terms, root);
    let survives = cache.survives_rollback_to(&terms, at);
    terms.rollback_to(checkpoint);
    assert!(!survives, "the rollback recycles cached constants");
    cache.rebind_after_rollback(&terms, survives);
    assert_eq!(cache.len(), 0);
    assert!(!cache.validate(&terms));
}

#[test]
fn a_foreign_rollback_clears_the_cache() {
    // A rollback that does not go through the lane's re-binding (any other
    // structural epoch change) retires the cache even when it only discarded
    // ids above it: the cache cannot tell, so it fails closed.
    let mut terms = TermStore::new();
    let root = nested_root(&mut terms);
    let (mut cache, _) = populated(&mut terms, root);
    let checkpoint = terms.rollback_checkpoint();
    let _scratch = terms.mk_fresh_var("scratch", Sort::Real);
    terms.rollback_to(checkpoint);
    assert!(!cache.validate(&terms));
    assert_eq!(cache.len(), 0);
}
