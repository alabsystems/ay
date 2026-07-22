// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::{IncrementalNegationCache, TheoryLemmaSeenSet};
use ay_core::{Sort, TermStore, TheoryLit};

#[test]
fn negation_cache_seeds_once_and_syncs_only_pending_terms() {
    let mut terms = TermStore::new();
    let p = terms.mk_var("p", Sort::Bool);
    let q = terms.mk_var("q", Sort::Bool);

    let mut cache = IncrementalNegationCache::seed(&mut terms, [p], true);
    let seeded_p_not = *cache
        .as_map()
        .get(&p)
        .expect("seeded cache should contain the initial term");

    cache.note_fresh_term(p);
    cache.note_fresh_term(q);
    cache.note_fresh_term(q);

    assert_eq!(
        cache.as_map().len(),
        1,
        "pending terms must not materialize before sync"
    );

    cache.sync_pending(&mut terms);

    assert_eq!(
        cache.as_map().len(),
        2,
        "sync should materialize exactly one fresh negation"
    );
    assert_eq!(
        cache.as_map().get(&p),
        Some(&seeded_p_not),
        "sync must not rebuild existing negations"
    );
    assert_eq!(
        cache.as_map().get(&q),
        Some(&terms.mk_not(q)),
        "sync should materialize the pending term's negation"
    );
}

#[test]
fn theory_lemma_seen_set_uses_canonical_clause_semantics_issue_8785() {
    let mut terms = TermStore::new();
    let p = terms.mk_var("p", Sort::Bool);
    let q = terms.mk_var("q", Sort::Bool);
    let mut seen = TheoryLemmaSeenSet::default();

    assert!(seen.insert(&[TheoryLit::new(p, true), TheoryLit::new(q, false)]));
    assert!(
        !seen.insert(&[TheoryLit::new(p, true), TheoryLit::new(q, false)]),
        "identical clauses should deduplicate"
    );
    assert!(
        !seen.insert(&[TheoryLit::new(q, false), TheoryLit::new(p, true)]),
        "clause order should not make the same disjunction look fresh"
    );
    assert!(
        seen.insert(&[TheoryLit::new(q, true), TheoryLit::new(p, true)]),
        "literal polarity remains part of the clause key"
    );
}
